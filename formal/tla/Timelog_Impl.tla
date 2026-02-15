---- MODULE Timelog_Impl ----
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Timelog implementation sketch with mutable + immutable sequencing model. *)
(* Mirrors code identifiers in comments for traceability:                 *)
(*   - op_seq                                                              *)
(*   - applied_seq                                                         *)
(*   - tl_snapshot_acquire_internal                                        *)
(*   - tl_filter_iter_next                                                 *)
(*   - tl_compact_merge                                                    *)
(*   - tl_build_l0_segment_from_memrun                                     *)
(***************************************************************************)

CONSTANTS RecIds, Ts, Vals, SourceIds

NoSnapshot == "NO_SNAPSHOT"

SourceType(src) ==
  /\ src \in [wm : Nat, applied_seq : Nat, data : [RecIds -> [ts : Ts, val : Vals, seq : Nat] \cup {NULL}]]

VARIABLES op_seq, active, immutables, manifest, tomb_wm, snapshot

vars == <<op_seq, active, immutables, manifest, tomb_wm, snapshot>>

Init ==
  /\ op_seq = 0
  /\ active = [r \in RecIds |-> NULL]
  /\ immutables = [s \in SourceIds |-> [wm |-> 0, applied_seq |-> 0, data |-> [r \in RecIds |-> NULL]]]
  /\ manifest = {}
  /\ tomb_wm = [t \in Ts |-> 0]
  /\ snapshot = NoSnapshot

TypeOK ==
  /\ op_seq \in Nat
  /\ active \in [RecIds -> [ts : Ts, val : Vals, seq : Nat] \cup {NULL}]
  /\ immutables \in [SourceIds -> [wm : Nat, applied_seq : Nat, data : [RecIds -> [ts : Ts, val : Vals, seq : Nat] \cup {NULL}]]]
  /\ manifest \subseteq SourceIds
  /\ tomb_wm \in [Ts -> Nat]
  /\ snapshot \in {NoSnapshot} \cup {
       [manifest : SUBSET SourceIds,
        memview : [RecIds -> [ts : Ts, val : Vals, seq : Nat] \cup {NULL}],
        seq : Nat]
     }

Append(r, t, v) ==
  /\ r \in RecIds /\ t \in Ts /\ v \in Vals
  /\ op_seq' = op_seq + 1
  /\ active' = [active EXCEPT ![r] = [ts |-> t, val |-> v, seq |-> op_seq']]
  /\ UNCHANGED <<immutables, manifest, tomb_wm, snapshot>>

DeleteAt(t) ==
  /\ t \in Ts
  /\ op_seq' = op_seq + 1
  /\ tomb_wm' = [tomb_wm EXCEPT ![t] = IF @ > op_seq' THEN @ ELSE op_seq']
  /\ UNCHANGED <<active, immutables, manifest, snapshot>>

SnapshotAcquire ==
  (*************************************************************************)
  (* tl_snapshot_acquire_internal: capture (manifest + memview + op_seq). *)
  (*************************************************************************)
  /\ snapshot' = [manifest |-> manifest, memview |-> active, seq |-> op_seq]
  /\ UNCHANGED <<op_seq, active, immutables, manifest, tomb_wm>>

SnapshotRelease ==
  /\ snapshot # NoSnapshot
  /\ snapshot' = NoSnapshot
  /\ UNCHANGED <<op_seq, active, immutables, manifest, tomb_wm>>

Flush ==
  (*************************************************************************)
  (* Internal nondeterministic flush: tl_build_l0_segment_from_memrun.     *)
  (* Active mutable run becomes immutable source with applied_seq snapshot. *)
  (*************************************************************************)
  /\ \E s \in SourceIds \ manifest :
      /\ \E r \in RecIds : active[r] # NULL
      /\ immutables' = [immutables EXCEPT
            ![s] = [wm |-> op_seq, applied_seq |-> op_seq, data |-> active]]
      /\ manifest' = manifest \cup {s}
  /\ active' = [r \in RecIds |-> NULL]
  /\ UNCHANGED <<op_seq, tomb_wm, snapshot>>

MergeRec(a, b) ==
  IF a = NULL THEN b
  ELSE IF b = NULL THEN a
  ELSE IF a.seq >= b.seq THEN a ELSE b

Compact ==
  (*************************************************************************)
  (* Internal nondeterministic compaction: tl_compact_merge.               *)
  (*************************************************************************)
  /\ \E s1, s2, sout \in SourceIds :
      /\ s1 # s2 /\ s1 \in manifest /\ s2 \in manifest /\ sout \notin manifest
      /\ LET d1 == immutables[s1].data
             d2 == immutables[s2].data
             merged == [r \in RecIds |-> MergeRec(d1[r], d2[r])]
             newApplied == IF immutables[s1].applied_seq >= immutables[s2].applied_seq
                              THEN immutables[s1].applied_seq ELSE immutables[s2].applied_seq
             newWm == IF immutables[s1].wm >= immutables[s2].wm
                         THEN immutables[s1].wm ELSE immutables[s2].wm
         IN immutables' = [immutables EXCEPT
               ![sout] = [wm |-> newWm, applied_seq |-> newApplied, data |-> merged]]
      /\ manifest' = (manifest \ {s1, s2}) \cup {sout}
  /\ UNCHANGED <<op_seq, active, tomb_wm, snapshot>>

GCSource ==
  (*************************************************************************)
  (* Internal nondeterministic source GC / retirement.                     *)
  (*************************************************************************)
  /\ \E s \in manifest : manifest' = manifest \ {s}
  /\ UNCHANGED <<op_seq, active, immutables, tomb_wm, snapshot>>

TombAt(ts) == tomb_wm[ts]

ActiveVisible(snap, r) ==
  LET rec == snap.memview[r]
      wm  == IF rec = NULL THEN 0 ELSE rec.seq
  IN rec # NULL /\ TombAt(rec.ts) <= wm

ImmutableVisible(s, r) ==
  LET rec == immutables[s].data[r]
      wm  == immutables[s].applied_seq
  IN rec # NULL /\ TombAt(rec.ts) <= wm

QueryResult(snap) ==
  (*************************************************************************)
  (* tl_filter_iter_next rule:                                             *)
  (*   active uses per-record watermark (rec.seq)                          *)
  (*   immutable uses per-source watermark (applied_seq)                   *)
  (*************************************************************************)
  { <<"active", r, snap.memview[r].ts, snap.memview[r].seq>> :
      r \in RecIds /\ ActiveVisible(snap, r) }
  \cup
  { <<s, r, immutables[s].data[r].ts, immutables[s].data[r].seq>> :
      s \in snap.manifest /\ r \in RecIds /\ ImmutableVisible(s, r) }

QueryEnabled == snapshot # NoSnapshot

Next ==
  \E r \in RecIds, t \in Ts, v \in Vals : Append(r, t, v)
  \/ \E t \in Ts : DeleteAt(t)
  \/ SnapshotAcquire
  \/ SnapshotRelease
  \/ Flush
  \/ Compact
  \/ GCSource

Spec == Init /\ [][Next]_vars

Inv == TypeOK

=============================================================================
