----------------------------- MODULE Timelog_Abstract -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*******************************************************************************
Abstract user-visible contract for timelog.

State:
  - recs:       set of records [ts, handle, seq]
  - tombs:      set of tombstones [a, b, seq] representing [a, b)
  - nextSeq:    next sequence number to allocate
  - snapshots:  mapping snapId -> snapSeq

Visibility:
  record r is visible in snapshot sid iff
    r.seq <= snapshots[sid]
    /\ MaxTombSeqAt(r.ts, snapshots[sid]) < r.seq
*******************************************************************************)

CONSTANTS TS, Handles, MaxSeq, SnapIds

VARIABLES recs, tombs, nextSeq, snapshots

vars == << recs, tombs, nextSeq, snapshots >>

Record(ts, h, s) == [ts |-> ts, handle |-> h, seq |-> s]
Tomb(a, b, s)   == [a |-> a, b |-> b, seq |-> s]

RecordType(r) ==
  /\ r \in [ts : TS, handle : Handles, seq : 1..MaxSeq]

TombType(t) ==
  /\ t \in [a : TS, b : TS, seq : 1..MaxSeq]
  /\ t.a < t.b

StateTypeInvariant ==
  /\ recs \subseteq { Record(ts, h, s) : ts \in TS, h \in Handles, s \in 1..MaxSeq }
  /\ tombs \subseteq { Tomb(a, b, s) : a \in TS, b \in TS, s \in 1..MaxSeq }
  /\ \A t \in tombs : t.a < t.b
  /\ nextSeq \in 1..(MaxSeq + 1)
  /\ snapshots \in [SnapIds -> 0..MaxSeq]

MonotoneSeqInvariant ==
  /\ \A r \in recs : r.seq < nextSeq
  /\ \A t \in tombs : t.seq < nextSeq

Init ==
  /\ recs = {}
  /\ tombs = {}
  /\ nextSeq = 1
  /\ snapshots = [sid \in SnapIds |-> 0]

Append ==
  /\ nextSeq <= MaxSeq
  /\ \E ts \in TS, h \in Handles :
       recs' = recs \cup { Record(ts, h, nextSeq) }
  /\ tombs' = tombs
  /\ snapshots' = snapshots
  /\ nextSeq' = nextSeq + 1

DeleteRange ==
  /\ nextSeq <= MaxSeq
  /\ \E a \in TS, b \in TS :
       /\ a < b
       /\ tombs' = tombs \cup { Tomb(a, b, nextSeq) }
  /\ recs' = recs
  /\ snapshots' = snapshots
  /\ nextSeq' = nextSeq + 1

AcquireSnapshot ==
  /\ \E sid \in SnapIds :
       snapshots' = [snapshots EXCEPT ![sid] = nextSeq - 1]
  /\ recs' = recs
  /\ tombs' = tombs
  /\ nextSeq' = nextSeq

Stutter ==
  /\ recs' = recs
  /\ tombs' = tombs
  /\ snapshots' = snapshots
  /\ nextSeq' = nextSeq

Next == Append \/ DeleteRange \/ AcquireSnapshot \/ Stutter

MaxTombSeqAt(ts, snapSeq) ==
  LET Covering == { t.seq : t \in tombs /\ t.a <= ts /\ ts < t.b /\ t.seq <= snapSeq } IN
    IF Covering = {} THEN 0 ELSE Max(Covering)

Visible(sid, r) ==
  /\ sid \in SnapIds
  /\ r \in recs
  /\ r.seq <= snapshots[sid]
  /\ MaxTombSeqAt(r.ts, snapshots[sid]) < r.seq

InRange(r, t1, t2) == t1 <= r.ts /\ r.ts < t2

VisibleRangeSet(sid, t1, t2) ==
  { r \in recs : Visible(sid, r) /\ InRange(r, t1, t2) }

CountInSeq(res, x) == Cardinality({ i \in DOMAIN res : res[i] = x })

(*******************************************************************************
Query semantics for [t1, t2):
  - result is a sequence over visible records in range
  - every visible record appears exactly once
  - duplicates are preserved because distinct records (e.g., same ts/handle but
    different seq) are separate elements and must each appear once
*******************************************************************************)
QueryOK(sid, t1, t2, res) ==
  /\ res \in Seq(VisibleRangeSet(sid, t1, t2))
  /\ \A r \in VisibleRangeSet(sid, t1, t2) : CountInSeq(res, r) = 1

(*******************************************************************************
Exact-point behavior (duplicates preserved):
  Point query at t is equivalent to [t, t+1) and returns all visible records with
  r.ts = t, including duplicates.
*******************************************************************************)
PointQuerySet(sid, t) ==
  { r \in recs : Visible(sid, r) /\ r.ts = t }

PointQueryOK(sid, t, res) ==
  /\ res \in Seq(PointQuerySet(sid, t))
  /\ \A r \in PointQuerySet(sid, t) : CountInSeq(res, r) = 1

Spec == Init /\ [][Next]_vars

THEOREM TypeSafety == Spec => []StateTypeInvariant

=============================================================================
