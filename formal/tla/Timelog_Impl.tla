---- MODULE Timelog_Impl ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************
Implementation-level Timelog model with an explicit refinement mapping to
Timelog_Abstract.
***************************************************************************)

CONSTANTS RecordDomain, SnapshotDomain, QueryDomain

VARIABLES
    ghostRecords,
    logRecords,
    tombstoneSet,
    snapshotCuts,
    queryOut,
    watermark,
    sourcePins,
    snapshotPins

ImplVars ==
    << ghostRecords,
       logRecords,
       tombstoneSet,
       snapshotCuts,
       queryOut,
       watermark,
       sourcePins,
       snapshotPins >>

(***************************************************************************
Refinement mapping:
  - abstract records from ghost/log records
  - abstract tombstones from modeled tombstone set
  - abstract snapshots from impl snapshot sequence cuts
  - query outputs mapped directly
***************************************************************************)

ImplRecords == ghostRecords \cup logRecords

ImplSnapshots == {snapshotCuts[i] : i \in 1..Len(snapshotCuts)}

Abs == INSTANCE Timelog_Abstract
    WITH records <- ImplRecords,
         tombstones <- tombstoneSet,
         snapshots <- ImplSnapshots,
         queryResult <- queryOut

TypeCorrectness ==
    /\ ghostRecords \subseteq RecordDomain
    /\ logRecords \subseteq RecordDomain
    /\ tombstoneSet \subseteq RecordDomain
    /\ snapshotCuts \in Seq(SnapshotDomain)
    /\ queryOut \in QueryDomain
    /\ watermark \in Nat
    /\ sourcePins \in Nat
    /\ snapshotPins \in Nat

WatermarkMonotonic == watermark >= Cardinality(ImplSnapshots)

SourcePinningConstraint == snapshotPins <= sourcePins

SnapshotPinningConstraint ==
    /\ snapshotPins = 0 => Len(snapshotCuts) = 0
    /\ sourcePins = 0 => snapshotPins = 0

Init ==
    /\ ghostRecords = {}
    /\ logRecords = {}
    /\ tombstoneSet = {}
    /\ snapshotCuts = <<>>
    /\ queryOut \in QueryDomain
    /\ watermark = 0
    /\ sourcePins = 0
    /\ snapshotPins = 0

Insert(r) ==
    /\ r \in RecordDomain
    /\ ghostRecords' = ghostRecords \cup {r}
    /\ logRecords' = logRecords \cup {r}
    /\ UNCHANGED <<tombstoneSet, snapshotCuts, queryOut, sourcePins, snapshotPins>>
    /\ watermark' = watermark + 1

Delete(r) ==
    /\ r \in RecordDomain
    /\ tombstoneSet' = tombstoneSet \cup {r}
    /\ logRecords' = logRecords \ {r}
    /\ ghostRecords' = ghostRecords
    /\ UNCHANGED <<snapshotCuts, queryOut, sourcePins, snapshotPins>>
    /\ watermark' = watermark + 1

Flush ==
    /\ sourcePins > 0
    /\ snapshotCuts' = Append(snapshotCuts, watermark)
    /\ UNCHANGED <<ghostRecords, logRecords, tombstoneSet, queryOut, sourcePins, snapshotPins>>
    /\ watermark' = watermark

Compact ==
    /\ sourcePins = 0
    /\ ghostRecords' = ghostRecords \ tombstoneSet
    /\ logRecords' = logRecords \ tombstoneSet
    /\ tombstoneSet' = {}
    /\ snapshotCuts' = <<>>
    /\ UNCHANGED <<queryOut, sourcePins, snapshotPins>>
    /\ watermark' = watermark

PinSource ==
    /\ sourcePins' = sourcePins + 1
    /\ UNCHANGED <<ghostRecords, logRecords, tombstoneSet, snapshotCuts, queryOut, watermark, snapshotPins>>

UnpinSource ==
    /\ sourcePins > 0
    /\ sourcePins' = sourcePins - 1
    /\ snapshotPins <= sourcePins'
    /\ UNCHANGED <<ghostRecords, logRecords, tombstoneSet, snapshotCuts, queryOut, watermark, snapshotPins>>

PinSnapshot ==
    /\ sourcePins > snapshotPins
    /\ snapshotPins' = snapshotPins + 1
    /\ UNCHANGED <<ghostRecords, logRecords, tombstoneSet, snapshotCuts, queryOut, watermark, sourcePins>>

UnpinSnapshot ==
    /\ snapshotPins > 0
    /\ snapshotPins' = snapshotPins - 1
    /\ IF snapshotPins' = 0 THEN snapshotCuts' = <<>> ELSE snapshotCuts' = snapshotCuts
    /\ UNCHANGED <<ghostRecords, logRecords, tombstoneSet, queryOut, watermark, sourcePins>>

Query(q) ==
    /\ q \in QueryDomain
    /\ queryOut' = q
    /\ UNCHANGED <<ghostRecords, logRecords, tombstoneSet, snapshotCuts, watermark, sourcePins, snapshotPins>>

Next ==
    \/ \E r \in RecordDomain : Insert(r)
    \/ \E r \in RecordDomain : Delete(r)
    \/ Flush
    \/ Compact
    \/ PinSource
    \/ UnpinSource
    \/ PinSnapshot
    \/ UnpinSnapshot
    \/ \E q \in QueryDomain : Query(q)

Spec == Init /\ [][Next]_ImplVars

Refinement == Abs!Spec

====
