---- MODULE Timelog_Abstract ----
EXTENDS Naturals, Sequences

(***************************************************************************
Abstract Timelog model used as the refinement target for Timelog_Impl.
***************************************************************************)

CONSTANTS RecordDomain, SnapshotDomain, QueryDomain

VARIABLES records, tombstones, snapshots, queryResult

AbsVars == <<records, tombstones, snapshots, queryResult>>

AbsTypeOK ==
    /\ records \subseteq RecordDomain
    /\ tombstones \subseteq RecordDomain
    /\ snapshots \subseteq SnapshotDomain
    /\ queryResult \in QueryDomain

AbsInit ==
    /\ records = {}
    /\ tombstones = {}
    /\ snapshots = {}
    /\ queryResult \in QueryDomain

AbsNext ==
    /\ records' \subseteq RecordDomain
    /\ tombstones' \subseteq RecordDomain
    /\ snapshots' \subseteq SnapshotDomain
    /\ queryResult' \in QueryDomain

Spec == AbsInit /\ [][AbsNext]_AbsVars

====
