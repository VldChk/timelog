# Formal specifications

## Abstract contract

`formal/tla/Timelog_Abstract.tla` defines the abstract, user-visible correctness contract for timelog and is the **single source of truth** for externally observable behavior.

The model captures:
- state as records `(ts, handle, seq)`, tombstones `([a,b), seq)`, `nextSeq`, and snapshots `snapId -> snapSeq`
- visibility (`rec.seq <= snapSeq` and `max_tomb_seq(ts, snapSeq) < rec.seq`)
- query behavior for half-open ranges `[t1, t2)`
- exact-point query behavior with duplicates preserved

Use `formal/tla/Timelog_Abstract.cfg` to run bounded TLC exploration with constants for `TS`, `Handles`, `MaxSeq`, and `SnapIds`.
