# What Is Timelog

Timelog is a native-C, in-memory, time-indexed multimap for Python.

`Contract`
- Primary key is `timestamp` (`int64`).
- Range semantics are half-open: `[t1, t2)`.
- Duplicate timestamps are allowed and preserved.
- Reads are snapshot-consistent.
- Writes require external single-writer coordination.

`Problem solved`
- Timestamp-driven systems repeatedly need queries like "all rows in `[t1, t2)`" and "drop rows before `t_cutoff`".
- Generic Python containers are not designed for efficient time-range navigation and retention.
- Timelog provides a lightweight embedded index for these operations without requiring a full TSDB.

`Implementation note`
- Timelog uses a mutable ingest layer (memtable), immutable paged segments, and background/manual maintenance (flush/compaction).
- The design is LSM-inspired but specialized for in-memory timestamp indexing.

`Out of scope`
- Timelog is not a distributed database.
- Timelog is not a vectorized analytics engine for payloads.
