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

`Positioning`
- Timelog's wedge is **O(1) out-of-order append** and **snapshot-safe concurrent reads over live Python objects**: appends stay cheap even when timestamps arrive out of order, and independent threads read consistent snapshots while writes proceed.
- It is *not positioned as* the fastest static range-query index. Range scans are fast, but the differentiator is out-of-order ingestion plus concurrency over Python objects — not winning every static benchmark.

`Out of scope`
- Timelog is not a distributed database.
- Timelog is not a vectorized analytics engine for payloads.
