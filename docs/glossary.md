# Glossary

- `L0`: Delta layer (memtable flush outputs), may overlap in time.
- `L1`: Main compacted layer, non-overlapping by configured windows.
- `Memtable`: Mutable ingest structure for records and tombstones.
- `Memrun`: Sealed immutable memtable unit queued for flush.
- `Memview`: Immutable snapshot capture of mutable/sealed memtable state.
- `Manifest`: Immutable catalog root for published segments.
- `Tombstone`: Logical delete interval `[t1, t2)`.
- `Watermark` / `applied_seq`: Sequence context used in tombstone visibility filtering.
- `OOO`: Out-of-order records relative to dominant ingest order.
- `Snapshot`: Consistent read view pinned for iterator lifetime.
