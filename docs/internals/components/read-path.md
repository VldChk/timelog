# Internals: Read Path

Sources:
- `core/src/query/*`
- `core/src/query/tl_snapshot.c`

## Snapshot Acquisition (Current)

`Contract`
- Readers get a stable snapshot view for iterator lifetime.

`Implementation note`
- Snapshot capture uses writer lock + manifest acquire + memview capture/cache by epoch.
- Snapshot acquire does not run a standalone seqlock retry loop in current implementation.
- Seqlock remains part of publication consistency boundaries.

## Query Planning and Execution

1. Build source set from L1, L0, and memview.
2. Prune by range using segment/page metadata.
3. Build iterators per source.
4. K-way merge by timestamp.
5. Apply tombstone visibility filtering.

## Point vs Range

- Range iterators implement `[t1, t2)` semantics.
- Point lookup path is optimized but equivalent to exact timestamp semantics.

`Contract`
- API guarantee is non-decreasing timestamp output with duplicates preserved.
- Tie-order stability is not a public guarantee.
