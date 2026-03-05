# Internals: Tombstone Watermark Model

This page documents the current sequencing model used to decide record visibility under tombstones.

Sources:
- `core/src/internal/tl_intervals.*`
- `core/src/query/tl_filter.c`
- `core/src/query/tl_point.c`
- `core/src/delta/tl_flush.c`

## Model

- Tombstones carry sequence information (max-seq by interval fragments).
- Sources carry applied-seq/watermark context.
- Visibility rule is based on comparing tombstone sequence and source watermark.

`Implementation note`
- Filtering logic uses strict comparison semantics in core query/flush paths.
- This model supports snapshot-consistent delete visibility across mutable and immutable sources.

## Why It Exists

- Correctly handle interleaving of inserts/deletes across active, sealed, and segment sources.
- Preserve deterministic visibility semantics under compaction and publication races.
