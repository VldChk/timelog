# Internals: Write Path

Sources:
- `core/src/tl_timelog.c`
- `core/src/delta/tl_memtable.*`
- `core/src/delta/tl_flush.*`

## Flow

1. Append/delete enters mutable memtable state.
2. In-order records append to active run.
3. Out-of-order records append to OOO head and are chunk-flushed into immutable OOO runs.
4. Memtable seals into immutable memrun objects.
5. Flush builds immutable L0 segments and publishes via manifest swap.

## Data Structures (Current)

- active run + seq vector
- OOO head + seq vector
- immutable OOO runset
- coalesced tombstone intervals
- fixed-capacity sealed memrun ring queue

## Write-Path Guarantees

`Contract`
- All writes first enter the L0/delta path.
- `append_batch` provides all-or-nothing semantics for failure classes that return no commit.

`Implementation note`
- Busy/backpressure may occur after write acceptance; see error semantics doc.
