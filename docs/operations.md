# Operations and Troubleshooting

## Lifecycle Safety

`Contract`
- `close()` is not a synchronization barrier for in-flight API calls; caller must ensure exclusive access for close.
- `close()` always discards ALL data (the engine is in-memory; `reopen()`
  starts empty). `flush()` is about visibility while the instance is OPEN:
  it materializes pending writes into immutable segments so `views()` /
  zero-copy readers can see them — it does not make anything survive close.
- Explicit `close()` can raise while active iterators, `PageSpan` instances, memoryview exports, or other snapshot pins are still alive. Release readers and buffer exports before closing.
- Scope-style usage (`log = Timelog()`) is supported. If the object is collected without explicit close, finalization auto-closes as a best-effort cleanup path.

## Maintenance Modes

- Background mode: worker auto-starts at open.
- Disabled mode: use `flush()` and `maint_step()` manually.

## Snapshot and Iterator Hygiene

- Acquire snapshot/iterator for read isolation.
- Destroy iterators before releasing their snapshot.

## Space Reclaim After Deletes (Retention Runbook)

- Deletes are logical tombstones. Query results respect them immediately; physical
  memory is reclaimed only when compaction rewrites the affected windows.
- In background mode the worker re-evaluates compaction triggers on every
  wake-up (default 100 ms): new L0 segments — including ones you publish
  with explicit `flush()` — and the `delete_debt_threshold` knob both fire
  without further writes once the tombstones have reached L0 segments.
- The standard retention pattern (background mode):
  `Timelog(delete_debt_threshold=0.2)`; on each retention tick call
  `cutoff(horizon)` then `flush()`. The flush lands the tombstone in L0;
  the worker then compacts and physically frees the dead records and their
  Python objects.
- Boundary: a tombstone that never reaches a segment (deletes issued with
  no flush and no further writes, on an idle instance) stays
  memtable-resident and reclaims nothing — call `flush()` after large
  deletes. In `maintenance="disabled"` mode run `flush()`, `compact()`,
  then `maint_step()` yourself.
- Released objects are freed via a deferred queue drained on engine
  entrypoints; `log.retired_queue_len` exposes the pending count. Monitor
  reclaim with `stats()["storage"]` (`tombstone_count`, `records_estimate`
  vs `pages_total`).

## Process Exit Behavior

- Exiting the interpreter with live (un-closed) instances is supported and
  SILENT: the process is terminating and the OS reclaims all memory.
- A warning is printed to stderr at exit only for genuine anomalies: a
  PageSpan/memoryview export still pinned, or undrained deferred releases.
  Release exported buffers (or call `close()`) before exit to clear it.

## Common Failure Patterns

1. Retrying writes after busy: can duplicate records.
2. Omitting flush before close: drops unflushed records.
3. Assuming point-delete at `TL_TS_MAX`: not representable via `[ts, ts+1)`.
4. Treating physical `views()` output as tombstone-filtered logical results.
5. Expecting deletes alone to shrink memory: reclaim requires compaction over the
   deleted windows (see "Space Reclaim After Deletes").

## Operational Checklist

1. Pick maintenance mode for workload.
2. Tune memtable/page/compaction bounds.
3. Use preset constructor first, then tune.
4. Validate behavior under expected out-of-order and delete density.
