# Operations and Troubleshooting

## Lifecycle Safety

`Contract`
- `close()` is not a synchronization barrier for in-flight API calls; caller must ensure exclusive access for close.
- `flush()` before `close()` if you need active/sealed writes materialized into immutable segments.
- Explicit `close()` can raise while active iterators, `PageSpan` instances, memoryview exports, or other snapshot pins are still alive. Release readers and buffer exports before closing.
- Scope-style usage (`log = Timelog()`) is supported. If the object is collected without explicit close, finalization auto-closes as a best-effort cleanup path.

## Maintenance Modes

- Background mode: worker auto-starts at open.
- Disabled mode: use `flush()` and `maint_step()` manually.

## Snapshot and Iterator Hygiene

- Acquire snapshot/iterator for read isolation.
- Destroy iterators before releasing their snapshot.

## Space Reclaim After Deletes

- Deletes are logical tombstones. Query results respect them immediately; physical
  memory is reclaimed only when compaction rewrites the affected windows.
- Compaction is triggered by new L0 segments (continued writes) or by the
  `delete_debt_threshold` knob. A retention-shaped workload that deletes old data but
  stops writing into those windows may therefore retain space indefinitely.
- If reclaim matters for your workload: monitor `stats()["storage"]`
  (`tombstone_count`, `records_estimate` vs `pages_total`), set
  `delete_debt_threshold`, and run `compact()` (plus `maint_step()` in disabled mode)
  after large deletes.

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
