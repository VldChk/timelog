# Operations and Troubleshooting

## Lifecycle Safety

`Contract`
- `close()` is not a synchronization barrier for in-flight API calls; caller must ensure exclusive access for close.
- `flush()` before `close()` if you need active/sealed writes materialized into immutable segments.

## Maintenance Modes

- Background mode: worker auto-starts at open.
- Disabled mode: use `flush()` and `maint_step()` manually.

## Snapshot and Iterator Hygiene

- Acquire snapshot/iterator for read isolation.
- Destroy iterators before releasing their snapshot.

## Common Failure Patterns

1. Retrying writes after busy: can duplicate records.
2. Omitting flush before close: drops unflushed records.
3. Assuming point-delete at `TL_TS_MAX`: not representable via `[ts, ts+1)`.
4. Treating physical `views()` output as tombstone-filtered logical results.

## Operational Checklist

1. Pick maintenance mode for workload.
2. Tune memtable/page/compaction bounds.
3. Use preset constructor first, then tune.
4. Validate behavior under expected out-of-order and delete density.
