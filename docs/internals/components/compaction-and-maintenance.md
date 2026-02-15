# Internals: Compaction and Maintenance

Sources:
- `core/src/maint/tl_compaction.*`
- `core/src/tl_timelog.c`

## Maintenance Control Plane

- Background mode: worker loop executes flush/compaction work.
- Manual mode: caller executes incremental maintenance steps.

`Contract`
- In background mode, worker auto-starts at open.

## Compaction Goals

1. Bound read amplification.
2. Maintain L1 non-overlap.
3. Reclaim tombstoned data physically.

## Publish and Retry

`Implementation note`
- Compaction publish validates against current manifest and retries on conflicts.
- Retry/EBUSY counters are tracked in stats.

## Grid Freeze

`Implementation note`
- After L1 creation, window grid is frozen (`window_grid_frozen`) to preserve partition invariants.
