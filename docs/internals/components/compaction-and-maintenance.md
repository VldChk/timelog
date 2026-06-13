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

## Tuning: `max_delta_segments` (the tiering↔leveling dial)

`tl_compact_needed()` requests compaction when **either** the L0 segment count reaches
`max_delta_segments` **or** delete-debt reaches `delete_debt_threshold`; an explicit `tl_compact()` requests
compaction regardless of either. The background worker or manual `tl_maint_step()` call performs the merge.
`max_delta_segments` (default 8) is the tiering↔leveling dial: lower
collapses the overlapping L0 tier into leveled L1 eagerly (low read fan-in, high write-amp + compaction
CPU); higher lets L0 accumulate (cheap writes, higher read fan-in). It controls the *eagerness of L0
collapse only* — the L0→L1 merge and L1 non-overlap discipline are invariant.

`Implementation note`
- The per-compaction drain is bounded independently by `max_compaction_inputs` / `max_compaction_windows`
  (`tl__compact_select_greedy`), so a high trigger with a low `max_inputs` produces more frequent, smaller
  compactions than the trigger count alone suggests.
- In-memory write-amp is CPU + a transient old+new RAM spike (only partly bounded by
  `max_compaction_windows`) + per-handle re-traversal in the CPython binding — cheaper than disk, not free.

See [Configuration → Tuning `max_delta_segments`](../../configuration.md) for the measured trade-off curve
and tuning guidance.

## Publish and Retry

`Implementation note`
- Compaction publish validates against current manifest and retries on conflicts.
- Retry/EBUSY counters are tracked in stats.

## Grid Freeze

`Implementation note`
- After L1 creation, window grid is frozen (`window_grid_frozen`) to preserve partition invariants.
