# Configuration

Sources of truth:
- C API config: `core/include/timelog/timelog.h` (`tl_config_t`)
- Python facade kwargs/presets: `python/timelog/__init__.py`

## Key Runtime Modes

- `maintenance="background"` (default)
- `maintenance="disabled"` (manual maintenance)

`Contract`
- In background mode, maintenance worker is auto-started by open.

## Important Parameters

- `time_unit`: `s|ms|us|ns`
- `target_page_bytes`
- `memtable_max_bytes`
- `ooo_budget_bytes`
- `sealed_max_runs`
- `sealed_wait_ms`
- `max_delta_segments` — the tiering↔leveling dial (see the dedicated section below)
- `window_size`, `window_origin`
- `delete_debt_threshold`
- `compaction={target_bytes,max_inputs,max_windows}`
- `adaptive={target_records,min_window,max_window,hysteresis_pct,window_quantum,alpha,warmup_flushes,stale_flushes,failure_backoff_threshold,failure_backoff_pct}`

## Backpressure: `busy_policy`

How write-path backpressure (engine `TL_EBUSY`) is surfaced. In every case
THE WRITE WAS ACCEPTED — the policy only decides what happens next:

- `busy_policy="raise"` — raise `TimelogBusyError` (do not retry the write;
  it is already in the log). Right for latency-sensitive callers that want
  to shed load explicitly.
- `busy_policy="flush"` — synchronously flush to relieve pressure, then
  continue. The production default for streaming ingest (`for_streaming`).
- `busy_policy="silent"` — swallow the signal and continue. Use only with
  external monitoring: watch `stats()["operational"]["busy_events"]`, which
  counts backpressure under every policy.

Chronic backpressure means maintenance cannot keep up: lower the ingest
rate, raise `memtable_max_bytes`/`sealed_max_runs`, or switch to
`maintenance="disabled"` + periodic manual `flush()` for bulk loads.

## Retention floor: `min_ts`

`Timelog(min_ts=X)` installs a persistent lower bound: writes below `X`
raise `ValueError`, and the floor is applied as a delete on open. Read it
back via `log.min_ts_floor` or `stats()["config"]["min_ts"]`. (This is the
configuration knob; the `min_ts()` METHOD reports the smallest timestamp
currently visible in the data.)

## Python Presets

- `for_streaming`: background + flush busy policy.
- `for_bulk_ingest`: disabled maintenance + larger memtable.
- `for_low_latency`: stricter busy behavior + small memtable.

## Zero Semantics

`Contract`
- For most numeric fields, `0` means "use engine default".
- Exceptions are documented in the public header and facade docs (notably fields where `0` can mean disabled or immediate behavior).

## Tuning `max_delta_segments` (the tiering↔leveling dial)

`max_delta_segments` (default **8**) bounds the number of L0 segments before the compaction worker
collapses them into the leveled L1. It is Timelog's single tiering↔leveling knob — an *analogy* for how
eagerly the overlapping L0 tier is collapsed; it does **not** change the L0→L1 merge algorithm or L1's
non-overlapping-window discipline, which are fixed.

- **Lower** (2–4) → eager *leveling*: compact often. Low read fan-in, but high write-amplification and
  compaction CPU.
- **Higher** (16–32) → lazy *tiering*: let L0 accumulate. Cheap writes, but higher read fan-in.

### Measured trade-off (saved experiments; directional, not contractual)

Knob matrix — *steady workload, N=400k, 3 paired-seed medians* (internal compaction benchmark; see
[the benchmark artifact](benchmarks/max_delta_segments.md)):

| `max_delta_segments` | write-amp (segment re-merge **proxy**, not bytes) | compaction CPU | point read p50 |
|---|---|---|---|
| 2  | 75.0 | 57.9 ms | ~720 ns |
| 8 (default) | 18.7 | 24.9 ms | ~690 ns |
| 32 | 2.68 | 5.6 ms | ~750 ns |

The knob swings **write-amp ~28×** and **compaction CPU ~10×**, while **point-read latency stays nearly
flat** (~650–760 ns across steady / out-of-order / delete workloads). Reads stay flat because in-order and
mildly-out-of-order segments hold *disjoint* time ranges that fence-pointer pruning skips; in-order read
latency grows only gently with L0 depth (≈1.2× at 32 segments, ≈1.7× at 128).

**The exception — adversarial out-of-order overlap** (*N=200k*): when every L0 segment spans the whole time
domain, fence-pruning cannot skip any segment and every query merges all of them. There, **not compacting
costs ~5.3× read latency** (~600 ns → ~3170 ns); conversely, compacting uses ~23% fewer pages (49 vs 64).
This is the case the default protects against.

### Guidance

- **Default (8)** — balanced and safe for unknown / mixed workloads. Under adversarial out-of-order overlap
  it already delivers the compacted ~600 ns reads (a lower trigger gains nothing there), and it rewrites far
  less than an eager trigger = 2 (steady-workload write-amp 18.7 vs 75.0, above). It is a safe default under
  the current (limited) evidence — *not* a proven optimum. Changing it would need subprocess-isolated,
  ≥5-seed, 2–5M-record validation showing a higher value dominates **without** regressing the adversarial-OOO
  read cliff.
- **Lower (2–4)** — only if you must minimize read latency under *heavy out-of-order overlap* and can afford
  the cost: trigger = 2 measured a **write-amp of 75.0 and 57.9 ms compaction CPU** — ~4× the write-amp and
  ~2.3× the CPU of the default (table above). Usually unnecessary — the default already delivers ~600 ns
  out-of-order reads.
- **Higher (16–32)** — for **write-heavy, in-order / mildly-out-of-order** workloads whose segments
  fence-prune: cuts compaction CPU up to ~4.4× and write-amp up to ~7× **versus the default (8)** at little
  read cost. Caveats:
  - The savings assume the **default unbounded `compaction.max_inputs` / `max_windows`**. If you cap those,
    each compaction drains only that many L0 segments, so a high trigger yields *more frequent, smaller*
    compactions and the savings shrink.
  - **Workload drift is silent.** A workload that starts in-order and later develops time-overlap inherits
    the ~5.3× read cliff with no error. The "free" read result depends on fence-pruning, which is
    `window_size`-sensitive.
  - The recommendation is in *segment count*; the byte and latency impact scales with `memtable_max_bytes`
    (bigger memtable → bigger L0 segments) and `window_size`.

### The "never compacts" trap

Raising `max_delta_segments` above the number of L0 segments your workload ever accumulates stops the
**automatic L0-count trigger** from firing. Compaction can *still* be driven by:

- `delete_debt_threshold` (when > 0): delete / TTL-driven compaction still runs and drains the L0 backlog
  as a side effect; and
- an explicit `compact()` call, which requests compaction regardless of the knob.

The genuine trap is therefore a **delete-free workload that relies solely on the automatic trigger and never
calls `compact()`** — there, L0 (and read-amplification) grow unbounded. In the benchmark, setting
`max_delta_segments = 32` against a workload that only ever produced 16 L0 segments compacted *zero* times →
5.3× slower reads. In manual mode (`maintenance="disabled"`) the automatic trigger never runs at all — you
must call `flush()`/`compact()` and then drive `maint_step()` until the requested work is complete.

### Not a space / delete lever

Space-amplification is driven by tombstones, not this knob (a delete-storm workload held space-amp ≈ 1.67 at
every trigger value). To reclaim deleted space, use `delete_debt_threshold` and `delete_before` / TTL
deletes, not `max_delta_segments`.

### In-memory cost note (RUM)

Because Timelog is in-memory, compaction write-amplification is CPU + transient RAM (memcpy) — not disk I/O,
fsync, or flash wear — which is *cheaper* than a disk LSM and why the default is comparatively relaxed. It is
**not free**, though: each compaction transiently holds the old and new segments together (a RAM spike that
the `compaction.max_windows` cap only partly bounds), re-traverses every surviving record (in the CPython
binding that is per-`PyObject` handle work), and adds cache pressure. A very low trigger (2) therefore
*thrashes* — the 75.0 write-amp / 57.9 ms above.

See also: [Compaction and Maintenance internals](internals/components/compaction-and-maintenance.md) ·
[Performance methodology](PERFORMANCE_METHODOLOGY.md).
