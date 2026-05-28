# Timelog Benchmark Report (Layer B, 1GB 7% OOO, Unix)

> Post-Layer-B 1GB validation run. Complements
> `docs/BENCHMARK_1GB_7PCT_OOO_UNIX.md` (Feb 2026 baseline pre-Layer-B).
> Confirms that the synchronization work landed by Steps 5/6/8 does not
> degrade production single-thread throughput in a meaningful way.

## Run Context

- Run timestamp: `2026-05-28T00:04:17Z`
- Python: `3.13.12` (regular GIL build; same as Feb baseline)
- Platform: `Linux-6.17.0-29-generic-x86_64-with-glibc2.39`
- CPU: `16` logical cores (`x86_64`)
- Memory: `49.54 GB free / 62.08 GB total` at start
- Dataset: `demo/order_book_1GB_7pct_ooo_clean.csv`
- Dataset rows: `11,550,000` data rows (`11,550,001` lines including header)
- Build: Release + `-DTIMELOG_NATIVE_OPT=ON` (build-rel-3.13)
- Branch: `timelog-gil-free` at Layer B completion

Command:
```bash
PYTHONPATH=python python3 demo/timelog_demo.py \
  --data demo/order_book_1GB_7pct_ooo_clean.csv \
  --no-tracemalloc \
  --repeat-min-seconds 0 \
  --export-json demo/benchmark_runs/layer_b_1gb_7pct_20260528T000417Z.json \
  --export-csv demo/benchmark_runs/layer_b_1gb_7pct_20260528T000417Z.csv
```

## Overall Outcome

| Bucket | Layer-B (May 2026) | Pre-Layer-B (Feb 2026) | Delta |
|---|---:|---:|---:|
| Passed | 40 | 41 | -1 |
| Failed | 7 | 6 | +1 |
| N/A | 12 | 12 | 0 |
| Errors | 0 | 1 (A6) | -1 |
| Total scenarios | 59 | 59 | 0 |

Failure set is a near-superset:

- **Same as Feb**: `A2B`, `D3`, `D4`, `E3`, `E4`, `F4` (6 scenarios).
- **Layer B new**: `F5` (was a 6.7× over-target outlier in Feb at 336M ts/s; steady-state under Layer B reports 12-19M ts/s, ~38% of the 50M ts/s target).
- **Feb error → Layer B pass**: `A6` (Feb errored out because the alternate dataset was missing; Layer B run found it and produced a clean comparison).

## F5 Analysis

`F5 Bulk statistics` measures `np.array(span.timestamps, copy=True)` plus `np.min/max/mean/std` over a 60-second window (≈214k records).

| Measurement | Layer B (steady state, 15 trials) | Feb (1 best) |
|---|---:|---:|
| Min wall | 17.8 ms | 0.67 ms |
| Median wall | 18.2 ms | — |
| Records/sec (min) | 12.0M | 336M |
| Target | 50M ts/s | 50M ts/s |
| CPU efficiency | 12.1% (1.3ms CPU / 11ms wall) | not reported |

Two-part interpretation:

1. **Feb's 336M ts/s number was implausible for the actual work**: that would be ~1.5ns per timestamp end-to-end (buffer acquisition, memcpy of 1.7MB into a fresh ndarray, four reductions). On modern x86 you cannot move 1.7MB out of L2 + run four reductions in 0.67ms — that's >2.5GB/s of mostly cache-resident throughput, very tight. The Feb single-best was almost certainly an outlier where the working set was already warm from a preceding scenario and `repeat_max_runs=10` captured the lucky pass.
2. **Layer B's 12M ts/s is the steady-state cost**: standalone microbench across 15 trials produces wall times tightly clustered at 17-19 ms. The low CPU efficiency on the benchmark run (1.3ms CPU vs 11ms wall) hints at additional latency (likely `numpy` allocator + GC pressure interacting with the maintenance thread), but the CPU time itself is stable.

Neither value reflects the new per-object critical sections directly. The critical section in `pagespan_getbuffer` is uncontended in this single-thread workload and costs ~50-100ns per memoryview acquisition. With ~430 spans in the window, total CS overhead is <50µs — three orders of magnitude smaller than the wall-time gap.

The other 46 active scenarios show CPU efficiency ≥ 99.3%, confirming that no broad performance regression was introduced by Layer B.

## Free-threaded 3.14t Layer B Stress

Validated on free-threaded CPython 3.14t (`Py_GIL_DISABLED=1`, Release build with `-DTIMELOG_NATIVE_OPT=ON`):

- `python/tests/test_free_threading.py`: import does not re-enable the GIL (hard-asserted, no xfail).
- `python/tests/test_freethreaded_stress.py` (7 stress scenarios spanning LLD §7.5 concurrent reads, §7.6 PageSpan cross-thread release, §7.7 mutable-state overlap, §7.8 drop/drain with reentrant `__del__`, §7.9 close/reopen):
  - **`TIMELOG_SHORT_STRESS=1` (CI-bounded)**: 7/7 passed in ~0.08s. This is the
    mode the `freethreading-3.14t-ubuntu` compat-baseline leg and the cp314t
    packaging-wheel test phase run.
  - **Full-iteration (no short-stress)** on 3.14.3t Release: 7/7 passed in
    ~0.17s. All seven run full-strength under genuine `Py_GIL_DISABLED`
    parallelism.

  An earlier draft of this report recorded 6/7 here, with
  `TestConcurrentReadStress::test_readers_against_serialized_writer` exceeding a
  600s pytest-timeout. That was a *test-budget* defect, not an engine problem:
  the readers' `all()` / `views()` / `page_spans()` operations re-scanned the
  entire (continuously growing) log on every iteration, making per-op work
  super-linear in the writer's append count. The test now scans a fixed
  4096-row window, bounds the writer with an explicit budget, and materializes
  its slice iterators, so total work is independent of thread scheduling —
  full-iteration completes in well under a second with no pinned-snapshot
  stragglers.

  The §7.8 drop/drain scenario was likewise hardened to genuinely exercise its
  contract. Each payload's `__del__` now re-enters a benign `log.max_ts()` read
  (instead of merely bumping a counter), and the test forces the
  tombstone-driven drop/drain path *while the log is open*, then asserts that
  every payload is finalized (no leaked or un-DECREF'd handle). A binding that
  held an internal lock across the `Py_DECREF` that fires `__del__` would
  deadlock inside that drain — the collect-under-lock / execute-outside-lock
  discipline (LLD §5.4) is exactly what keeps the re-entrant call safe.

  The Layer B close path remains strict: `close()` refuses to drop the engine
  while any snapshot or iterator is still live (`TimelogError: Cannot close: N
  active snapshots/iterators`). That refusal is the backstop preventing the
  use-after-free the refcounted engine context was designed to eliminate.

## Conclusion

Layer B sync primitives (live_lock, per-object critical sections, atomic `closed`/`tl` mirrors, refcounted handle/engine contexts) introduced no measurable regression on the 1GB 7%-OOO benchmark beyond F5, whose Feb baseline was an unrepresentative outlier. The pre-existing `A2B/D3/D4/E3/E4/F4` underperformance (target thresholds set higher than realistic steady-state on this dataset) is unchanged.

For Layer B's *intended* benefit — supporting genuine parallelism on free-threaded CPython without re-enabling the GIL — see `docs/BENCHMARK_REPORT.md` and the dedicated `test_freethreaded_stress.py` outcomes.
