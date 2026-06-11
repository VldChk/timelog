# Extended Perf A/B Artifact

Purpose: preserve the raw evidence for the current `AUDIT_REPORT.md` same-harness
performance ratios for `feat/perf-wins`.

Source files were found in `/tmp` with mtimes on 2026-06-09:

- `/tmp/timelog-perf-ab-extended-baseline.json`
- `/tmp/timelog-perf-ab-extended-current.json`

Saved copies:

- `perf_ab_extended_baseline_2026-06-09.json`
- `perf_ab_extended_current_2026-06-09.json`

Both runs report:

- Python `3.13.12`
- `pinned_cpu: true`
- 5 reps per operation
- baseline module:
  `/tmp/timelog-baseline-perf/python/timelog/_timelog.cpython-313-x86_64-linux-gnu.so`
- current module:
  `/home/vldvhk/Documents/tl-feat-perf/python/timelog/_timelog.cpython-313-x86_64-linux-gnu.so`

Median ratios (`baseline_ns / current_ns`):

| operation | baseline ns | current ns | ratio |
|---|---:|---:|---:|
| `facade_append_obj_auto` | 513.887475 | 117.105185 | 4.39x |
| `facade_append_ts_obj` | 352.106316 | 103.893472 | 3.39x |
| `facade_append_obj_ts_kw` | 364.731000 | 109.566246 | 3.33x |
| `raw_point` | 457.121305 | 337.060630 | 1.36x |
| `raw_equal` | 548.816045 | 429.258025 | 1.28x |
| `raw_next_ts` | 393.831515 | 299.831415 | 1.31x |
| `raw_prev_ts` | 854.740925 | 741.135385 | 1.15x |
| `raw_range` | 575.910767 | 457.963992 | 1.26x |
| `raw_since` | 533.144242 | 420.458400 | 1.27x |
| `raw_until` | 540.850883 | 440.080208 | 1.23x |
| `raw_delete_range` | 18059.635470 | 13289.338990 | 1.36x |
| `raw_delete_before` | 109.713330 | 80.787490 | 1.36x |

