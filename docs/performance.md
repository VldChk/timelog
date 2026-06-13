# Performance and Complexity

Primary methodology: `docs/PERFORMANCE_METHODOLOGY.md`.

## Current Release Snapshot (v1.3.0)

v1.3 builds on the v1.2 subinterpreter/free-threaded runtime work and focuses
on reducing Python/C boundary overhead:

- `append(obj)` now stays in the C extension fast path for auto-timestamping.
- Common positional methods use `METH_FASTCALL`-style dispatch.
- `bulk_append(timestamps, objects)` ingests native int64 timestamp buffers
  without per-record tuple construction.
- Lower/upper-bound search uses a size-gated branchless path where the measured
  data shows a win, and keeps the conventional path for very large arrays.

Same-harness A/B against the v1.2.0 wheel, Linux x86_64, pinned CPU,
CPython `3.13.12`, median of 5:

| Operation | v1.2.0 median | v1.3.0 median | Ratio |
|---|---:|---:|---:|
| `append(obj)` | 513.9 ns | 117.1 ns | 4.39x |
| `append(ts, obj)` | 352.1 ns | 103.9 ns | 3.39x |
| `append(obj, ts=...)` | 364.7 ns | 109.6 ns | 3.33x |
| `point(ts)` | 457.1 ns | 337.1 ns | 1.36x |
| `equal(ts)` | 548.8 ns | 429.3 ns | 1.28x |
| `next_ts(ts)` | 393.8 ns | 299.8 ns | 1.31x |
| `range(t1, t2)` | 575.9 ns | 458.0 ns | 1.26x |
| `delete_range(t1, t2)` | 18,059.6 ns | 13,289.3 ns | 1.36x |
| `delete_before(ts)` | 109.7 ns | 80.8 ns | 1.36x |

`bulk_append` measured provenance:

| Path | ns/record | Relative |
|---|---:|---:|
| `bulk_append(np.int64 array, list)` | 113.3 | 1.00x |
| `append(int(ts), obj)` loop after v1.3 append folding | 252.1 | bulk is 2.23x faster |
| `extend(zip(ts_list, objects))` | 397.2 | bulk is 3.51x faster |

Artifact: `docs/benchmarks/bulk_append.md`.

Search microbenchmark:

- Size-gated branchless search measured 1.9x-5.0x faster across the gated
  seams up to 262,144 records.
- At very large sizes the advantage disappears, so the implementation is
  deliberately gated rather than universally branchless.

These numbers are same-machine evidence for the v1.3 release work. They are
not a hardware-independent guarantee and should not be mixed with historical
1GB workload numbers below.

## Measurement Policy

`Contract`
- Compare only apples-to-apples scenarios with matching operation, timing boundary, unit, data shape, state profile, maintenance mode, layer, and environment.

## Safe Claim Framing

Use conditional wording tied to measured conditions:

- Insert path: amortized O(1) on memtable ingest path under bounded maintenance contention.
- Delete path: tombstone insertion complexity depends on tombstone interval state; avoid universal O(1) claim.
- Point lookup: near O(log N) when fan-out is bounded.
- Range query: near O(log N + M) with bounded fan-out and linear scan in output size `M`.

## Reporting Rules

- Publish unit-consistent metrics (ops/sec vs records/sec vs queries/sec).
- Separate setup/warmup/measure/teardown timings.
- Include statistical summaries (median/p95/p99/MAD).
- Keep complexity claims tied to explicit sweep dimensions (`N`, `K`, `T`, `M`).

## Native C Engine Benchmark

For engine-only measurements (without Python wrapper/runtime overhead), use:

```bash
cmake -S . -B build-native \
  -DCMAKE_BUILD_TYPE=Release \
  -DTIMELOG_BUILD_PYTHON=OFF \
  -DTIMELOG_BUILD_CORE_TESTS=OFF \
  -DTIMELOG_BUILD_DEMOS=ON
cmake --build build-native --target timelog_native_benchmark -j2
./build-native/timelog_native_benchmark --records 5000000 --batch-size 4096 --ooo-rate 0.05 --scan-loops 1
```

Interpretation guardrails:

- This benchmark measures native Timelog APIs directly in C.
- It excludes Python object creation, Python/C boundary overhead, and Python iterator costs.
- It is valid for "engine ceiling" framing, not end-to-end application throughput claims.

## Python Methodology Benchmark (CSV auto-generation)

For end-to-end Python facade benchmarking, use:

```bash
python demo/timelog_benchmark.py \
  --profile pr \
  --data demo/generated_5pct.csv \
  --generate-data \
  --ooo-rate 0.05
```

Notes:

- The harness can auto-generate `generated_*.csv` inputs when missing.
- Scenario `A6` comparison data (`generated_5pct.csv` and `generated_20pct.csv`) is bootstrapped automatically.

## Historical Reports

- `docs/BENCHMARK_REPORT.md`
- `docs/BENCHMARK_1GB_7PCT_OOO_UNIX.md`
- `docs/benchmarks/max_delta_segments.md`

These are snapshots, not universal guarantees. Prefer the current-release
tables above for v1.3 release notes and README claims.
