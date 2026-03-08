# Performance and Complexity

Primary methodology: `docs/PERFORMANCE_METHODOLOGY.md`.

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

These are snapshots, not universal guarantees.
