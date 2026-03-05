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

## Historical Reports

- `docs/BENCHMARK_REPORT.md`
- `docs/BENCHMARK_1GB_7PCT_OOO_UNIX.md`

These are snapshots, not universal guarantees.
