# Timelog Methodology Benchmark Report

- Timestamp: `2026-07-08T06:36:03.209607`
- Profile: `pr`
- Platform: `Linux-6.17.0-35-generic-x86_64-with-glibc2.39`
- Python: `3.13.12 (main, Feb 14 2026, 17:43:49) [GCC 13.3.0]`
- CPU Count: `16`
- Data Path: `demo/generated_5pct.csv`

## Gate Summary

| Gate | pass | fail | warn | na |
|---|---:|---:|---:|---:|
| correctness | 14 | 0 | 0 | 0 |
| complexity | 3 | 0 | 0 | 11 |
| throughput | 0 | 0 | 0 | 14 |

## Scenario Results

| Scenario | Name | Type | Unit | Median | p95 | p99 | Correctness | Complexity | Throughput |
|---|---|---|---|---:|---:|---:|---|---|---|
| A2 | Batch ingestion | e2e | records_in_per_sec | 259,436.168 | 259,611.557 | 259,627.147 | PASS | NA | NA |
| A2B | Batch ingestion (background maintenance) | e2e | records_in_per_sec | 4,038,346.850 | 4,112,931.383 | 4,119,561.119 | PASS | NA | NA |
| B4 | Full scan | engine_only | records_out_per_sec | 15,362,913.497 | 16,005,709.835 | 16,062,847.287 | PASS | NA | NA |
| B5 | Point query | engine_only | queries_per_sec | 94,178.010 | 94,312.745 | 94,324.722 | PASS | NA | NA |
| D3 | Verify deletion | api_overhead | ops_per_sec | 18,061.952 | 20,320.138 | 20,520.866 | PASS | NA | NA |
| D4 | Query after delete | api_overhead | records_out_per_sec | 6,040,390.884 | 6,172,809.134 | 6,184,579.645 | PASS | NA | NA |
| E3 | Background mode | api_overhead | records_in_per_sec | 5,461,689.737 | 5,475,332.515 | 5,476,545.206 | PASS | NA | NA |
| E4 | Maintenance lifecycle | api_overhead | records_in_per_sec | 5,665,214.438 | 6,060,253.016 | 6,095,367.556 | PASS | NA | NA |
| F4 | NumPy integration | engine_only | timestamps_per_sec | 36,665,441.953 | 38,199,830.208 | 38,336,220.275 | PASS | NA | NA |
| I3 | Mixed read (memtable + segments) | engine_only | records_out_per_sec | 14,458,125.908 | 14,529,280.967 | 14,535,605.861 | PASS | NA | NA |
| J1 | Verify O(M) iteration count | engine_only | ops_per_sec | 1,813,718.290 | 1,852,149.910 | 1,855,566.054 | PASS | PASS | NA |
| J2 | Verify scaling behavior | engine_only | ops_per_sec | 1,098,730.661 | 1,105,903.866 | 1,106,541.484 | PASS | PASS | NA |
| J3 | Verify no quadratic behavior | engine_only | ops_per_sec | 614,076.891 | 614,725.595 | 614,783.257 | PASS | PASS | NA |
| K1 | Append latency distribution (background) | mixed_workload | ops_per_sec | 1,029,694.536 | 1,039,233.778 | 1,040,081.710 | PASS | NA | NA |

## Apples Contract

Methodology comparison is performed only when scenario apples-contract metadata matches baseline.
