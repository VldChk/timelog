# Timelog Methodology Benchmark Report

- Timestamp: `2026-02-15T18:22:13.031968`
- Profile: `pr`
- Platform: `Linux-6.17.0-14-generic-x86_64-with-glibc2.39`
- Python: `3.13.12 (main, Feb 14 2026, 17:43:49) [GCC 13.3.0]`
- CPU Count: `16`
- Data Path: `demo/order_book_1GB_7pct_ooo_clean.csv`

## Gate Summary

| Gate | pass | fail | warn | na |
|---|---:|---:|---:|---:|
| correctness | 14 | 0 | 0 | 0 |
| complexity | 3 | 0 | 0 | 11 |
| throughput | 0 | 0 | 0 | 14 |

## Scenario Results

| Scenario | Name | Type | Unit | Median | p95 | p99 | Correctness | Complexity | Throughput |
|---|---|---|---|---:|---:|---:|---|---|---|
| A2 | Batch ingestion | e2e | records_in_per_sec | 225,744.928 | 227,307.524 | 227,446.422 | PASS | NA | NA |
| A2B | Batch ingestion (background maintenance) | e2e | records_in_per_sec | 3,418,195.039 | 3,491,150.051 | 3,497,634.941 | PASS | NA | NA |
| B4 | Full scan | engine_only | records_out_per_sec | 14,760,953.740 | 15,698,643.491 | 15,781,993.691 | PASS | NA | NA |
| B5 | Point query | engine_only | queries_per_sec | 80,586.762 | 83,242.488 | 83,478.553 | PASS | NA | NA |
| D3 | Verify deletion | api_overhead | ops_per_sec | 13,174.710 | 13,214.050 | 13,217.547 | PASS | NA | NA |
| D4 | Query after delete | api_overhead | records_out_per_sec | 3,884,957.398 | 5,128,539.121 | 5,239,079.719 | PASS | NA | NA |
| E3 | Background mode | api_overhead | records_in_per_sec | 2,104,808.254 | 2,141,494.296 | 2,144,755.278 | PASS | NA | NA |
| E4 | Maintenance lifecycle | api_overhead | records_in_per_sec | 2,120,170.186 | 2,250,081.496 | 2,261,629.168 | PASS | NA | NA |
| F4 | NumPy integration | engine_only | timestamps_per_sec | 33,404,081.236 | 33,651,768.544 | 33,673,785.193 | PASS | NA | NA |
| I3 | Mixed read (memtable + segments) | engine_only | records_out_per_sec | 13,316,767.806 | 13,691,641.373 | 13,724,963.468 | PASS | NA | NA |
| J1 | Verify O(M) iteration count | engine_only | ops_per_sec | 1,454,858.146 | 1,531,830.653 | 1,538,672.653 | PASS | PASS | NA |
| J2 | Verify scaling behavior | engine_only | ops_per_sec | 903,386.777 | 953,122.818 | 957,543.799 | PASS | PASS | NA |
| J3 | Verify no quadratic behavior | engine_only | ops_per_sec | 489,400.787 | 531,565.561 | 535,313.541 | PASS | PASS | NA |
| K1 | Append latency distribution (background) | mixed_workload | ops_per_sec | 699,505.953 | 759,471.245 | 764,801.493 | PASS | NA | NA |

## Apples Contract

Methodology comparison is performed only when scenario apples-contract metadata matches baseline.
