# Timelog Methodology Benchmark Report

- Timestamp: `2026-02-15T18:23:27.663766`
- Profile: `custom`
- Platform: `Linux-6.17.0-14-generic-x86_64-with-glibc2.39`
- Python: `3.13.12 (main, Feb 14 2026, 17:43:49) [GCC 13.3.0]`
- CPU Count: `16`
- Data Path: `demo/order_book_1GB_7pct_ooo_clean.csv`

## Gate Summary

| Gate | pass | fail | warn | na |
|---|---:|---:|---:|---:|
| correctness | 1 | 0 | 0 | 0 |
| complexity | 0 | 0 | 0 | 1 |
| throughput | 0 | 0 | 0 | 1 |

## Scenario Results

| Scenario | Name | Type | Unit | Median | p95 | p99 | Correctness | Complexity | Throughput |
|---|---|---|---|---:|---:|---:|---|---|---|
| A6 | Order sensitivity (mostly vs less-ordered) | e2e | records_in_per_sec | 275,129.484 | 283,386.373 | 286,542.259 | PASS | NA | NA |

## Apples Contract

Methodology comparison is performed only when scenario apples-contract metadata matches baseline.
