# Timelog Methodology Benchmark Report

- Timestamp: `2026-02-22T04:23:34.893743`
- Profile: `full`
- Platform: `Linux-6.11.0-1018-azure-x86_64-with-glibc2.39`
- Python: `3.13.11 (main, Dec  8 2025, 02:51:34) [GCC 13.3.0]`
- CPU Count: `4`
- Data Path: `demo/order_book_50MB_5pct_ooo_clean.csv`

## Gate Summary

| Gate | pass | fail | warn | na |
|---|---:|---:|---:|---:|
| correctness | 59 | 0 | 0 | 0 |
| complexity | 3 | 0 | 0 | 56 |
| throughput | 0 | 0 | 0 | 59 |

## Scenario Results

| Scenario | Name | Type | Unit | Median | p95 | p99 | Correctness | Complexity | Throughput |
|---|---|---|---|---:|---:|---:|---|---|---|
| A0 | Ingest breakdown (parse vs Timelog vs end-to-end) | e2e | records_in_per_sec | 78,555.023 | 79,581.952 | 79,832.949 | PASS | NA | NA |
| A1 | Single record append | e2e | records_in_per_sec | 161,338.638 | 163,317.254 | 163,346.055 | PASS | NA | NA |
| A2 | Batch ingestion | e2e | records_in_per_sec | 137,662.542 | 141,185.780 | 141,237.520 | PASS | NA | NA |
| A2B | Batch ingestion (background maintenance) | e2e | records_in_per_sec | 2,290,930.374 | 2,468,291.398 | 2,469,290.173 | PASS | NA | NA |
| A3 | Streaming ingestion | e2e | records_in_per_sec | 152,096.315 | 154,496.498 | 154,689.586 | PASS | NA | NA |
| A4 | Out-of-order ingestion | e2e | records_in_per_sec | 140,229.983 | 141,249.597 | 141,419.041 | PASS | NA | NA |
| A5 | Backpressure handling | e2e | records_in_per_sec | 153,311.466 | 160,581.023 | 161,346.263 | PASS | NA | NA |
| A6 | Order sensitivity (mostly vs less-ordered) | e2e | records_in_per_sec | 164,919.772 | 165,944.199 | 166,306.826 | PASS | NA | NA |
| B1 | Range query slice | engine_only | records_out_per_sec | 6,406,663.913 | 6,737,159.694 | 6,829,065.224 | PASS | NA | NA |
| B2 | Since query | engine_only | records_out_per_sec | 7,531,253.975 | 7,713,460.680 | 7,741,571.239 | PASS | NA | NA |
| B3 | Until query | engine_only | records_out_per_sec | 8,449,002.765 | 8,604,315.394 | 8,641,115.878 | PASS | NA | NA |
| B4 | Full scan | engine_only | records_out_per_sec | 8,526,537.356 | 8,610,753.837 | 8,625,386.437 | PASS | NA | NA |
| B5 | Point query | engine_only | queries_per_sec | 50,934.537 | 51,484.299 | 51,558.526 | PASS | NA | NA |
| B6 | Microsecond window | engine_only | queries_per_sec | 516,176.425 | 520,520.760 | 520,573.430 | PASS | NA | NA |
| B7 | len(log) full count benchmark | engine_only | ops_per_sec | 149,260.916 | 149,995.326 | 150,036.761 | PASS | NA | NA |
| B8 | len(slice) remaining-count benchmark | engine_only | ops_per_sec | 81,920.443 | 82,393.776 | 82,585.412 | PASS | NA | NA |
| C1 | Orders per second | engine_only | records_out_per_sec | 8,803,968.932 | 8,977,641.444 | 8,990,523.177 | PASS | NA | NA |
| C1B | Orders/sec (single pass) | engine_only | records_out_per_sec | 3,538,903.012 | 3,608,642.123 | 3,612,458.653 | PASS | NA | NA |
| C2 | Buy/Sell ratio | engine_only | records_out_per_sec | 4,944,723.066 | 5,075,147.592 | 5,079,544.072 | PASS | NA | NA |
| C3 | Volume-weighted price (VWAP) | engine_only | records_out_per_sec | 3,467,082.626 | 3,505,279.554 | 3,505,455.480 | PASS | NA | NA |
| C4 | Order fill rate | engine_only | records_out_per_sec | 4,677,952.145 | 4,788,453.901 | 4,804,177.940 | PASS | NA | NA |
| C5 | Ticker activity | engine_only | records_out_per_sec | 2,611,886.025 | 2,677,819.927 | 2,687,217.672 | PASS | NA | NA |
| C6 | Spread analysis | engine_only | records_out_per_sec | 3,197,202.402 | 3,254,760.748 | 3,258,840.131 | PASS | NA | NA |
| C7 | Commission totals | engine_only | records_out_per_sec | 4,770,166.260 | 4,830,085.299 | 4,830,815.079 | PASS | NA | NA |
| C8 | Latency histogram | engine_only | records_out_per_sec | 3,361,641.453 | 3,403,941.911 | 3,413,141.648 | PASS | NA | NA |
| D1 | Delete time range | api_overhead | ops_per_sec | 159,111.120 | 161,644.266 | 162,080.523 | PASS | NA | NA |
| D2 | Evict old data | api_overhead | ops_per_sec | 158,230.300 | 159,783.500 | 159,867.868 | PASS | NA | NA |
| D3 | Verify deletion | api_overhead | ops_per_sec | 6,192.871 | 6,251.366 | 6,268.559 | PASS | NA | NA |
| D4 | Query after delete | api_overhead | records_out_per_sec | 4,278,197.134 | 4,729,147.903 | 4,745,852.609 | PASS | NA | NA |
| E1 | Manual flush | api_overhead | ms_per_op | 308.544 | 323.060 | 324.324 | PASS | NA | NA |
| E2 | Request compaction | api_overhead | ms_per_op | 310.768 | 329.651 | 332.455 | PASS | NA | NA |
| E3 | Background mode | api_overhead | records_in_per_sec | 1,469,238.809 | 1,499,389.970 | 1,505,866.208 | PASS | NA | NA |
| E4 | Maintenance lifecycle | api_overhead | records_in_per_sec | 1,540,423.667 | 1,605,479.394 | 1,606,332.447 | PASS | NA | NA |
| F1 | PageSpan iteration | engine_only | timestamps_per_sec | 623,193,887.036 | 642,672,596.476 | 645,327,450.577 | PASS | NA | NA |
| F2 | Timestamp memoryview | engine_only | timestamps_per_sec | 111,014,384.204 | 112,557,894.772 | 112,642,343.545 | PASS | NA | NA |
| F3 | Objects view | engine_only | objects_per_sec | 6,080,938.490 | 6,254,405.339 | 6,270,994.731 | PASS | NA | NA |
| F4 | NumPy integration | engine_only | timestamps_per_sec | 0.000 | 0.000 | 0.000 | PASS | NA | NA |
| F5 | Bulk statistics | engine_only | timestamps_per_sec | 0.000 | 0.000 | 0.000 | PASS | NA | NA |
| G1 | Batch iteration | engine_only | records_out_per_sec | 10,528,401.950 | 10,815,198.953 | 10,834,229.459 | PASS | NA | NA |
| G2 | Context manager | engine_only | records_out_per_sec | 8,505,885.721 | 8,613,194.547 | 8,621,873.969 | PASS | NA | NA |
| G3 | Early termination | engine_only | records_out_per_sec | 6,767,625.523 | 7,012,248.581 | 7,045,862.232 | PASS | NA | NA |
| G4 | Multiple iterators | engine_only | records_out_per_sec | 9,472,561.569 | 9,664,399.324 | 9,721,038.422 | PASS | NA | NA |
| H1 | Trade reconstruction | engine_only | records_out_per_sec | 81,404.356 | 87,381.476 | 87,656.659 | PASS | NA | NA |
| H2 | Market replay | engine_only | records_out_per_sec | 7,893,716.402 | 7,966,438.344 | 7,984,891.043 | PASS | NA | NA |
| H3 | Anomaly detection | engine_only | records_out_per_sec | 9,287,087.230 | 9,418,688.991 | 9,419,109.063 | PASS | NA | NA |
| H3B | Anomaly detection (single pass) | engine_only | records_out_per_sec | 3,720,014.962 | 3,803,811.445 | 3,808,306.518 | PASS | NA | NA |
| H4 | Audit trail | engine_only | queries_per_sec | 5,767.912 | 5,811.716 | 5,820.393 | PASS | NA | NA |
| I1 | Memtable read (hot data) | engine_only | records_out_per_sec | 594,987.307 | 652,569.814 | 653,677.451 | PASS | NA | NA |
| I2 | Cold data read (segments) | engine_only | records_out_per_sec | 4,535,513.584 | 4,668,277.840 | 4,671,296.872 | PASS | NA | NA |
| I3 | Mixed read (memtable + segments) | engine_only | records_out_per_sec | 8,414,671.056 | 8,500,531.966 | 8,503,336.754 | PASS | NA | NA |
| J1 | Verify O(M) iteration count | engine_only | ops_per_sec | 952,864.083 | 979,581.046 | 984,450.142 | PASS | PASS | NA |
| J2 | Verify scaling behavior | engine_only | ops_per_sec | 604,476.023 | 618,498.211 | 618,900.171 | PASS | PASS | NA |
| J3 | Verify no quadratic behavior | engine_only | ops_per_sec | 329,764.543 | 341,686.041 | 341,873.523 | PASS | PASS | NA |
| K1 | Append latency distribution (background) | mixed_workload | ops_per_sec | 367,595.381 | 377,876.578 | 378,528.593 | PASS | NA | NA |
| K1B | Append latency (manual flush/compact) | mixed_workload | ops_per_sec | 335,044.460 | 357,557.728 | 358,387.797 | PASS | NA | NA |
| K2 | Mixed workload (hot read) | mixed_workload | ops_per_sec | 524,393.566 | 540,002.829 | 542,566.883 | PASS | NA | NA |
| K3 | Mixed workload (cold read) | mixed_workload | ops_per_sec | 554,769.927 | 562,515.193 | 563,099.079 | PASS | NA | NA |
| K4 | Delete impact (hot vs cold) | mixed_workload | ops_per_sec | 360,360.157 | 376,764.435 | 377,319.327 | PASS | NA | NA |
| K5 | A2B stress grid (OOO + background) | mixed_workload | ops_per_sec | 81,127.702 | 83,158.756 | 83,206.277 | PASS | NA | NA |

## Apples Contract

Methodology comparison is performed only when scenario apples-contract metadata matches baseline.
