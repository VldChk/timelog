# Timelog Methodology Benchmark Report

- Timestamp: `2026-03-01T04:24:56.013077`
- Profile: `full`
- Platform: `Linux-6.14.0-1017-azure-x86_64-with-glibc2.39`
- Python: `3.13.12 (main, Feb  4 2026, 13:48:12) [GCC 13.3.0]`
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
| A0 | Ingest breakdown (parse vs Timelog vs end-to-end) | e2e | records_in_per_sec | 81,054.112 | 82,839.531 | 82,998.415 | PASS | NA | NA |
| A1 | Single record append | e2e | records_in_per_sec | 164,298.052 | 165,283.448 | 165,298.184 | PASS | NA | NA |
| A2 | Batch ingestion | e2e | records_in_per_sec | 141,003.414 | 143,708.716 | 144,026.891 | PASS | NA | NA |
| A2B | Batch ingestion (background maintenance) | e2e | records_in_per_sec | 2,290,449.579 | 2,343,733.828 | 2,345,421.758 | PASS | NA | NA |
| A3 | Streaming ingestion | e2e | records_in_per_sec | 157,994.415 | 158,995.294 | 159,136.204 | PASS | NA | NA |
| A4 | Out-of-order ingestion | e2e | records_in_per_sec | 151,267.825 | 152,103.675 | 152,150.204 | PASS | NA | NA |
| A5 | Backpressure handling | e2e | records_in_per_sec | 161,983.213 | 164,050.454 | 164,208.082 | PASS | NA | NA |
| A6 | Order sensitivity (mostly vs less-ordered) | e2e | records_in_per_sec | 173,815.878 | 175,603.552 | 175,938.540 | PASS | NA | NA |
| B1 | Range query slice | engine_only | records_out_per_sec | 5,892,883.133 | 6,074,839.998 | 6,094,553.274 | PASS | NA | NA |
| B2 | Since query | engine_only | records_out_per_sec | 8,288,207.348 | 8,365,061.248 | 8,368,736.126 | PASS | NA | NA |
| B3 | Until query | engine_only | records_out_per_sec | 9,358,911.047 | 9,465,341.307 | 9,472,824.842 | PASS | NA | NA |
| B4 | Full scan | engine_only | records_out_per_sec | 9,699,941.278 | 9,881,530.961 | 9,899,402.688 | PASS | NA | NA |
| B5 | Point query | engine_only | queries_per_sec | 50,993.235 | 52,144.617 | 52,263.226 | PASS | NA | NA |
| B6 | Microsecond window | engine_only | queries_per_sec | 535,721.290 | 552,812.201 | 560,482.158 | PASS | NA | NA |
| B7 | len(log) full count benchmark | engine_only | ops_per_sec | 153,250.805 | 154,568.979 | 155,064.207 | PASS | NA | NA |
| B8 | len(slice) remaining-count benchmark | engine_only | ops_per_sec | 87,825.666 | 88,251.195 | 88,328.790 | PASS | NA | NA |
| C1 | Orders per second | engine_only | records_out_per_sec | 8,619,327.759 | 8,891,378.078 | 8,962,780.047 | PASS | NA | NA |
| C1B | Orders/sec (single pass) | engine_only | records_out_per_sec | 3,739,976.610 | 3,838,691.143 | 3,839,806.775 | PASS | NA | NA |
| C2 | Buy/Sell ratio | engine_only | records_out_per_sec | 6,091,944.043 | 6,213,329.927 | 6,216,084.249 | PASS | NA | NA |
| C3 | Volume-weighted price (VWAP) | engine_only | records_out_per_sec | 4,627,249.975 | 4,702,707.066 | 4,727,232.493 | PASS | NA | NA |
| C4 | Order fill rate | engine_only | records_out_per_sec | 5,430,645.759 | 5,476,851.332 | 5,484,026.001 | PASS | NA | NA |
| C5 | Ticker activity | engine_only | records_out_per_sec | 2,852,092.105 | 2,951,709.967 | 2,952,982.207 | PASS | NA | NA |
| C6 | Spread analysis | engine_only | records_out_per_sec | 4,206,860.722 | 4,276,388.780 | 4,278,831.945 | PASS | NA | NA |
| C7 | Commission totals | engine_only | records_out_per_sec | 6,013,985.186 | 6,129,557.164 | 6,132,015.336 | PASS | NA | NA |
| C8 | Latency histogram | engine_only | records_out_per_sec | 3,673,163.481 | 3,712,413.750 | 3,719,262.179 | PASS | NA | NA |
| D1 | Delete time range | api_overhead | ops_per_sec | 171,628.092 | 172,970.410 | 172,984.061 | PASS | NA | NA |
| D2 | Evict old data | api_overhead | ops_per_sec | 169,637.631 | 170,992.436 | 171,061.859 | PASS | NA | NA |
| D3 | Verify deletion | api_overhead | ops_per_sec | 8,738.360 | 8,950.056 | 8,979.471 | PASS | NA | NA |
| D4 | Query after delete | api_overhead | records_out_per_sec | 4,288,203.906 | 4,669,425.091 | 4,694,845.515 | PASS | NA | NA |
| E1 | Manual flush | api_overhead | ms_per_op | 290.406 | 301.069 | 301.627 | PASS | NA | NA |
| E2 | Request compaction | api_overhead | ms_per_op | 289.371 | 304.091 | 306.954 | PASS | NA | NA |
| E3 | Background mode | api_overhead | records_in_per_sec | 1,506,104.292 | 1,530,565.419 | 1,541,195.412 | PASS | NA | NA |
| E4 | Maintenance lifecycle | api_overhead | records_in_per_sec | 1,606,273.218 | 1,659,332.781 | 1,659,747.775 | PASS | NA | NA |
| F1 | PageSpan iteration | engine_only | timestamps_per_sec | 540,041,031.799 | 558,955,171.503 | 559,351,061.380 | PASS | NA | NA |
| F2 | Timestamp memoryview | engine_only | timestamps_per_sec | 95,155,546.513 | 98,335,647.246 | 98,845,246.328 | PASS | NA | NA |
| F3 | Objects view | engine_only | objects_per_sec | 7,581,598.458 | 7,699,117.798 | 7,730,381.620 | PASS | NA | NA |
| F4 | NumPy integration | engine_only | timestamps_per_sec | 0.000 | 0.000 | 0.000 | PASS | NA | NA |
| F5 | Bulk statistics | engine_only | timestamps_per_sec | 0.000 | 0.000 | 0.000 | PASS | NA | NA |
| G1 | Batch iteration | engine_only | records_out_per_sec | 10,821,482.269 | 11,009,528.590 | 11,050,347.385 | PASS | NA | NA |
| G2 | Context manager | engine_only | records_out_per_sec | 9,231,022.190 | 9,515,417.973 | 9,557,887.241 | PASS | NA | NA |
| G3 | Early termination | engine_only | records_out_per_sec | 6,539,818.647 | 6,671,549.260 | 6,699,879.528 | PASS | NA | NA |
| G4 | Multiple iterators | engine_only | records_out_per_sec | 9,274,286.636 | 9,496,942.145 | 9,567,044.582 | PASS | NA | NA |
| H1 | Trade reconstruction | engine_only | records_out_per_sec | 50,333.112 | 52,865.717 | 52,971.401 | PASS | NA | NA |
| H2 | Market replay | engine_only | records_out_per_sec | 9,063,863.614 | 9,252,693.350 | 9,263,603.648 | PASS | NA | NA |
| H3 | Anomaly detection | engine_only | records_out_per_sec | 9,293,188.875 | 9,422,376.339 | 9,466,983.997 | PASS | NA | NA |
| H3B | Anomaly detection (single pass) | engine_only | records_out_per_sec | 3,844,389.642 | 4,133,506.155 | 4,138,079.801 | PASS | NA | NA |
| H4 | Audit trail | engine_only | queries_per_sec | 5,786.922 | 5,880.935 | 5,911.842 | PASS | NA | NA |
| I1 | Memtable read (hot data) | engine_only | records_out_per_sec | 616,831.383 | 692,102.376 | 693,430.618 | PASS | NA | NA |
| I2 | Cold data read (segments) | engine_only | records_out_per_sec | 4,443,145.646 | 4,478,795.017 | 4,479,628.219 | PASS | NA | NA |
| I3 | Mixed read (memtable + segments) | engine_only | records_out_per_sec | 9,617,010.010 | 9,748,056.496 | 9,768,606.658 | PASS | NA | NA |
| J1 | Verify O(M) iteration count | engine_only | ops_per_sec | 1,057,921.156 | 1,076,797.864 | 1,079,273.074 | PASS | PASS | NA |
| J2 | Verify scaling behavior | engine_only | ops_per_sec | 676,556.333 | 701,067.902 | 702,730.331 | PASS | PASS | NA |
| J3 | Verify no quadratic behavior | engine_only | ops_per_sec | 367,424.598 | 373,300.818 | 374,717.568 | PASS | PASS | NA |
| K1 | Append latency distribution (background) | mixed_workload | ops_per_sec | 405,595.389 | 411,417.044 | 411,764.710 | PASS | NA | NA |
| K1B | Append latency (manual flush/compact) | mixed_workload | ops_per_sec | 360,465.325 | 377,975.989 | 378,598.759 | PASS | NA | NA |
| K2 | Mixed workload (hot read) | mixed_workload | ops_per_sec | 538,164.860 | 548,674.389 | 549,288.173 | PASS | NA | NA |
| K3 | Mixed workload (cold read) | mixed_workload | ops_per_sec | 608,211.537 | 615,434.729 | 617,283.254 | PASS | NA | NA |
| K4 | Delete impact (hot vs cold) | mixed_workload | ops_per_sec | 393,837.802 | 407,725.046 | 407,843.518 | PASS | NA | NA |
| K5 | A2B stress grid (OOO + background) | mixed_workload | ops_per_sec | 87,949.128 | 88,509.480 | 88,526.396 | PASS | NA | NA |

## Apples Contract

Methodology comparison is performed only when scenario apples-contract metadata matches baseline.
