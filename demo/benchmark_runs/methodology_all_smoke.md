# Timelog Methodology Benchmark Report

- Timestamp: `2026-02-15T18:22:46.188625`
- Profile: `all-smoke`
- Platform: `Linux-6.17.0-14-generic-x86_64-with-glibc2.39`
- Python: `3.13.12 (main, Feb 14 2026, 17:43:49) [GCC 13.3.0]`
- CPU Count: `16`
- Data Path: `demo/order_book_1GB_7pct_ooo_clean.csv`

## Gate Summary

| Gate | pass | fail | warn | na |
|---|---:|---:|---:|---:|
| correctness | 59 | 0 | 0 | 0 |
| complexity | 3 | 0 | 0 | 56 |
| throughput | 0 | 0 | 0 | 59 |

## Scenario Results

| Scenario | Name | Type | Unit | Median | p95 | p99 | Correctness | Complexity | Throughput |
|---|---|---|---|---:|---:|---:|---|---|---|
| A0 | Ingest breakdown (parse vs Timelog vs end-to-end) | e2e | records_in_per_sec | 118,363.042 | 118,363.042 | 118,363.042 | PASS | NA | NA |
| A1 | Single record append | e2e | records_in_per_sec | 241,724.571 | 241,724.571 | 241,724.571 | PASS | NA | NA |
| A2 | Batch ingestion | e2e | records_in_per_sec | 226,054.434 | 226,054.434 | 226,054.434 | PASS | NA | NA |
| A2B | Batch ingestion (background maintenance) | e2e | records_in_per_sec | 3,372,769.212 | 3,372,769.212 | 3,372,769.212 | PASS | NA | NA |
| A3 | Streaming ingestion | e2e | records_in_per_sec | 245,277.591 | 245,277.591 | 245,277.591 | PASS | NA | NA |
| A4 | Out-of-order ingestion | e2e | records_in_per_sec | 221,727.651 | 221,727.651 | 221,727.651 | PASS | NA | NA |
| A5 | Backpressure handling | e2e | records_in_per_sec | 226,883.406 | 226,883.406 | 226,883.406 | PASS | NA | NA |
| A6 | Order sensitivity (mostly vs less-ordered) | e2e | records_in_per_sec | 214,124.437 | 214,124.437 | 214,124.437 | PASS | NA | NA |
| B1 | Range query slice | engine_only | records_out_per_sec | 12,175,878.390 | 12,175,878.390 | 12,175,878.390 | PASS | NA | NA |
| B2 | Since query | engine_only | records_out_per_sec | 12,558,807.568 | 12,558,807.568 | 12,558,807.568 | PASS | NA | NA |
| B3 | Until query | engine_only | records_out_per_sec | 10,329,579.702 | 10,329,579.702 | 10,329,579.702 | PASS | NA | NA |
| B4 | Full scan | engine_only | records_out_per_sec | 13,937,956.300 | 13,937,956.300 | 13,937,956.300 | PASS | NA | NA |
| B5 | Point query | engine_only | queries_per_sec | 85,401.100 | 85,401.100 | 85,401.100 | PASS | NA | NA |
| B6 | Microsecond window | engine_only | queries_per_sec | 730,302.819 | 730,302.819 | 730,302.819 | PASS | NA | NA |
| B7 | len(log) full count benchmark | engine_only | ops_per_sec | 252,983.203 | 252,983.203 | 252,983.203 | PASS | NA | NA |
| B8 | len(slice) remaining-count benchmark | engine_only | ops_per_sec | 179,491.293 | 179,491.293 | 179,491.293 | PASS | NA | NA |
| C1 | Orders per second | engine_only | records_out_per_sec | 15,529,476.869 | 15,529,476.869 | 15,529,476.869 | PASS | NA | NA |
| C1B | Orders/sec (single pass) | engine_only | records_out_per_sec | 4,550,841.342 | 4,550,841.342 | 4,550,841.342 | PASS | NA | NA |
| C2 | Buy/Sell ratio | engine_only | records_out_per_sec | 6,981,652.775 | 6,981,652.775 | 6,981,652.775 | PASS | NA | NA |
| C3 | Volume-weighted price (VWAP) | engine_only | records_out_per_sec | 4,878,968.645 | 4,878,968.645 | 4,878,968.645 | PASS | NA | NA |
| C4 | Order fill rate | engine_only | records_out_per_sec | 6,584,800.476 | 6,584,800.476 | 6,584,800.476 | PASS | NA | NA |
| C5 | Ticker activity | engine_only | records_out_per_sec | 3,854,064.313 | 3,854,064.313 | 3,854,064.313 | PASS | NA | NA |
| C6 | Spread analysis | engine_only | records_out_per_sec | 5,371,668.713 | 5,371,668.713 | 5,371,668.713 | PASS | NA | NA |
| C7 | Commission totals | engine_only | records_out_per_sec | 6,726,098.473 | 6,726,098.473 | 6,726,098.473 | PASS | NA | NA |
| C8 | Latency histogram | engine_only | records_out_per_sec | 5,663,583.071 | 5,663,583.071 | 5,663,583.071 | PASS | NA | NA |
| D1 | Delete time range | api_overhead | ops_per_sec | 248,036.591 | 248,036.591 | 248,036.591 | PASS | NA | NA |
| D2 | Evict old data | api_overhead | ops_per_sec | 245,816.687 | 245,816.687 | 245,816.687 | PASS | NA | NA |
| D3 | Verify deletion | api_overhead | ops_per_sec | 13,025.243 | 13,025.243 | 13,025.243 | PASS | NA | NA |
| D4 | Query after delete | api_overhead | records_out_per_sec | 4,828,022.927 | 4,828,022.927 | 4,828,022.927 | PASS | NA | NA |
| E1 | Manual flush | api_overhead | ms_per_op | 206.188 | 206.188 | 206.188 | PASS | NA | NA |
| E2 | Request compaction | api_overhead | ms_per_op | 184.200 | 184.200 | 184.200 | PASS | NA | NA |
| E3 | Background mode | api_overhead | records_in_per_sec | 2,236,897.763 | 2,236,897.763 | 2,236,897.763 | PASS | NA | NA |
| E4 | Maintenance lifecycle | api_overhead | records_in_per_sec | 1,834,496.749 | 1,834,496.749 | 1,834,496.749 | PASS | NA | NA |
| F1 | PageSpan iteration | engine_only | timestamps_per_sec | 974,440,408.389 | 974,440,408.389 | 974,440,408.389 | PASS | NA | NA |
| F2 | Timestamp memoryview | engine_only | timestamps_per_sec | 357,726,818.324 | 357,726,818.324 | 357,726,818.324 | PASS | NA | NA |
| F3 | Objects view | engine_only | objects_per_sec | 7,108,057.734 | 7,108,057.734 | 7,108,057.734 | PASS | NA | NA |
| F4 | NumPy integration | engine_only | timestamps_per_sec | 27,149,140.988 | 27,149,140.988 | 27,149,140.988 | PASS | NA | NA |
| F5 | Bulk statistics | engine_only | timestamps_per_sec | 170,922,640.664 | 170,922,640.664 | 170,922,640.664 | PASS | NA | NA |
| G1 | Batch iteration | engine_only | records_out_per_sec | 14,532,135.710 | 14,532,135.710 | 14,532,135.710 | PASS | NA | NA |
| G2 | Context manager | engine_only | records_out_per_sec | 14,074,672.617 | 14,074,672.617 | 14,074,672.617 | PASS | NA | NA |
| G3 | Early termination | engine_only | records_out_per_sec | 11,225,788.770 | 11,225,788.770 | 11,225,788.770 | PASS | NA | NA |
| G4 | Multiple iterators | engine_only | records_out_per_sec | 11,386,245.823 | 11,386,245.823 | 11,386,245.823 | PASS | NA | NA |
| H1 | Trade reconstruction | engine_only | records_out_per_sec | 113,629.908 | 113,629.908 | 113,629.908 | PASS | NA | NA |
| H2 | Market replay | engine_only | records_out_per_sec | 13,878,886.456 | 13,878,886.456 | 13,878,886.456 | PASS | NA | NA |
| H3 | Anomaly detection | engine_only | records_out_per_sec | 13,182,516.555 | 13,182,516.555 | 13,182,516.555 | PASS | NA | NA |
| H3B | Anomaly detection (single pass) | engine_only | records_out_per_sec | 6,371,376.312 | 6,371,376.312 | 6,371,376.312 | PASS | NA | NA |
| H4 | Audit trail | engine_only | queries_per_sec | 8,846.514 | 8,846.514 | 8,846.514 | PASS | NA | NA |
| I1 | Memtable read (hot data) | engine_only | records_out_per_sec | 990,798.455 | 990,798.455 | 990,798.455 | PASS | NA | NA |
| I2 | Cold data read (segments) | engine_only | records_out_per_sec | 10,463,825.177 | 10,463,825.177 | 10,463,825.177 | PASS | NA | NA |
| I3 | Mixed read (memtable + segments) | engine_only | records_out_per_sec | 13,148,516.400 | 13,148,516.400 | 13,148,516.400 | PASS | NA | NA |
| J1 | Verify O(M) iteration count | engine_only | ops_per_sec | 1,173,408.408 | 1,173,408.408 | 1,173,408.408 | PASS | PASS | NA |
| J2 | Verify scaling behavior | engine_only | ops_per_sec | 821,368.381 | 821,368.381 | 821,368.381 | PASS | PASS | NA |
| J3 | Verify no quadratic behavior | engine_only | ops_per_sec | 453,519.933 | 453,519.933 | 453,519.933 | PASS | PASS | NA |
| K1 | Append latency distribution (background) | mixed_workload | ops_per_sec | 699,079.731 | 699,079.731 | 699,079.731 | PASS | NA | NA |
| K1B | Append latency (manual flush/compact) | mixed_workload | ops_per_sec | 424,271.666 | 424,271.666 | 424,271.666 | PASS | NA | NA |
| K2 | Mixed workload (hot read) | mixed_workload | ops_per_sec | 935,292.141 | 935,292.141 | 935,292.141 | PASS | NA | NA |
| K3 | Mixed workload (cold read) | mixed_workload | ops_per_sec | 945,077.930 | 945,077.930 | 945,077.930 | PASS | NA | NA |
| K4 | Delete impact (hot vs cold) | mixed_workload | ops_per_sec | 475,438.841 | 475,438.841 | 475,438.841 | PASS | NA | NA |
| K5 | A2B stress grid (OOO + background) | mixed_workload | ops_per_sec | 211,163.732 | 211,163.732 | 211,163.732 | PASS | NA | NA |

## Apples Contract

Methodology comparison is performed only when scenario apples-contract metadata matches baseline.
