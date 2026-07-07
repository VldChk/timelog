# Timelog Methodology Benchmark Report

- Timestamp: `2026-07-07T14:58:53.244756`
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
| A2 | Batch ingestion | e2e | records_in_per_sec | 249,524.977 | 254,773.536 | 255,240.074 | PASS | NA | NA |
| A2B | Batch ingestion (background maintenance) | e2e | records_in_per_sec | 4,122,917.360 | 4,162,077.529 | 4,165,558.433 | PASS | NA | NA |
| B4 | Full scan | engine_only | records_out_per_sec | 15,299,697.356 | 15,407,356.239 | 15,416,925.918 | PASS | NA | NA |
| B5 | Point query | engine_only | queries_per_sec | 93,319.047 | 94,354.841 | 94,446.911 | PASS | NA | NA |
| D3 | Verify deletion | api_overhead | ops_per_sec | 17,489.550 | 18,051.826 | 18,101.806 | PASS | NA | NA |
| D4 | Query after delete | api_overhead | records_out_per_sec | 5,529,035.231 | 5,629,709.963 | 5,638,658.828 | PASS | NA | NA |
| E3 | Background mode | api_overhead | records_in_per_sec | 5,481,316.002 | 5,636,527.209 | 5,650,323.760 | PASS | NA | NA |
| E4 | Maintenance lifecycle | api_overhead | records_in_per_sec | 5,259,680.968 | 5,822,665.547 | 5,872,708.621 | PASS | NA | NA |
| F4 | NumPy integration | engine_only | timestamps_per_sec | 0.000 | 0.000 | 0.000 | PASS | NA | NA |
| I3 | Mixed read (memtable + segments) | engine_only | records_out_per_sec | 14,853,257.900 | 14,899,268.706 | 14,903,358.556 | PASS | NA | NA |
| J1 | Verify O(M) iteration count | engine_only | ops_per_sec | 1,856,876.139 | 1,871,891.083 | 1,873,225.745 | PASS | PASS | NA |
| J2 | Verify scaling behavior | engine_only | ops_per_sec | 1,149,070.341 | 1,157,027.333 | 1,157,734.621 | PASS | PASS | NA |
| J3 | Verify no quadratic behavior | engine_only | ops_per_sec | 623,913.927 | 633,133.239 | 633,952.734 | PASS | PASS | NA |
| K1 | Append latency distribution (background) | mixed_workload | ops_per_sec | 971,798.221 | 1,005,718.633 | 1,008,733.781 | PASS | NA | NA |

## Apples Contract

Methodology comparison is performed only when scenario apples-contract metadata matches baseline.
