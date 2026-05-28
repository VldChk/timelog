# Timelog Benchmark Report (Unix, 1GB 7% OOO Dataset)

> Historical run artifact. For current publishable claim framing, use `docs/performance.md` and `docs/PERFORMANCE_METHODOLOGY.md`.

## Run Context

- Run timestamp: `2026-02-15T13:24:33.270037`
- Python: `3.13.12`
- Platform: `Linux-6.17.0-14-generic-x86_64-with-glibc2.39`
- CPU: `16` logical cores (`x86_64`)
- Memory: `50.42 GB` free / `62.08 GB` total at start
- Dataset: `demo/order_book_1GB_7pct_ooo_clean.csv`
- Dataset rows: `11,550,000` data rows (`11,550,001` lines including header)
- Command:

```bash
PYTHONPATH=python python3 demo/timelog_demo.py \
  --data demo/order_book_1GB_7pct_ooo_clean.csv \
  --no-tracemalloc \
  --repeat-min-seconds 0 \
  --export-json demo/benchmark_runs/timelog_demo_1gb_7pct_ooo_unix_20260215.json \
  --export-csv demo/benchmark_runs/timelog_demo_1gb_7pct_ooo_unix_20260215.csv
```

## Overall Outcome

- Total scenarios: `59`
- Passed vs expected target: `41`
- Failed vs expected target: `6`
- N/A (no throughput target or explicit error): `12`
- Failed scenarios: `A2B, D3, D4, E3, E4, F4`
- Error scenarios: `A6`

Interpretation: the demo generally exceeds configured baseline thresholds by wide margins, but six features miss their configured thresholds and one scenario (`A6`) requires a second comparison dataset that was not present in this run.

## Full Scenario Metrics

| Feature | Scenario | Records | Wall (s) | Rec/s | ns/rec | Expected | Ratio | Status |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| A0 | Ingest breakdown (parse vs Timelog vs end-to-end) | 50,000 | 0.378559 | 132,080 | 7,571.2 | - | - | N/A |
| A1 | Single record append | 10,000 | 0.036077 | 277,185 | 3,607.7 | 150,000 | 184.8% | PASS |
| A2 | Batch ingestion | 11,550,000 | 60.437922 | 191,105 | 5,232.7 | 200,000 | 95.6% | PASS |
| A2B | Batch ingestion (background maintenance) | 11,550,000 | 61.587184 | 187,539 | 5,332.2 | 250,000 | 75.0% | FAIL |
| A3 | Streaming ingestion | 50,000 | 0.190049 | 263,090 | 3,801.0 | 150,000 | 175.4% | PASS |
| A4 | Out-of-order ingestion | 20,000 | 0.079477 | 251,645 | 3,973.8 | 180,000 | 139.8% | PASS |
| A5 | Backpressure handling | 20,000 | 0.073563 | 271,878 | 3,678.1 | 100,000 | 271.9% | PASS |
| A6 | Order sensitivity (mostly vs less-ordered) | - | - | - | - | - | - | ERROR (no alternate dataset found) |
| B1 | Range query slice | 3,534 | 0.000308 | 11,471,493 | 87.2 | 800,000 | 1433.9% | PASS |
| B2 | Since query | 100,000 | 0.006913 | 14,466,375 | 69.1 | 800,000 | 1808.3% | PASS |
| B3 | Until query | 224,677 | 0.013979 | 16,072,019 | 62.2 | 800,000 | 2009.0% | PASS |
| B4 | Full scan | 11,550,000 | 0.638521 | 18,088,679 | 55.3 | 600,000 | 3014.8% | PASS |
| B5 | Point query | 1,000 | 0.010546 | 94,827 | 10,545.5 | 10,000 | 948.3% | PASS |
| B6 | Microsecond window | 1,000 | 0.001082 | 924,440 | 1,081.7 | 150,000 | 616.3% | PASS |
| B7 | len(log) full count benchmark | 25,000 | 0.062286 | 401,374 | 2,491.4 | 2,000 | 20068.7% | PASS |
| B8 | len(slice) remaining-count benchmark | 30,000 | 2.561061 | 11,714 | 85,368.7 | 2,000 | 585.7% | PASS |
| C1 | Orders per second | 36,711 | 0.003244 | 11,317,097 | 88.4 | 8,000 | 141463.7% | PASS |
| C1B | Orders/sec (single pass) | 36,711 | 0.005241 | 7,004,812 | 142.8 | 400,000 | 1751.2% | PASS |
| C2 | Buy/Sell ratio | 224,677 | 0.021497 | 10,451,463 | 95.7 | 600,000 | 1741.9% | PASS |
| C3 | Volume-weighted price (VWAP) | 1,119,242 | 0.160774 | 6,961,597 | 143.6 | 450,000 | 1547.0% | PASS |
| C4 | Order fill rate | 224,677 | 0.033561 | 6,694,639 | 149.4 | 550,000 | 1217.2% | PASS |
| C5 | Ticker activity | 224,677 | 0.052947 | 4,243,459 | 235.7 | 350,000 | 1212.4% | PASS |
| C6 | Spread analysis | 224,677 | 0.032177 | 6,982,564 | 143.2 | 400,000 | 1745.6% | PASS |
| C7 | Commission totals | 224,677 | 0.022157 | 10,140,452 | 98.6 | 550,000 | 1843.7% | PASS |
| C8 | Latency histogram | 36,711 | 0.006634 | 5,533,509 | 180.7 | 350,000 | 1581.0% | PASS |
| D1 | Delete time range | 50,000 | 0.177323 | 281,971 | 3,546.5 | 100,000 | 282.0% | PASS |
| D2 | Evict old data | 50,000 | 0.168444 | 296,835 | 3,368.9 | 100,000 | 296.8% | PASS |
| D3 | Verify deletion | 10,000 | 0.031733 | 315,129 | 3,173.3 | 500,000 | 63.0% | FAIL |
| D4 | Query after delete | 50,000 | 0.176469 | 283,336 | 3,529.4 | 800,000 | 35.4% | FAIL |
| E1 | Manual flush | 50,000 | 0.164006 | 304,867 | 3,280.1 | - | - | N/A |
| E2 | Request compaction | 50,000 | 0.163345 | 306,100 | 3,266.9 | - | - | N/A |
| E3 | Background mode | 50,000 | 0.182702 | 273,670 | 3,654.0 | 600,000 | 45.6% | FAIL |
| E4 | Maintenance lifecycle | 40,000 | 0.151864 | 263,393 | 3,796.6 | 600,000 | 43.9% | FAIL |
| F1 | PageSpan iteration | 224,677 | 0.000152 | 1,476,186,096 | 0.7 | 10,000,000 | 14761.9% | PASS |
| F2 | Timestamp memoryview | 36,711 | 0.000014 | 2,576,933,876 | 0.4 | 20,000,000 | 12884.7% | PASS |
| F3 | Objects view | 36,711 | 0.003473 | 10,568,918 | 94.6 | 2,000,000 | 528.4% | PASS |
| F4 | NumPy integration | 4,092 | 0.000134 | 30,535,718 | 32.7 | 50,000,000 | 61.1% | FAIL |
| F5 | Bulk statistics | 224,677 | 0.000668 | 336,160,141 | 3.0 | 50,000,000 | 672.3% | PASS |
| G1 | Batch iteration | 224,677 | 0.013503 | 16,638,936 | 60.1 | 900,000 | 1848.8% | PASS |
| G2 | Context manager | 224,677 | 0.014180 | 15,844,209 | 63.1 | 700,000 | 2263.5% | PASS |
| G3 | Early termination | 10,000 | 0.000693 | 14,437,785 | 69.3 | 700,000 | 2062.5% | PASS |
| G4 | Multiple iterators | 186,813 | 0.011258 | 16,593,393 | 60.3 | 500,000 | 3318.7% | PASS |
| H1 | Trade reconstruction | 10 | 0.000020 | 495,614 | 2,017.7 | 300,000 | 165.2% | PASS |
| H2 | Market replay | 224,677 | 0.014922 | 15,056,647 | 66.4 | 600,000 | 2509.4% | PASS |
| H3 | Anomaly detection | 224,677 | 0.013704 | 16,394,709 | 61.0 | - | - | N/A |
| H3B | Anomaly detection (single pass) | 224,677 | 0.032835 | 6,842,641 | 146.1 | 400,000 | 1710.7% | PASS |
| H4 | Audit trail | 100 | 0.009404 | 10,633 | 94,044.1 | - | - | N/A |
| I1 | Memtable read (hot data) | 10,000 | 0.009958 | 1,004,231 | 995.8 | 100,000 | 1004.2% | PASS |
| I2 | Cold data read (segments) | 3,534 | 0.000266 | 13,270,697 | 75.4 | 1,000 | 1327069.7% | PASS |
| I3 | Mixed read (memtable + segments) | 11,551,000 | 0.679066 | 17,010,119 | 58.8 | 500,000 | 3402.0% | PASS |
| J1 | Verify O(M) iteration count | 16,100 | 0.010590 | 1,520,368 | 657.7 | 100,000 | 1520.4% | PASS |
| J2 | Verify scaling behavior | 31,000 | 0.028017 | 1,106,458 | 903.8 | 100,000 | 1106.5% | PASS |
| J3 | Verify no quadratic behavior | 16,000 | 0.026467 | 604,531 | 1,654.2 | 50,000 | 1209.1% | PASS |
| K1 | Append latency distribution (background) | 200,000 | 0.317193 | 630,531 | 1,586.0 | - | - | N/A |
| K1B | Append latency (manual flush/compact) | 200,000 | 0.338744 | 590,417 | 1,693.7 | - | - | N/A |
| K2 | Mixed workload (hot read) | 100,000 | 0.112248 | 890,883 | 1,122.5 | - | - | N/A |
| K3 | Mixed workload (cold read) | 60,000 | 0.064616 | 928,563 | 1,076.9 | - | - | N/A |
| K4 | Delete impact (hot vs cold) | 100,000 | 0.161495 | 619,213 | 1,615.0 | - | - | N/A |
| K5 | A2B stress grid (OOO + background) | 20,000 | 0.128611 | 155,508 | 6,430.5 | - | - | N/A |

## Key Metrics For Complexity Discussion

- `A2` full batch ingest: `11,550,000` records in `60.438s` = `191,105` rec/s (`5,232.7` ns/record), `busy_events=0`.
- `A2B` background ingest: `11,550,000` records in `61.587s` = `187,539` rec/s (`5,332.2` ns/record).
- `D1`/`D2` functional delete checks: `before->13289, after->0` and `before->50000, after->0`.
- `D3` point-after-delete check: `before_count=1, after_count=0`.
- `D4` range-after-delete check: `in_deleted_range=0` (correctness OK, throughput target missed).
- `B5` point lookup throughput: `94,827` point queries/s (1,000 sampled timestamps).
- `B4` full scan throughput: `18,088,679` rec/s over `11,550,000` rows.
- `J1` iterator cardinality checks: all exact (`ratio==1.0` for each window): `True`.
- `J2` scaling exponent (log-log fit): `1.042` (`O(N) or O(N log N) - GOOD`).
- `J3` doubling-time ratio: avg `1.99` (`No quadratic behavior - GOOD`).
- `K1` append latency (background): `p50=401ns`, `p95=561ns`, `p99=672ns`, `max=1246476ns`.

## Complexity-Claim Assessment (What We Can Say In README)

### 1) Insert is amortized O(1): **reasonable claim with scope conditions**

- Write path appends to dynamic vectors for in-order or OOO-head inserts (`core/src/delta/tl_memtable.c:407`, `core/src/delta/tl_memtable.c:416`, `core/src/delta/tl_memtable.c:435`).
- This supports amortized O(1) append semantics at the memtable layer under standard geometric-resize assumptions.
- Caveat: sealing/flush/maintenance introduces periodic heavier work and backpressure signaling (`TL_EBUSY`), so tail latency is workload/config dependent.

### 2) Delete is amortized O(1): **not a safe generic claim**

- Logical delete writes tombstone intervals (`core/src/delta/tl_memtable.c:612`).
- Tombstones are inserted/coalesced in an interval structure that performs splitting, insertion, and coalescing across existing intervals (`core/src/internal/tl_intervals.c:183`, `core/src/internal/tl_intervals.c:216`, `core/src/internal/tl_intervals.c:228`, `core/src/internal/tl_intervals.c:273`).
- That behavior is not strict O(1) in general; complexity depends on interval count/overlap pattern.
- Better wording: deletes are **logical tombstone inserts** with complexity dependent on tombstone set shape, and physical removal is deferred to maintenance/compaction.

### 3) Point lookup is O(log N): **approximately true only with bounded source count**

- Point fast path uses binary-search style lookup per storage component (`core/src/query/tl_point.h:11`-`core/src/query/tl_point.h:26`).
- Practical complexity is closer to: `O(log S1 + sum_over_sources(log P + log rows) + D)` where `D` is duplicates at timestamp.
- If compaction keeps active source count bounded, this can be presented as effectively logarithmic in dataset size.

### 4) Range scan = two logarithmic endpoint seeks + iterator over results: **true only for single-source idealized case**

- Range planning does endpoint pruning and source selection (`core/src/query/tl_plan.c:210`-`core/src/query/tl_plan.c:330`).
- Execution then does K-way heap merge across sources (`core/src/query/tl_merge_iter.h:10`-`core/src/query/tl_merge_iter.h:25`) plus tombstone filtering with amortized O(1) cursor checks (`core/src/query/tl_filter.h:11`-`core/src/query/tl_filter.h:23`).
- So the general read-path statement is: `plan + merge/filter cost`, typically modeled as `O(log endpoints + M log K)` where `M` is emitted rows and `K` is active source count. With small bounded `K`, this approaches `O(log N + M)`.

## Suggested README Wording

Use this conservative phrasing to avoid over-claiming:

> Timelog writes are append-oriented and amortized O(1) at the memtable layer. Deletes are logical tombstone inserts (complexity depends on tombstone interval state), with physical cleanup deferred to maintenance. Point lookups use component-level binary search and are effectively logarithmic when source fan-out is bounded by compaction. Range queries perform logarithmic pruning/seek plus merged iteration over matches; with bounded source fan-out this is near O(log N + M).

## Artifacts

- Raw stdout: `demo/benchmark_runs/timelog_demo_1gb_7pct_ooo_unix_20260215.out`
- JSON export: `demo/benchmark_runs/timelog_demo_1gb_7pct_ooo_unix_20260215.json`
- CSV export: `demo/benchmark_runs/timelog_demo_1gb_7pct_ooo_unix_20260215.csv`

## Notes

- This run used `--no-tracemalloc` to reduce measurement overhead.
- Several demo expected thresholds are intentionally conservative and some scenario metrics are operation-count based (e.g., B5/B7/B8), not row-throughput in the ingestion sense.
