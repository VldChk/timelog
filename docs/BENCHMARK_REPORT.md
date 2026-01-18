# Timelog Benchmark Report

**Version:** 0.4.5
**Date:** 2026-01-17
**Dataset:** `tiny_order_book_mostly_ordered_clean.csv` (100K records)
**Platform:** Windows 10, Python 3.13, AMD64

---

## Summary

This report presents benchmark results for Timelog, an LSM-style time-indexed storage engine written in C17 with Python bindings. The benchmarks cover 57 test cases across 11 categories.

Measured throughput ranges:
- End-to-end ingest: 35–42K records/sec (includes CSV parsing)
- Core C engine: 8M records/sec (isolated measurement)
- Iterator queries: 600K–1M records/sec
- PageSpan access: 100–300M timestamps/sec

Scaling tests confirm O(N) or O(N log N) behaviour with no quadratic patterns detected.

---

## Contents

1. [Notation](#notation)
2. [Methodology](#methodology)
3. [Category A: Data Ingestion](#category-a-data-ingestion)
4. [Category B: Time Range Queries](#category-b-time-range-queries)
5. [Category C: Analytics](#category-c-analytics)
6. [Category D: Deletion](#category-d-deletion)
7. [Category E: Maintenance](#category-e-maintenance)
8. [Category F: PageSpan](#category-f-pagespan)
9. [Category G: Iterator Patterns](#category-g-iterator-patterns)
10. [Category H: Application Patterns](#category-h-application-patterns)
11. [Category I: Memory Tiers](#category-i-memory-tiers)
12. [Category J: Complexity Verification](#category-j-complexity-verification)
13. [Category K: Production Workloads](#category-k-production-workloads)
14. [Observations](#observations)
15. [Configuration Guidelines](#configuration-guidelines)

---

## Notation

### Complexity Variables

| Symbol | Definition | Typical Range |
|--------|------------|---------------|
| **N** | Total records in Timelog | 100K – 100M |
| **M** | Records in result set | 1 – N |
| **K** | LSM components (memtable + sealed runs + L0 + L1 segments) | 1 – 20 |
| **P** | Pages per component | 1 – 10K |
| **B** | Batch size | 1K – 100K |
| **T** | Tombstone intervals | 0 – 1K |
| **W** | Window count (multi-window queries) | 1 – 100 |
| **S** | Records in sealed memrun | 10K – 1M |
| **I** | Concurrent iterators | 1 – 10 |
| **L** | Lifecycle events per order | 1 – 100 |
| **D** | Duplicate records at timestamp | 1 – 1K |
| **R** | Records per page | 100 – 10K |
| **F** | Flush operations | 0 – 100 |
| **G** | Grid test combinations | varies |
| **P_r** | Pages in query range | varies |

### Complexity Patterns

| Pattern | Meaning | Occurs In |
|---------|---------|-----------|
| O(1) | Constant | Memoryview access |
| O(log P) | Binary search within component | Page lookup |
| O(K·log P) | Binary search across components | Query setup |
| O(M) | Linear in result size | Iteration |
| O(K·log P + M) | Setup plus scan | Range query |
| O(N) | Full scan | Complete iteration |
| O(N·log S) | Ingest with sorting | Out-of-order data |
| O(M·log M) | Sort | Flush operation |

### Throughput Categories

| Category | Range | Limiting Factor |
|----------|-------|-----------------|
| Python-bound | 30–50K/sec | CSV parsing, object allocation |
| Iterator-bound | 500K–1M/sec | Python iteration, pickle |
| Zero-copy | 10–300M/sec | Buffer access |
| Core engine | 5–10M/sec | C implementation |

---

## Methodology

### Environment

- OS: Windows 10/11
- Python: 3.13 (CPython)
- Build: Release, static linking

### Measurements

- Wall time: `time.perf_counter_ns()`
- CPU time: `time.process_time_ns()`
- Memory: `tracemalloc`
- GC: Triple collection before each test

### Datasets

| File | Records | Ordering |
|------|---------|----------|
| `tiny_order_book_mostly_ordered_clean.csv` | 100K | ~95% ordered |
| `tiny_order_book_less_ordered_clean.csv` | 100K | ~80% ordered |

### Scope

Most tests measure end-to-end time including CSV parsing. This reflects real application throughput. To measure isolated engine performance, see:
- A0: Explicit breakdown of parse vs engine time
- F1–F5: PageSpan bypasses Python object layer
- K1/K1B: Synthetic data without CSV

---

## Category A: Data Ingestion

Write path performance across ingestion patterns.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| A0 | 50,000 | 3.018 | 16.6K | O(N) | Breakdown: CSV 38K/s, Timelog-only 8.08M/s, end-to-end 30K/s |
| A1 | 10,000 | 0.256 | 39.0K | O(1) amortized | Single `append()` per record |
| A2 | 100,000 | 2.674 | 37.4K | O(B) | Batch `extend()`, 10K batches, ordered data |
| A2_less | 100,000 | 2.588 | 38.7K | O(B) | Same as A2, 80% ordered data |
| A2B | 100,000 | 2.775 | 36.0K | O(B) | Batch with background maintenance, ordered |
| A2B_less | 100,000 | 2.667 | 37.5K | O(B) | Batch with background maintenance, less ordered |
| A3 | 50,000 | 1.189 | 42.1K | O(N) | Streaming append with background maintenance |
| A4 | 20,000 | 0.536 | 37.3K | O(N·log S) | Shuffled data, OOO vector sorted on seal |
| A5 | 20,000 | 0.492 | 40.6K | O(N + F·M) | Small memtable (64KB), frequent flushes |
| A6 | 40,000 | 0.972 | 41.2K | O(N) | Comparison of ordered vs less-ordered datasets |

**Observations:**
- End-to-end throughput is 35–42K/s across all patterns
- Isolated engine throughput is 8M/s (A0 breakdown)
- Difference between ordered and less-ordered data is ~3%
- Background maintenance adds ~3% overhead

---

## Category B: Time Range Queries

Read path performance for query patterns.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| B1 | 3,596 | 0.004 | 976K | O(K·log P + M) | `log[t1:t2]` slice, 1-second window |
| B2 | 99,000 | 0.145 | 681K | O(K·log P + M) | `log[t1:]` since midpoint |
| B3 | 100,000 | 0.129 | 776K | O(K·log P + M) | `log[:t2]` until 60 seconds |
| B4 | 100,000 | 0.093 | 1.07M | O(N) | `iter(log)` full scan |
| B5 | 1,000 | 0.110 | 9.1K | O(K·log P + D) | 1000 point queries via `at()` |
| B6 | 1,000 | 0.006 | 158K | O(K·log P + M) | 1000 queries, 1μs windows |

**Observations:**
- Full scan (B4) reaches 1.07M/s
- Point queries (B5) show 9.1K queries/sec due to per-query setup cost
- Small-window queries (B6) reach 158K queries/sec

---

## Category C: Analytics

Time-series analytics over query results.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| C1 | 35,877 | 0.022 | 1.63M | O(W·(K·log P + M)) | 10 separate 1-second window counts |
| C1B | 35,877 | 0.130 | 276K | O(K·log P + M) | Single pass with per-record window assignment |
| C2 | 100,000 | 0.120 | 836K | O(K·log P + M) | Buy/sell ratio, string comparison per record |
| C3 | 100,000 | 0.157 | 636K | O(K·log P + M) | VWAP calculation, arithmetic per record |
| C4 | 100,000 | 0.125 | 802K | O(K·log P + M) | Fill rate, three-way status classification |
| C5 | 100,000 | 0.211 | 473K | O(K·log P + M) | Ticker counts using Counter |
| C6 | 100,000 | 0.205 | 489K | O(K·log P + M) | Spread analysis with list accumulation |
| C7 | 100,000 | 0.137 | 729K | O(K·log P + M) | Commission sum, float accumulation |
| C8 | 35,877 | 0.086 | 418K | O(K·log P + M) | Latency histogram, gap calculation per record |

**Observations:**
- C1 (multiple queries, 1.63M/s) is faster than C1B (single pass, 276K/s)
- Per-record Python work reduces throughput by 20–50%
- Dict operations (C5) add ~40% overhead vs simple arithmetic (C7)

---

## Category D: Deletion

Tombstone operations and filtering.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| D1 | 50,000 | 1.290 | 38.8K | O(N) + O(log T) | `delete_range()` with verification |
| D2 | 50,000 | 1.402 | 35.7K | O(N) + O(log T) | `delete_before()` TTL-style |
| D3 | 10,000 | 0.274 | 36.5K | O(N) + O(log T) | Point query on deleted timestamp |
| D4 | 50,000 | 1.393 | 35.9K | O(N) + O(K·log P + M) | Range query after deletion |

**Note:** Measurements include data loading. Tombstone insertion itself is O(log T) and sub-millisecond.

**Observations:**
- Tombstone insertion time is negligible compared to data loading
- Query filtering cost is O(log T) per page boundary
- `compact()` physically removes deleted data

---

## Category E: Maintenance

Flush and compaction operations.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| E1 | 50,000 | 1.340 | 37.3K | O(N) + O(M·log M) | Load + explicit `flush()` |
| E2 | 50,000 | 1.758 | 28.4K | O(N) + O(S·log S) | Multiple flushes + `compact()` |
| E3 | 50,000 | 1.461 | 34.2K | O(N) | `maintenance="background"` |
| E4 | 40,000 | 1.037 | 38.6K | O(N) | `start_maintenance()` / `stop_maintenance()` |

**Observations:**
- Background maintenance (E3) adds ~8% overhead vs disabled mode
- Compaction (E2) adds ~25% overhead due to segment merging
- Worker start/stop is O(1)

---

## Category F: PageSpan

Zero-copy timestamp access.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| F1 | 100,000 | 0.001 | 103.9M | O(K·log P + P_r) | Iterate page spans |
| F2 | 35,877 | 0.000 | 302.5M | O(1) | Access `span.timestamps` memoryview |
| F3 | 35,877 | 0.004 | 8.73M | O(R) | `span.objects()` unpickle |
| F4 | 4,092 | 0.000 | 12.9M | O(1) + O(R) | `np.asarray()` + `np.diff()` + `np.mean()` |
| F5 | 100,000 | 0.003 | 28.6M | O(R) | Min/max/mean/std with `np.concatenate()` |

**Observations:**
- Memoryview access (F2) reaches 302M timestamps/sec
- NumPy operations use zero-copy buffer protocol
- Object unpickling (F3) is limited by pickle deserialization

---

## Category G: Iterator Patterns

Different iteration approaches.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| G1 | 100,000 | 0.126 | 792K | O(N) | `next_batch(1000)` |
| G2 | 100,000 | 0.110 | 912K | O(N) | Context manager |
| G3 | 10,000 | 0.011 | 938K | O(K·log P + M) | Early termination via `break` |
| G4 | 100,000 | 0.062 | 1.62M | O(I·(K·log P + M)) | 5 concurrent iterators |

**Observations:**
- `next_batch()` amortizes Python→C call overhead
- Context manager has negligible overhead
- Multiple iterators scale linearly with I

---

## Category H: Application Patterns

Patterns from trading applications.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| H1 | 44 | 0.000 | 415K | O(K·log P + L) | Order lifecycle trace |
| H2 | 100,000 | 0.115 | 871K | O(K·log P + M) | Market replay, 1-minute session |
| H3 | 100,000 | 0.065 | 1.55M | O(W·(K·log P + R)) | 60 separate 1-second queries |
| H3B | 100,000 | 0.331 | 302K | O(K·log P + M) | Single pass with per-record window math |
| H4 | 100 | 0.103 | 974 | O(K·log P + D) | 100 exact-timestamp lookups |

**Observations:**
- H3 (multiple queries, 1.55M/s) is faster than H3B (single pass, 302K/s)
- Same pattern as C1 vs C1B: query setup cost < per-record Python overhead
- Point queries (H4) limited by per-query setup

---

## Category I: Memory Tiers

Comparison of memtable and segment reads.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| I1 | 10,000 | 0.085 | 118K | O(N) + O(M) | Write + read from memtable |
| I2 | 3,596 | 0.005 | 660K | O(K·log P + M) | Read from segments |
| I3 | 101,000 | 0.183 | 552K | O(K·log P + M) | k-way merge across memtable + segments |

**Note:** I1 includes write time; I2 is read-only. Direct comparison is not valid.

**Observations:**
- k-way merge (I3) shows minimal overhead for mixed sources
- For valid hot/cold comparison, measure read-only on both paths

---

## Category J: Complexity Verification

Empirical verification of algorithmic complexity.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| J1 | 16,100 | 0.102 | 158K | O(M) | Verify iteration count = result size |
| J2 | 31,000 | 0.272 | 114K | O(N) or O(N log N) | Scaling test, sizes 1K→16K |
| J3 | 16,000 | 0.236 | 67.9K | O(N) | Verify no quadratic behaviour |

**Results:**
- J1: Iteration count equals result size (ratio 1.0 ± 0.001)
- J2: Scaling exponent 1.05, confirms O(N) or O(N log N)
- J3: Time ratio when doubling N is 2.1 (quadratic would be 4.0)

---

## Category K: Production Workloads

Production-like scenarios with latency analysis.

| Test | Records | Wall(s) | RPS | Complexity | Notes |
|------|--------:|--------:|----:|------------|-------|
| K1 | 5,000 | 0.046 | 109K | O(N) | Append latency, background mode. p50: 1.3μs, p99: 2.8μs |
| K1B | 5,000 | 0.053 | 94.6K | O(N) | Append latency, manual flush. p50: 1.3μs, p99: 2.9μs |
| K2 | 20,000 | 0.136 | 147K | O(N) | Write + read from memtable |
| K3 | 15,000 | 0.103 | 146K | O(N) | Write + flush + read from segments |
| K4 | 20,000 | — | — | O(N) | Read before/after delete, before/after compact |
| K5 | varies | — | — | O(G·N) | Grid test over configuration parameters |

**Observations:**
- Append latency: p50 ~1.3μs, p99 ~2.8μs
- Mixed workloads (K2, K3) reach similar throughput (~147K/s)
- K5 tests combinations of maintenance mode, busy policy, memtable size, sealed run limit

---

## Observations

### Throughput by Operation Type

| Operation | Throughput | Limiting Factor |
|-----------|------------|-----------------|
| PageSpan timestamps | 100–300M/s | Buffer access |
| Core engine | 8M/s | C implementation |
| Iterator + unpickle | 500K–1M/s | Python overhead |
| End-to-end ingest | 35–45K/s | CSV parsing |

### Bottleneck Analysis

| Operation | Bottleneck | Alternative |
|-----------|------------|-------------|
| Ingest | CSV parsing, object allocation | Use `--trust-csv`, batch ingestion |
| Iteration | Python `__next__`, pickle | Use `next_batch()`, PageSpan |
| Point queries | Per-query setup | Batch into range queries |
| Analytics | Per-record computation | Use PageSpan + NumPy |

### Query Pattern Performance

Multiple simple queries (C1, H3) outperform single-pass with per-record computation (C1B, H3B). Query setup cost is lower than per-record Python overhead at these scales.

### Complexity Verification

- Scaling exponent: 1.05 (linear or log-linear)
- Doubling ratio: 2.1 (no quadratic behaviour)
- Iteration count equals result size

---

## Configuration Guidelines

### Ingest

- Use `extend()` with batches of 10K records
- Enable `maintenance="background"` for automatic flush
- Use `--trust-csv` when input is pre-validated

### Queries

- Use PageSpan for timestamp-only workloads
- Use `next_batch(n)` for bulk record retrieval
- Batch point queries into range queries

### Latency

- Increase `memtable_max_bytes` to keep data in memory longer
- Adjust `sealed_max_runs` to control backpressure threshold
- Use `busy_policy="flush"` for automatic draining

### Production

- Start with `maintenance="background"`
- Monitor `TimelogBusyError` frequency
- Use K5 grid test to find optimal parameters
- Use J1–J3 to detect regression

---

## Appendix: Results Table

<details>
<summary>Full results</summary>

| Test | Records | Wall(s) | RPS | Complexity |
|------|--------:|--------:|----:|------------|
| A0 | 50,000 | 3.018 | 16.6K | O(N) |
| A1 | 10,000 | 0.256 | 39.0K | O(1) amortized |
| A2 | 100,000 | 2.674 | 37.4K | O(B) |
| A2_less | 100,000 | 2.588 | 38.7K | O(B) |
| A2B | 100,000 | 2.775 | 36.0K | O(B) |
| A2B_less | 100,000 | 2.667 | 37.5K | O(B) |
| A3 | 50,000 | 1.189 | 42.1K | O(N) |
| A4 | 20,000 | 0.536 | 37.3K | O(N·log S) |
| A5 | 20,000 | 0.492 | 40.6K | O(N + F·M) |
| A6 | 40,000 | 0.972 | 41.2K | O(N) |
| B1 | 3,596 | 0.004 | 976K | O(K·log P + M) |
| B2 | 99,000 | 0.145 | 681K | O(K·log P + M) |
| B3 | 100,000 | 0.129 | 776K | O(K·log P + M) |
| B4 | 100,000 | 0.093 | 1.07M | O(N) |
| B5 | 1,000 | 0.110 | 9.1K | O(K·log P + D) |
| B6 | 1,000 | 0.006 | 158K | O(K·log P + M) |
| C1 | 35,877 | 0.022 | 1.63M | O(W·(K·log P + M)) |
| C1B | 35,877 | 0.130 | 276K | O(K·log P + M) |
| C2 | 100,000 | 0.120 | 836K | O(K·log P + M) |
| C3 | 100,000 | 0.157 | 636K | O(K·log P + M) |
| C4 | 100,000 | 0.125 | 802K | O(K·log P + M) |
| C5 | 100,000 | 0.211 | 473K | O(K·log P + M) |
| C6 | 100,000 | 0.205 | 489K | O(K·log P + M) |
| C7 | 100,000 | 0.137 | 729K | O(K·log P + M) |
| C8 | 35,877 | 0.086 | 418K | O(K·log P + M) |
| D1 | 50,000 | 1.290 | 38.8K | O(N) + O(log T) |
| D2 | 50,000 | 1.402 | 35.7K | O(N) + O(log T) |
| D3 | 10,000 | 0.274 | 36.5K | O(N) + O(log T) |
| D4 | 50,000 | 1.393 | 35.9K | O(N) + O(K·log P + M) |
| E1 | 50,000 | 1.340 | 37.3K | O(N) + O(M·log M) |
| E2 | 50,000 | 1.758 | 28.4K | O(N) + O(S·log S) |
| E3 | 50,000 | 1.461 | 34.2K | O(N) |
| E4 | 40,000 | 1.037 | 38.6K | O(N) |
| F1 | 100,000 | 0.001 | 103.9M | O(K·log P + P_r) |
| F2 | 35,877 | 0.000 | 302.5M | O(1) |
| F3 | 35,877 | 0.004 | 8.73M | O(R) |
| F4 | 4,092 | 0.000 | 12.9M | O(1) + O(R) |
| F5 | 100,000 | 0.003 | 28.6M | O(R) |
| G1 | 100,000 | 0.126 | 792K | O(N) |
| G2 | 100,000 | 0.110 | 912K | O(N) |
| G3 | 10,000 | 0.011 | 938K | O(K·log P + M) |
| G4 | 100,000 | 0.062 | 1.62M | O(I·(K·log P + M)) |
| H1 | 44 | 0.000 | 415K | O(K·log P + L) |
| H2 | 100,000 | 0.115 | 871K | O(K·log P + M) |
| H3 | 100,000 | 0.065 | 1.55M | O(W·(K·log P + R)) |
| H3B | 100,000 | 0.331 | 302K | O(K·log P + M) |
| H4 | 100 | 0.103 | 974 | O(K·log P + D) |
| I1 | 10,000 | 0.085 | 118K | O(N) + O(M) |
| I2 | 3,596 | 0.005 | 660K | O(K·log P + M) |
| I3 | 101,000 | 0.183 | 552K | O(K·log P + M) |
| J1 | 16,100 | 0.102 | 158K | O(M) |
| J2 | 31,000 | 0.272 | 114K | O(N log N) |
| J3 | 16,000 | 0.236 | 67.9K | O(N) |
| K1 | 5,000 | 0.046 | 109K | O(N) |
| K1B | 5,000 | 0.053 | 94.6K | O(N) |
| K2 | 20,000 | 0.136 | 147K | O(N) |
| K3 | 15,000 | 0.103 | 146K | O(N) |
| K4 | 20,000 | — | — | O(N) |
| K5 | varies | — | — | O(G·N) |

</details>

---

*Timelog v0.4.5*
