# Timelog Performance Methodology (Apples-to-Apples)

## 1. Goal

Define a repeatable, defensible method to evaluate Timelog performance and complexity claims without mixing incomparable measurements.

This methodology separates:
- correctness from performance
- end-to-end throughput from engine-only throughput
- operation-count benchmarks from row-throughput benchmarks
- steady-state complexity from one-time setup cost

## 2. "Apples" Contract (What Must Match Before Comparing)

Two results are comparable only if all fields below match.

| Dimension | Required Match | Examples of mismatch (not comparable) |
|---|---|---|
| Operation type | Same API behavior | `append` vs `extend`, `point` vs `range` |
| Timing boundary | Same boundary type | end-to-end (CSV+Python+engine) vs engine-only |
| Unit of work | Same denominator | rows/sec vs queries/sec |
| Data shape | Same distribution | 0% OOO vs 7% OOO, low vs high duplicates |
| State profile | Same hot/warm/cold state | memtable-hot vs post-flush segment scan |
| Maintenance mode | Same mode/config | background vs disabled/manual |
| Runtime layer | Same layer | Python facade vs C core |
| Environment | Same machine/build | debug vs release, different CPU governor |

If any dimension differs, treat comparison as directional only.

## 3. Canonical Measurement Types

Each benchmark must declare exactly one `measurement_type`.

1. `e2e`
- Includes parsing, object creation, API calls, and return processing.
- Use for user-visible throughput claims.

2. `engine_only`
- Excludes CSV parse and object construction from timed window.
- Use for data-structure/algorithm claims.

3. `api_overhead`
- Measures control-path APIs where rows are not the denominator (`len`, lifecycle ops, maintenance calls).
- Use ops/sec or latency distributions.

4. `mixed_workload`
- Interleaves writes/reads/deletes according to a fixed schedule.
- Use for tail-latency and interference claims.

## 4. Canonical Units (No Unit Ambiguity)

Each scenario must declare exactly one primary unit.

| Operation class | Primary unit | Secondary unit |
|---|---|---|
| Ingestion (append/extend) | `records_in_per_sec` | `ns_per_record_in` |
| Range scan | `records_out_per_sec` | `scan_ns_per_record_out` |
| Point lookup | `queries_per_sec` | `p50/p95/p99 query latency` |
| Delete / cutoff insertion | `ops_per_sec` | `p50/p95/p99 op latency` |
| Flush / compact | `ms_per_op` | bytes processed/op |
| Buffer/NumPy access | `timestamps_per_sec` or `bytes_per_sec` | latency distribution |

Rule: do not label op-count benchmarks as row-throughput benchmarks.

## 5. Timing Window Rules

Every scenario must publish four phases:
- `setup_time`: data generation/loading/preconditioning
- `warmup_time`: untimed warmup executions
- `measure_time`: only timed phase for KPI
- `teardown_time`: cleanup/finalization

KPI is computed only from `measure_time`.

## 6. State Profiles

Every read/write benchmark must declare one profile:

1. `hot`
- Data mostly in memtable / recently accessed structures.

2. `warm`
- Segment-backed but page cache likely warm.

3. `cold`
- Segment-backed after cache perturbation or fresh process.

4. `mixed`
- Interleaved hot + cold populations.

State must be reported in output metadata.

## 7. Complexity Hypotheses to Test

Theoretical claims are accepted only after scaling tests against controlled axes.

### 7.1 Insert path
Hypothesis:
- amortized append cost is constant per record at memtable layer

Validation:
- sweep `N` with fixed data shape and maintenance settings
- fit `ns_per_record_in` vs `N`
- pass condition: slope ~ 0 within tolerance and no superlinear exponent

### 7.2 Delete path
Hypothesis:
- delete is logical tombstone insertion, complexity depends on tombstone interval state

Validation:
- sweep tombstone interval count `T` and overlap patterns
- fit latency vs `log2(T)` and overlap factor
- do not claim strict O(1) unless experimentally and structurally justified

### 7.3 Point lookup
Hypothesis:
- effectively logarithmic in data size when source fan-out `K` is bounded

Validation:
- sweep `N` at fixed bounded `K`
- separately sweep `K` at fixed `N`
- model `latency = a + b*log2(N) + c*K + d*D`
  where `D` = duplicates at target timestamp

### 7.4 Range query
Hypothesis:
- seek overhead is logarithmic-like; iteration is linear in result size `M`

Validation:
- run `M=0`/tiny windows to estimate seek term
- run varied `M` windows to estimate scan term
- model `latency = a + b*log2(N) + c*M + d*M*log2(K)`
- with bounded `K`, expect near `O(log N + M)` behavior

## 8. Experiment Matrix

Minimum matrix for each release:

| Axis | Values |
|---|---|
| Data size `N` | 100K, 500K, 1M, 5M, 11.55M |
| OOO ratio | 0%, 1%, 7%, 20% |
| Tombstone density | 0%, 1%, 5%, 20% of covered time range |
| Fan-out state `K` | compacted (low K), fragmented (high K) |
| Maintenance mode | disabled/manual, background |
| Layer | engine-only, Python API, e2e |

Not every scenario needs full matrix, but complexity claims must include N/K sweeps.

## 9. Statistical Protocol

For each scenario point:
- warmup runs: >= 3
- measured runs: >= 10 (prefer 20)
- report median + p95 + p99 + MAD
- use confidence interval (bootstrap or t-interval) for headline metric

Regression acceptance uses medians, not single best run.

## 10. Regression Gates

Use independent gates:

1. Correctness gate (hard fail)
- Any semantic mismatch = fail regardless of throughput.

2. Complexity gate (hard fail for release claims)
- Exponent/slope violates hypothesis tolerance.

3. Throughput gate (soft or hard by tier)
- Compare against same apples contract only.
- Default threshold: fail only if median regresses by >10% vs baseline with same contract.

## 11. Output Schema Requirements

Each benchmark result row must include:
- `scenario_id`
- `measurement_type`
- `primary_unit`
- `timing_boundary`
- `state_profile`
- `dataset_id`
- `N`, `M`, `K`, `T`, `ooo_ratio`, `duplicate_rate`
- `maintenance_mode`
- `setup_time`, `measure_time`, `teardown_time`
- `median`, `p95`, `p99`, `mad`
- `expected_model` (equation or complexity form)

Without this metadata, result is informational only.

## 12. How To Interpret Current `timelog_demo.py` Results

Current demo output is useful, but some scenarios mix units and setup costs. Specifically:
- `D3`/`D4`: include load/setup in timed region while compared against high ops/scan throughput targets.
- `E3`/`E4`: include lifecycle/background overhead in short windows, not pure maintenance microbenchmarks.
- `F4`: very small sample window can produce noisy rates.

Action: keep demo for broad smoke/perf signal, but introduce separate methodology-compliant microbenches for release claims.

## 13. Recommended Next Implementation Steps

1. Annotate each `timelog_demo.py` feature with:
- `measurement_type`
- `primary_unit`
- explicit timed phase boundaries

2. Split mixed scenarios into separate benchmarks:
- setup benchmark
- operation microbenchmark
- integrated e2e benchmark

3. Add a small benchmark harness that:
- runs N/K/T sweeps
- fits scaling models
- emits complexity verdicts with confidence intervals

4. Maintain baselines per environment class:
- Linux/Windows, CPU family, Python version, build flags

This enables precise claims in README without over- or under-stating complexity.
