# `max_delta_segments` Benchmark Artifact

This artifact backs the numeric guidance in [Configuration](../configuration.md).
It is a directional benchmark snapshot, not a contractual performance guarantee.

## Method

- Driver shape: subprocess-isolated compaction lab, three paired seeds per cell.
- Runtime: CPython 3.13.12 source-tree build.
- Rows: 400,000 for the three-workload matrix.
- Source tree: baseline `e7e7efb` source checkout.
- Matrix seeds: `[1, 2, 3]`; adversarial confirmation repeats use deterministic
  shuffled inputs with seeds `13`, `14`, and `15`.
- Replay commands from the audit scratch tree:
  - `python ideas-lab/harness/run_matrix.py /home/vldvhk/Documents/timelog/python ideas-lab/experiments/exp04-compaction/knob_matrix_baseline.json`
  - `PYTHONPATH=/home/vldvhk/Documents/timelog/python python ideas-lab/experiments/exp04-compaction/confirm.py > ideas-lab/experiments/exp04-compaction/exp04_confirm.json`
- Raw artifacts checked in with this docs snapshot:
  [knob_matrix_baseline.json](knob_matrix_baseline.json) and
  [exp04_confirm.json](exp04_confirm.json).
- Write-amp is a segment re-merge proxy, not byte write amplification.
- Point/range latency units are nanoseconds.

## Three-Workload Matrix

| workload | `max_delta_segments` | WA proxy | space amp | compaction CPU | point p50 | point p99 | range p50 |
|---|---:|---:|---:|---:|---:|---:|---:|
| steady | 2 | 75.0 | 1.00 | 57.9 ms | 721 | 1233 | 16962 |
| steady | 4 | 20.7 | 1.00 | 34.9 ms | 691 | 1152 | 17713 |
| steady | 8 | 18.7 | 1.00 | 24.9 ms | 691 | 1182 | 17824 |
| steady | 16 | 17.7 | 1.00 | 15.4 ms | 701 | 1192 | 17332 |
| steady | 32 | 2.68 | 1.01 | 5.6 ms | 752 | 1202 | 18365 |
| ooo | 2 | 75.0 | 1.00 | 55.9 ms | 651 | 1082 | 12574 |
| ooo | 4 | 20.7 | 1.00 | 35.5 ms | 672 | 1132 | 13856 |
| ooo | 8 | 18.7 | 1.00 | 24.5 ms | 682 | 1142 | 13946 |
| ooo | 16 | 17.7 | 1.00 | 16.2 ms | 662 | 1072 | 12724 |
| ooo | 32 | 2.68 | 1.01 | 5.7 ms | 732 | 1172 | 12664 |
| delete_storm | 2 | 45.4 | 1.67 | 56.3 ms | 701 | 1152 | 16481 |
| delete_storm | 4 | 12.8 | 1.67 | 35.3 ms | 701 | 1183 | 17082 |
| delete_storm | 8 | 11.6 | 1.67 | 24.7 ms | 691 | 1112 | 16581 |
| delete_storm | 16 | 11.0 | 1.67 | 16.0 ms | 711 | 1132 | 16942 |
| delete_storm | 32 | 2.01 | 1.69 | 5.7 ms | 762 | 1263 | 16341 |

## Adversarial Full-Overlap OOO Check

This separate N=200k check creates L0 segments that all span the full time
domain, so fence-pruning cannot skip them.

| `max_delta_segments` | point p50 | point p99 | WA proxy | compactions | final L0 | final L1 | pages |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 601 | 932 | 23 | 8 | 0 | 1 | 49 |
| 8 | 602 | 911 | 17 | 2 | 0 | 1 | 49 |
| 32 | 3166 | 3998 | 0 | 0 | 16 | 0 | 64 |
| no compaction | 3166 | 4078 | 0 | 0 | 16 | 0 | 64 |

## Interpretation

- The knob swings WA proxy from 2.68 to 75.0 in the steady/ooo matrix: about 28x.
- It swings compaction CPU from about 5.6 ms to about 57.9 ms: about 10x.
- Point p50 stays near 650-760 ns in steady/mild-OOO/delete-storm workloads
  because time-range fence pruning skips most disjoint segments.
- The adversarial full-overlap case is the exception: no compaction produced a
  3166 ns point p50 versus about 600 ns with the default/eager triggers.
- Delete-heavy space amp is governed by tombstones and reclaim policy, not by
  this trigger alone.
