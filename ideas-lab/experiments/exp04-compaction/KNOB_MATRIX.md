# C4-knobs — compaction knob matrix (real, harness-driven, subprocess-isolated)

Driver: `harness/run_matrix.py` → `harness/compaction_lab.py` (subprocess per cell, 3 paired seeds → median).
3 workloads × `max_delta_segments` ∈ {2,4,8,16,32} × N=400k. Baseline build. (`knob_matrix_baseline.json`)

## Result (median of 3 seeds)

| workload | trig | WA | SA | compact CPU | point p50 | point p99 | range p50 |
|---|---|---|---|---|---|---|---|
| steady | 2 | **75.0** | 1.00 | 57.9 ms | 721 | 1233 | 16962 |
| steady | 8 | 18.7 | 1.00 | 24.9 ms | 691 | 1182 | 17824 |
| steady | 32 | **2.68** | 1.01 | 5.6 ms | 752 | 1202 | 18365 |
| ooo | 2 | 75.0 | 1.00 | 55.9 ms | 651 | 1082 | 12574 |
| ooo | 8 | 18.7 | 1.00 | 24.5 ms | 682 | 1142 | 13946 |
| ooo | 32 | 2.68 | 1.01 | 5.7 ms | 732 | 1172 | 12664 |
| delete_storm | 2 | 45.4 | **1.67** | 56.3 ms | 701 | 1152 | 16481 |
| delete_storm | 8 | 11.6 | 1.67 | 24.7 ms | 691 | 1112 | 16581 |
| delete_storm | 32 | 2.01 | 1.69 | 5.7 ms | 762 | 1263 | 16341 |

## Findings (measured, not asserted)
1. **`max_delta_segments` swings write-amp 28×** (2.68 → 75) and **compaction CPU ~10×** (5.6 → 58 ms) —
   the tiering↔leveling dial, quantified. Lower trigger = eager leveling (high WA/CPU); higher = lazy tiering.
2. **Read-amp is nearly flat** across the trigger for these workloads (point p50 ~690–760 ns) — because
   in-order / mildly-OOO segments have disjoint time ranges that fence-prune well. The 5.3× read explosion
   from exp04 needs *adversarial full-overlap OOO* (every segment spanning the whole domain), not the 20%-late
   `ooo` workload here.
3. **Space-amp** is governed by deletes, not the trigger: `delete_storm` holds **SA≈1.67** at every trigger
   (tombstone-resident space) — this is what whole-window-drop (C4-wwd) and delete-debt (C5-canon) target.
4. **RUM-aware conclusion:** since in-memory write-amp is *cheap* (no disk), and read-amp barely moves, the
   default trigger=8 is **conservative** — for in-order/mild-OOO workloads a *higher* trigger (16–32) cuts
   compaction CPU ~3–4× at ~no read cost. The right policy is **workload-adaptive**: low trigger only when
   overlap (OOO degree) is high. This is the evidence base for an adaptive trigger (C4-roi).

## Verdict: 🟩 actionable tuning + 🟦 adaptive-trigger opportunity
The matrix is the seed for: (a) document `max_delta_segments` with this trade curve; (b) consider a higher
default for mild workloads or make it OOO-overlap-adaptive (C4-roi prototype); (c) deletes need a *different*
lever (WWD/delete-debt),
not the trigger. The same matrix can be re-run on future WWD or true-granular builds for before/after comparison.
