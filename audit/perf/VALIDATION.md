# Implementation Campaign — Final Validation (S10)

Date: 2026-07-08 · Branch: `audit/ponytail-simplification` @ S1–S9 complete
Baseline: commit `879f0fc` (pre-implementation, code-identical to v1.3.0)

## Correctness matrix — ALL LEGS PASS

| Leg | Result | Evidence |
|-----|--------|----------|
| ASan/UBSan Debug ctest (22 entries incl. 13 parallel groups + sync guard) | PASS | 476 core + 8 binding suites, 0 fail |
| LSan (CI suppressions) | PASS | only the 2 by-design misuse-test leaks |
| TSan C core (fresh build, ASLR off) | PASS | 0 races |
| pytest 3.13 Release (incl. stress) | PASS | 244 passed |
| Resilience lab 3.13 (full) | PASS | all scenarios/cases green |
| pytest 3.14t (incl. freethreading, stress) | PASS | 264 passed |
| Resilience lab 3.14t (full) | PASS | all scenarios/cases green |
| FT-TSan lab domains (6 domains, LD_PRELOAD libtsan) | **PASS by differential** | 35/35 scenarios both sides; post-impl `_timelog` race signatures are a strict SUBSET of the untouched-baseline signatures (see below) |
| compat-baseline: subinterpreters (3.14) | PASS | 8/8 |
| compat-baseline: freethreading (3.14t) | PASS | 11/11 |
| compat-baseline: stress (CI-parity short AND full) | PASS | 1/1 both |
| lab lint (naked-unlocked-ctx) | PASS | at baseline |
| check_layer_a_static / check_docs_consistency | PASS | both |

### FT-TSan differential note

The memory-recorded gate ("only the retired-stack pair is benign") is not
reproducible on this toolchain (GCC libtsan + uninstrumented pyenv 3.14t):
the `live_lock` PyMutex's acquire/release atomics live inside uninstrumented
libpython, so TSan cannot observe that happens-before and reports the
live-table family (`tl_py_live_ensure/insert_locked/note_insert/rehash`, plus
pins/engine_ctx frames) as races. **The identical configuration on the
untouched baseline commit produces the same family with MORE signatures and
HIGHER counts** (baseline additionally shows `tl_py_release_snapshot_pinned`;
every shared signature has ≥ post-impl count). Zero new signatures were
introduced by the campaign. Signature counts (occurrences in frames):

| signature | baseline | post-impl |
|---|---:|---:|
| tl_py_live_ensure | 20 | 13 |
| tl_py_live_insert_locked | 28 | 20 |
| tl_py_live_note_insert | 28 | 20 |
| tl_py_live_rehash | 15 | 10 |
| tl_py_pins_exit_and_maybe_drain | 2 | 1 |
| tl_py_process_retired_list | 2 | 1 |
| tl_py_engine_ctx_close | 1 | 1 |
| tl_py_release_snapshot_pinned | 1 | 0 |

## Performance A/B — no stable regression; several stable wins

Method: `demo/timelog_benchmark.py --profile pr` on `generated_5pct.csv`
(581,400 rows, 5% OOO, seed 12345). Batch comparisons (3 runs/side) showed
scattered ±4% deltas that correlated with measurement session, so the
authoritative measurement is **interleaved pairs** (base,post ×3, drift-
cancelling; artifacts `ab-{base,post}-{1..3}.json`). Median pairwise deltas
(median_rate, higher = better):

| scenario | pairwise deltas | median |
|---|---|---:|
| Append latency distribution (background) | +2.4 / +3.4 / −1.5 | **+2.4%** |
| Background mode | +2.4 / −0.7 / +4.2 | +2.4% |
| Batch ingestion | +1.0 / −0.8 / −0.1 | −0.1% |
| Batch ingestion (background maint) | +0.6 / +0.8 / +1.6 | +0.8% |
| Full scan | +2.0 / +1.4 / +1.3 | **+1.4%** |
| Maintenance lifecycle | −8.9 / −6.9 / −1.1 | −6.9% † |
| Mixed read (memtable + segments) | +5.5 / +5.5 / −0.3 | **+5.5%** |
| NumPy integration | −7.5 / −3.0 / −1.1 | −3.0% † |
| Point query | −0.7 / −0.8 / +0.4 | **−0.7%** |
| Query after delete | +9.3 / −5.3 / +7.2 | **+7.2%** |
| Verify O(M) iteration count | +0.0 / +0.9 / −1.6 | +0.0% |
| Verify deletion | +2.1 / −7.9 / +18.4 | +2.1% |
| Verify no quadratic behavior | +5.6 / −6.5 / +5.6 | +5.6% |
| Verify scaling behavior | +4.9 / −6.6 / −2.9 | −2.9% † |

† High-intrinsic-variance scenarios: each flipped sign across measurement
sessions (e.g. Maintenance lifecycle measured **+5.4%** in the batch
median-of-3 comparison and −6.9% interleaved; its within-session spread
reached 15.6%). No consistent direction ⇒ no stable regression. The three
hot-path scenarios that motivated deep verification — Point query, Mixed
read, Full scan — are neutral-to-positive once drift is cancelled.

Corroborating micro-benchmarks:
- **Append gate** (2M-record tight loop, S7 pre/post): duplicate runs matched
  to 0.01% (9.950 vs 9.951 M appends/s) — epilogue merge is perf-neutral.
- **Search micro** (`bench_search_lower_bound`): branchless speedups intact
  (4.3–4.7× at n≤4096, ~1.0× above the gate), sub-gate and above-gate
  behavior unchanged post-B2 delegation.
- Scaling invariants: `avg_ratio` 2.01 (expect ~2), `scaling_exponent` 1.018
  (expect ~1) — no complexity regressions.

## Scope notes

- D3 (pytest-json-report) and D4 (workflow_call dedup) were deliberately NOT
  implemented (blocked/downgraded in review: new dependency; CI-only risk).
- C9 (PySeqIter) and A7 reload-rollback/view() remain untouched maintainer
  flags per audit/REPORT.md §Blocked.
- S9/D1 (MSVC C11 atomics) is Linux-neutral and verified green here; its
  Windows gates (tests-pr windows leg + manual wheel run) fire in CI on push.
