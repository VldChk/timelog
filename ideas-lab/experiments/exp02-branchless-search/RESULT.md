# exp02 — Branchless `lower_bound` (idea N17 / new theme T9)

**Hypothesis:** Rewriting `tl_record_lower_bound` (the most-used search, `tl_search.h`, called from
point/count/segment-iter) as a branchless cmov form beats the branchy binary search on
unpredictable query timestamps — without any data-layout change or invariant impact.

**Change:** `core/src/internal/tl_search.h` — branchy `lo/hi` loop → power-of-two-step form where the
offset is `+= (predicate) * (length - half)` (arithmetic, so the compiler emits `cmov`, not a branch).
**~7 LOC**, one inline function. Result provably identical to the branchy search.

## A. Isolated microbench (`bench_lower_bound.c`, `-O3 -march=native`, 1M random queries)

| n (records) | branchy ns | branchless ns | **speedup** | bl+prefetch ns | pf speedup |
|---|---|---|---|---|---|
| 256 | 29.4 | 5.6 | **5.22×** | 7.1 | 4.17× |
| 1024 | 38.2 | 7.1 | **5.41×** | 9.0 | 4.26× |
| **4096 (1 page)** | 49.0 | 10.6 | **4.60×** | 12.3 | 4.00× |
| 16384 | 64.6 | 16.6 | **3.90×** | 19.3 | 3.35× |
| 65536 | 82.5 | 27.0 | **3.06×** | 30.7 | 2.68× |
| 1048576 | 174.6 | 217.9 | **0.80× ✗** | 140.8 | 1.24× |

- `cmov` confirmed emitted (4 instrs in the asm). Identical results verified on 24,576 queries × 6 sizes.
- **The 1M-row inversion is the key finding, not a flaw:** on huge out-of-cache arrays the *branchy*
  version wins because the CPU speculatively prefetches *both* children down mispredicted paths, hiding
  DRAM latency. The prefetch variant recovers it (1.24×). Timelog's per-page record arrays are bounded
  at ~4096 (`TL_DEFAULT_TARGET_PAGE_BYTES`=64 KiB / 16 B), squarely in the 3–5× winning regime → pure
  branchless is the correct choice for the hot path.

## B. End-to-end (Release, Python 3.13, pinned core, vs baseline)

| Op | Baseline | exp02 | Δ |
|----|----------|-------|---|
| `point(ts)` | 372.7 ns | **306.1 ns** | **−17.9%** |
| `next_ts(ts)` | 321.1 ns | **277.4 ns** | **−13.6%** |
| `append(ts,obj)` *(control, untouched)* | 125.8 ns | 121.7 ns | −3.2% (noise) |

The append control (~0%) confirms the point/next_ts wins are the search change, not drift. Note the
end-to-end point win (−67 ns) exceeds one lower_bound's saving because the point path runs lower_bound
across multiple merge sources.

## Correctness
- **480 / 480 core C tests pass, 0 failed** (point, range, count, segment-iter all exercise lower_bound).
- Differential equivalence with the branchy form on 24,576 boundary-inclusive queries.

## Verdict: 🟩 LOW-HANGING FRUIT (highest ROI found)
~7 LOC, no layout/invariant change, −18% on the point hot path end-to-end, 3–5× on the search itself,
full suite green. This is the single best effort:reward ratio in the lab.

**Productionization gate:** ASan/UBSan + TSan core run; confirm `cmov` emission on the project's actual
Release flags (GCC may need `-O2`+; the change is still *correct* if a branch is emitted, just not faster);
apply the same transform to `tl_page_lower_bound`/`tl_page_upper_bound`/`tl_recvec_*` for consistency.

## Adjacent ideas surfaced (not yet built — see classification)
- N18 SoA catalog split (dense `max_ts[]`), N19 SIMD intra-page final-block scan, N21 prefetch on
  merge page-advance, N20 loser-tree k-way merge. T9 is a rich, under-explored seam.
