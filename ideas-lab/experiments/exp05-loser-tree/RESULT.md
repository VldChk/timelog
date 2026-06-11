# exp05 — Loser/tournament tree vs binary min-heap for k-way merge (idea N20 / T9)

**Hypothesis (from research):** Timelog's read-path k-way merge uses a binary min-heap (`tl_heap_t`,
`sift_down` ~2·log₂K comparisons/record); a loser/tournament tree does ~log₂K, so it should be faster —
especially relevant after exp04 showed the OOO 5.3× read penalty comes from merging many overlapping
segments (large K).

**Method:** standalone C microbench (`bench_kmerge.c`) merging K sorted sources (1M records total),
mirroring the real entry shape `{ts, tie_break, handle}` and `(ts,tie)` comparison. Binary min-heap with
`replace_top`+`sift_down` (a faithful copy of the real structure) vs a tournament (winner) tree doing one
comparison per leaf→root level. Output verified identical. `-O3 -march=native` and `-O2`, pinned core.

## Result (ns per emitted record)

| K | heap | tournament tree | speedup |
|---|---|---|---|
| 2 | 8.48 | 7.72 | 1.10× |
| 4 | 12.23 | 11.49 | 1.06× |
| 8 | 15.39 | 15.20 | 1.01× |
| **16** | 18.03 | 19.65 | **0.92×** |
| **32** | 19.98 | 23.55 | **0.85×** |
| **64** | 33.87 | 38.62 | **0.88×** |

(−O2 nearly identical: heap wins from K≥16.) Output identical on every K.

## Why the heap wins (the structural reason)
`replace_top` feeds the next record **from the same source** that just won. Because each source is sorted,
that replacement is usually only slightly larger than the old minimum, so `sift_down` **short-circuits
after 0–1 levels** — far below its 2·log₂K worst case. The tournament tree, by contrast, *always* replays
the full leaf→root path (log₂M comparisons + array writes, M = K padded to a power of two) and touches
more memory (the `tree[2M]` array + siblings). At the K values that actually occur in Timelog's merge
(L0 overlap + L1 windows + memview ≈ 8–64), the heap's early termination beats the tree's fixed path.

## Verdict: 🟥 NOT-FOR-US — measured net-negative at relevant K
The existing binary heap with `replace_top` is already the right structure; a loser/tournament tree is
**slower** for K≥16 and only marginally faster for K≤4 (not worth a major refactor of `tl_heap` +
`tl_merge_iter` + `tl_submerge` that must also preserve deterministic tie-break + watermark propagation).
The research's honest hedge ("single-digit %, not 5–12×") was generous — the real number is **below 1.0×**.

**Consequence for the OOO read-amp finding (exp04):** the 5.3× penalty from many overlapping segments is
**not** fixable with a better merge data structure — it is inherent to merging K sources. The correct fix
is to *reduce K* via compaction (which exp04 showed works) — not to speed up the merge of a large K.

> A clean example of "verify, don't classify": this would have been seeded 🟦 cool-but-costly on the
> research evidence alone; one microbench moved it to 🟥 and saved a large, risky refactor.
