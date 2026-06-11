# Idea 1 — Branchless `lower_bound` across all 5 search seams (DETAILED PLAN)

## Goal
Replace the branchy binary search in all five core search functions with the branchless
power-of-two-step form (arithmetic predicate → compiler emits `cmov`), measured 3–5× on page-sized
arrays and −15% on `point` end-to-end (exp02), with **provably identical results** and **zero regression**.

## Exact call sites (all in scope)
| # | Function | File | Layout | Predicate |
|---|----------|------|--------|-----------|
| a | `tl_record_lower_bound` | `core/src/internal/tl_search.h` (inline) | AoS `data[i].ts` | `< target` |
| b | `tl_page_lower_bound` | `core/src/storage/tl_page.c` | SoA `ts[i]` | `< target` |
| c | `tl_page_upper_bound` | `core/src/storage/tl_page.c` | SoA `ts[i]` | `<= target` |
| d | `tl_recvec_lower_bound` | `core/src/internal/tl_recvec.c` | AoS `data[i].ts` | `< target` |
| e | `tl_recvec_upper_bound` | `core/src/internal/tl_recvec.c` | AoS `data[i].ts` | `<= target` |

(`tl_record_lower_bound` was already done in exp02; here it is part of one coherent, reviewed change.)

## The transform (index-based; identical shape for AoS & SoA)
```c
/* lower_bound: first index i in [0,N] with KEY(i) >= target */
size_t base = 0, length = N;
while (length > 0) {
    size_t half = length / 2;
    /* arithmetic (no data-dependent branch) -> cmov */
    base += (size_t)(KEY(base + half) < target) * (length - half);
    length = half;
}
return base;
```
`upper_bound` is identical with predicate `KEY(base + half) <= target`. `KEY(i)` = `data[i].ts` (AoS) or
`ts[i]` (SoA). The existing `TL_ASSERT` and `count == 0 → return 0` early-outs are **preserved**
(the loop already returns 0 for `N==0`, so the guard is belt-and-suspenders, not load-bearing).

## Correctness argument
- This is the standard power-of-two-step lower_bound; in exp02 it was verified **identical** to the branchy
  form on 24,576 boundary-inclusive queries × 6 sizes. `<` → first `>=` (lower); `<=` → first `>` (upper).
- Invariants: `base ∈ [0,N]`, `length` strictly decreases (`half < length` for `length>0`), terminates in
  ⌈log2 N⌉ steps. No overflow: `base+half ≤ N-1` when accessed (`half < length`, `base ≤ N-length`), and
  `length-half ≥ 0`.
- Result type/range unchanged → all callers (point/range/count/segment-iter) see identical indices.

## Risks & mitigations
1. **`cmov` not emitted** (GCC sometimes branches) → still **correct**, just maybe not faster. Mitigation:
   inspect asm for `cmov`; the arithmetic-multiply form maximizes emission. Acceptable either way (never
   wrong; never slower than branchy for our bounded array sizes).
2. **Huge-array inversion** (exp02: branchless loses >~250K elements). Mitigation: every search here is over
   a **page** (≤~4096 records) or a memtable run/recvec (≤ `memtable_max_bytes`/16 = ~65K default) — all in
   the regime where branchless wins (exp02: 65536 → 3.06×). No unbounded single-array search exists. Verify.
3. **Signedness**: `(int64 < int64)` → `int 0/1` → `(size_t)` → `* (size_t)` — clean, no UB.

## Measurement & the regression-catching test
- **New C differential test** `test_search_branchless` (added to `core/tests/`): for each of the 5 functions,
  compare against an in-test reference branchy implementation across: empty, single, all-below, all-above,
  duplicates, and random arrays at sizes {0,1,2,3,7,8,9,255,256,4096,65535} with targets at/between/outside
  keys. Must be bit-identical. (This is the gate that would catch any off-by-one.)
- **Existing 480 core tests** exercise these via point/range/count/segment-iter — must stay 480/480.
- **Perf re-confirm:** point-query microbench (exp02 harness) shows ≤ baseline latency (expect −10–18%).

## Done = green
480 core (+ the new differential test) · 9/9 ctest · 98 pytest · asm shows cmov (informational) ·
point microbench not slower. Then commit `feat(core): branchless lower_bound across page/recvec/record search`.

---

## v2 — REVISED after hostile plan review (2 adversarial subagents)

The review found **no correctness defect** (bit-identical on 12.5M+ cases; cmov confirmed on shipped
`-O3 -flto` GCC; FT-safe) but **two real blockers** that change the design:

### BLOCKER fix — size-gate to guarantee ZERO regression at any configured size
`validate_config` (`tl_timelog.c:142-186`) puts **no upper bound** on `memtable_max_bytes` or
`target_page_bytes`. A supported bulk-ingest config (e.g. 32 MiB memtable → ~2M-record `active_run`, or a
32 MiB page) is searched by `tl_recvec_*`/`tl_page_*` on the hot path. Measured crossover (shipped flags,
this HW) is **~1–2M elements**, where branchless **loses 15–22%**. So the transform is **size-gated**:

```c
#define TL_LOWER_BOUND_BRANCHLESS_MAX ((size_t)1 << 18)  /* 262144 — robust-win zone, margin below ~1-2M crossover */

if (n <= TL_LOWER_BOUND_BRANCHLESS_MAX) {   /* branchless: cmov, 2.3-5x win (default page ~4K, memtable ~65K) */
    size_t base=0, length=n;
    while (length>0){ size_t half=length/2; base += (size_t)(KEY(base+half) <STRICT> target)*(length-half); length=half; }
    return base;
} else {                                    /* branchy fallback == today's code -> ZERO regression for huge configs */
    size_t lo=0, hi=n;
    while (lo<hi){ size_t mid=lo+(hi-lo)/2; if (KEY(mid) <STRICT> target) lo=mid+1; else hi=mid; }
    return lo;
}
```
The default config (page ~4090 rec, memtable ~65K rec) is entirely inside the branchless zone → full win;
only non-default huge buffers fall back to the *existing* branchy code → provably no regression. The gate
is one `size_t` compare (negligible). *No config-validation change* (keeps user-facing semantics intact).

### Scope correction (honesty) — 5 of 10 searches; the other 5 are intentionally excluded
Excluded (search over **metadata** arrays, far smaller than record arrays, no measurable benefit — like the
SoA-catalog finding's ~1.0×): `tl_page_catalog_find_first_ge`/`find_start_ge` (tl_page.c, over `n_pages`),
`intervals_lower_bound`/`intervals_max_seq_internal` (tl_intervals.c, over tombstone count),
`tl_manifest_l1_find_first_overlap` (tl_manifest.c, over `n_l1`). The plan no longer claims "no other search
exists."

### Measurement fix — isolated per-function bench across the crossover
The differential test proves *correctness* only. Perf gate is now a **standalone microbench of each of the
5 functions** at sizes {256, 4096, 65535, 262144, 1048576, 2097152, 8388608, 16777216} on the shipped
flags, asserting: (a) branchless ≥ branchy below the gate, (b) the gated function is **never slower than
pure-branchy** at any size (the gate guarantees this). Plus the end-to-end point/range bench (informational).

### MSVC note (CI item)
cmov confirmed on GCC 13 `-O3`. MSVC `/O2 /GL` cmov heuristics differ and weren't testable on Linux; with
the size-gate the result is correct regardless, and at worst MSVC emits a branch ≈ today. Flag for Windows CI.
