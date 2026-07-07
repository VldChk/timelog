# Ponytail Audit — Unit: internal-datastructures

Auditor stance: lazy senior dev. Read all 12 files in full (~2,413 LOC). Verdict up front:
**the machinery is well-built and hand-rolling is justified everywhere it is hot — but roughly
330 LOC of this unit is dead in production (tests-only or zero callers anywhere).** That is the
finding that matters. No library adoption survives honest fit-checking; the leads below are
recorded with the reasons they fail.

## Executive Summary

| # | Finding | Rung | LOC saved (est) | Risk |
|---|---------|------|-----------------|------|
| S1 | Delete 6 production-dead `tl_recvec` functions | 1 (does-not-need-to-exist) | ~190 prod + ~130 test/bench glue | low |
| S2 | Delete `tl_heap_build` (Floyd heapify, tests-only) | 1 | ~40 prod + ~90 test | low |
| S3 | Delete 5 dead `tl_intervals` entry points; fix stale doc | 1 | ~85 prod + ~150 test | low |
| S4 | Delete 3 zero-caller `tl_range.h` inline predicates | 1 | ~25 | low |
| S5 | Unreachable defensive branches in `intervals_coalesce`/`intervals_append` → assert | 1 | ~12 | medium |
| S6 | (fallback if S1 partially rejected) `tl_recvec_lower_bound` delegates to `tl_record_lower_bound` | 2 (already-in-this-codebase) | ~25 | low |

Everything else earns its keep — see the NO-and-NO section, which is most of this report by weight.

Counts of "LOC saved" include the whole diff (header decls + doc comments + test deletions noted
separately since deleting tests-of-dead-code is cleanup, not lost coverage).

---

## Per-File Walkthrough

### core/src/internal/tl_recvec.{c,h} (354 + 184 LOC)

Dynamic array of `tl_record_t` (16-byte ts+handle pairs). Growth policy is already factored
through shared helpers `tl__grow_capacity` / `tl__alloc_would_overflow` (`tl_alloc.h:127,150`),
so there is no duplicated growth logic to hunt. Production callers (memtable, memview,
compaction) use: init/destroy/clear/reserve/push/push_n/sort_with_seqs/data/len/is_empty/get/take.

**Dead in production (S1):**

- `tl_recvec_insert` (tl_recvec.c:150-175, header 75-79). Positional insert with `memmove` tail
  shift. Callers: only `core/tests/test_internal_data_structures.c:243,360`. The engine's whole
  OOO design (Option B mini-LSM, CLAUDE.md) exists precisely so nobody does sorted positional
  inserts; this function is the road not taken, kept alive by its own tests.
- `tl_recvec_shrink_to_fit` (tl_recvec.c:75-102, header 60-65). Only caller:
  `test_internal_data_structures.c:381`.
- `tl_recvec_sort` + its comparator `cmp_record_ts` (tl_recvec.c:181-205, header 85-92).
  **Zero callers anywhere — not even tests.** The header comment at tl_recvec.h:18
  ("call tl_recvec_sort() at seal time") is stale: the seal path actually uses
  `tl_recvec_sort_with_seqs` (`tl_memtable.c:387,468`, `tl_memview.c:415`).
- `tl_recvec_lower_bound` (tl_recvec.c:266-295) and `tl_recvec_upper_bound` (tl_recvec.c:297-326).
  Callers: `test_search_branchless.c` and `bench_search_lower_bound.c` only. Production binary
  search runs on raw arrays via `tl_record_lower_bound` (tl_search.h) — see `tl_count.h:76,389,471`,
  `tl_point.c:80`, `tl_submerge.c:153`, `tl_submerge.h:50,54` — and on pages via
  `tl_page_lower_bound`. Note there is **no production upper_bound consumer at all**: half-open
  `[t1,t2)` semantics mean both ends are lower_bound (CLAUDE.md "Binary Search" section), so
  upper_bound is speculative generality. (Cross-unit lead: `tl_page_upper_bound` at
  `storage/tl_page.c:177` also appears tests-only; flagged for the storage unit.)
- `tl_recvec_range_bounds` (tl_recvec.c:328-336, header 121-126). Two lower_bound calls in a
  trench coat. Only `test_internal_data_structures.c:215-225`.

Deletion glue: `test_search_branchless.c:101-102,175-181,227-233` compares the recvec variants
against a branchy oracle; the production branchless forms remain directly covered there via
`tl_record_lower_bound` (line 78) and `tl_page_lower/upper_bound` (line 130), so the perf-win
safety net survives deletion. `bench_search_lower_bound.c` benchmarks the recvec variants; either
drop those legs or keep local static copies in the bench file (bench is not shipped code).

**Alive and earning keep:** `tl_recvec_sort_with_seqs` (tl_recvec.c:229-260) allocates a
pair-array to co-sort records with a parallel seq array. This looks clunky but is the correct
portable answer: `qsort_r`/`qsort_s` have three incompatible signatures across glibc/BSD/MSVC,
which fails the GCC+Clang+MSVC `-Werror` requirement. NO-and-NO.

### core/src/internal/tl_seqvec.{c,h} (130 + 63 LOC)

Dynamic array of `tl_seq_t`. Every function has production callers in `tl_memtable.c`
(push:592, push_n_const:705, reserve:586, clear:146, take:958, data/len throughout). No dead code.
It is structurally a clone of recvec modulo element type — see NO-and-NO on why I do not
recommend macro-genericizing.

### core/src/internal/tl_heap.{c,h} (226 + 108 LOC)

Binary min-heap over a concrete 40-byte entry struct, ordered by `(ts, tie_break_key)`
(tl_heap.c:17-22). Backs all three merge paths (`tl_merge_iter.c`, `tl_submerge.c`,
`tl_flush.c:201-289`, `tl_compaction.c:1096-1162`). sift_up/sift_down/replace_top are textbook
and correct; `replace_top` (tl_heap.c:219-226) is a genuine perf primitive (pop+push in one sift)
used on the merge hot path (`tl_merge_iter.c:235`, `tl_submerge.c:122`, `tl_flush.c:286`).

**Dead in production (S2):** `tl_heap_build` (tl_heap.c:188-217, header 79-87) — Floyd's O(n)
bottom-up heapify, complete with a comment explaining why it beats repeated push. Callers:
`test_internal_data_structures.c:1281,1366` only. All four production sites do
`tl_heap_reserve` + push loop (e.g. `tl_flush.c:201-221`, `tl_submerge.c:57-81`), which is the
right call because K is "a handful of sources" (tl_heap.c:8-9) — O(K log K) vs O(K) is noise at
K≈4-16 and the push loop interleaves with per-source EOF/error handling that heapify cannot.
The optimization is real CS and really unused.

### core/src/internal/tl_intervals.{c,h} (824 + 298 LOC)

The tombstone interval set — canonical form (sorted, disjoint, non-adjacent, half-open) with
per-interval `max_seq` aggregation. This is the invariant-#5 machine and the most domain-specific
structure in the unit.

**Dead in production (S3):**

- `tl_intervals_max_seq` (tl_intervals.c:389-392) — **zero callers anywhere, including tests.**
- `tl_intervals_imm_contains` (tl_intervals.c:385-387) — **zero callers anywhere.**
- `tl_intervals_contains` (tl_intervals.c:380-383, header 113-118) — tests-only
  (`test_internal_data_structures.c:607-641,913-915`). Production containment goes through
  `tl_intervals_imm_max_seq` (`tl_point.c:306-349`) and the cursor (`tl_filter.c:60`,
  `tl_flush.c:239`, `tl_compaction.c:1175`, `tl_count.h:406,488`, `tl_memtable.c:335,485,980`)
  because the read path needs the seq for write-vs-delete ordering, not a boolean.
- `tl_intervals_union` — the mutable-input wrapper (tl_intervals.c:576-588, header 130-137).
  Adds only an aliasing check over `intervals_union_impl`; production exclusively uses
  `tl_intervals_union_imm` (`tl_compaction.c:190`, `tl_tombstone_utils.h:54`). Tests at
  `test_internal_data_structures.c:659-760,956` can call `union_imm` via `tl_intervals_as_imm`.
- `tl_intervals_covered_span` (tl_intervals.c:679-702, header 216-223) — tests-only
  (`test_internal_data_structures.c:996,1012`). The header doc claims it is "the compaction
  policy's delete-debt metric"; that is **stale** — H-18 replaced delete-debt with the
  cursor-based O(T+W) sweep and nothing in `core/src/maint/` calls it. If deletion is refused,
  the doc must be fixed; it currently misleads readers about a live dependency.

**Unreachable defensive branches (S5, medium confidence):**

- `intervals_coalesce` lines 112-122 handle "prev is unbounded and another interval follows".
  Canonical invariant (validator rule 5, tl_intervals.c:790-792) says the unbounded interval is
  always last, and every internal producer preserves that: `intervals_split_at` keeps the
  unbounded remainder last (tl_intervals.c:88-94); the bounded-insert walk asserts it never lands
  on an unbounded interval (`TL_ASSERT(!it->end_unbounded)`, tl_intervals.c:245); insert_unbounded
  returns immediately upon touching one (tl_intervals.c:323-326); clip_lower preserves order.
  So an unbounded `prev` with a successor `cur` cannot reach coalesce from any production path.
  The replace-prev logic at line 116-118 (`if (cur->start <= prev->start)`) is code for a state
  the module itself makes impossible. Replace the block with `TL_ASSERT` or delete (~11 lines).
- Same class: `intervals_append`'s `if (prev->end_unbounded) return TL_OK;` (tl_intervals.c:416-418)
  — union_impl only appends an unbounded interval in its terminal `!has_next` branch
  (tl_intervals.c:541-549) and breaks immediately after, so no append ever follows one.
  (~3 lines). Keep only if the team wants belt-and-braces here; then make it an assert so
  violations are loud in debug rather than silently swallowed.

**Observation (robustness, not a simplification):** `tl_intervals_insert` can return `TL_ENOMEM`
after the first `intervals_split_at` succeeded and before `intervals_coalesce` runs
(tl_intervals.c:210-217). A split creates two touching intervals with equal `max_seq`, which
violates canonical rule 4 (non-adjacency) until coalesce merges them back. Coverage semantics
stay correct (contains/max_seq/cursor all still answer right), but `tl_intervals_validate` would
fail on the ENOMEM-abandoned state. Benign today; worth a comment or a coalesce-on-error.

**Alive and earning keep:** insert/insert_unbounded (split + gap-fill walk + coalesce), union_imp,
clip/clip_lower, take, cursor_max_seq/skip_to, and the debug validators are all multiply-used and
implement invariant 5 plus the max_seq aggregation the tombstone-watermark model needs. I
considered rewriting `tl_intervals_insert` as "union with a one-interval set" to delete
~100 lines of split/walk machinery — rejected; see NO-and-NO (it turns the compaction residual
builder quadratic).

### core/src/internal/tl_tombstone_utils.h (65 LOC)

One shared helper, two callers (`tl_plan.c`, `tl_snapshot.c`). Linear scan to find the contiguous
overlapping sub-range (correct: sorted + disjoint ⇒ overlap set is contiguous), then union_imm
into the accumulator. The scan is O(T) but the union is O(T) anyway, so no asymptotic waste.
NO findings.

### core/src/internal/tl_range.h (59 LOC)

Five inline predicates for half-open ranges with an explicit `t2_unbounded` flag (correctly, not a
sentinel — TL_TS_MAX is a legal timestamp, header lines 13-15).

**Dead (S4):** `tl_ts_before_end` (lines 23-25), `tl_ts_at_or_past_end` (lines 28-30),
`tl_range_overlap_start` (lines 55-57) — **zero callers anywhere** (verified across core/,
bindings/, tests). `tl_range_overlap_start` is additionally just `TL_MAX(min_ts, t1)`
(tl_defs.h:138). Only `tl_range_overlaps` (6 callers) and `tl_range_is_empty` (2 callers) live.

### core/src/internal/tl_search.h (45 LOC)

`tl_record_lower_bound`: size-gated branchless (cmov) lower bound with branchy fallback above
`TL_LOWER_BOUND_BRANCHLESS_MAX` (tl_defs.h:50, 262144). This is a shipped, measured perf win
(point queries −15.2% per the ideas-lab record) and is directly diff-tested against a branchy
oracle in `test_search_branchless.c:78-79`. stdlib `bsearch` cannot express lower_bound (returns
*any* match, no insertion point). NO findings — this file is exactly as big as it needs to be.

### core/src/internal/tl_records.h (45 LOC)

`tl_records_copy`: overflow-checked alloc+memcpy, two callers (`tl_memview.c:329,340`).
Micro-nit, not a finding: the explicit `tl__alloc_would_overflow` pre-check (line 31-33) is
redundant with `tl__mallocarray`'s own overflow check (tl_alloc.h:92-96, "Returns NULL if …
overflows") — but removing it would fold `TL_EOVERFLOW` into `TL_ENOMEM`, a caller-visible status
change for 3 saved lines. Not worth it. NO finding.

---

## Simplifications (detailed)

### S1 — Delete six dead `tl_recvec` functions [rung 1, ~190 prod LOC, low risk]

`tl_recvec_insert`, `tl_recvec_shrink_to_fit`, `tl_recvec_sort` (+`cmp_record_ts`),
`tl_recvec_lower_bound`, `tl_recvec_upper_bound`, `tl_recvec_range_bounds`. Evidence per function
above. No public-API impact (all internal, `core/src/internal/`). Perf impact: zero — none are on
any executed path. Diff: tl_recvec.c −148, tl_recvec.h −~42, delete corresponding tests in
`test_internal_data_structures.c` (~120 lines), retarget/trim `test_search_branchless.c` recvec
legs (~10 lines) and the recvec legs of `bench_search_lower_bound.c` (bench-only). Also fix the
stale seal-time comment at tl_recvec.h:17-19. Existing coverage of the branchless search survives
via the `tl_record_lower_bound` and `tl_page_*` legs.

### S2 — Delete `tl_heap_build` [rung 1, ~40 prod LOC, low risk]

Floyd heapify with zero production callers; all merge constructors use reserve+push
(tl_flush.c:201-221, tl_compaction.c:1096-1114, tl_submerge.c:57-81, tl_merge_iter.c:154).
Delete tests at test_internal_data_structures.c:1265-1295, 1355-1370. Zero perf impact.

### S3 — Delete five dead `tl_intervals` entry points [rung 1, ~85 prod LOC, low risk]

`tl_intervals_max_seq` and `tl_intervals_imm_contains` have zero callers full stop — deleting them
is free. `tl_intervals_contains`, `tl_intervals_union` (mutable), `tl_intervals_covered_span` are
tests-only; rewrite those asserts against `tl_intervals_imm_max_seq(as_imm(iv), ts) != 0` and
`tl_intervals_union_imm`, and delete the covered_span tests. Independently of deletion, the
covered_span header doc (tl_intervals.h:216-223) claiming compaction uses it is stale post-H-18
and must be corrected.

### S4 — Delete three dead `tl_range.h` predicates [rung 1, ~25 LOC, low risk]

`tl_ts_before_end`, `tl_ts_at_or_past_end`, `tl_range_overlap_start`: zero callers anywhere.
Inline header functions, so zero binary/perf impact; purely reader burden.

### S5 — Collapse unreachable defensive branches in tl_intervals.c [rung 1, ~12 LOC, medium risk]

`intervals_coalesce` lines 112-122 and `intervals_append` lines 416-418, per the reachability
argument in the walkthrough. Medium risk only because the argument is invariant-based rather than
type-based; recommend `TL_ASSERT(!prev->end_unbounded)` rather than silent deletion, which keeps
debug builds loud if a future producer breaks rule 5. Needs no new tests (validator + existing
~200 interval tests cover canonical behavior).

### S6 — Fallback: delegate `tl_recvec_lower_bound` [rung 2, ~25 LOC, low risk]

Only if S1's search-function deletion is rejected (e.g. to keep the bench harness untouched):
`tl_recvec_lower_bound` (tl_recvec.c:266-295) is a line-for-line duplicate of
`tl_record_lower_bound` (tl_search.h:14-43) — same gate, same branchless loop, same fallback.
Replace the body with `return tl_record_lower_bound(rv->data, rv->len, ts);` (include
tl_search.h). Identical codegen after inlining; the duplicate is a future divergence hazard
(a gate-constant or cmov tweak applied to one and not the other would silently fork behavior).

---

## Prior-Art Leads (honest fit notes — verification is a later phase)

1. **Binary min-heap for K-way merge** — candidates: klib `ksort.h` heap macros (MIT),
   PostgreSQL `binaryheap.c` (PostgreSQL licence, BSD-like), CCAN `heap` (check per-module licence).
   Fit: poor. Generic heaps take `void*` elements + comparator function pointer ⇒ indirect call
   per comparison inside sift on the merge hot path; the current heap inlines a two-field compare
   on a concrete 40-byte struct (tl_heap.c:17-22) and offers `replace_top`, which several generic
   heaps lack. Zero-regression rule makes adoption a net loss. Keep hand-rolled.
2. **Dynamic array (recvec/seqvec)** — candidates: klib `kvec.h` (MIT), stb `stb_ds.h`
   (MIT/public-domain dual), CCAN `darray`. Fit: fails the allocator seam — the engine requires a
   per-instance `tl_alloc_ctx_t*` (tl_recvec.h:29-34); kvec/stb_ds route through global
   malloc/realloc macros (stb_ds's `STBDS_REALLOC(context,…)` context is a compile-time global,
   not per-vector). Macro-based codegen also complicates MSVC `/WX`. Current code already
   centralizes growth policy in `tl__grow_capacity`; a library saves little.
3. **Coalescing interval map with value aggregation (tombstones)** — the textbook match is Boost
   ICL `interval_map` with a max-combiner, which is C++ and disqualified. C candidates:
   cgranges (MIT) and similar interval-overlap indexes are *static* query structures with no
   coalescing insert and no per-interval aggregate; nothing mature in pure C implements
   "canonical half-open interval set with max_seq merge + unbounded end". Keep hand-rolled.
4. **Co-sorting parallel arrays** (`tl_recvec_sort_with_seqs`) — stdlib `qsort_r`/`qsort_s` are
   non-portable across glibc/BSD/MSVC (three incompatible signatures), failing the three-compiler
   `-Werror` gate. klib `ksort.h` (MIT) typed sort would *speed up* seal (inlined comparator vs
   qsort's indirect) but that is an optimization lead, not a simplification — current pair-array
   approach is the smallest portable correct answer.
5. **Branchless lower_bound** — no stdlib equivalent (`bsearch` cannot return the first-≥
   position). The implementation matches the well-known Lomuto/"branchless binary search"
   pattern and is a measured shipped win; adopting anything would be motion without progress.

---

## NO and NO (earns its keep — grounded)

- **`tl_heap` hand-rolled heap**: hot-path (query merge) perf property — inlined concrete-type
  comparator + `replace_top` (tl_merge_iter.c:235, tl_submerge.c:122). Generic prior art costs an
  indirect call per sift comparison. Simpler alternatives (sorted list, resort per pop) are
  asymptotically worse. Keep.
- **`tl_intervals` insert machinery** (split_at + gap-walk + coalesce, tl_intervals.c:179-345):
  I explicitly evaluated rewriting insert as `union_impl(existing, single_interval)` to delete
  ~100 lines. Rejected: the compaction residual builder (`tl_compaction.c:899-943`) performs T
  sequential ascending inserts into a growing set; the current walk appends at the end with no
  memmove (O(T) total), while a union-per-insert rewrite copies the whole set each time —
  O(T²) — inside compaction, whose throughput is a documented product concern (CLAUDE.md OOO
  profiling table). Violates the zero-perf-regression rule.
- **`end_unbounded` flag instead of a sentinel end** (tl_intervals.h:31-36, tl_range.h:13-15):
  TL_TS_MAX is a legal timestamp; `[t1, +inf)` must contain it, and half-open `[t1, TL_TS_MAX)`
  cannot. The flag is the invariant-#4-respecting representation; a sentinel would corrupt
  boundary semantics. Keep.
- **`tl_seqvec` as a separate type from `tl_recvec`**: yes, it is a structural clone (~130 LOC of
  boilerplate), and a `TL_VEC_DEFINE(type)` macro could fold both. Rejected as a recommendation:
  growth/overflow logic is already shared via `tl_alloc.h` helpers, both modules are stable,
  fully-tested leaf code, and macro-generated containers cost debuggability (no symbols to
  breakpoint per-type) and MSVC `/WX` friction for ≈100 net saved lines. If a third element-type
  vector ever appears, revisit.
- **`SIZE_MAX` length guards** (`tl_recvec.c:111`, `tl_heap.c:141`, `tl_seqvec.c:77`,
  `tl_intervals.c:49,202,287`): look like impossible-state paranoia, but they are load-bearing —
  without them `reserve(len + 1)` wraps to 0, returns TL_OK, and the subsequent write at
  `data[SIZE_MAX]` is UB. Two lines each, cheap, correct. Keep.
- **Two-form (branchless/branchy) lower_bound with a size gate** (tl_search.h:21,
  tl_recvec.c:273): the gate is not speculative config — it encodes the measured crossover where
  branch prediction beats cmov on huge arrays; constant lives in one place (tl_defs.h:50) and the
  differential test sweeps both sides of the gate (test_search_branchless.c header comment). Keep.
- **`tl_tombstone_utils.h` linear overlap scan**: O(T) scan before an O(T) union — binary-searching
  the ends would add code without changing the asymptote. Keep.
- **Cursor-based tombstone filtering** (`tl_intervals_cursor_*`, tl_intervals.c:708-764): the
  amortized-O(1) cursor is exactly the H-18-adjacent pattern CLAUDE.md mandates over per-record
  O(log T) probes; both functions are multiply used on the read path. Keep.
- **`tl_records_copy` overflow pre-check redundancy**: removal would change the returned status
  (TL_EOVERFLOW → TL_ENOMEM) for 3 lines. Not worth a behavior change. Keep.

## Test-Coverage Notes

All S1–S4 deletions remove code whose only coverage is tests asserting the dead code works;
no production behavior loses coverage. The branchless-search safety net survives via
`test_search_branchless.c` legs that target `tl_record_lower_bound`/`tl_page_*` directly.
S5 needs no new tests (debug validator + existing interval suites); recommend converting the
deleted branches to `TL_ASSERT`s so any future invariant-5 violation is caught in Debug/ASan CI.
