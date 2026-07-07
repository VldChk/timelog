# Ponytail Audit — Unit: query (read path)

Auditor: lazy-senior persona, full read of all 24 files (4,791 LOC) in `core/src/query/`.
Ladder rungs: 1=does-not-need-to-exist, 2=already-in-this-codebase, 3=stdlib, 4=platform, 5=existing-dependency, 6=one-liner, 7=minimal-rewrite.

## Executive Summary

The read path is disciplined and mostly earns its complexity: the two-level merge (outer
k-way over iterator vtable-lites, inner submerge over raw arrays) is a deliberate perf
structure, snapshot acquisition's two-phase sort/cache is invariant-driven (H-09/#6), and
the pagespan owner's free-before-hook ordering is a documented allocator-lifetime contract.
No prior-art adoption survives the hard constraints — every candidate loses to something
already in-tree (`tl_heap`, `tl_recvec`, `tl_refcount.h`, `tl_intervals`).

The fat is **duplication and write-only state**, not architecture:

1. `tl_stats` (in `tl_timelog.c`) reimplements `tl_snapshot_count_range_internal` for the
   unbounded range, and to feed it `tl_count.h` carries two "full-extent" counting
   functions that are provably identical to the range-intersected variants called with
   `[TL_TS_MIN, +inf)`. ~110 LOC deletable.
2. `tl_memrun_iter` and `tl_active_iter` are the same iterator twice — four files whose
   `next`/`seek`/`destroy` bodies are line-identical wrappers over `tl_submerge`, differing
   only in which sources their `init` feeds to `tl_iter_build_submerge`. ~200 LOC net.
3. `tl_point.c` hand-rolls the dynamic record array that `internal/tl_recvec` already
   provides for every other record container in the engine.
4. A sweep of write-only fields (`kmerge.alloc`, `plan.tomb_capacity`,
   `plan.segments_pruned`/`memruns_pruned`), a dead parameter (`head_watermark`), a dead
   flag bit (`TL_PAGESPAN_REQUIRE_ZEROCOPY`), and one provably-dead visibility branch in
   the point path.

Estimated honest total: **~460 LOC** removable at low/low-medium risk with zero functional
or performance regression. Nothing here touches the public `timelog.h` contract except the
(optional, flagged) pagespan flag-bit deletion, which is semi-public binding-facing API.

---

## Per-File Walkthrough

### tl_count.h (499 LOC)
Header-only counting helpers, `TL_INLINE`, shared by `tl_snapshot.c` (count API) and
`tl_timelog.c` (stats).

- `tl__range_overlap_half_open` (35–59): computes half-open intersection with unbounded
  flags. `internal/tl_range.h` has only boolean predicates (`tl_range_overlaps` returns
  bool, no intersection output) — so this earns its keep. Placement nit: it is generic
  range logic living in a counting header; could move to `tl_range.h`, but that saves
  nothing. **NO/NO.**
- `tl__count_records_sorted_range` (66–82), `tl__count_records_in_memrun_range` (89–108),
  `tl__memrun_record_bounds` (111–142): tight binary-search counters. Fine.
- **FINDING S1a** — `tl__visible_records_in_segment` (149–189) and
  `tl__visible_records_in_memrun` (192–233) are exactly the `_range` variants (243–296,
  299–349) specialized to the unbounded query `[TL_TS_MIN, +inf)`. Proof: in the range
  variant, intersecting `[TL_TS_MIN, +inf)` with the source extent yields the source
  extent unchanged (`lo = max(TL_TS_MIN, src_start) = src_start`;
  `hi_unbounded = true && src_end_unbounded`; `hi = src_end_exclusive`), after which the
  gross count and the per-tombstone triple-intersect loop are line-for-line the same
  computation as the full-extent versions' loops against the source extent
  (compare 166–188 with 272–295). The full-extent pair is called from exactly three
  sites, all in `tl_timelog.c` stats (2087, 2095, 2113). See S1.
- **FINDING S9** — the OOO-runs branch of `tl__count_active_visible_range` (456–494)
  reimplements `tl__count_visible_sorted_range` (377–413) inline because the latter
  requires a per-record `seqs[]` array while OOO runs have a single source watermark. The
  codebase already has the "seqs-or-watermark" pattern: `collect_from_sorted` in
  `tl_point.c:84` does `seqs != NULL ? seqs[idx] : watermark`. Adding a `watermark`
  parameter + NULL-seqs support to `tl__count_visible_sorted_range` deletes the ~30-line
  inline copy. Perf: one predictable per-record branch on the *count* path (not the
  append/iteration hot paths); count is already O(records) row-scanning here. Rung 2
  (pattern exists in-tree), ~25 LOC net, low risk.

### tl_pagespan_iter.c / .h (493 + 244 LOC)
Streaming zero-copy span iterator with atomically refcounted owner.

- Owner lifecycle (96–171): uses in-tree `TL_REFCOUNT_ACQUIRE/RELEASE` macros
  (`internal/tl_refcount.h`) — already the right dedup. The free-owner-before-hook
  ordering in `owner_destroy` (135–157) looks inverted but is a documented
  allocator-lifetime contract ("a binding hook may Py_DECREF the timelog and thereby free
  the allocator that holds the owner struct"). **NO/NO** — do not "simplify" this.
- Empty-range snapshot acquisition (333–346): acquires a snapshot even for `t1 >= t2`
  because bindings pair `pins_enter()` with the release hook; skipping owner creation
  would leak the pin. Documented, symmetric, correct. **NO/NO.**
- Phase state machine (61–65, 226–292): L1-then-L0 enumeration. The
  `TL_PAGESPAN_INCLUDE_L0/L1` conditionals are only ever exercised with both bits set in
  production — the sole binding call site passes `TL_PAGESPAN_DEFAULT`
  (`bindings/cpython/src/py_span_iter.c:164–166`); non-default combinations appear only in
  `core/tests/test_pagespan_iter.c`. Speculative selectivity, but it is semi-public
  `TL_API` surface and the cost is ~10 LOC of guards; removing it is an api-change for
  marginal gain. Noted, not recommended.
- **FINDING S5g** — `TL_PAGESPAN_REQUIRE_ZEROCOPY` (tl_pagespan_iter.h:119) is defined,
  OR'd into `TL_PAGESPAN_DEFAULT` (126–128), set by one test
  (`test_pagespan_iter.c:115`), and **never read by any implementation code** (repo-wide
  grep: no consumer). Dead flag bit. Rung 1, ~4 LOC. Flag loudly: **api-change**
  (semi-public enum in a binding-facing header) — cheapest correct move may be a comment
  demoting it to "reserved" like VISIBLE_ONLY, or deletion at the next API-break window.
- `page->flags != TL_PAGE_FULLY_LIVE → TL_EINTERNAL` (437–439): fail-loud invariant guard
  with rationale comment. Keep.

### tl_point.c / .h (444 + 89 LOC)
Point-lookup fast path (skips the k-way merge; measured perf win per project memory).

- **FINDING S3** — `ensure_capacity` (23–51) + `add_record` (54–64) +
  the `records/count/capacity/alloc` fields of `tl_point_result_t` (tl_point.h:37–42) are
  a hand-rolled dynamic array of `tl_record_t`. `internal/tl_recvec.h` exists precisely
  for this: "The vector backs every contiguous record container in the engine", with
  `tl_recvec_push` (amortised O(1), geometric growth), `tl_recvec_reserve`,
  `tl_recvec_destroy` (idempotent). Rung 2. Replace `tl_point_result_t` internals with an
  embedded `tl_recvec_t` (consumer `tl_timelog.c:1454` reads `.records[i]`/`.count`
  directly — becomes `.rv.data`/`.rv.len`, internal struct, 3 touch points). Append cost
  is identical (same amortised doubling); the point path's measured speed lives in the
  binary searches, not the result buffer. ~40 LOC net, low risk. Existing point-query
  tests cover it.
- **FINDING S5f** — dead branch in `collect_from_page` (120–123):
  `if (tomb_seq > watermark) { idx++; continue; }` is loop-invariant AND unreachable. Its
  only caller, `collect_from_segment`, already returns early at line 144
  (`if (tomb_seq > seg->applied_seq) return TL_OK;`) and then passes
  `watermark = seg->applied_seq` (181). So inside the loop `tomb_seq <= watermark` always
  holds. Delete the branch and the now-unused `watermark` parameter. Rung 1, ~6 LOC, low
  risk, fully covered by point-lookup + tombstone tests. (If one insists on keeping the
  defense, it belongs as a single check before the loop, not per-row.)
- **FINDING S8b** — `max_tomb_seq_at` (298–356): the L0 loop (325–337) and L1 loop
  (341–353) are body-identical; likewise the two loops in
  `tl_snapshot_collect_tombstones` (see below). A 5-line static helper taking a segment
  collapses both pairs. Rung 7, ~12 LOC here. The L1 loop itself is defensive (L1 is
  tombstone-free by invariant) but self-documents and costs a scan over typically-empty
  interval sets — keep the defense, share the body.

### tl_plan.c / .h (374 + 168 LOC)
Query planning: prune sources, prime iterators, collect tombstones.

- **FINDING S5b/S5c** — write-only plan state:
  - `tomb_capacity` (tl_plan.h:87): set to `tomb_count` at build (tl_plan.c:336), zeroed
    in destroy (373), never read anywhere in the repo. Rung 1, ~3 LOC.
  - `segments_pruned` / `memruns_pruned` (tl_plan.h:90–91): incremented in five places
    (219, 224, 255, 273/279 region), **zero readers repo-wide** (grep over all .c/.h
    including tests returned nothing). Write-only "stats". Rung 1, ~12 LOC.
- **FINDING S6** — sealed-memrun priority computation (286–301) is loop-invariant
  (`base_priority` depends only on the manifest) yet recomputed per memrun; and the
  `if (i > UINT32_MAX)` arm is impossible — `i` indexes the sealed ring buffer, a small
  fixed-capacity queue (invariant H-07), never 4 billion entries. Hoist `base_priority`
  above the loop, keep the single saturating add. Rung 6, ~8 LOC, zero perf change
  (planning path, loop runs a handful of times).
- **FINDING S7** — `add_segment_tombstones` / `add_memrun_tombstones` /
  `add_active_tombstones` (147–169): three single-use 6-line wrappers whose bodies are
  `tl_tombstones_add_intervals(accum, X_tombs_imm(y), t1, t2, unb)`. Inline at the call
  sites (233, 262, 307, 321). Rung 6, ~15 LOC net.
- **FINDING S10** — `ensure_source_capacity` (21–57) hand-rolls the overflow guard
  (`new_cap > SIZE_MAX / sizeof(...)`) + malloc/memcpy/free. The allocator seam already
  provides `tl__mallocarray` (used 30 lines away in `tl_point.c:38`) which owns the
  multiply-overflow check; `tl__realloc` also exists per the engineering guide. Rung 2,
  ~8 LOC.
- Tombstone collection interleaved with source scanning (vs. calling
  `tl_snapshot_collect_tombstones`): **NO/NO** — the interleaving is a deliberate single
  pass over sources; the standalone collector exists for count/stats which don't build
  iterators. Unifying would re-scan every source. The two also differ subtly in overlap
  predicates (plan adds a segment's tombstones whenever the segment is selected for any
  reason; `tl_tombstones_add_intervals` filters internally), so a merge is not
  behavior-preserving for free.
- The `iter.segment` inline-init / `iter.memrun`+destroy-on-exhausted dance in
  `add_*_source` (60–145) is three near-identical functions, but they differ in real ways
  (segment init cannot fail; memrun/active can) — collapses naturally if S2 lands
  (three kinds → two).

### tl_merge_iter.c / .h (337 + 152 LOC)
Outer k-way merge over the plan's tagged-union sources.

- `source_next/done/seek` if-chain dispatch (23–84): hand-rolled 3-way dispatch over
  `tl_iter_kind_t`, with MSVC C4702 pragma for the defensive fallback. **NO/NO** on
  replacing with function pointers — the branch on a 2–3 value enum is cheaper and
  inlines; this is the hot merge loop. (S2 shrinks it to 2 arms for free.)
- Peek + `replace_top` instead of pop/push (208–235): correct ENOMEM-safety reasoning
  documented ("a pop/push pair would risk losing a record if push failed"). Keep.
- Error latching + heap clear on failure (239–244): H-16 requirement. Keep.
- **FINDING S5a** — `tl_kmerge_iter_t.alloc` (tl_merge_iter.h:47): assigned once
  (tl_merge_iter.c:128), never read — `tl_heap` carries its own allocator. Rung 1, ~3 LOC.
- `tl_kmerge_iter_seek` (257–337) vs `tl_submerge_seek`: two implementations of
  heap-preserve forward seek. **NO/NO** on unifying — see the two-level-merge entry in
  the no-and-no section.

### tl_snapshot.c / .h (336 + 177 LOC)
Snapshot acquisition, tombstone collection, count.

- Acquisition (71–164): writer_mu-serialized capture, then off-lock OOO-head sort, then
  epoch-revalidated cache store. Every line is invariant-driven (#6 snapshot consistency,
  #8 two-phase capture, "never do expensive work under writer_mu"). **NO/NO** — the
  complexity is the design.
- **FINDING S8a** — `tl_snapshot_collect_tombstones` L0 loop (227–244) and L1 loop
  (247–264) are body-identical (10 lines each, only the `l0_get`/`l1_get` accessor
  differs). Same shared-helper treatment as S8b. Rung 7, ~14 LOC.
- `tl_snapshot_count_range_internal` (274–336): clean per-source dispatch into
  `tl_count.h`. This is the function `tl_stats` should be calling — see S1.
- Debug iterator tracking (54–65): `#ifdef TL_DEBUG` counters; cheap, catches
  release-with-outstanding-iterators. Keep.

### tl_segment_iter.c / .h (229 + 110 LOC)
Page-catalog + in-page binary-search cursor. The forward-only monotonicity clamps in
`seek` (179–213: `new_page_idx < it->page_idx` clamp, same-page `new_row_idx <
old_row_idx` clamp) look paranoid but are load-bearing: the kmerge seek preserves heap
entries with `ts >= target` and sources must never re-yield consumed records. **NO/NO.**
The bitmask page-flag tests with rationale comments (22, 199) are deliberate
(future-flag safety). Nothing to remove; this file is already minimal.

### tl_submerge.c / .h (179 + 85 LOC)
Inner k-way merge over raw sorted arrays. Tight; the direct
`src->data[src->pos++]` advance with no function-pointer dispatch is exactly why the
two-level merge exists. `tl_submerge_src_init`'s `pos > end` clamp (57–59) is defensive
for direct/test callers with empty ranges — 3 LOC, fine. **NO/NO.**

### tl_memrun_iter.c / .h + tl_active_iter.c / .h (135+114 / 125+97 LOC)
- **FINDING S2** — these are the same iterator implemented twice. Compare
  `tl_memrun_iter_next` (81–110) with `tl_active_iter_next` (72–100) and
  `tl_memrun_iter_seek` (112–135) with `tl_active_iter_seek` (102–125): the bodies are
  line-identical (delegate to `tl_submerge_next`/`_seek`, latch `done`). The structs are
  identical except the borrowed source pointer (`mr` vs `mv`), which after init is only
  ever NULLed in destroy — dead weight (**S5e**). Only the `init` functions differ: which
  buffers they hand to `tl_iter_build_submerge`, plus memrun's redundant pruning (the
  plan already checks `tl_memrun_has_records` + range overlap at tl_plan.c:272–281 before
  constructing the iterator) and active's sortedness assert.
  Proposal (conservative): one `tl_delta_iter_t { tl_submerge_t merge; t1; t2;
  t2_unbounded; done; }` with `tl_delta_iter_init_memrun()` / `_init_active()` and shared
  `next/seek/destroy/done`. `tl_plan.h`'s union drops from 3 members to 2,
  `tl_iter_kind_t` from 3 kinds to 2, and `source_next/done/seek` in tl_merge_iter.c lose
  an arm each. Internal API only (consumers: tl_plan, tl_merge_iter, and
  `core/tests/test_delta_internal.c` — 35 references, mechanical renames). Rung 7,
  ~200 LOC net (4 files ≈ 471 LOC → ~260, plus plan/merge shrinkage, minus test churn),
  low-medium risk, zero perf delta (same submerge underneath; one fewer dispatch arm).
  Deeper cut (optional, medium risk): drop the wrapper entirely and put `tl_submerge_t`
  in the plan union — the wrappers' seek guards (`target <= t1` no-op, `target >= t2` →
  done) are already implied by submerge source bounds (`end` is clipped to t2 at init, so
  seek past t2 exhausts naturally), and the init-time pruning is redundant with the
  plan's. ~350 LOC, but loses the defensive layer test code exercises directly; take the
  conservative version first.

### tl_iter_build.c / .h (96 + 30 LOC)
- **FINDING S4** — `count_sources` (3–24) exists only to size the `srcs` malloc exactly;
  but `tl_iter_build_submerge` already sets `merge->src_count = idx` after filling (87)
  and `tl_submerge_build` iterates `src_count`, so over-allocating is harmless. Pass
  `2 + run_count` to `tl_submerge_init` and delete `count_sources`. Cost: ≤ a few unused
  56-byte slots for the iterator's lifetime; benefit: one fewer pass over the runset and
  ~24 LOC. Rung 7, low risk.
- **FINDING S5d** — the `head_watermark` parameter is dead: the memrun caller passes it
  with `head_len == 0` (source never created, tl_memrun_iter.c:49–52), the active caller
  passes non-NULL `head_seqs` so the ternary at line 84 always selects 0
  (tl_active_iter.c:40–43). Furthermore the ternaries at lines 62 and 84
  (`X_seqs != NULL ? 0 : X_watermark`) are doubly-defensive — `tl_submerge` itself
  ignores `watermark` whenever `seqs != NULL` (tl_submerge.c:72, 113, 163). Delete the
  parameter and the ternaries. Rung 1, ~6 LOC.

### tl_filter.c / .h (78 + 82 LOC)
Tombstone-filtering wrapper. The `tomb_cursor.len == 0` fast path (30–39) skips the
per-record cursor call on the common no-deletes case — 10 LOC buying a hot-path win.
The skip-ahead via `can_skip` + `cursor_skip_to` + `kmerge_seek` (62–71) is the
documented watermark-safe optimization. **NO/NO** — already minimal.

### tl_segment_range.h (118 LOC)
Fence-pointer counting without row scans (boundary pages via lower_bound, interior via
prefix sums). `tl_count_records_in_segment_since` shares the first-page logic of
`_range`; factoring the last-page part out would save ~8 lines at the cost of a
harder-to-read seam across an unbounded/bounded split. Not worth it. **NO/NO.**

---

## Findings Index (with LOC estimates)

| # | Title | Rung | Where | LOC saved | Risk | API change |
|---|-------|------|-------|-----------|------|------------|
| S1 | `tl_stats` should call `tl_snapshot_count_range_internal(TL_TS_MIN,0,true)`; delete full-extent helpers | 2 | tl_count.h:149–233, tl_timelog.c:2070–2118 | ~110 | low | no |
| S2 | Merge `tl_memrun_iter` + `tl_active_iter` into one delta iterator | 7 | 4 files | ~200 | low-med | internal only |
| S3 | Replace tl_point's hand-rolled array with in-tree `tl_recvec` | 2 | tl_point.c:23–64, tl_point.h:37–42 | ~40 | low | internal only |
| S4 | Delete `count_sources` two-pass; over-allocate `2+run_count` | 7 | tl_iter_build.c:3–24, 48–49 | ~24 | low | no |
| S5 | Dead-state sweep: kmerge.alloc, tomb_capacity, pruned counters, head_watermark, mr/mv fields, dead point branch, REQUIRE_ZEROCOPY | 1 | see walkthrough | ~30 | low | flag bit only |
| S6 | Hoist loop-invariant `base_priority`; drop impossible `i > UINT32_MAX` | 6 | tl_plan.c:286–301 | ~8 | low | no |
| S7 | Inline three single-use tombstone-adder wrappers | 6 | tl_plan.c:147–169 | ~15 | low | no |
| S8 | Shared helper for identical L0/L1 loops | 7 | tl_snapshot.c:227–264, tl_point.c:325–353 | ~25 | low | no |
| S9 | NULL-seqs+watermark support in `tl__count_visible_sorted_range`; absorb OOO-run inline loop | 2 | tl_count.h:377–494 | ~25 | low | no |
| S10 | Use `tl__mallocarray`/`tl__realloc` in `ensure_source_capacity` | 2 | tl_plan.c:21–57 | ~8 | low | no |

Test coverage note: S1/S3/S5f ride on existing stats/point/tombstone suites; S2 requires
mechanical updates to `test_delta_internal.c` (35 refs) but the behavior is pinned by the
full query/merge suites; S4/S5/S6/S7/S8/S10 are behavior-preserving refactors under the
existing ~485 C tests. None require new test surfaces.

---

## Prior-Art Leads (honest fit notes; later research verifies)

1. **K-way merge iterator** (tl_merge_iter, tl_submerge). Candidates: CCAN `heap`
   (BSD-MIT), PostgreSQL `binaryheap` (PostgreSQL licence — MIT-compatible-ish but
   server-embedded, extraction cost), RocksDB MergingIterator (C++ — fails pure-C).
   Fit: **poor**. The heap is already factored into in-tree `tl_heap`; the merge payload
   (watermark + tie_break_key + error latching per H-16) is domain-specific; hot-loop
   zero-regression rule kills any indirection a generic library adds.
2. **Dynamic arrays** (tl_point result, tl_plan sources). Candidates: klib `kvec.h` (MIT),
   `stb_ds.h` (MIT/Unlicense). Fit: **beaten by rung 2** — in-tree `tl_recvec` already
   covers `tl_record_t` arrays and respects the allocator seam; stb_ds's realloc hooks fit
   the seam awkwardly (global, not per-context). For the one non-record array
   (plan sources) a kvec-style macro would save <30 LOC — not worth a vendored file.
3. **Atomic refcounted owner** (pagespan). Candidates: liburcu `urcu/ref.h` (**LGPL —
   fails licence gate**), Concurrency Kit (BSD; primitives only, no destructor-carrying
   refcount). Fit: **no** — in-tree `tl_refcount.h` macros are already shared and tuned
   for the GCC-TSan fence limitation this project has documented; any import would need
   the same acq_rel decrement treatment.
4. **Interval set / tombstone cursor** (consumed here, lives in `internal/tl_intervals`).
   Candidates: CCAN interval modules, various interval-tree libs. Fit: **no** — the
   canonical form (sorted, non-overlapping, non-adjacent, half-open — invariant #5) plus
   `max_seq` skyline semantics is bespoke; the cursor's amortized-O(1) forward scan is
   simpler than any tree.
5. **lower_bound**. C stdlib `bsearch` does not provide lower_bound semantics; the
   in-tree branchless `tl_record_lower_bound` is a measured v1.3 perf win (point −15%,
   3–5× search). **Do not touch.**

---

## Explicit NO-and-NO (earns its keep)

| Aspect | Why prior art / simplification is a bad trade |
|--------|-----------------------------------------------|
| Two-level merge: kmerge-over-iterators + submerge-over-arrays, with duplicated heap-seek logic (tl_merge_iter.c:257–337 vs tl_submerge.c:131–179) | Deliberate perf structure: the inner merge advances raw arrays (`src->data[src->pos++]`, tl_submerge.c:111–122) with zero dispatch; unifying behind one polymorphic source interface adds indirection to the hottest read loop. Zero-regression rule → non-finding. |
| Snapshot acquisition two-phase sort + epoch-checked cache (tl_snapshot.c:96–149) | Invariants #6/#8: writer_mu serializes publishers and capture; the O(N log N) OOO-head sort must run off-lock; the cache store revalidates the memtable epoch. Every "redundant" lock/unlock is the design. |
| Pagespan owner freed BEFORE release hook (tl_pagespan_iter.c:135–157, header 79–93) | Documented allocator-lifetime contract: the binding hook may free the allocator that owns the owner struct. "Fixing" the ordering is a use-after-free. |
| Empty-range pagespan open still acquires snapshot/owner (tl_pagespan_iter.c:333–346) | Pin symmetry with binding `pins_enter`/release-hook pairing; skipping would leak the pin. Documented in-code. |
| `source_next/done/seek` if-chain instead of vtable (tl_merge_iter.c:23–84) | 2–3-arm enum branch beats function-pointer dispatch on the merge hot path; MSVC pragma handles the defensive fallback. |
| Segment-iter seek monotonicity clamps (tl_segment_iter.c:179–213) | Load-bearing for kmerge's heap-preserving seek: sources are forward-only and must never re-yield consumed records. Not paranoia. |
| Filter's no-tombstone fast path (tl_filter.c:30–39) | 10 LOC that skip a per-record cursor call in the common no-deletes case — hot query iteration. |
| Plan's inline tombstone collection vs reusing `tl_snapshot_collect_tombstones` | Single pass over sources during planning; the standalone collector serves count/stats which build no iterators. Subtly different overlap predicates make unification non-free. |
| Defensive L1 tombstone loops (tl_plan.c:231–234, tl_snapshot.c:247–264, tl_point.c:339–353) | L1 is tombstone-free by invariant, but the loops cost a scan over empty interval sets and keep the code correct if that invariant ever changes; each site says so in a comment. (Share the loop body per S8, keep the defense.) |
| `tl__range_overlap_half_open` (tl_count.h:35–59) | No intersection-computing helper exists in `tl_range.h` (predicates only); hand-rolled interval intersection is 20 honest lines. |
| Peek+replace_top instead of pop/push in both merges (tl_merge_iter.c:206–235, tl_submerge.c:108–126) | ENOMEM safety: a failed push after pop would lose a record. Documented. |
| `tl_segment_range.h` boundary/interior counting split | Fence-pointer + prefix-sum counting is what makes count O(log P) instead of O(M); the near-duplication between `_range` and `_since` (~8 lines) reads better duplicated across the bounded/unbounded split. |
