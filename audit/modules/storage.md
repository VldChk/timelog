# Ponytail Audit — Unit: storage

Auditor stance: lazy senior dev. Read all 3,074 lines of the unit (plus the
call sites in `query/`, `maint/`, `delta/`, `tl_timelog.c`, `internal/`, and the
C tests needed to ground every claim). The storage layer is, overall, tight and
disciplined: single-allocation SoA pages, COW manifest with release-mode
invariant checks, refcounting through a shared macro. The fat that exists is
mostly **speculative V2 machinery, dead convenience APIs, and duplicated
validation/cleanup code** — not architectural over-engineering.

## Files reviewed (LOC)

| File | LOC |
|---|---|
| core/src/storage/tl_page.c | 457 |
| core/src/storage/tl_page.h | 402 |
| core/src/storage/tl_segment.c | 638 |
| core/src/storage/tl_segment.h | 346 |
| core/src/storage/tl_manifest.c | 688 |
| core/src/storage/tl_manifest.h | 251 |
| core/src/storage/tl_window.c | 127 |
| core/src/storage/tl_window.h | 165 |
| **Total** | **3,074** |

## Executive summary

- **Biggest deletion candidate (rung 1):** the V2 row-delete machinery
  (`tl_rowbitset_t`, `row_del`/`row_del_kind` fields, `tl_page_row_is_deleted`,
  `TL_PAGE_FULLY_DELETED`/`PARTIAL_DELETED` handling). The header says it
  outright: "never instantiated in V1" (tl_page.h:23-25). It costs ~110 LOC,
  16 bytes per page header, and — notably — **a per-record inline call on the
  merge hot loop** (tl_segment_iter.c:134). Deleting it is a perf-neutral-to-
  positive simplification.
- **Real duplicate (rung 2):** `tl_window_default_size` is duplicated as a
  static `default_window_size` in tl_timelog.c:97 — and the two copies have
  **already drifted** (`default:` returns 1H **seconds** vs 1H **milliseconds**).
  Production uses the static; the storage one is test-only. Textbook case for
  deleting one copy.
- **Second duplicate (rung 2):** the 29-line release-mode tombstone
  canonical-form check in `tl_segment_build_l0` re-implements
  `tl_intervals_arr_validate` rule-for-rule; the shared validator is just
  locked behind `#ifdef TL_DEBUG`.
- Several dead convenience APIs (`tl_page_upper_bound`,
  `tl_window_bounds_for_ts`, `tl_window_contains{,_bounded}`,
  `tl_segment_page_prefix_counts`, `cap_l0`/`cap_l1`) have **zero production
  callers**.
- ~45 LOC of segment-builder error-path cleanup collapses onto the existing
  `segment_destroy()` because `TL_NEW` is calloc-backed.
- The things that look heavy — release-mode L1/window validation, O(n²)
  manifest add/remove validation, dual segment bounds, fence-pointer metadata
  duplication — all **earn their keep** (see NO-and-NO).

Total honest LOC-saved estimate across all findings: **~330–370** (~11% of the
unit), with zero hot-path regression and one small hot-path *improvement*.

---

## Per-file walkthrough

### tl_page.{h,c} — page + builder + binary search + catalog

- **SoA single-allocation layout** (tl_page.c:61-107): header + ts[] + h[] in
  one `tl__malloc` with `tl_align_up_safe` between regions, every size step
  overflow-checked. Correct and deliberate ("destruction is a single free…
  SoA data sits next to its metadata in cache", tl_page.c:33-36). Keep.
- **Binary search** (tl_page.c:141-211): branchless cmov variant under a size
  gate (`TL_LOWER_BOUND_BRANCHLESS_MAX`, tl_defs.h:50) with a branchy
  fallback. This is the measured v1.3 perf win. Keep. But `tl_page_upper_bound`
  has no production caller (finding S4), and both `count == 0` early returns
  (tl_page.c:144-146, 180-182) are dead-defensive: the builder rejects
  `count == 0` (tl_page.c:43-45) and both loop forms handle n=0 naturally.
- **V2 delete machinery** (tl_page.h:14-36, 71-74, 205-236; tl_page.c:241-255):
  speculative, never instantiated — finding S1.
- **Page catalog** (tl_page.c:266-457): a plain grow-by-doubling array of
  `tl_page_meta_t` using the shared `tl__grow_capacity` helper, plus two
  lower_bound variants over meta fields. The metadata duplication
  (min/max/count/flags cached from the page header) is fence-pointer design —
  binary search touches only the contiguous meta array, not each page. Keep
  (N8).
- `tl_page_builder_t` (tl_page.h:90-94) is a 3-field struct whose
  `target_page_bytes` is written once (tl_page.c:28) and never read;
  `tl_page_builder_build` uses only `pb->alloc` (tl_page.c:97). Single
  production consumer: `build_pages` in tl_segment.c:115-116. Finding S10.
- `memset(backing, 0, sizeof(tl_page_t))` at tl_page.c:102 is redundant: all
  10 fields of `tl_page_t` are assigned at tl_page.c:104-120 (finding S7).

### tl_segment.{h,c} — L0/L1 builders, tombstones, refcount

- **compute_tombstone_bounds** (tl_segment.c:12-40): straightforward, shared
  by builder and debug validator. Keep.
- **Release-mode tombstone canonical-form loop** (tl_segment.c:204-236):
  duplicates `tl_intervals_arr_validate` (tl_intervals.c:772-812) — finding S5.
- **build_pages** (tl_segment.c:111-169): includes the H-13 cross-page
  sortedness check (tl_segment.c:134-141) which is invariant-mandated — keep.
  Its 8-line rollback loop and the callers' four hand-rolled cleanup blocks
  collapse onto `segment_destroy()` — finding S6.
- **Prefix-count block duplicated verbatim** between build_l0
  (tl_segment.c:280-297) and build_l1 (tl_segment.c:391-407) — part of S6.
- **Release-mode L1 window containment check** (tl_segment.c:419-423): H-12.
  Keep (N3).
- **Refcounting** (tl_segment.c:433-458): uses shared `TL_REFCOUNT_ACQUIRE/
  RELEASE` from tl_refcount.h with the acq_rel-folded decrement documented at
  tl_segment.h:203-217 (GCC TSan can't model fences). Already the in-codebase
  dedupe. Keep (N7).
- Accessors: `tl_segment_page_prefix_counts` (tl_segment.h:285-287) has zero
  callers; the NULL-fallback loop in `tl_segment_page_prefix_sum`
  (tl_segment.h:300-308) is unreachable for published segments — finding S9.
  `tl_segment_is_l0/is_l1/is_tombstone_only` are test-only but 1-liners that
  document the model; not worth deleting.
- **Debug validator** (tl_segment.c:468-636): thorough, matches CLAUDE.md
  invariants, uses `has_content` instead of sentinel timestamps because
  TL_TS_MAX is legitimate data (tl_segment.c:502-504). Keep.

### tl_manifest.{h,c} — COW builder + publication invariants

- **manifest_destroy / create / refcount** (tl_manifest.c:9-81): minimal. The
  field-by-field zeroing after calloc-backed `TL_NEW` is redundant (S7).
- **l1_find_first_overlap** (tl_manifest.c:87-111): third hand-rolled
  lower_bound in the unit; correctness argument documented (non-overlap ⇒
  max_ts monotone). Keep; see prior-art lead P1.
- **Builder add/remove ×4** (tl_manifest.c:239-303): four structurally
  identical 15-line functions over a shared `ensure_capacity`. Tolerable;
  a macro would save ~30 lines at the cost of a concept (see P2).
- **validate_removals / validate_adds** (tl_manifest.c:331-412): O(n²) pointer
  scans implementing H-10/H-11. n = tens of segments; a hash set would be
  over-engineering. Keep (N4).
- **build** (tl_manifest.c:434-600): single-allocation arrays sized by
  `count_kept`, acquire-on-insert, `qsort` (stdlib — good) then release-mode
  non-overlap check (tl_manifest.c:560-575, H-14 — keep, N3), then cached
  global bounds. `cap_l0`/`cap_l1` are write-only fields and the comment at
  tl_manifest.c:535-536 references a "cap_l1 sanity assertion" that does not
  exist — finding S8.
- **Debug validator** (tl_manifest.c:608-686): checks flush-order generations,
  window sort/non-overlap/unbounded-last, cached bounds. Keep.

### tl_window.{h,c} — grid math

- **tl_floor_div_i64** (tl_window.h:45-58): necessary — C `/` truncates toward
  zero; no stdlib signed floor division exists. Also used by
  maint/tl_adaptive.c:192. Keep (N6).
- **tl_window_id_for_ts / tl_window_bounds** (tl_window.c:24-110): overflow-
  checked with saturation and the unbounded-trailing-window encoding that the
  L1 invariants depend on. Heavily used by compaction. Keep (N6).
- **tl_window_default_size** (tl_window.c:7-18): duplicated in tl_timelog.c —
  finding S3.
- **tl_window_bounds_for_ts** (tl_window.c:116-127), **tl_window_contains**
  (tl_window.h:141-150), **tl_window_contains_bounded** (tl_window.h:159-163):
  zero production callers — finding S2.

---

## Findings (ranked)

### S1. Delete the V2 row-delete machinery — rung 1 (does-not-need-to-exist)

**Evidence:**
- tl_page.h:23-25: "V1 does not emit per-page delete masks. These types are
  defined for forward compatibility but are **never instantiated in V1**."
- tl_page.h:11: "V1 only produces FULLY_LIVE pages; other values are reserved
  for V2."
- The only writer is the page builder, which hardwires
  `flags = TL_PAGE_FULLY_LIVE; row_del = NULL; row_del_kind = TL_ROWDEL_NONE`
  (tl_page.c:117-119); the debug validator *rejects* anything else
  (tl_page.c:249-255: `if (page->flags != TL_PAGE_FULLY_LIVE) return false;`).
- Consumers burn cycles on it anyway: `tl_page_row_is_deleted(page, it->row_idx)`
  is called **per record** in the segment iterator hot loop
  (tl_segment_iter.c:134) and per candidate row in point lookup
  (tl_point.c:111); page-level `TL_PAGE_FULLY_DELETED` pruning checks sit at
  tl_point.c:176, tl_segment_iter.c:22, 199.
- `tl_page_row_is_deleted` itself is 32 lines of defensive checks for
  metadata that cannot exist (tl_page.h:205-236).

**Proposal:** delete `tl_page_del_flags_t` extra values, `tl_rowdel_kind_t`,
`tl_rowbitset_t`, the `row_del`/`row_del_kind`/`reserved` fields, the `flags`
field (or reduce to nothing), `tl_page_row_is_deleted`, the validator clauses,
and the five query-side call sites. Reintroduce with V2 when V2 actually
exists — git remembers.

**LOC saved:** ~110 (≈80 in tl_page.h/.c, ≈15 in query/, ≈15 validator).
**Perf:** removes one predictable branch per record from the merge loop and
one per page from pruning — zero-regression, plausibly a small win; shrinks
`tl_page_t` by 16 bytes. **Risk:** medium — this is a *deliberate* forward-
compat seam; deleting it is a product decision, and it touches query files
outside this unit. Behavior fully covered by existing range/point/tombstone
tests (~485 C tests). **api-change:** no (internal headers only).

### S2. Delete dead window helpers — rung 1

**Evidence:** repo-wide grep (core/src + bindings):
- `tl_window_contains_bounded` (tl_window.h:159-163): **zero callers anywhere**,
  including tests.
- `tl_window_contains` (tl_window.h:141-150): callers only in
  core/tests/test_storage_internal.c:155-177.
- `tl_window_bounds_for_ts` (tl_window.h:112-132 + tl_window.c:116-127):
  callers only in tests. Compaction composes the two primitives itself
  (tl_compaction.c:246→277 uses `tl_window_id_for_ts` then `tl_window_bounds`).

**Proposal:** delete all three; port the handful of test assertions to the two
real primitives (the `tl_window_contains` tests are genuinely half-open-
semantics tests and can inline `ts >= start && (unbounded || ts < end)`).

**LOC saved:** ~55 in production headers/impl (test churn extra but small).
**Risk:** low. **api-change:** no (internal).

### S3. Deduplicate `default_window_size` — rung 2 (already-in-this-codebase)

**Evidence:**
- tl_window.c:7-18 `tl_window_default_size(unit)`: switch over S/MS/US/NS,
  `default: return TL_WINDOW_1H_S;`
- tl_timelog.c:97-105 static `default_window_size(unit)`: same switch,
  `default: return TL_WINDOW_1H_MS;` — **the copies have drifted** on the
  defensive default.
- Production path uses only the static (tl_timelog.c:205-206:
  `tl->effective_window_size = (cfg->window_size == 0) ?
  default_window_size(cfg->time_unit) : ...`); the public one is exercised
  only by test_storage_internal.c:73-83.

**Proposal:** delete the static in tl_timelog.c and call
`tl_window_default_size`, or (lazier) delete the storage one and move the
tests. Either way, one source of truth. Note the drift is currently harmless
(`tl_config_validate` rejects invalid time units before the default is
consulted — tl_timelog.c:164 region), but it is exactly how a real
inconsistency ships later.

**LOC saved:** ~12. **Risk:** low. Well covered by existing config tests.

### S4. `tl_page_upper_bound` has no production caller — rung 1

**Evidence:**
- Grep: callers are only core/tests/test_search_branchless.c:131,182,234,
  core/tests/bench_search_lower_bound.c:236,281, and
  test_storage_internal.c:380-383. No hit in core/src outside tl_page.c.
- The header's own justification is stale: tl_page.h:164-166 says point
  queries use "start = lower_bound(target); end = upper_bound(target)", but
  the actual point path does lower_bound + forward scan
  (tl_point.c:106-116).

**Proposal:** delete tl_page.c:177-211 and tl_page.h:177-183, and drop the
upper-bound legs of the branchless test/bench.

**LOC saved:** ~40 production, more in tests/bench.
**Risk:** low — but flag: the branchless upper_bound was built alongside the
measured lower_bound win and the bench compares both; deleting removes a
benchmarked artifact someone may want when a real caller (e.g. inclusive-end
queries) appears. Lazy verdict: it hasn't appeared; delete.

### S5. Reuse `tl_intervals_arr_validate` in `tl_segment_build_l0` — rung 2

**Evidence:**
- tl_segment.c:208-236: 29-line release-mode loop enforcing: max_seq != 0,
  bounded start<end, sorted by start, non-overlap, no equal-seq adjacency,
  unbounded-only-last — plus `max_seq <= applied_seq`.
- tl_intervals.c:772-812 (`tl_intervals_arr_validate`): the **same rules**,
  rule-for-rule (start<end at 784, max_seq!=0 at 787, unbounded-last at 790,
  sorted at 797, non-overlap at 801, equal-seq adjacency at 805-809), minus
  only the applied_seq cap. It is `#ifdef TL_DEBUG` (tl_intervals.c:770,
  tl_intervals.h:279-296) purely by placement, not by cost.

**Proposal:** move `tl_intervals_arr_validate` out of `TL_DEBUG` (it is O(T),
called at flush-build time — off hot path; tombstone counts are small and
H-18 already caps debt windows), then build_l0 becomes the validate call plus
a 4-line `max_seq <= applied_seq` loop. The debug segment validator
(tl_segment.c:492-499) already uses exactly this composition — build_l0 would
match it.

**LOC saved:** ~22, and one source of truth for canonical form (CLAUDE.md
invariant #5). **Risk:** low; the EINVAL rejections are directly tested in
test_storage_internal.c and delta tests.

### S6. Collapse segment-builder error paths onto `segment_destroy` — rung 7

**Evidence:**
- `TL_NEW` is calloc-backed (tl_alloc.h:173-174: `tl__calloc(ctx, 1, sizeof)`),
  so a fresh `tl_segment_t` is fully zeroed; `segment_destroy`
  (tl_segment.c:86-103) safely handles every partially-built state (pages via
  catalog, catalog, prefix counts, tombstones, seg — all NULL-tolerant).
- Yet there are five hand-rolled cleanup blocks:
  - build_pages rollback loop, tl_segment.c:161-168;
  - build_l0 create_tombstones failure, tl_segment.c:260-264;
  - build_l0 build_pages failure, tl_segment.c:269-274;
  - build_l0 prefix-alloc failure, tl_segment.c:283-291 (destroys tombstones,
    loops pages, destroys catalog, frees seg — i.e. re-implements
    segment_destroy);
  - build_l1 equivalents at tl_segment.c:382-385 and 394-401.
- The prefix-sum construction itself is duplicated verbatim:
  tl_segment.c:280-297 vs 391-407 (18 lines ×2).

**Proposal:** (a) factor `build_prefix_counts(seg)` as a static helper;
(b) make every builder failure after `TL_NEW` do `segment_destroy(seg);
return st;`. build_pages then doesn't need its rollback loop at all (callers
destroy via segment_destroy; the one un-pushed page still needs its local
destroy at tl_segment.c:152).

**LOC saved:** ~45. **Perf:** error paths only — off hot path by definition.
**Risk:** low-medium: error paths have only indirect coverage today (flush
ENOMEM fault injection in test_delta_internal.c:45-51, 794-847 reaches
build_l0; no direct storage-unit ENOMEM tests — grep for "fail" in
test_storage_internal.c finds none). ASan/LSan in Debug CI would catch a leak
regression through the delta tests, but a direct injection test for both
builders should accompany this change.

### S7. Drop redundant zeroing after calloc-backed TL_NEW — rung 6

**Evidence:**
- tl_segment.c:247-254 and 368-376: `seg->window_start = 0; ...
  seg->page_prefix_counts = NULL;` immediately after `TL_NEW` (calloc).
- tl_manifest.c:43-51 (create) and the else-branches at 497-499, 511-513
  (`m->l0 = NULL; m->cap_l0 = 0;`): same.
- tl_page.c:102: `memset(backing, 0, sizeof(tl_page_t))` on a block whose
  every field is assigned at tl_page.c:104-120.

**Proposal:** delete the dead stores (keep the non-zero assignments).
**LOC saved:** ~20. **Risk:** near-zero mechanically; note this is partly a
style call — explicit init documents the struct contract. The memset deletion
is unambiguous. All off hot path (page build ≈ once per ~4K records at
flush/compaction).

### S8. Delete write-only `cap_l0`/`cap_l1` manifest fields — rung 1

**Evidence:** tl_manifest.h:34,39 ("Capacity cache (diagnostic; == n_l0 when
published)"). Writes at tl_manifest.c:45,48,496,499,510,513. Repo-wide grep:
**no reads anywhere** (core, bindings, tests). The comment at
tl_manifest.c:535-536 justifying insert order "for the cap_l1 sanity
assertion" references an assertion that does not exist in the file.

**Proposal:** delete both fields, their six stores, and fix the stale comment.
**LOC saved:** ~12 (+8 bytes/manifest). **Risk:** low.

### S9. Dead prefix-counts accessor + unreachable NULL fallback — rung 1 / 6

**Evidence:**
- `tl_segment_page_prefix_counts` (tl_segment.h:285-287): zero callers
  anywhere (only `tl_segment_page_prefix_sum` is used —
  tl_segment_range.h:86,112).
- The NULL-fallback loop inside `tl_segment_page_prefix_sum`
  (tl_segment.h:300-308) is unreachable: both builders allocate the prefix
  array whenever `page_count > 0` and **fail the whole build with TL_ENOMEM
  otherwise** (tl_segment.c:282-291, 393-401), so no published segment with
  pages ever has `page_prefix_counts == NULL`; when `page_count == 0`,
  `first == last` returns at tl_segment.h:296-298.

**Proposal:** delete the accessor; replace the fallback with
`TL_ASSERT(seg->page_prefix_counts != NULL)`.
**LOC saved:** ~14. **Perf:** removes a branch from the range-count
precompute path — neutral-to-positive. **Risk:** low.

### S10. Collapse `tl_page_builder_t` — rung 7

**Evidence:**
- The struct (tl_page.h:90-94) carries `alloc`, `target_page_bytes`,
  `records_per_page`. `target_page_bytes` is written (tl_page.c:28) and never
  read again. `tl_page_builder_build` uses only `pb->alloc` (tl_page.c:97) —
  neither capacity field.
- Single production consumer: `build_pages` (tl_segment.c:115-116 init;
  :145 build; :118 reads `pb.records_per_page`).

**Proposal:** `tl_page_build(alloc, records, count, out)` +
keep `tl_page_builder_compute_capacity(target_page_bytes)`; delete the struct
and `tl_page_builder_init`. build_pages calls compute_capacity once.
**LOC saved:** ~25 gross; net ~15 after test updates (test_storage_internal.c
and test_search_branchless.c construct builders directly).
**Risk:** low. **api-change:** no (internal header).

### Micro-notes (not counted above)

- `tl_page_lower_bound`/`upper_bound` `count == 0` early returns
  (tl_page.c:144-146, 180-182) are unreachable for published pages and
  redundant even defensively (both loops handle n=0). 6 LOC.
- `tl_page_builder_compute_capacity`'s `target <= header_size` clamp
  (tl_page.c:12-14) plus TL_MIN_PAGE_ROWS floor is fine; leave it.

---

## Prior-art leads (fit notes, not verdicts)

### P1. Typed lower_bound over sorted arrays
- **Sub-problem:** five hand-rolled lower_bound loops in this unit alone:
  tl_page.c:141-175 (branchless+branchy), 177-211 (upper), catalog
  find_first_ge/find_start_ge (tl_page.c:352-397), manifest
  l1_find_first_overlap (tl_manifest.c:87-111). More exist in other units.
- **Candidates:** none good. C stdlib `bsearch` returns *any* match — wrong
  semantics for lower_bound. klib/CCAN/stb do not ship a lower_bound
  primitive (klib's ksort.h is sorting; CCAN asearch is bsearch-typed).
- **Fit notes:** the branchless page-level variant is a measured v1.3 win
  (point −15.2%) and must stay hand-rolled. The three *branchy* struct-keyed
  copies could be stamped from one local macro
  (`TL_LOWER_BOUND(arr, n, expr)`), saving ~30 LOC — in-codebase dedupe, not
  a library adoption. External adoption verdict: expected NO.

### P2. Growable pointer array
- **Sub-problem:** manifest builder's four add/remove functions +
  `ensure_capacity` (tl_manifest.c:199-303) and page catalog reserve/push
  (tl_page.c:291-346) — classic dynamic array.
- **Candidates:** klib `kvec.h` (MIT), `stb_ds.h` (MIT/Unlicense).
- **Fit notes:** kvec hardwires libc `realloc`/`free` — violates the
  `tl__realloc` allocator seam unless the vendored copy is patched. stb_ds's
  `STBDS_REALLOC(ctx,...)` override exists but the context plumbing is
  awkward for per-instance `tl_alloc_ctx_t*`. Both build on MSVC/-Werror with
  care. Honest assessment: the codebase already owns `tl__grow_capacity` +
  overflow guards; a 20-line internal `tl_ptrvec` would beat either library,
  and even that is marginal for two call sites. Expected NO on external
  adoption; possible small internal dedupe.

### P3. Intrusive refcounting
- **Sub-problem:** segment + manifest refcount (tl_segment.c:433-458,
  tl_manifest.c:63-81) — acquire/release with destruction at zero.
- **Candidates:** liburcu `urcu/ref.h` (**LGPL — fails license constraint**),
  Concurrency Kit (BSD-2; `ck_pr` primitives but no ready refcount object),
  GLib GRefCount (LGPL — fails).
- **Fit notes:** already deduplicated in-house via `TL_REFCOUNT_ACQUIRE/
  RELEASE` (tl_refcount.h), and deliberately tuned: the acquire half is folded
  into the acq_rel RMW because GCC TSan does not model
  `atomic_thread_fence` (tl_segment.h:203-217; also a documented project
  constraint). Any library adoption would re-open the TSan question for zero
  LOC win. Verdict: NO.

### P4. Overflow-checked integer arithmetic (used by window math)
- **Sub-problem:** `tl_add/sub/mul_overflow_i64` consumed at
  tl_window.c:35,72,85,100.
- **Candidates:** platform rung — C23 `<stdckdint.h>` `ckd_*`;
  GCC/Clang `__builtin_*_overflow`; MSVC needs a manual fallback.
- **Fit notes:** these live in internal/tl_math.h (outside this unit) and
  almost certainly already wrap the builtins; MSVC + C17 keeps a hand-rolled
  fallback necessary. Recorded only so the internal-unit auditor checks that
  tl_math uses the builtins where available.

---

## NO-and-NO (earns its keep)

- **N1. Single-allocation SoA page layout with overflow-checked alignment
  math** (tl_page.c:61-124). Simpler alternatives regress: two allocations
  double free/alloc traffic on flush/compaction and fragment; a flexible
  array member can't host *two* differently-typed arrays; skipping the
  overflow checks violates the "count is caller-supplied" hardening. The
  ~30 lines of size arithmetic are the price of one-free destruction.
- **N2. Branchless binary search + size gate** (tl_page.c:151-163, 187-198).
  Measured product win (v1.3: point −15.2%, search 3–5×). The duplicated
  branchy fallback is required above the gate where cmov's unconditional
  dependent loads lose. Perf is the product; do not "simplify".
- **N3. Release-mode invariant checks** — L1 window containment
  (tl_segment.c:419-423, H-12), manifest L1 non-overlap after sort
  (tl_manifest.c:560-575, H-14), cross-page sortedness (tl_segment.c:134-141,
  H-13), tombstone canonical form on build_l0 (S5 dedupes it but must keep it
  in release). CLAUDE.md explicitly requires these in release builds; they
  run at publication frequency, not per record.
- **N4. O(n²) validate_removals/validate_adds** (tl_manifest.c:331-412,
  H-10/H-11). n is tens of segments and this runs once per flush/compaction
  publish; a hash set (uthash etc.) is more code and a dependency for a
  non-problem.
- **N5. The COW manifest builder as a whole** (tl_manifest.c:113-600). A
  "simpler" mutate-under-lock design violates immutability-after-publication
  and the seqlock publication protocol (CLAUDE.md invariants 1, 6); the
  builder is the mechanism behind H-17 strict publish. Not simplifiable
  without violating invariants — non-finding by rule.
- **N6. Window math: floor division + saturating overflow handling**
  (tl_window.h:45-58, tl_window.c:49-110). C has no signed floor division;
  negative timestamps and INT64 edges are real (tests at
  test_storage_internal.c:89-245 exercise exactly these). The unbounded-
  trailing-window encoding is load-bearing for L1 non-overlap.
- **N7. Refcount macros** (via tl_refcount.h). Already shared between segment
  and manifest; TSan-tuned acq_rel decrement per the documented GCC fence
  limitation. Leave alone.
- **N8. Page catalog metadata duplication** (tl_page.h:264-270 caches
  min/max/count/flags from the page header). Deliberate fence-pointer design:
  catalog binary search touches one contiguous array instead of chasing a
  pointer per probe. Removing the cache would regress query pruning. (The
  `flags` member alone dies with S1.)
- **N9. Segment dual bounds** (record_* + tomb_* + overall min/max,
  tl_segment.h:63-72). All three pairs are consumed: overall bounds for
  manifest pruning (tl_manifest.c:582-589), record bounds by count/plan
  (tl_count.h:157-158, tl_plan.c:247), tomb bounds by snapshot tombstone
  collection (tl_snapshot.c:232,252). The build_l0 comment explains why the
  union matters: "pruning a segment that holds an out-of-record-range
  tombstone would silently lose deletes" (tl_segment.c:299-300).
- **N10. `tl_page_meta_t.page` back-pointer + non-owning catalog.** The
  segment owns pages, catalog owns metadata only (tl_page.h:289-292);
  inverting ownership would complicate the rollback story for no gain.

## Safety net notes

- Findings S1–S5, S8–S10 are behavior-preserving deletions/dedupes of code
  paths exercised by the existing ~485 C tests (storage_internal, delta,
  compaction, functional) — high confidence.
- S6 (error-path consolidation) is the one finding that *needs new tests*:
  direct ENOMEM injection on `tl_segment_build_l0/l1` (today only reached
  indirectly through flush fault-injection in test_delta_internal.c).
- S2/S3/S4/S10 require mechanical test updates (they delete test-only APIs).
