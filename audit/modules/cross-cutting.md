# Cross-Cutting Simplification Audit — timelog

Unit: **cross-cutting** (repo-wide duplication patterns across all production C).
Scope: `core/src/**` (73 files) + `bindings/cpython/src/**` (8 files + 10 headers), ~29,700 LOC total.
Method: exhaustive grep quantification + full reads of every file implicated by a pattern hit.
Auditor stance: lazy-senior ("ponytail") — the best code is code never written; laziness never applies to reading.

---

## Executive Summary

The codebase is in unusually good cross-cutting shape: the dangerous shared machinery is
**already consolidated** (refcounting in `tl_refcount.h`, growth arithmetic in
`tl__grow_capacity`, the branchless binary search canonical in `tl_search.h`, closed-checks in
`TL_PY_DEFINE_CHECK`). The real cross-cutting debt is not duplication of live code — it is
**speculative "library completeness"**: internal utility modules (recvec, intervals, heap,
alloc, locks, seqlock, range, page) each carry a tail of functions with **zero production
callers**, kept alive only by tests that test the dead code, or by nothing at all.

Four findings survive scrutiny:

| # | Finding | Rung | Est. LOC saved | Risk |
|---|---------|------|----------------|------|
| 1 | Delete ~30 production-dead internal functions | 1 (does-not-need-to-exist) | ~430 prod (+~200 test churn) | low |
| 2 | Merge `tl_memrun_iter` + `tl_active_iter` into one `tl_delta_iter` | 7 (minimal-rewrite) | ~180 | medium |
| 3 | Delegate `tl_page_lower_bound` to a `tl_ts_lower_bound` in `tl_search.h` | 2 (already-in-this-codebase) | ~25 | low |
| 4 | Use `tl__grow_capacity` at the 2 straggler grow sites | 2 (already-in-this-codebase) | ~12 | low |

Everything else the audit brief asked about (goto variance, refcount macros, iterator
vtables, TL_CHECK, memcpy loops, header boilerplate) is a grounded **NO and NO** — see §4.

---

## 1. Quantification of the Eight Instructed Patterns

### 1.1 `goto` cleanup boilerplate

**Count**: 58 goto statements across 7 files:
`py_timelog.c` (13), `tl_compaction.c` (10), `tl_plan.c` (8), `tl_memview.c` (6),
`module.c` (6), `tl_point.c` (4), `py_iter.c` (2).

**Label variance** (9 spellings): `fail` ×20, `error_stream` ×9, `cleanup` ×8, `error` ×6,
`stats_error` ×4, `error_seq` ×4, `rollback` ×3, `success` ×2, `done` ×2.

**Verdict: NO simplification.** C17 has no `defer`; single-exit-with-goto is the canonical
kernel-style idiom and CLAUDE.md documents it as the house pattern. Label-name variance is
per-function-local and costs zero LOC to keep; a rename sweep saves zero lines. The only
micro-nit found: `tl_flush.c:250-266` repeats an identical 4-line free sequence
(`tl_heap_destroy` + 3× `tl__free`) twice inline instead of using a `goto fail` — ~6 lines,
not worth the churn on its own but fold it in if finding #4 touches that function anyway.

### 1.2 Refcount acquire/release idiom

**Already consolidated.** `core/src/internal/tl_refcount.h:16-39` defines
`TL_REFCOUNT_ACQUIRE` (CAS loop with post-final-release and overflow guards) and
`TL_REFCOUNT_RELEASE` (acq_rel `fetch_sub`, deliberately NOT a relaxed-dec + fence because
"GCC ThreadSanitizer does not model [the fence]" — tl_refcount.h:12-14). All 7 refcounted
types use it:

- `tl_ooorun.c:55,66` (run), `tl_ooorun.c:189,200` (runset)
- `tl_memrun.c:159,170`
- `tl_memview.c:492,503`
- `tl_manifest.c:67,78`
- `tl_segment.c:439,455`
- `tl_pagespan_iter.c:161,168` (span owner)

What remains per type is ~12 lines of wrapper (`NULL` check + macro call + destroy body,
e.g. `tl_memrun.c:154-182`). A `TL_DEFINE_REFCOUNT_PAIR(prefix, type, destroy_body)`
generator macro could save ~60 net LOC across 7 sites, but the destroy bodies genuinely
differ (inline free lists vs. `manifest_destroy(m)` call), and macro-generated functions
degrade stack traces, grep-ability, and debugger stepping in exactly the code where the
project has burned TSan-debugging hours (see the tl_refcount.h comment). **Verdict: NO —
the memory-ordering hazard is already centralized; the residue is honest glue.**

### 1.3 Iterator vtable/interface duplication

**No vtables exist.** Grep for `(*next)`, `(*close)`, `vtable`, `_ops` across core: zero
hits. Polymorphism is a tagged union (`tl_plan.h:36-59`, kinds SEGMENT/MEMRUN/ACTIVE) with a
3-way if-chain in exactly three ~15-line static helpers (`tl_merge_iter.c:23-80`,
`source_next`/`source_done`/`source_seek`). That is the minimal C encoding; a vtable would
be *more* lines plus an indirect call per record on the hot k-way merge. **NO** on dispatch.

**But the leaf iterators ARE duplicated** — this is finding #2 (§2.2): `tl_memrun_iter_t`
(`tl_memrun_iter.h`) and `tl_active_iter_t` (`tl_active_iter.h`) have field-for-field
identical structs (modulo the borrowed back-pointer `mr`/`mv`, which is used only inside
their own init), and their `next`/`seek`/`destroy` bodies are token-identical
(`tl_memrun_iter.c:81-135` ≡ `tl_active_iter.c:72-125`). Both are thin adapters over
`tl_submerge_t`, differing only in which accessors feed `tl_iter_build_submerge()`.

`tl_submerge.c` vs `tl_merge_iter.c` share a structural skeleton (heap prime /
peek+replace_top / EOF-pop / seek-via-lower_bound) but differ fundamentally: submerge
sources are flat arrays with infallible advance (`tl_submerge.c:111-126`), kmerge sources
are fallible iterators with error-latching (`tl_merge_iter.c:239-244`). Unifying them
requires an advance-callback, i.e. an indirect call per record on the hottest read path.
**NO** per the zero-perf-regression rule.

### 1.4 Hand-rolled binary searches outside `tl_search.h`

The canonical dual-mode (branchless-cmov under `TL_LOWER_BOUND_BRANCHLESS_MAX`, branchy
above) lower_bound lives in `tl_search.h:14-43`. Full copies of that exact algorithm:

| Site | Element | Status |
|------|---------|--------|
| `tl_recvec.c:266-295` `tl_recvec_lower_bound` | `tl_record_t.ts` | **production-dead** (only caller is `tl_recvec_range_bounds`, itself test-only) |
| `tl_recvec.c:297-326` `tl_recvec_upper_bound` | `tl_record_t.ts` | **production-dead** (tests/bench only) |
| `tl_page.c:141-176` `tl_page_lower_bound` | `int64 ts[]` | **live + hot** (segment_iter, pagespan_iter, point, segment_range) |
| `tl_page.c:177-210` `tl_page_upper_bound` | `int64 ts[]` | **production-dead** (tests/bench only) |

Plain 7-line branchy searches over *other* keys (not duplicates of the algorithm, just the
textbook loop): `tl_manifest.c:101` (L1 by window_start), `tl_page.c:365,387` (catalog by
max_ts/min_ts), `tl_intervals.c:35,359` (interval starts). These search strided struct
members; a generic version needs an accessor macro that costs more than the ~20 lines it
saves. **NO** for those five.

**Findings**: delete the three dead copies (§2.1); then the only real duplicate left is
`tl_page_lower_bound` — add `TL_INLINE size_t tl_ts_lower_bound(const tl_ts_t*, size_t,
tl_ts_t)` beside `tl_record_lower_bound` in `tl_search.h` and make `tl_page_lower_bound`
delegate (§2.3). `tl_page_lower_bound` is already an extern function in a .c file, so
callers pay a call either way; delegating to a `TL_INLINE` helper is codegen-identical.
Bonus: the `TL_LOWER_BOUND_BRANCHLESS_MAX` gate — a measured v1.3 perf win — gets exactly
one tuning point instead of two (currently five).

Note: do NOT "simplify" upper_bound as `lower_bound(ts+1)` — `ts == TL_TS_MAX` makes `+1`
signed overflow (UB). (Moot once the dead upper_bounds are deleted.)

### 1.5 Grow-array (realloc doubling) outside `tl_recvec`

Shared helper exists: `tl__grow_capacity` (`tl_alloc.h:150-163`, overflow-safe doubling with
min cap) — used by `tl_intervals.c:15`, `tl_heap.c:117`, `tl_seqvec.c:54`,
`tl_manifest.c:207`. Stragglers that hand-roll it:

- `tl_memtable.c:243-251` — verbatim reimplementation (`new_cap = 64; while (new_cap <
  needed) { if (new_cap > SIZE_MAX/2) ... new_cap *= 2; }`) inside dropped-record
  collection. Replace with `tl__grow_capacity(*dropped_cap, needed, 64)`: −10 lines. The
  only semantic delta (exact-fit cap when doubling would overflow `SIZE_MAX/2`) is
  unreachable for `needed = len+1`.
- `tl_flush.c:250` — `new_cap = (dropped_cap == 0) ? 64 : dropped_cap * 2;` — same helper
  fits: −3 lines.
- `bindings/cpython/src/py_handle.c:395-405` — power-of-two hash-table growth driven by a
  0.7 load factor (`used * 10 <= cap * 7`, py_handle.c:396). Different algorithm (load
  factor, tombstones), and the binding does not include core-internal headers. **Leave it.**

Both core sites are on the dropped-record (tombstone-drop) path — flush/seal, not append —
so cold. Finding #4 (§2.4).

### 1.6 Per-file header boilerplate

52/52 headers use `#ifndef TL_*_H` guards (zero `#pragma once`, zero license banners, zero
CRT boilerplate). Sampled `tl_segment.h:1-8`, `tl_flush.h:1-8`, `tl_heap.h:1-5`,
`tl_filter.h:1-6`: uniform, minimal, relative-path includes. **NO finding — nothing to
delete, and consistency is already perfect.**

### 1.7 TL_CHECK / error-propagation macro consistency

There is **no** general `TL_CHECK` macro. Status propagation is 173 explicit
`if (st != TL_OK)` sites (top: `tl_compaction.c` 37, `tl_timelog.c` 20, `tl_intervals.c` 14,
`tl_point.c` 13, `tl_memtable.c` 13). The only check-macros are `TL_CHECK_OPEN`
(`tl_timelog.c:28`, 9 uses) and the binding's `TL_PY_DEFINE_CHECK` (5 uses, one per heap
type) — both single-purpose and consolidated.

**Verdict: NO.** Roughly half the 173 sites do cleanup or status remapping rather than bare
`return st;`, so a propagation macro covers ~85 sites × 2 lines ≈ 170 LOC — at the price of
hiding control flow in a codebase whose review culture (per project memory) is explicitly
hostile to hidden control flow. Uniform-and-explicit beats terse-and-macro'd here; there is
also zero inconsistency to fix.

### 1.8 memcpy-loop patterns

Repo-wide scan for element-by-element copy loops found exactly two:
`tl_recvec.c:254` (`rv->data[i] = tmp[i].rec` — unpacking a sort-pair array) and
`tl_page.c:110` (`page->ts[i] = records[i].ts` — AoS→SoA transpose). Neither is expressible
as `memcpy` (strided source). Everything else already uses `memcpy`/`memset`. **NO finding.**

---

## 2. Findings (Ladder-Classified)

### 2.1 [rung 1 — does-not-need-to-exist] Delete the production-dead function tail (~430 prod LOC)

A systematic sweep (342 internal functions declared in `core/src/**/*.h`, each grepped for
callers in `core/src` + `bindings/cpython/src`, then cross-checked against `core/tests`)
found the following **verified** dead groups. "Zero-ref" = no references anywhere including
tests; "test-only" = production decl+def only, referenced solely by tests/benches.

**Zero-ref (delete today, no test churn, ~120 LOC):**

| Function | Site | Body LOC |
|----------|------|----------|
| `tl__reallocarray` | `tl_alloc.c:173` (+`tl_alloc.h:104`) | 16 |
| `tl__alloc_get_total/count/peak` | `tl_alloc.c:243-253` (+h:195-197) | 12 |
| `tl_memtable_insert_tombstone_unbounded` | `tl_memtable.c:795` (+h:202) | 16 |
| `tl_recvec_sort` (+ its `cmp_record_ts`) | `tl_recvec.c:197-204` (+h:92) | 9+ |
| `tl_recvec_get_mut` | `tl_recvec.h:157` | 6 |
| `tl_intervals_max_seq` | `tl_intervals.c:389` (+h:123) | 4 |
| `tl_lock_is_held`, `tl_lock_highest_held` (+ release-mode stubs) | `tl_locks.h:81-96,126-127` | 20 |
| `tl_range_overlap_start`, `tl_ts_at_or_past_end`, `tl_ts_before_end` | `tl_range.h:23-30,55-57` | 20 |
| `tl_window_contains_bounded` | `tl_window.h:159` | ~8 |
| `tl_point_result_empty` | `tl_point.h:78` | 4 |
| `tl_snapshot_alloc` | `tl_snapshot.h:75` | 4 |
| `tl_memview_shared_epoch` | `tl_memview.h:207` | 4 |
| `tl_ooorun_gen` | `tl_ooorun.h:96` | 4 |

**Test-only (delete + prune the tests that exist solely to test them, ~310 prod LOC):**

| Function | Site | Body LOC | Test refs |
|----------|------|----------|-----------|
| `tl_recvec_lower_bound` | `tl_recvec.c:266` | 30 | 8 |
| `tl_recvec_upper_bound` | `tl_recvec.c:297` | 30 | 9 |
| `tl_recvec_range_bounds` | `tl_recvec.c:328` | 9 | 3 |
| `tl_recvec_insert` | `tl_recvec.c:150` | 26 | 2 |
| `tl_recvec_shrink_to_fit` | `tl_recvec.c:75` | 28 | 1 |
| `tl_page_upper_bound` | `tl_page.c:177` | 35 | 9 |
| `tl_heap_build` | `tl_heap.c:188` | 30 | 2 |
| `tl_heap_len` | `tl_heap.h:100` | 4 | many |
| `tl_intervals_union` | `tl_intervals.c:576` | 13 | 6 |
| `tl_intervals_covered_span` | `tl_intervals.c:679` | 24 | 2 |
| `tl_intervals_contains` | `tl_intervals.c:380` | 4 | 15 |
| `tl_memrun_create` | `tl_memrun.c:94` | 40 | 28 |
| `tl_memtable_seal` (4-line adapter; prod uses `_seal_ex`, `tl_timelog.c:551,607,1138`) | `tl_memtable.c:1059` | 4 | 16 |
| `tl_manifest_version` | `tl_manifest.h:210` | 4 | 2 |
| Seqlock reader side: `tl_seqlock_read/is_even/validate/current` | `tl_seqlock.h:87-112` | 28 | several |

Plus corresponding header declarations and doc comments (~150 additional lines).

**Notes and caveats:**
- High-fan-in test helpers (`tl_memrun_create` ×28, `tl_memtable_seal` ×16,
  `tl_intervals_contains` ×15) should be **moved into the test tree** as static helpers
  rather than rewritten at every call site — production still sheds the code; tests keep
  their vocabulary. `tl_intervals_contains` is 4 lines; trivially inlined into tests.
- The **seqlock reader side** is explicitly documented as "a hook for future lock-free
  optimisations on the read side" (`tl_seqlock.h:21-22`) and CLAUDE.md invariant #6 confirms
  production snapshot acquisition takes `writer_mu` instead of running a reader retry loop.
  That is textbook speculative code — YAGNI says delete (28 trivial lines to re-add), but
  flag it to the author since it encodes a considered design direction.
- `tl_recvec.c` keeps its live core (`init/reserve/push/sort-at-seal` path used by
  `tl_memtable.c`, `tl_compaction.c`); only its search/insert/shrink tail dies. Same for
  `tl_intervals` (the canonical-set core and cursor are hot and heavily used).
- All deletions are internal — the public contract (`core/include/timelog/timelog.h`) is
  untouched. Debug validators (`tl_memrun_validate`, `tl_memtable_validate`) were NOT
  verified dead (likely reachable under `TL_DEBUG`) and are excluded.
- Safety net: existing 485-test C suite still compiles the live core; the deleted-function
  tests are deleted with their subjects. Recommend one `-DTIMELOG_BUILD_*` full matrix run
  (Debug/ASan + Release + MSVC) to catch any `#if`-guarded caller the grep missed.

**Estimated total: ~430 production LOC (+~150 header/doc lines), minus ~50 lines of new
test-side helpers ⇒ net ~500 lines out of the shipped library.**

### 2.2 [rung 7 — minimal-rewrite] Merge `tl_memrun_iter` and `tl_active_iter` into one `tl_delta_iter`

**Evidence:**
- Structs identical modulo back-pointer: `tl_memrun_iter.h` (`mr` + t1/t2/t2_unbounded +
  `tl_submerge_t merge` + `done`) vs `tl_active_iter.h` (`mv` + same four fields).
- `tl_memrun_iter_next` (`tl_memrun_iter.c:81-110`) and `tl_active_iter_next`
  (`tl_active_iter.c:72-100`) are token-identical; same for `_seek`
  (`tl_memrun_iter.c:112-135` ≡ `tl_active_iter.c:102-125`) and `_destroy`.
- Only `_init` differs: which accessors feed `tl_iter_build_submerge(...)`
  (`tl_memrun_iter.c:42-55` passes memrun run/ooo-runs with NULL seqs + watermarks;
  `tl_active_iter.c:33-46` passes memview run/head/runs with seq arrays), plus memrun's
  early-out range check (`tl_memrun_iter.c:27-36`).

**Proposal:** one `tl_delta_iter_t` with `tl_delta_iter_init_memrun()` /
`tl_delta_iter_init_memview()` and shared `next/seek/destroy/done`. The plan's tagged union
(`tl_plan.h:45-49`) drops from 3 members to 2; `source_next/done/seek` in
`tl_merge_iter.c:23-80` drop from 3-way to 2-way dispatch. The `has_variable_watermark`
computation (`tl_merge_iter.c:144`) keys off `kind == TL_ITER_ACTIVE` — replace with a
`bool variable_watermark` set at plan-build time (`tl_plan.c` already distinguishes the two
when it assigns priorities).

**Cost/benefit:** −4 files → 2; ~471 lines (260 .c + 211 .h) → ~290 ⇒ **~180 LOC saved**,
one fewer concept in the read path. Perf: identical or marginally better (shorter dispatch
chain); the shared `next` body is what both compile to today. Risk: medium — touches
read-path plumbing across plan/merge/point (`tl_point.c` also instantiates these iterators);
fully covered by the existing query/merge/OOO test suites (no new tests needed). No public
API change.

### 2.3 [rung 2 — already-in-this-codebase] `tl_page_lower_bound` re-implements `tl_search.h`

`tl_page.c:141-176` is the `tl_search.h:14-43` algorithm re-typed for a flat `int64` array
(the comment even cross-references `TL_LOWER_BOUND_BRANCHLESS_MAX`). After 2.1 deletes the
recvec/page dead copies, add the array variant next to the canonical:

```c
/* tl_search.h */
TL_INLINE size_t tl_ts_lower_bound(const tl_ts_t* ts, size_t len, tl_ts_t target);
```

and reduce `tl_page_lower_bound` to bounds-check + delegate. **~25 LOC net saved**, and the
branchless/branchy gate — a measured perf asset — has exactly one implementation. Hot path,
but codegen-identical: the page function is already extern-called, and the helper is
`TL_INLINE` in a header exactly like `tl_record_lower_bound` (which `tl_submerge.c:153`,
`tl_count.h:76` etc. already inline). Covered by `test_search_branchless.c` +
`bench_search_lower_bound.c` (both already differential-test page vs reference — they keep
working unchanged).

### 2.4 [rung 2 — already-in-this-codebase] Two grow-sites bypass `tl__grow_capacity`

- `tl_memtable.c:243-251`: replace the 9-line manual doubling loop with
  `size_t new_cap = tl__grow_capacity(*dropped_cap, needed, 64);` (+ existing `== 0` /
  `tl__alloc_would_overflow` checks, matching the four existing users, e.g.
  `tl_heap.c:117-118`).
- `tl_flush.c:250`: `tl__grow_capacity(dropped_cap, dropped_len + 1, 64)` replaces the
  ternary-double.

**~12 LOC saved**, both on cold tombstone-drop collection paths (flush/seal, not append).
Behavior-identical for all reachable inputs. Covered by existing flush/tombstone drop tests.

---

## 3. Prior-Art Leads (honest fit notes — later phases verify)

| Sub-problem | In-repo | Candidates | Fit notes |
|---|---|---|---|
| Portable threads/mutex/cond shim | `tl_sync.c/h` (806 LOC, pthreads+Win32) | **tinycthread** (zlib), C11 `<threads.h>` | C11 threads: MSVC still doesn't ship it → dead end. tinycthread: license OK, MSVC OK, vendorable single pair; but it lacks `tl_mutex_is_held` debug tracking (`tl_sync.h`), `tl_thread_set_name`, and the ms-granular `tl_cond_timedwait`; project is effectively unmaintained; and the existing shim is already TSan-proven on 3.14t. Weak lead — glue would eat most of the ~400-line win. |
| Binary min-heap (k-way merge) | `tl_heap.c/h` (334 LOC) | klib `ksort.h` heap fns, CCAN `heap` (BSD-MIT) | Poor fit: entries are 32-byte structs with `(ts, tie_break_key)` composite ordering and a `replace_top` op that the hot merge relies on (`tl_merge_iter.c:235`); generic heaps do pop+push (2× sift) or need comparator indirection. Zero-perf-regression rule kills it. |
| Open-addressing hash (live handles) | `py_handle.c` (~250 LOC of table) | klib `khash.h` (MIT) | License/compiler fine, allocator-overridable. But the table chains resized-out arrays on `retired_tables` (`py_handle.c:69-73,225-226`) so lock-free readers survive rehash — khash frees on resize, breaking the free-threaded design. Poor fit. |
| Lock-free MPSC stack (retired queue) | `py_handle.c:237-260` Treiber push (~60 LOC) | Concurrency Kit `ck_stack` (BSD-2) | CK's MSVC coverage is partial and its custom fences are exactly what the project's TSan notes warn about (GCC TSan can't see fences). Vendoring a dependency for 60 already-C11-atomic lines is a net loss. |
| Dynamic arrays | `tl_recvec`/`tl_seqvec` (+`tl__grow_capacity`) | klib `kvec.h`, `stb_ds.h` | kvec calls libc `realloc` directly (breaks the `tl__*` allocator seam, CLAUDE.md hard rule); stb_ds allocator override is global not per-context. In-repo growth is already one shared helper. Poor fit. |
| Interval set w/ seq watermarks | `tl_intervals` (1,122 LOC) | (none mature in C) | Canonical half-open, non-adjacent-merged, **seq-tagged** intervals with an amortized-O(1) cursor (`tl_intervals_cursor_max_seq`, hot in `tl_count.h:471+`) is domain-specific; generic interval libs carry no per-interval metadata. NO — earns its keep. |
| Sorting | `qsort` (`tl_recvec.c:204`, `tl_manifest.c:554`, memview seal) | klib `ks_introsort` (MIT) | Already stdlib (rung 3 satisfied). A specialized sort would be a *perf* experiment (comparator devirtualization on the O(H log H) seal), not a simplification — out of scope here. |
| Atomics shim | `tl_atomic.h` (389 LOC, C11 + MSVC Interlocked dual) | — | This IS the platform layer (MSVC has no reliable C mode `<stdatomic.h>`; `tl_atomic.h:17-21`). No candidate is simpler than the problem. |

---

## 4. NO and NO (machinery that earns its keep)

1. **goto-cleanup pattern (58 sites, 9 label spellings)** — C17 has no defer; this is the
   documented house idiom (CLAUDE.md "Cleanup Pattern"). Variance is cosmetic; consolidation
   saves 0 LOC. (§1.1)
2. **Per-type refcount wrappers** — the TSan-sensitive memory-ordering core is already the
   single `tl_refcount.h` macro pair; a further generator macro (~60 LOC) trades stack-trace
   and grep clarity in the exact area where the project debugged fence-visibility
   false-positives (tl_refcount.h:11-14). (§1.2)
3. **K-merge tagged-union dispatch** (`tl_merge_iter.c:23-80`) — 3-way if-chain is minimal;
   a vtable adds lines *and* an indirect call per record on the hottest path. (§1.3)
4. **`tl_submerge` vs `tl_kmerge` structural echo** — infallible-flat vs fallible-iterator
   sources; unifying needs per-record callback indirection. Hot path ⇒ non-finding by the
   zero-perf-regression rule. (§1.3)
5. **Absence of a TL_CHECK propagation macro** — 173 uniform explicit sites; ~half need
   cleanup/remap anyway; macro hides control flow for ~170 LOC in a review culture that
   punishes hidden control flow. Consistency is already perfect. (§1.7)
6. **memcpy loops** — both remaining element loops are strided transposes memcpy cannot
   express. (§1.8)
7. **Header boilerplate** — 52/52 headers minimal and uniform. (§1.6)
8. **`tl_count.h` internal repetition** — the three `lower_bound`-pair idioms
   (`tl_count.h:76,389,471`) sit in variants with genuinely different visibility semantics
   (per-record seqs vs run-level watermark vs no skyline); merging needs parameter explosion
   worse than the ~15 repeated lines.
9. **`tl_atomic.h` / `tl_sync` / `tl_seqlock` writer side / `tl_intervals` core /
   `tl_heap`** — see §3: each is either the platform truth (MSVC), TSan-constrained, or
   perf-tuned beyond what mature libraries offer under the hard adoption constraints.
10. **py_handle.c hash growth** (`py_handle.c:395-405`) — load-factor-driven power-of-two
    growth is a different algorithm from `tl__grow_capacity`, and bindings correctly do not
    include core-internal headers.

---

## 5. Per-File Walkthrough (files read in full for this unit)

- `CLAUDE.md` — architecture/invariant baseline for all judgments.
- `core/src/internal/tl_refcount.h` (42) — consolidation already done; §1.2.
- `core/src/internal/tl_search.h` (46) — canonical lower_bound; §1.4.
- `core/src/internal/tl_locks.h` (151) — TL_LOCK macros live; `is_held`/`highest_held` dead (§2.1).
- `core/src/internal/tl_range.h` (59) — `overlaps`/`is_empty` live; 3 of 5 predicates dead (§2.1).
- `core/src/internal/tl_seqlock.h` (114) — writer side live (publication windows, invariant
  #6); reader side speculative (§2.1 caveat).
- `core/src/query/tl_merge_iter.h/.c` (153+337) — dispatch minimal; error latch (H-16) respected; §1.3.
- `core/src/query/tl_plan.h` (169) — tagged union; 2 accessors unused but trivial.
- `core/src/query/tl_iter_build.c` (97) — the single shared submerge builder; good.
- `core/src/query/tl_memrun_iter.c` (135) + `tl_active_iter.c` (125) — duplication finding #2.
- `core/src/query/tl_submerge.c` (179) — flat-source merge; distinct from kmerge by design.
- Targeted full reads of the implicated regions in: `tl_recvec.c`, `tl_page.c`,
  `tl_manifest.c`, `tl_memrun.c`, `tl_ooorun.c`, `tl_memtable.c`, `tl_flush.c`,
  `tl_alloc.h/.c`, `tl_heap.c`, `tl_intervals.c`, `tl_count.h`, `tl_atomic.h`, `tl_sync.h`,
  `py_handle.c`, plus grep-quantification across all 83 production files.

## 6. Suggested Order of Attack

1. **2.1 zero-ref deletions** — mechanical, no test churn, ~120 LOC, one CI matrix run.
2. **2.4 grow-capacity stragglers** — 12 LOC, trivial review.
3. **2.1 test-only deletions** — move 3 helpers into tests, prune dead-code tests, ~380 LOC.
4. **2.3 search delegation** — small, keeps the perf asset single-sourced.
5. **2.2 delta-iter merge** — the one change needing real review (read-path plumbing);
   do it alone in its own PR with the full validation matrix.
