 Implementation Plan: Timelog V2 PageSpan Core API Unification

 Status: Ready for implementation
 LLD: docs/timelog_v2_lld_pagespan_core_api_unification.md
 Last Updated: 2026-01-15

 ---
 Executive Summary

 Move PageSpan enumeration logic from CPython bindings into the C core. This eliminates code duplication where py_span_iter.c re-implements the same catalog binary search + lower_bound logic 
  that exists in tl_segment_iter.c.

 Key Change: Bindings become thin wrappers calling core API instead of walking internal structures directly.

 ---
 1. Files to Create
 ┌──────────────────────────────┬───────────────────────────────────────┐
 │             File             │                Purpose                │
 ├──────────────────────────────┼───────────────────────────────────────┤
 │ src/query/tl_pagespan_iter.h │ Public header for binding consumption │
 ├──────────────────────────────┼───────────────────────────────────────┤
 │ src/query/tl_pagespan_iter.c │ Streaming iterator implementation     │
 ├──────────────────────────────┼───────────────────────────────────────┤
 │ tests/test_pagespan_iter.c   │ TDD test suite for core API           │
 └──────────────────────────────┴───────────────────────────────────────┘
 ---
 2. Core Types

 2.1 Public Types (in header)

 /* Opaque types */
 typedef struct tl_pagespan_owner tl_pagespan_owner_t;
 typedef struct tl_pagespan_iter  tl_pagespan_iter_t;

 /* Span view - returned by iter_next */
 typedef struct tl_pagespan_view {
     tl_pagespan_owner_t* owner;     /* Owned ref (caller must decref) */
     const tl_ts_t*       ts;        /* Pointer to page ts array */
     const tl_handle_t*   h;         /* Pointer to page handle array */
     uint32_t             len;       /* Row count (always > 0) */
     tl_ts_t              first_ts;  /* == ts[0] */
     tl_ts_t              last_ts;   /* == ts[len-1] */
 } tl_pagespan_view_t;

 /* Release hooks for binding cleanup */
 typedef void (*tl_pagespan_owner_release_fn)(void* user);
 typedef struct tl_pagespan_owner_hooks {
     void* user;
     tl_pagespan_owner_release_fn on_release;
 } tl_pagespan_owner_hooks_t;

 2.2 Internal Types (in .c file)

 struct tl_pagespan_owner {
     uint32_t                    refcnt;
     tl_snapshot_t*              snapshot;   /* Owned */
     tl_alloc_ctx_t*             alloc;      /* Borrowed */
     tl_pagespan_owner_hooks_t   hooks;      /* Copied */
 };

 typedef enum { PHASE_L1 = 0, PHASE_L0 = 1, PHASE_DONE = 2 } iter_phase_t;

 struct tl_pagespan_iter {
     tl_pagespan_owner_t* owner;
     const tl_manifest_t* manifest;  /* Borrowed from snapshot */
     tl_ts_t t1, t2;
     uint32_t flags;

     iter_phase_t phase;
     uint32_t seg_idx;

     const tl_segment_t* current_seg;
     uint32_t page_idx, page_end;

     bool closed;
 };

 ---
 3. Flags

 enum {
     TL_PAGESPAN_SEGMENTS_ONLY    = 1u << 0,  /* Required in B4 */
     TL_PAGESPAN_INCLUDE_L0       = 1u << 1,
     TL_PAGESPAN_INCLUDE_L1       = 1u << 2,
     TL_PAGESPAN_VISIBLE_ONLY     = 1u << 3,  /* Reserved: EINVAL */
     TL_PAGESPAN_REQUIRE_ZEROCOPY = 1u << 4,
 };

 #define TL_PAGESPAN_DEFAULT \
     (TL_PAGESPAN_SEGMENTS_ONLY | TL_PAGESPAN_INCLUDE_L0 | \
      TL_PAGESPAN_INCLUDE_L1 | TL_PAGESPAN_REQUIRE_ZEROCOPY)

 Rules:
 - flags == 0 treated as TL_PAGESPAN_DEFAULT
 - TL_PAGESPAN_SEGMENTS_ONLY required (return TL_EINVAL if not set)
 - TL_PAGESPAN_VISIBLE_ONLY reserved (return TL_EINVAL if set)

 ---
 4. Function Signatures

 /**
  * Open iterator for [t1, t2) range.
  * Acquires snapshot internally; pins until all views released.
  */
 tl_status_t tl_pagespan_iter_open(
     tl_timelog_t* tl,
     tl_ts_t t1,
     tl_ts_t t2,
     uint32_t flags,
     const tl_pagespan_owner_hooks_t* hooks,  /* Optional */
     tl_pagespan_iter_t** out);

 /**
  * Get next span. Returns TL_OK with view, or TL_EOF when exhausted.
  * View's owner is incref'd (caller must decref via view_release).
  */
 tl_status_t tl_pagespan_iter_next(
     tl_pagespan_iter_t* it,
     tl_pagespan_view_t* out_view);

 /**
  * Close iterator. Idempotent, safe on NULL.
  */
 void tl_pagespan_iter_close(tl_pagespan_iter_t* it);

 /**
  * Owner reference counting.
  */
 void tl_pagespan_owner_incref(tl_pagespan_owner_t* owner);
 void tl_pagespan_owner_decref(tl_pagespan_owner_t* owner);

 /**
  * View helper - decrefs owner and zeroes view.
  */
 static inline void tl_pagespan_view_release(tl_pagespan_view_t* v);

 ---
 5. Algorithm (Streaming)

 5.1 iter_open Flow

 1. Validate: tl != NULL, out != NULL
 2. Normalize flags (0 -> DEFAULT)
 3. Validate B4: SEGMENTS_ONLY required, VISIBLE_ONLY forbidden
 4. Empty range (t1 >= t2): create iter with phase=DONE, return TL_OK
 5. Acquire snapshot via tl_snapshot_acquire()
 6. Create owner (refcnt=1, holds snapshot)
 7. Create iterator (holds owner ref)
 8. Initialize phase to PHASE_L1 or PHASE_L0 based on flags
 9. Return TL_OK

 5.2 iter_next Flow

 1. Check closed/done -> TL_EOF
 2. Loop:
    a. If no current_seg, call advance_to_next_segment()
    b. If advance fails -> TL_EOF
    c. Scan pages in [page_idx, page_end):
       - Validate page flags: if flags != TL_PAGE_FULLY_LIVE, return TL_EINTERNAL
         (V1/B4 only produces FULLY_LIVE pages; other states = corruption)
       - Compute row_start = tl_page_lower_bound(page, t1)
       - Compute row_end = tl_page_lower_bound(page, t2)
       - If row_start < row_end:
         * Build view (incref owner)
         * Return TL_OK
    d. Exhaust segment -> current_seg = NULL, continue loop

 5.3 init_segment_cursor (Canonical Algorithm from tl_segment_iter_init)

 static bool init_segment_cursor(tl_pagespan_iter_t* it, const tl_segment_t* seg) {
     if (!seg || seg->page_count == 0) return false;
     if (!tl_range_overlaps(seg->min_ts, seg->max_ts, it->t1, it->t2, false))
         return false;

     const tl_page_catalog_t* cat = tl_segment_catalog(seg);
     size_t first = tl_page_catalog_find_first_ge(cat, it->t1);
     size_t last = tl_page_catalog_find_start_ge(cat, it->t2);

     if (first >= last) return false;

     it->current_seg = seg;
     it->page_idx = (uint32_t)first;
     it->page_end = (uint32_t)last;
     return true;
 }

 ---
 6. Owner Lifecycle

 Reference Counting Rules
 ┌─────────────────────────┬───────────────────────────┐
 │          Event          │      Refcount Change      │
 ├─────────────────────────┼───────────────────────────┤
 │ iter_open creates owner │ refcnt = 1                │
 ├─────────────────────────┼───────────────────────────┤
 │ iter_next returns TL_OK │ refcnt++ (view holds ref) │
 ├─────────────────────────┼───────────────────────────┤
 │ iter_close              │ refcnt--                  │
 ├─────────────────────────┼───────────────────────────┤
 │ view_release            │ refcnt--                  │
 ├─────────────────────────┼───────────────────────────┤
 │ refcnt -> 0             │ destroy owner             │
 └─────────────────────────┴───────────────────────────┘
 Destruction Order (CRITICAL)

 static void owner_destroy(tl_pagespan_owner_t* owner) {
     tl_snapshot_t* snap = owner->snapshot;
     tl_alloc_ctx_t* alloc = owner->alloc;
     tl_pagespan_owner_hooks_t hooks = owner->hooks;

     // 1. Release snapshot (no binding code)
     if (snap) tl_snapshot_release(snap);

     // 2. Free owner struct BEFORE calling hook
     tl__free(alloc, owner);

     // 3. Call release hook (may run Python code via binding)
     if (hooks.on_release) {
         hooks.on_release(hooks.user);
     }
 }

 Rationale: Free owner before hook because hook may Py_DECREF timelog, which owns the allocator. Must not use allocator after timelog refcount drops.

 ---
 7. TDD Test Plan

 Phase 1: Validation Tests (5 tests)

 - pagespan_flags_default_value - DEFAULT = correct combination
 - pagespan_iter_open_null_timelog_returns_einval
 - pagespan_iter_open_null_out_returns_einval
 - pagespan_iter_open_visible_only_returns_einval
 - pagespan_iter_open_without_segments_only_returns_einval

 Phase 2: Empty Cases (2 tests)

 - pagespan_empty_timelog_returns_eof
 - pagespan_empty_range_returns_eof (t1 >= t2)

 Phase 3: Single Page (2 tests)

 - pagespan_single_page_full_range
 - pagespan_single_page_partial_range

 Phase 4: Multi-Page/Segment (2 tests)

 - pagespan_multiple_pages_single_segment
 - pagespan_l1_and_l0_segments

 Phase 5: Range Filtering (2 tests)

 - pagespan_range_excludes_earlier_segments
 - pagespan_range_no_overlap_returns_eof

 Phase 6: Owner Refcounting (2 tests)

 - pagespan_owner_refcount_incremented_per_view
 - pagespan_views_valid_after_iter_close

 Phase 7: Release Hooks (2 tests)

 - pagespan_release_hook_called_on_owner_destruction
 - pagespan_release_hook_null_is_safe

 Phase 8: Stress (1 test)

 - pagespan_stress_many_segments (100 segments)

 Total: 18 core API tests

 ---
 8. Binding Refactor

 8.1 Changes to py_span_iter.c

 DELETE:
 - collect_spans() function (~75 lines)
 - process_segment_catalog() function (~50 lines)
 - span_desc_t* spans array in PyPageSpanIter

 ADD:
 - tl_pagespan_iter_t* core_iter field
 - Call tl_pagespan_iter_open() in factory
 - Call tl_pagespan_iter_next() in tp_iternext

 8.2 Release Hook Implementation

 typedef struct {
     PyObject* timelog;
     tl_py_handle_ctx_t* handle_ctx;
 } tl_py_iter_context_t;

 static void py_pagespan_release_hook(void* user) {
     tl_py_iter_context_t* ctx = user;
     // Called with GIL held
     tl_py_pins_exit_and_maybe_drain(ctx->handle_ctx);
     Py_DECREF(ctx->timelog);
     PyMem_Free(ctx);
 }

 8.3 Pin Protocol Preservation

 // In PyPageSpanIter_Create:
 tl_py_pins_enter(&tl_obj->handle_ctx);  // BEFORE iter_open
 // ... open iterator with hooks ...
 // pins_exit called by hook when owner destroyed

 ---
 9. CMakeLists.txt Changes

 # Add to src/query sources in root CMakeLists.txt
 set(TIMELOG_QUERY_SOURCES
     src/query/tl_snapshot.c
     src/query/tl_segment_iter.c
     src/query/tl_pagespan_iter.c    # NEW
     # ...
 )

 # Add test
 add_executable(test_pagespan_iter tests/test_pagespan_iter.c)
 target_link_libraries(test_pagespan_iter PRIVATE timelog)
 add_test(NAME pagespan_iter_tests COMMAND test_pagespan_iter)

 ---
 10. Critical Invariants
 ┌─────┬─────────────────────────────────────┬─────────────────────────────────┐
 │ ID  │              Invariant              │           Enforcement           │
 ├─────┼─────────────────────────────────────┼─────────────────────────────────┤
 │ I1  │ Owner holds snapshot until refcnt=0 │ Single destroy routine          │
 ├─────┼─────────────────────────────────────┼─────────────────────────────────┤
 │ I2  │ Views valid after iter_close        │ Each view holds owner ref       │
 ├─────┼─────────────────────────────────────┼─────────────────────────────────┤
 │ I3  │ No Python in core                   │ Hooks are opaque void* + fn ptr │
 ├─────┼─────────────────────────────────────┼─────────────────────────────────┤
 │ I4  │ Streaming (no pre-alloc)            │ Iterator struct is fixed size   │
 ├─────┼─────────────────────────────────────┼─────────────────────────────────┤
 │ I5  │ B4 flag requirements                │ EINVAL for unsupported flags    │
 ├─────┼─────────────────────────────────────┼─────────────────────────────────┤
 │ I6  │ Half-open [t1, t2)                  │ t1 inclusive, t2 exclusive      │
 ├─────┼─────────────────────────────────────┼─────────────────────────────────┤
 │ I7  │ Only FULLY_LIVE pages               │ Skip other page flags           │
 ├─────┼─────────────────────────────────────┼─────────────────────────────────┤
 │ I8  │ L1 before L0 ordering               │ Phase state machine             │
 ├─────┼─────────────────────────────────────┼─────────────────────────────────┤
 │ I9  │ Binary search for pages             │ Use catalog find functions      │
 ├─────┼─────────────────────────────────────┼─────────────────────────────────┤
 │ I10 │ Free owner before hook              │ Allocator lifetime              │
 └─────┴─────────────────────────────────────┴─────────────────────────────────┘
 ---
 11. Verification Checklist

 Core Implementation

 - Compiles with -Wall -Wextra -Werror
 - No internal headers in public header
 - ASan clean (no leaks)
 - TSan clean (no races)
 - All 18 tests pass

 B4 Behavior Preservation

 - Empty timelog -> TL_EOF
 - Empty range -> TL_EOF
 - Only TL_PAGE_FULLY_LIVE
 - L1 then L0 order
 - Binary search (O(log n))

 Binding Migration

 - All test_py_span.c tests pass (36 tests)
 - Same spans, same order
 - Buffer protocol works
 - Context manager works
 - pins_exit called once

 ---
 12. Critical Files Reference
 ┌──────────────────────────────────────────────────────┬─────────┬───────────────────────────────────┐
 │                         File                         │  Lines  │             Relevance             │
 ├──────────────────────────────────────────────────────┼─────────┼───────────────────────────────────┤
 │ src/query/tl_segment_iter.c                          │ 74-137  │ Canonical range pruning algorithm │
 ├──────────────────────────────────────────────────────┼─────────┼───────────────────────────────────┤
 │ src/storage/tl_page.c                                │ 418-469 │ Catalog binary search functions   │
 ├──────────────────────────────────────────────────────┼─────────┼───────────────────────────────────┤
 │ src/storage/tl_page.h                                │ 70-88   │ Page structure (ts[], h[], flags) │
 ├──────────────────────────────────────────────────────┼─────────┼───────────────────────────────────┤
 │ bindings/cpython/src/py_span_iter.c                  │ 161-289 │ Code to be replaced               │
 ├──────────────────────────────────────────────────────┼─────────┼───────────────────────────────────┤
 │ docs/timelog_v2_lld_pagespan_core_api_unification.md │ Full    │ Specification                     │
 └──────────────────────────────────────────────────────┴─────────┴───────────────────────────────────┘
 ---
 13. Implementation Order

 1. Create header - tl_pagespan_iter.h with types and signatures
 2. Create test stubs - All 18 tests as failing stubs
 3. Implement owner - refcount, destroy with hooks
 4. Implement iter_open - validation, snapshot, owner creation
 5. Implement iter_next - streaming algorithm
 6. Implement iter_close - cleanup
 7. Run tests - All core tests pass
 8. Refactor binding - Replace py_span_iter.c internals
 9. Run binding tests - All B4 tests pass
 10. Sanitizer runs - ASan, TSan clean

 ---
 14. Risk Mitigations
 ┌─────────────────────┬─────────────────────────────────────────┐
 │        Risk         │               Mitigation                │
 ├─────────────────────┼─────────────────────────────────────────┤
 │ UAF in page pointer │ Owner holds snapshot ref                │
 ├─────────────────────┼─────────────────────────────────────────┤
 │ Allocator lifetime  │ Free owner before hook callback         │
 ├─────────────────────┼─────────────────────────────────────────┤
 │ Hook re-entrancy    │ Hook called after core cleanup complete │
 ├─────────────────────┼─────────────────────────────────────────┤
 │ Binding regression  │ All 36 B4 tests must pass unchanged     │
 ├─────────────────────┼─────────────────────────────────────────┤
 │ Memory leak         │ TDD + ASan verification                 │
 └─────────────────────┴─────────────────────────────────────────┘
 ---
 Status

 Ready for implementation - Plan reviewed and approved.

 Prerequisites completed:
 - B4 binding implementation complete (36 tests passing)
 - LLD reviewed and updated with feedback
 - Current binding code analyzed for refactor scope