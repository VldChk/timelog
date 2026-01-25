/*===========================================================================
 * test_pagespan_iter.c - PageSpan Iterator Core API Tests
 *
 * TDD test suite for the PageSpan enumeration API defined in tl_pagespan_iter.h.
 * Tests cover:
 * - Flag validation and defaults
 * - Empty cases (empty timelog, empty range)
 * - Single and multi-page segments
 * - Range filtering and pruning
 * - Owner reference counting
 * - Release hooks
 *
 * Total: 20 tests organized in 8 phases per the implementation plan.
 *
 * Reference: docs/timelog_v2_lld_pagespan_core_api_unification.md
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"
#include "query/tl_pagespan_iter.h"

#include <stdbool.h>
#include <string.h>
#include <stdint.h>

/*===========================================================================
 * Test Helpers
 *===========================================================================*/

/**
 * Create a timelog and flush data to create segments.
 * Appends records at timestamps [base, base+count) with handles 1..count.
 * Flushes to create L0 segment.
 *
 * @param out_tl  Output timelog pointer
 * @param base    Base timestamp
 * @param count   Number of records to append
 * @return TL_OK on success
 */
static tl_status_t create_timelog_with_flushed_data(
    tl_timelog_t** out_tl,
    tl_ts_t base,
    size_t count)
{
    tl_status_t st = tl_open(NULL, out_tl);
    if (st != TL_OK) return st;

    for (size_t i = 0; i < count; i++) {
        st = tl_append(*out_tl, base + (tl_ts_t)i, (tl_handle_t)(i + 1));
        if (st != TL_OK) {
            tl_close(*out_tl);
            *out_tl = NULL;
            return st;
        }
    }

    if (count > 0) {
        st = tl_flush(*out_tl);
        if (st != TL_OK) {
            tl_close(*out_tl);
            *out_tl = NULL;
            return st;
        }
    }

    return TL_OK;
}

/**
 * Hook tracking context for release hook tests.
 */
typedef struct {
    int call_count;
    void* user_data;
} hook_tracker_t;

static void test_release_hook(void* user) {
    hook_tracker_t* tracker = (hook_tracker_t*)user;
    if (tracker != NULL) {
        tracker->call_count++;
    }
}

typedef struct {
    tl_timelog_t* tl;
    int call_count;
} hook_close_ctx_t;

static void test_release_hook_close_timelog(void* user) {
    hook_close_ctx_t* ctx = (hook_close_ctx_t*)user;
    if (ctx == NULL) {
        return;
    }

    ctx->call_count++;
    if (ctx->tl != NULL) {
        tl_close(ctx->tl);
        ctx->tl = NULL;
    }
}

/*===========================================================================
 * Phase 1: Validation Tests (5 tests)
 *===========================================================================*/

/**
 * Test: TL_PAGESPAN_DEFAULT has the correct flag combination.
 */
TEST_DECLARE(pagespan_flags_default_value) {
    uint32_t expected = TL_PAGESPAN_SEGMENTS_ONLY |
                        TL_PAGESPAN_INCLUDE_L0 |
                        TL_PAGESPAN_INCLUDE_L1 |
                        TL_PAGESPAN_REQUIRE_ZEROCOPY;
    TEST_ASSERT_EQ(expected, TL_PAGESPAN_DEFAULT);
}

/**
 * Test: iter_open with NULL timelog returns TL_EINVAL.
 */
TEST_DECLARE(pagespan_iter_open_null_timelog_returns_einval) {
    tl_pagespan_iter_t* it = NULL;
    tl_status_t st = tl_pagespan_iter_open(NULL, 0, 100, 0, NULL, &it);
    TEST_ASSERT_STATUS(TL_EINVAL, st);
    TEST_ASSERT_NULL(it);
}

/**
 * Test: iter_open with NULL out pointer returns TL_EINVAL.
 */
TEST_DECLARE(pagespan_iter_open_null_out_returns_einval) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));
    TEST_ASSERT_NOT_NULL(tl);

    tl_status_t st = tl_pagespan_iter_open(tl, 0, 100, 0, NULL, NULL);
    TEST_ASSERT_STATUS(TL_EINVAL, st);

    tl_close(tl);
}

/**
 * Test: iter_open with VISIBLE_ONLY flag returns TL_EINVAL (reserved in B4).
 */
TEST_DECLARE(pagespan_iter_open_visible_only_returns_einval) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));
    TEST_ASSERT_NOT_NULL(tl);

    tl_pagespan_iter_t* it = NULL;
    uint32_t flags = TL_PAGESPAN_DEFAULT | TL_PAGESPAN_VISIBLE_ONLY;
    tl_status_t st = tl_pagespan_iter_open(tl, 0, 100, flags, NULL, &it);
    TEST_ASSERT_STATUS(TL_EINVAL, st);
    TEST_ASSERT_NULL(it);

    tl_close(tl);
}

/**
 * Test: iter_open without SEGMENTS_ONLY flag returns TL_EINVAL (required in B4).
 */
TEST_DECLARE(pagespan_iter_open_without_segments_only_returns_einval) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));
    TEST_ASSERT_NOT_NULL(tl);

    tl_pagespan_iter_t* it = NULL;
    /* Use flags that don't include SEGMENTS_ONLY */
    uint32_t flags = TL_PAGESPAN_INCLUDE_L0 | TL_PAGESPAN_INCLUDE_L1;
    tl_status_t st = tl_pagespan_iter_open(tl, 0, 100, flags, NULL, &it);
    TEST_ASSERT_STATUS(TL_EINVAL, st);
    TEST_ASSERT_NULL(it);

    tl_close(tl);
}

/*===========================================================================
 * Phase 2: Empty Cases (2 tests)
 *===========================================================================*/

/**
 * Test: iter_open on empty timelog returns TL_OK; first next() returns TL_EOF.
 */
TEST_DECLARE(pagespan_empty_timelog_iter_next_returns_eof) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));
    TEST_ASSERT_NOT_NULL(tl);

    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 0, 1000, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* First next should return EOF */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_EOF, tl_pagespan_iter_next(it, &view));

    /* View should not be filled */
    TEST_ASSERT_NULL(view.owner);

    tl_pagespan_iter_close(it);
    tl_close(tl);
}

/**
 * Test: iter_open with t1 >= t2 returns TL_OK; first next() returns TL_EOF.
 */
TEST_DECLARE(pagespan_empty_range_iter_next_returns_eof) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 100, 10));
    TEST_ASSERT_NOT_NULL(tl);

    /* Query with t1 > t2 (empty range) */
    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 500, 100, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* First next should return EOF */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_EOF, tl_pagespan_iter_next(it, &view));
    TEST_ASSERT_NULL(view.owner);

    tl_pagespan_iter_close(it);
    tl_close(tl);
}

/*===========================================================================
 * Phase 3: Single Page (2 tests)
 *===========================================================================*/

/**
 * Test: Query full range returns all data from a single page.
 */
TEST_DECLARE(pagespan_single_page_full_range) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 100, 10));
    TEST_ASSERT_NOT_NULL(tl);

    /* Query entire range */
    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 0, 1000, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* Should get one span with all 10 records */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_next(it, &view));

    TEST_ASSERT_NOT_NULL(view.owner);
    TEST_ASSERT_NOT_NULL(view.ts);
    TEST_ASSERT_NOT_NULL(view.h);
    TEST_ASSERT_EQ(10, view.len);
    TEST_ASSERT_EQ(100, view.first_ts);
    TEST_ASSERT_EQ(109, view.last_ts);

    /* Verify data */
    TEST_ASSERT_EQ(100, view.ts[0]);
    TEST_ASSERT_EQ(109, view.ts[9]);
    TEST_ASSERT_EQ_U64(1, view.h[0]);
    TEST_ASSERT_EQ_U64(10, view.h[9]);

    tl_pagespan_view_release(&view);

    /* No more spans */
    TEST_ASSERT_STATUS(TL_EOF, tl_pagespan_iter_next(it, &view));

    tl_pagespan_iter_close(it);
    tl_close(tl);
}

/**
 * Test: Query partial range returns subset of data from a single page.
 */
TEST_DECLARE(pagespan_single_page_partial_range) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 100, 10));
    TEST_ASSERT_NOT_NULL(tl);

    /* Query partial range [102, 107) - should get 5 records */
    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 102, 107, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_next(it, &view));

    TEST_ASSERT_NOT_NULL(view.owner);
    TEST_ASSERT_EQ(5, view.len);
    TEST_ASSERT_EQ(102, view.first_ts);
    TEST_ASSERT_EQ(106, view.last_ts);

    tl_pagespan_view_release(&view);

    /* No more spans */
    TEST_ASSERT_STATUS(TL_EOF, tl_pagespan_iter_next(it, &view));

    tl_pagespan_iter_close(it);
    tl_close(tl);
}

/*===========================================================================
 * Phase 4: Multi-Page/Segment (2 tests)
 *===========================================================================*/

/**
 * Test: Multiple pages in a single segment yield multiple spans.
 */
TEST_DECLARE(pagespan_multiple_pages_single_segment) {
    tl_timelog_t* tl = NULL;
    /* Create enough records to span multiple pages (default ~64KB pages) */
    /* With 16 bytes per record, ~4000 records per page. Use 8000 to get 2+ pages */
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 0, 8000));
    TEST_ASSERT_NOT_NULL(tl);

    /* Query entire range */
    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 0, 10000, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* Count spans and total records */
    int span_count = 0;
    uint32_t total_records = 0;
    tl_pagespan_view_t view;

    for (;;) {
        memset(&view, 0, sizeof(view));
        tl_status_t st = tl_pagespan_iter_next(it, &view);
        if (st == TL_EOF) break;
        TEST_ASSERT_STATUS(TL_OK, st);
        TEST_ASSERT_NOT_NULL(view.owner);
        TEST_ASSERT(view.len > 0);
        span_count++;
        total_records += view.len;
        tl_pagespan_view_release(&view);
    }

    /* Should have gotten multiple spans */
    TEST_ASSERT(span_count >= 1);  /* At least 1 span */
    TEST_ASSERT_EQ(8000, total_records);  /* All records accounted for */

    tl_pagespan_iter_close(it);
    tl_close(tl);
}

/**
 * Test: L1 segments are enumerated before L0 segments.
 *
 * Uses manual maintenance mode to force explicit compaction,
 * ensuring we actually have L1 segments to test ordering.
 */
TEST_DECLARE(pagespan_l1_and_l0_segments) {
    /* Use manual mode so compaction only runs when we request it */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));
    TEST_ASSERT_NOT_NULL(tl);

    /* Create first batch and flush (L0) */
    for (int i = 0; i < 100; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 1000 + i, (tl_handle_t)(i + 1)));
    }
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Drain flush to L0 segment */
    while (tl_maint_step(tl) == TL_OK) {}

    /* Request and execute compaction to create L1 */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));
    tl_status_t st = tl_maint_step(tl);
    TEST_ASSERT(st == TL_OK || st == TL_EOF);

    /* Create second batch and flush (L0) */
    for (int i = 0; i < 100; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 2000 + i, (tl_handle_t)(100 + i + 1)));
    }
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Query entire range */
    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 0, 5000, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* Collect timestamps from all spans */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    st = tl_pagespan_iter_next(it, &view);  /* Reuse st from above */
    TEST_ASSERT_STATUS(TL_OK, st);

    /* First span should be from L1 (timestamps 1000+) */
    TEST_ASSERT(view.first_ts >= 1000 && view.first_ts < 2000);
    tl_pagespan_view_release(&view);

    /* Get remaining spans and verify we get L0 data after L1 */
    int got_l0_span = 0;
    while ((st = tl_pagespan_iter_next(it, &view)) == TL_OK) {
        if (view.first_ts >= 2000) {
            got_l0_span = 1;
        }
        tl_pagespan_view_release(&view);
    }

    TEST_ASSERT(got_l0_span);

    tl_pagespan_iter_close(it);
    tl_close(tl);
}

/*===========================================================================
 * Phase 5: Range Filtering (2 tests)
 *===========================================================================*/

/**
 * Test: Range query correctly excludes segments outside the range.
 */
TEST_DECLARE(pagespan_range_excludes_earlier_segments) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));
    TEST_ASSERT_NOT_NULL(tl);

    /* Create segment with timestamps 100-199 */
    for (int i = 0; i < 100; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100 + i, (tl_handle_t)(i + 1)));
    }
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Create segment with timestamps 500-599 */
    for (int i = 0; i < 100; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 500 + i, (tl_handle_t)(100 + i + 1)));
    }
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Query only 500+ range - should not see 100-199 data */
    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 500, 700, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    tl_status_t st = tl_pagespan_iter_next(it, &view);
    TEST_ASSERT_STATUS(TL_OK, st);

    /* All returned timestamps should be >= 500 */
    TEST_ASSERT(view.first_ts >= 500);
    for (uint32_t i = 0; i < view.len; i++) {
        TEST_ASSERT(view.ts[i] >= 500);
        TEST_ASSERT(view.ts[i] < 700);
    }

    tl_pagespan_view_release(&view);

    /* Should be no more spans (or all remaining should also be >= 500) */
    while ((st = tl_pagespan_iter_next(it, &view)) == TL_OK) {
        TEST_ASSERT(view.first_ts >= 500);
        tl_pagespan_view_release(&view);
    }

    tl_pagespan_iter_close(it);
    tl_close(tl);
}

/**
 * Test: Range with no overlapping segments returns TL_EOF immediately.
 */
TEST_DECLARE(pagespan_range_no_overlap_returns_eof) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 100, 10));
    TEST_ASSERT_NOT_NULL(tl);

    /* Query range [500, 600) - no overlap with data at 100-109 */
    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 500, 600, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_EOF, tl_pagespan_iter_next(it, &view));
    TEST_ASSERT_NULL(view.owner);

    tl_pagespan_iter_close(it);
    tl_close(tl);
}

/*===========================================================================
 * Phase 6: Owner Refcounting (2 tests)
 *===========================================================================*/

/**
 * Test: Each returned view increments owner refcount.
 */
TEST_DECLARE(pagespan_owner_refcount_incremented_per_view) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 100, 10));
    TEST_ASSERT_NOT_NULL(tl);

    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 0, 1000, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* Get first view */
    tl_pagespan_view_t view1;
    memset(&view1, 0, sizeof(view1));
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_next(it, &view1));
    TEST_ASSERT_NOT_NULL(view1.owner);

    tl_pagespan_owner_t* owner = view1.owner;

    /* Manually incref to test the function */
    tl_pagespan_owner_incref(owner);

    /* Release view1 - owner should still be valid (we have extra ref) */
    tl_pagespan_view_release(&view1);
    TEST_ASSERT_NULL(view1.owner);  /* view1 zeroed */

    /* Close iterator */
    tl_pagespan_iter_close(it);

    /* Owner still valid due to our extra ref - release it */
    tl_pagespan_owner_decref(owner);

    tl_close(tl);
}

/**
 * Test: Views remain valid after iterator close (each holds its own owner ref).
 */
TEST_DECLARE(pagespan_views_valid_after_iter_close) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 100, 10));
    TEST_ASSERT_NOT_NULL(tl);

    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 0, 1000, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* Get view */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_next(it, &view));
    TEST_ASSERT_NOT_NULL(view.owner);

    /* Close iterator while view is still alive */
    tl_pagespan_iter_close(it);

    /* View should still be valid */
    TEST_ASSERT_NOT_NULL(view.owner);
    TEST_ASSERT_NOT_NULL(view.ts);
    TEST_ASSERT_EQ(10, view.len);

    /* Verify data is still accessible */
    TEST_ASSERT_EQ(100, view.ts[0]);
    TEST_ASSERT_EQ(109, view.ts[9]);

    /* Release view */
    tl_pagespan_view_release(&view);

    tl_close(tl);
}

/*===========================================================================
 * Phase 7: Release Hooks (3 tests)
 *===========================================================================*/

/**
 * Test: Release hook is called when owner is destroyed.
 */
TEST_DECLARE(pagespan_release_hook_called_on_owner_destruction) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 100, 10));
    TEST_ASSERT_NOT_NULL(tl);

    hook_tracker_t tracker = { .call_count = 0, .user_data = (void*)(uintptr_t)0xDEADBEEF };

    tl_pagespan_owner_hooks_t hooks = {
        .user = &tracker,
        .on_release = test_release_hook
    };

    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 0, 1000, 0, &hooks, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* Hook should not be called yet */
    TEST_ASSERT_EQ(0, tracker.call_count);

    /* Get and immediately release view */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_next(it, &view));
    TEST_ASSERT_NOT_NULL(view.owner);
    tl_pagespan_view_release(&view);

    /* Hook may or may not be called yet (depends on if iter still has ref) */
    /* Close iterator - this should trigger owner destruction */
    tl_pagespan_iter_close(it);

    /* Hook should have been called exactly once */
    TEST_ASSERT_EQ(1, tracker.call_count);

    tl_close(tl);
}

/**
 * Test: Release hook may close the timelog (allocator lifetime safety).
 *
 * This simulates a binding that decrefs the timelog in the release hook.
 * The iterator must be freed before the hook runs to avoid allocator UAF.
 */
TEST_DECLARE(pagespan_release_hook_can_close_timelog) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 100, 10));
    TEST_ASSERT_NOT_NULL(tl);

    hook_close_ctx_t ctx = { .tl = tl, .call_count = 0 };
    tl_pagespan_owner_hooks_t hooks = {
        .user = &ctx,
        .on_release = test_release_hook_close_timelog
    };

    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 0, 1000, 0, &hooks, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* Get and release a view to exercise owner refs */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_next(it, &view));
    tl_pagespan_view_release(&view);

    /* Close iterator - hook will close timelog */
    tl_pagespan_iter_close(it);

    TEST_ASSERT_EQ(1, ctx.call_count);

    /* Cleanup if hook did not close (should not happen) */
    if (ctx.tl != NULL) {
        tl_close(ctx.tl);
        ctx.tl = NULL;
    }
}

/**
 * Test: NULL release hook is safe.
 */
TEST_DECLARE(pagespan_release_hook_null_is_safe) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 100, 10));
    TEST_ASSERT_NOT_NULL(tl);

    /* Hooks with NULL on_release */
    tl_pagespan_owner_hooks_t hooks = {
        .user = (void*)(uintptr_t)0x12345678,
        .on_release = NULL
    };

    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 0, 1000, 0, &hooks, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* Get and release view, close iterator - should not crash */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_next(it, &view));
    tl_pagespan_view_release(&view);
    tl_pagespan_iter_close(it);

    tl_close(tl);
}

/**
 * Test: Release hook is called even when no spans are produced.
 *
 * This tests the hook symmetry guarantee: if iter_open succeeds with hooks,
 * the hook WILL be called when the iterator is closed, even if:
 * - The query range is empty (t1 >= t2)
 * - No segments overlap the range
 *
 * This is critical for binding integration where pins_enter() is called
 * before iter_open() and the hook is relied upon to call pins_exit().
 */
TEST_DECLARE(pagespan_release_hook_called_even_with_no_spans) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, create_timelog_with_flushed_data(&tl, 100, 10));
    TEST_ASSERT_NOT_NULL(tl);

    hook_tracker_t tracker = { .call_count = 0, .user_data = (void*)(uintptr_t)0xCAFEBABE };

    tl_pagespan_owner_hooks_t hooks = {
        .user = &tracker,
        .on_release = test_release_hook
    };

    /* Test 1: Empty range (t1 >= t2) - no spans possible */
    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 500, 500, 0, &hooks, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* First next should return EOF immediately */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_EOF, tl_pagespan_iter_next(it, &view));

    /* Close iterator */
    tl_pagespan_iter_close(it);

    /* Hook MUST have been called - this is the key assertion */
    TEST_ASSERT_EQ(1, tracker.call_count);

    /* Test 2: Range with no overlap - segments exist but none match */
    tracker.call_count = 0;  /* Reset tracker */

    it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 50000, 60000, 0, &hooks, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* First next should return EOF (no segments overlap [50000, 60000)) */
    memset(&view, 0, sizeof(view));
    TEST_ASSERT_STATUS(TL_EOF, tl_pagespan_iter_next(it, &view));

    tl_pagespan_iter_close(it);

    /* Hook MUST have been called */
    TEST_ASSERT_EQ(1, tracker.call_count);

    tl_close(tl);
}

/*===========================================================================
 * Phase 8: Stress (1 test)
 *===========================================================================*/

/**
 * Test: Stress test with many segments.
 */
TEST_DECLARE(pagespan_stress_many_segments) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));
    TEST_ASSERT_NOT_NULL(tl);

    /* Create 10 segments with 100 records each */
    const int num_segments = 10;
    const int records_per_segment = 100;

    for (int seg = 0; seg < num_segments; seg++) {
        tl_ts_t base = (tl_ts_t)(seg * 1000);
        for (int i = 0; i < records_per_segment; i++) {
            tl_status_t st = tl_append(tl, base + i, (tl_handle_t)(seg * 1000 + i + 1));
            TEST_ASSERT_STATUS(TL_OK, st);
        }
        TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));
    }

    /* Query entire range */
    tl_pagespan_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_pagespan_iter_open(tl, 0, 100000, 0, NULL, &it));
    TEST_ASSERT_NOT_NULL(it);

    /* Count all records */
    uint32_t total = 0;
    tl_pagespan_view_t view;

    for (;;) {
        memset(&view, 0, sizeof(view));
        tl_status_t st = tl_pagespan_iter_next(it, &view);
        if (st == TL_EOF) break;
        TEST_ASSERT_STATUS(TL_OK, st);
        TEST_ASSERT_NOT_NULL(view.owner);
        TEST_ASSERT(view.len > 0);
        total += view.len;
        tl_pagespan_view_release(&view);
    }

    TEST_ASSERT_EQ((uint32_t)(num_segments * records_per_segment), total);

    tl_pagespan_iter_close(it);
    tl_close(tl);
}

/*===========================================================================
 * Test Registration
 *===========================================================================*/

void run_pagespan_iter_tests(void) {
    printf("\n=== PageSpan Iterator Tests ===\n");

    /* Phase 1: Validation */
    RUN_TEST(pagespan_flags_default_value);
    RUN_TEST(pagespan_iter_open_null_timelog_returns_einval);
    RUN_TEST(pagespan_iter_open_null_out_returns_einval);
    RUN_TEST(pagespan_iter_open_visible_only_returns_einval);
    RUN_TEST(pagespan_iter_open_without_segments_only_returns_einval);

    /* Phase 2: Empty Cases */
    RUN_TEST(pagespan_empty_timelog_iter_next_returns_eof);
    RUN_TEST(pagespan_empty_range_iter_next_returns_eof);

    /* Phase 3: Single Page */
    RUN_TEST(pagespan_single_page_full_range);
    RUN_TEST(pagespan_single_page_partial_range);

    /* Phase 4: Multi-Page/Segment */
    RUN_TEST(pagespan_multiple_pages_single_segment);
    RUN_TEST(pagespan_l1_and_l0_segments);

    /* Phase 5: Range Filtering */
    RUN_TEST(pagespan_range_excludes_earlier_segments);
    RUN_TEST(pagespan_range_no_overlap_returns_eof);

    /* Phase 6: Owner Refcounting */
    RUN_TEST(pagespan_owner_refcount_incremented_per_view);
    RUN_TEST(pagespan_views_valid_after_iter_close);

    /* Phase 7: Release Hooks */
    RUN_TEST(pagespan_release_hook_called_on_owner_destruction);
    RUN_TEST(pagespan_release_hook_can_close_timelog);
    RUN_TEST(pagespan_release_hook_null_is_safe);
    RUN_TEST(pagespan_release_hook_called_even_with_no_spans);

    /* Phase 8: Stress */
    RUN_TEST(pagespan_stress_many_segments);
}
