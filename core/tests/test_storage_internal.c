/*===========================================================================
 * test_storage_internal.c - Storage Layer Internal Tests
 *
 * These tests verify LLD-level invariants and internal API behavior for
 * the storage layer: windows, pages, catalogs, segments, and manifests.
 *
 * CLASSIFICATION: Internal (LLD-Driven)
 * These are IMPLEMENTATION tests, not SPEC tests.
 *
 * If these tests fail, the cause could be:
 * 1. A bug in the implementation (likely)
 * 2. An intentional internal refactor (update test accordingly)
 *
 * These tests do NOT verify public API contracts - see test_functional.c.
 *
 * Part of Phase 10: Test Suite Reorganization
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"

/* Internal headers - NOT public API */
#include "internal/tl_alloc.h"
#include "internal/tl_intervals.h"
#include "tl_window.h"
#include "tl_page.h"
#include "tl_segment.h"
#include "tl_manifest.h"

#include <string.h>
#include <stdint.h>

static tl_status_t test_segment_build_l0(tl_alloc_ctx_t* alloc,
                                          const tl_record_t* records,
                                          size_t record_count,
                                          const tl_interval_t* tombstones,
                                          size_t tombstones_len,
                                          size_t target_page_bytes,
                                          uint32_t generation,
                                          tl_segment_t** out) {
    tl_seq_t applied_seq = (generation == 0) ? 1 : (tl_seq_t)generation;
    return tl_segment_build_l0(alloc, records, record_count,
                               tombstones, tombstones_len,
                               target_page_bytes, generation, applied_seq, out);
}

static tl_status_t test_segment_build_l1(tl_alloc_ctx_t* alloc,
                                          const tl_record_t* records,
                                          size_t record_count,
                                          size_t target_page_bytes,
                                          tl_ts_t window_start,
                                          tl_ts_t window_end,
                                          bool window_end_unbounded,
                                          uint32_t generation,
                                          tl_segment_t** out) {
    tl_seq_t applied_seq = (generation == 0) ? 1 : (tl_seq_t)generation;
    return tl_segment_build_l1(alloc, records, record_count,
                               target_page_bytes, window_start, window_end,
                               window_end_unbounded, generation, applied_seq, out);
}

#define tl_segment_build_l0 test_segment_build_l0
#define tl_segment_build_l1 test_segment_build_l1

/*===========================================================================
 * Window Mapping Tests (Internal API)
 *
 * These test the internal window ID calculation and bounds functions.
 * Window mapping is an implementation detail of how timestamps are
 * partitioned into L1 segments.
 *===========================================================================*/

TEST_DECLARE(storage_window_default_size) {
    TEST_ASSERT_EQ(TL_WINDOW_1H_S, tl_window_default_size(TL_TIME_S));
    TEST_ASSERT_EQ(TL_WINDOW_1H_MS, tl_window_default_size(TL_TIME_MS));
    TEST_ASSERT_EQ(TL_WINDOW_1H_US, tl_window_default_size(TL_TIME_US));
    TEST_ASSERT_EQ(TL_WINDOW_1H_NS, tl_window_default_size(TL_TIME_NS));
}

/* M-06 fix test: Unknown enum returns safe default */
TEST_DECLARE(storage_window_default_size_unknown_enum) {
    /* Invalid enum value should return safe default (1 hour in seconds) */
    TEST_ASSERT_EQ(TL_WINDOW_1H_S, tl_window_default_size((tl_time_unit_t)99));
    TEST_ASSERT_EQ(TL_WINDOW_1H_S, tl_window_default_size((tl_time_unit_t)-1));
}

TEST_DECLARE(storage_window_id_positive) {
    /* ts = 25, size = 10, origin = 0 => window_id = 2 */
    int64_t id;
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(25, 10, 0, &id));
    TEST_ASSERT_EQ(2, id);
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(5, 10, 0, &id));
    TEST_ASSERT_EQ(0, id);
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(10, 10, 0, &id));
    TEST_ASSERT_EQ(1, id);
}

TEST_DECLARE(storage_window_id_negative) {
    /* Floor division is required for negative timestamps */
    /* ts = -1, size = 10, origin = 0 => floor(-1/10) = -1 */
    int64_t id;
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(-1, 10, 0, &id));
    TEST_ASSERT_EQ(-1, id);
}

TEST_DECLARE(storage_window_id_negative_exact) {
    /* ts = -10, size = 10, origin = 0 => floor(-10/10) = -1 */
    int64_t id;
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(-10, 10, 0, &id));
    TEST_ASSERT_EQ(-1, id);
}

TEST_DECLARE(storage_window_id_negative_past) {
    /* ts = -11, size = 10, origin = 0 => floor(-11/10) = -2 (C would give -1) */
    int64_t id;
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(-11, 10, 0, &id));
    TEST_ASSERT_EQ(-2, id);
}

TEST_DECLARE(storage_window_id_at_origin) {
    int64_t id;
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(0, 10, 0, &id));
    TEST_ASSERT_EQ(0, id);
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(100, 10, 100, &id));
    TEST_ASSERT_EQ(0, id);
}

TEST_DECLARE(storage_window_bounds_basic) {
    tl_ts_t start, end;
    bool unbounded;
    tl_window_bounds(2, 10, 0, &start, &end, &unbounded);
    TEST_ASSERT_EQ(20, start);
    TEST_ASSERT_EQ(30, end);
    TEST_ASSERT(!unbounded);
}

TEST_DECLARE(storage_window_bounds_negative_id) {
    tl_ts_t start, end;
    bool unbounded;
    tl_window_bounds(-1, 10, 0, &start, &end, &unbounded);
    TEST_ASSERT_EQ(-10, start);
    TEST_ASSERT_EQ(0, end);
    TEST_ASSERT(!unbounded);
}

TEST_DECLARE(storage_window_bounds_for_ts) {
    tl_ts_t start, end;
    bool unbounded;
    TEST_ASSERT_STATUS(TL_OK, tl_window_bounds_for_ts(25, 10, 0, &start, &end, &unbounded));
    TEST_ASSERT_EQ(20, start);
    TEST_ASSERT_EQ(30, end);
    TEST_ASSERT(!unbounded);
}

TEST_DECLARE(storage_window_contains) {
    TEST_ASSERT(tl_window_contains(20, 30, false, 20));
    TEST_ASSERT(tl_window_contains(20, 30, false, 25));
    TEST_ASSERT(!tl_window_contains(20, 30, false, 30)); /* Half-open: end is exclusive */
    TEST_ASSERT(!tl_window_contains(20, 30, false, 19));
}

TEST_DECLARE(storage_window_contains_unbounded) {
    /* Unbounded windows include everything >= start */
    TEST_ASSERT(tl_window_contains(20, TL_TS_MAX, true, 20));
    TEST_ASSERT(tl_window_contains(20, TL_TS_MAX, true, TL_TS_MAX));
    TEST_ASSERT(!tl_window_contains(20, TL_TS_MAX, true, 19));
}

TEST_DECLARE(storage_window_ts_max_unbounded) {
    /* Window containing TL_TS_MAX should be unbounded */
    tl_ts_t start, end;
    bool unbounded;
    /* Large window size that would overflow when added to start near TS_MAX */
    TEST_ASSERT_STATUS(TL_OK, tl_window_bounds_for_ts(TL_TS_MAX, 1000, 0, &start, &end, &unbounded));
    TEST_ASSERT(unbounded);
    TEST_ASSERT_EQ(TL_TS_MAX, end);
    /* The window should contain TL_TS_MAX */
    TEST_ASSERT(tl_window_contains(start, end, unbounded, TL_TS_MAX));
}

TEST_DECLARE(storage_window_id_overflow_underflow) {
    int64_t id;

    /* Case 1: ts = INT64_MAX, origin = INT64_MIN => overflow */
    TEST_ASSERT_STATUS(TL_EOVERFLOW, tl_window_id_for_ts(INT64_MAX, 1000, INT64_MIN, &id));

    /* Case 2: ts = INT64_MIN, origin = INT64_MAX => underflow */
    TEST_ASSERT_STATUS(TL_EOVERFLOW, tl_window_id_for_ts(INT64_MIN, 1000, INT64_MAX, &id));

    /* Valid edge case: ts = 0, origin = 0 => should work */
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(0, 1000, 0, &id));
    TEST_ASSERT_EQ(0, id);

    /* Valid edge case: large but valid subtraction */
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(INT64_MAX, 1000, 0, &id));
}

TEST_DECLARE(storage_window_bounds_for_ts_overflow) {
    tl_ts_t start, end;
    bool unbounded;

    /* Overflow in window_id computation */
    TEST_ASSERT_STATUS(TL_EOVERFLOW,
        tl_window_bounds_for_ts(INT64_MAX, 1000, INT64_MIN, &start, &end, &unbounded));
}

/* C-06 fix tests: window_size <= 0 should return TL_EINVAL or safe values */
TEST_DECLARE(storage_window_id_zero_size_invalid) {
    int64_t id;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_window_id_for_ts(100, 0, 0, &id));
}

TEST_DECLARE(storage_window_id_negative_size_invalid) {
    int64_t id;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_window_id_for_ts(100, -10, 0, &id));
}

TEST_DECLARE(storage_window_bounds_zero_size_degenerate) {
    tl_ts_t start, end;
    bool unbounded;

    /* window_size = 0 should return degenerate window [origin, origin) */
    tl_window_bounds(5, 0, 100, &start, &end, &unbounded);
    TEST_ASSERT_EQ(100, start);
    TEST_ASSERT_EQ(100, end);
    TEST_ASSERT(!unbounded);
}

TEST_DECLARE(storage_window_bounds_negative_size_degenerate) {
    tl_ts_t start, end;
    bool unbounded;

    /* window_size < 0 should return degenerate window [origin, origin) */
    tl_window_bounds(5, -10, 50, &start, &end, &unbounded);
    TEST_ASSERT_EQ(50, start);
    TEST_ASSERT_EQ(50, end);
    TEST_ASSERT(!unbounded);
}

TEST_DECLARE(storage_window_bounds_for_ts_zero_size_invalid) {
    tl_ts_t start, end;
    bool unbounded;

    /* window_size = 0 should return TL_EINVAL */
    TEST_ASSERT_STATUS(TL_EINVAL,
        tl_window_bounds_for_ts(100, 0, 0, &start, &end, &unbounded));
}

TEST_DECLARE(storage_floor_div_zero_divisor_safe) {
    /* Division by zero should return 0 as safe fallback */
    TEST_ASSERT_EQ(0, tl_floor_div_i64(100, 0));
    TEST_ASSERT_EQ(0, tl_floor_div_i64(-100, 0));
    TEST_ASSERT_EQ(0, tl_floor_div_i64(0, 0));
}

TEST_DECLARE(storage_floor_div_negative_divisor_safe) {
    /* Negative divisor should return 0 as safe fallback */
    TEST_ASSERT_EQ(0, tl_floor_div_i64(100, -10));
    TEST_ASSERT_EQ(0, tl_floor_div_i64(-100, -10));
}

/*===========================================================================
 * Page Tests (Internal API)
 *
 * These test the internal page builder and page structure.
 * Pages are implementation details - the public API exposes iterators.
 *===========================================================================*/

TEST_DECLARE(storage_page_builder_single_page) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    tl_record_t records[5];
    for (int i = 0; i < 5; i++) {
        records[i].ts = (tl_ts_t)(i * 10);
        records[i].handle = (tl_handle_t)(i + 1);
    }

    tl_page_t* page = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_page_builder_build(&pb, records, 5, &page));
    TEST_ASSERT_NOT_NULL(page);

    TEST_ASSERT_EQ(5, page->count);
    TEST_ASSERT_EQ(0, page->min_ts);
    TEST_ASSERT_EQ(40, page->max_ts);
    /*
     * Verify page is marked fully live.
     * NOTE: TL_PAGE_FULLY_LIVE = 0, so we must use equality (not bitwise AND).
     */
    TEST_ASSERT_EQ(TL_PAGE_FULLY_LIVE, page->flags);

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_page_builder_count_zero) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    tl_page_t* page = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_page_builder_build(&pb, NULL, 0, &page));
    TEST_ASSERT_NULL(page);

    tl__alloc_destroy(&alloc);
}

/* M-07 fix test: NULL records with non-zero count returns TL_EINVAL */
TEST_DECLARE(storage_page_builder_null_records_nonzero_count) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    tl_page_t* page = NULL;
    /* NULL records with count > 0 should return TL_EINVAL, not crash */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_page_builder_build(&pb, NULL, 5, &page));
    TEST_ASSERT_NULL(page);

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_page_capacity_tiny_target) {
    /* target_page_bytes < sizeof(tl_page_t) => returns TL_MIN_PAGE_ROWS */
    size_t cap = tl_page_builder_compute_capacity(1);
    TEST_ASSERT_EQ(TL_MIN_PAGE_ROWS, cap);
}

TEST_DECLARE(storage_page_capacity_zero_target) {
    size_t cap = tl_page_builder_compute_capacity(0);
    TEST_ASSERT_EQ(TL_MIN_PAGE_ROWS, cap);
}

TEST_DECLARE(storage_page_lower_bound_found) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    tl_record_t records[5] = {
        {10, 0}, {20, 0}, {30, 0}, {40, 0}, {50, 0}
    };

    tl_page_t* page = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_page_builder_build(&pb, records, 5, &page));
    TEST_ASSERT_NOT_NULL(page);

    TEST_ASSERT_EQ(0, tl_page_lower_bound(page, 5));   /* Before all */
    TEST_ASSERT_EQ(0, tl_page_lower_bound(page, 10));  /* Exact match */
    TEST_ASSERT_EQ(1, tl_page_lower_bound(page, 15));  /* Between */
    TEST_ASSERT_EQ(2, tl_page_lower_bound(page, 30));  /* Exact match */
    TEST_ASSERT_EQ(5, tl_page_lower_bound(page, 100)); /* After all */

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_page_upper_bound) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    /* Records with duplicates: 10, 20, 20, 20, 30 */
    tl_record_t records[5] = {
        {10, 0}, {20, 1}, {20, 2}, {20, 3}, {30, 0}
    };

    tl_page_t* page = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_page_builder_build(&pb, records, 5, &page));
    TEST_ASSERT_NOT_NULL(page);

    TEST_ASSERT_EQ(0, tl_page_upper_bound(page, 5));
    TEST_ASSERT_EQ(1, tl_page_upper_bound(page, 10));
    TEST_ASSERT_EQ(4, tl_page_upper_bound(page, 20)); /* After all 20s */
    TEST_ASSERT_EQ(5, tl_page_upper_bound(page, 30));

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_page_get_record) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    tl_record_t records[3] = {
        {100, 0xDEAD}, {200, 0xBEEF}, {300, 0xCAFE}
    };

    tl_page_t* page = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_page_builder_build(&pb, records, 3, &page));
    TEST_ASSERT_NOT_NULL(page);

    tl_record_t out;
    tl_page_get_record(page, 1, &out);
    TEST_ASSERT_EQ(200, out.ts);
    TEST_ASSERT_EQ(0xBEEF, out.handle);

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_page_destroy_null) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Should be safe to call on NULL */
    tl_page_destroy(NULL, &alloc);

    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Page Catalog Tests (Internal API)
 *
 * These test the internal page catalog used for organizing pages within
 * a segment. The catalog is not exposed in the public API.
 *===========================================================================*/

TEST_DECLARE(storage_catalog_init_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_catalog_t cat;
    tl_page_catalog_init(&cat, &alloc);

    TEST_ASSERT_EQ(0, tl_page_catalog_count(&cat));
    TEST_ASSERT_NULL(cat.pages);

    tl_page_catalog_destroy(&cat);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_catalog_push_single) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create a page */
    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);
    tl_record_t records[3] = {{10, 0}, {20, 0}, {30, 0}};
    tl_page_t* page = NULL;
    tl_page_builder_build(&pb, records, 3, &page);

    /* Push to catalog */
    tl_page_catalog_t cat;
    tl_page_catalog_init(&cat, &alloc);
    TEST_ASSERT_STATUS(TL_OK, tl_page_catalog_push(&cat, page));

    TEST_ASSERT_EQ(1, tl_page_catalog_count(&cat));
    const tl_page_meta_t* meta = tl_page_catalog_get(&cat, 0);
    TEST_ASSERT_EQ(10, meta->min_ts);
    TEST_ASSERT_EQ(30, meta->max_ts);
    TEST_ASSERT_EQ(3, meta->count);

    tl_page_destroy(page, &alloc);
    tl_page_catalog_destroy(&cat);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_catalog_find_first_ge) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    /* Create 3 pages with ranges [0,10), [20,30), [40,50) */
    tl_record_t r1[2] = {{0, 0}, {9, 0}};
    tl_record_t r2[2] = {{20, 0}, {29, 0}};
    tl_record_t r3[2] = {{40, 0}, {49, 0}};

    tl_page_t *p1 = NULL, *p2 = NULL, *p3 = NULL;
    tl_page_builder_build(&pb, r1, 2, &p1);
    tl_page_builder_build(&pb, r2, 2, &p2);
    tl_page_builder_build(&pb, r3, 2, &p3);

    tl_page_catalog_t cat;
    tl_page_catalog_init(&cat, &alloc);
    tl_page_catalog_push(&cat, p1);
    tl_page_catalog_push(&cat, p2);
    tl_page_catalog_push(&cat, p3);

    /* Find first page with max_ts >= ts */
    TEST_ASSERT_EQ(0, tl_page_catalog_find_first_ge(&cat, 5));   /* In page 0 */
    TEST_ASSERT_EQ(1, tl_page_catalog_find_first_ge(&cat, 15));  /* After p0, before p1 */
    TEST_ASSERT_EQ(1, tl_page_catalog_find_first_ge(&cat, 25));  /* In page 1 */
    TEST_ASSERT_EQ(2, tl_page_catalog_find_first_ge(&cat, 35));  /* After p1, before p2 */
    TEST_ASSERT_EQ(3, tl_page_catalog_find_first_ge(&cat, 100)); /* After all */

    tl_page_destroy(p1, &alloc);
    tl_page_destroy(p2, &alloc);
    tl_page_destroy(p3, &alloc);
    tl_page_catalog_destroy(&cat);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Segment Tests (Internal API)
 *
 * These test the internal segment builder and segment structure.
 * Includes reference counting tests which are implementation details.
 *===========================================================================*/

TEST_DECLARE(storage_segment_build_l0_records_only) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[10];
    for (int i = 0; i < 10; i++) {
        records[i].ts = (tl_ts_t)(i * 10);
        records[i].handle = (tl_handle_t)(i + 1);
    }

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, records, 10,
                                                   NULL, 0,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    TEST_ASSERT(tl_segment_is_l0(seg));
    TEST_ASSERT(!tl_segment_is_l1(seg));
    TEST_ASSERT_EQ(10, seg->record_count);
    TEST_ASSERT_EQ(0, seg->min_ts);
    TEST_ASSERT_EQ(90, seg->max_ts);
    TEST_ASSERT(!tl_segment_has_tombstones(seg));
    TEST_ASSERT_EQ(1, tl_segment_refcnt(seg));

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l0_with_tombstones) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[5] = {
        {10, 0}, {20, 0}, {30, 0}, {40, 0}, {50, 0}
    };
    tl_interval_t tombs[1] = {{100, 200, false, 1}};

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, records, 5,
                                                   tombs, 1,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    TEST_ASSERT(tl_segment_has_tombstones(seg));
    TEST_ASSERT_EQ(1, seg->tombstones->n);
    TEST_ASSERT_EQ(100, seg->tombstones->v[0].start);
    TEST_ASSERT_EQ(200, seg->tombstones->v[0].end);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l0_tombstone_only) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_interval_t tombs[1] = {{100, 200, false, 1}};

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, NULL, 0,
                                                   tombs, 1,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    TEST_ASSERT(tl_segment_is_tombstone_only(seg));
    TEST_ASSERT_EQ(0, seg->record_count);
    TEST_ASSERT_EQ(0, seg->page_count);

    /* Bounds from tombstones: min_ts = 100, max_ts = 199 (end - 1) */
    TEST_ASSERT_EQ(100, seg->min_ts);
    TEST_ASSERT_EQ(199, seg->max_ts);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l0_empty_invalid) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_segment_t* seg = NULL;
    /* 0 records + 0 tombstones => TL_EINVAL */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l0(&alloc, NULL, 0,
                                                       NULL, 0,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       1, &seg));
    TEST_ASSERT_NULL(seg);

    tl__alloc_destroy(&alloc);
}

/*
 * C-04 fix: tombstones_len > 0 with NULL pointer must return TL_EINVAL.
 * Before fix, this would cause memcpy with NULL src (undefined behavior).
 */
TEST_DECLARE(storage_segment_build_l0_null_tombstones_invalid) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Some records but NULL tombstones with non-zero len */
    tl_record_t records[2] = {{100, 1}, {200, 2}};

    tl_segment_t* seg = NULL;
    /* tombstones_len=2 but tombstones=NULL => TL_EINVAL (C-04 fix) */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l0(&alloc, records, 2,
                                                       NULL, 2,  /* NULL with len > 0 */
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       1, &seg));
    TEST_ASSERT_NULL(seg);

    tl__alloc_destroy(&alloc);
}

/*
 * C-04 fix: record_count > 0 with NULL pointer must return TL_EINVAL.
 * Before fix, TL_ASSERT would catch this in debug, but release builds had UB.
 * This variant has tombstones present (records-only validation still works).
 */
TEST_DECLARE(storage_segment_build_l0_null_records_invalid) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Some tombstones but NULL records with non-zero count */
    tl_interval_t tombs[1] = {{100, 200, false, 1}};

    tl_segment_t* seg = NULL;
    /* record_count=3 but records=NULL => TL_EINVAL (C-04 fix) */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l0(&alloc, NULL, 3,
                                                       tombs, 1,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       1, &seg));
    TEST_ASSERT_NULL(seg);

    tl__alloc_destroy(&alloc);
}

/*
 * C-04 fix: record_count > 0 with NULL pointer, no tombstones.
 * Covers the case where records validation is the ONLY thing preventing UB.
 */
TEST_DECLARE(storage_segment_build_l0_null_records_no_tombstones_invalid) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_segment_t* seg = NULL;
    /* record_count=5 but records=NULL, no tombstones => TL_EINVAL */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l0(&alloc, NULL, 5,
                                                       NULL, 0,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       1, &seg));
    TEST_ASSERT_NULL(seg);

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l0_unbounded_tombstone) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Unbounded interval [100, +inf) */
    tl_interval_t tombs[1] = {{100, 0, true, 1}};

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, NULL, 0,
                                                   tombs, 1,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));
    TEST_ASSERT_NOT_NULL(seg);

    /* max_ts should be TL_TS_MAX for unbounded */
    TEST_ASSERT_EQ(100, seg->min_ts);
    TEST_ASSERT_EQ(TL_TS_MAX, seg->max_ts);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l1) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[5] = {
        {100, 0}, {110, 0}, {120, 0}, {130, 0}, {140, 0}
    };

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, records, 5,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   100, 200, false, 1, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    TEST_ASSERT(tl_segment_is_l1(seg));
    TEST_ASSERT_EQ(100, seg->window_start);
    TEST_ASSERT_EQ(200, seg->window_end);
    TEST_ASSERT_NULL(seg->tombstones);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l1_min_below_window_start_einval) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{90, 1}, {110, 2}};
    tl_segment_t* seg = NULL;

    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l1(&alloc, records, 2,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       100, 200, false, 1, &seg));
    TEST_ASSERT_NULL(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l1_max_at_or_above_window_end_einval) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{100, 1}, {200, 2}};
    tl_segment_t* seg = NULL;

    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l1(&alloc, records, 2,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       100, 200, false, 1, &seg));
    TEST_ASSERT_NULL(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l1_exact_window_boundaries_ok) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{100, 1}, {199, 2}};
    tl_segment_t* seg = NULL;

    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, records, 2,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   100, 200, false, 1, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_pages_rejects_cross_page_out_of_order) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Force TL_MIN_PAGE_ROWS per page by using tiny target_page_bytes. */
    tl_record_t* records = TL_NEW_ARRAY(&alloc, tl_record_t, TL_MIN_PAGE_ROWS + 1);
    TEST_ASSERT_NOT_NULL(records);

    for (size_t i = 0; i < TL_MIN_PAGE_ROWS; i++) {
        records[i].ts = (tl_ts_t)(100 + (tl_ts_t)i);
        records[i].handle = (tl_handle_t)i;
    }
    /* Cross-page violation: first record of next page < last of previous page */
    records[TL_MIN_PAGE_ROWS].ts = 50;
    records[TL_MIN_PAGE_ROWS].handle = 999;

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l1(&alloc, records,
                                                       TL_MIN_PAGE_ROWS + 1,
                                                       1,  /* tiny target_page_bytes */
                                                       0, 1000, false, 1, &seg));
    TEST_ASSERT_NULL(seg);

    TL_FREE(&alloc, records);
    tl__alloc_destroy(&alloc);
}

/* C-05 fix test: unbounded mismatch should return TL_EINVAL */
TEST_DECLARE(storage_segment_build_l1_unbounded_mismatch_invalid) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{100, 1}, {200, 2}};

    tl_segment_t* seg = NULL;
    /* window_end_unbounded=true but window_end=500 (not TL_TS_MAX) => TL_EINVAL */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l1(&alloc, records, 2,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       0, 500, true, 1, &seg));
    TEST_ASSERT_NULL(seg);

    tl__alloc_destroy(&alloc);
}

/* C-05 fix test: valid unbounded config should succeed */
TEST_DECLARE(storage_segment_build_l1_unbounded_valid) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{100, 1}, {200, 2}};

    tl_segment_t* seg = NULL;
    /* window_end_unbounded=true and window_end=TL_TS_MAX => TL_OK */
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, records, 2,
                                                    TL_DEFAULT_TARGET_PAGE_BYTES,
                                                    0, TL_TS_MAX, true, 1, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    TEST_ASSERT(tl_segment_is_l1(seg));
    TEST_ASSERT(seg->window_end_unbounded);
    TEST_ASSERT_EQ(TL_TS_MAX, seg->window_end);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_refcnt_acquire_release) {
    /*
     * Tests internal reference counting behavior.
     * Reference counting is an implementation detail - a valid
     * implementation could use arena allocation or epoch-based reclamation.
     */
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[3] = {{10, 0}, {20, 0}, {30, 0}};

    tl_segment_t* seg = NULL;
    tl_segment_build_l0(&alloc, records, 3, NULL, 0,
                        TL_DEFAULT_TARGET_PAGE_BYTES, 1, &seg);

    TEST_ASSERT_EQ(1, tl_segment_refcnt(seg));

    tl_segment_acquire(seg);
    TEST_ASSERT_EQ(2, tl_segment_refcnt(seg));

    tl_segment_acquire(seg);
    TEST_ASSERT_EQ(3, tl_segment_refcnt(seg));

    tl_segment_release(seg);
    TEST_ASSERT_EQ(2, tl_segment_refcnt(seg));

    tl_segment_release(seg);
    TEST_ASSERT_EQ(1, tl_segment_refcnt(seg));

    tl_segment_release(seg); /* Destroys */

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_tombstones_imm) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_interval_t tombs[2] = {{10, 20, false, 1}, {30, 40, false, 1}};
    tl_record_t records[1] = {{5, 0}};

    tl_segment_t* seg = NULL;
    tl_segment_build_l0(&alloc, records, 1, tombs, 2,
                        TL_DEFAULT_TARGET_PAGE_BYTES, 1, &seg);

    tl_intervals_imm_t imm = tl_segment_tombstones_imm(seg);
    TEST_ASSERT_EQ(2, imm.len);
    TEST_ASSERT_EQ(10, imm.data[0].start);
    TEST_ASSERT_EQ(30, imm.data[1].start);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_l0_bounds_include_tombstones) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Records in range [100, 200] */
    tl_record_t records[3] = {{100, 0}, {150, 0}, {200, 0}};

    /* Tombstones in range [50, 80) and [300, 400) - outside records */
    tl_interval_t tombs[2] = {
        {50, 80, false, 1},   /* Earlier than records */
        {300, 400, false, 1}  /* Later than records */
    };

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, records, 3,
                                                   tombs, 2,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));
    TEST_ASSERT_NOT_NULL(seg);

    /* Bounds should cover both records AND tombstones */
    /* min_ts = min(100, 50) = 50 */
    /* max_ts = max(200, 79, 399) = 399 */
    TEST_ASSERT_EQ(50, seg->min_ts);
    TEST_ASSERT_EQ(399, seg->max_ts);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_l0_bounds_tombstones_extend_max) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Records in range [100, 200] */
    tl_record_t records[2] = {{100, 0}, {200, 0}};

    /* Unbounded tombstone starting after records */
    tl_interval_t tombs[1] = {{300, 0, true, 1}};  /* [300, +inf) */

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, records, 2,
                                                   tombs, 1,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));
    TEST_ASSERT_NOT_NULL(seg);

    /* max_ts should be TL_TS_MAX due to unbounded tombstone */
    TEST_ASSERT_EQ(100, seg->min_ts);
    TEST_ASSERT_EQ(TL_TS_MAX, seg->max_ts);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Manifest Tests (Internal API)
 *
 * These test the internal manifest builder and manifest structure.
 * The manifest builder is not exposed in the public API.
 *===========================================================================*/

TEST_DECLARE(storage_manifest_create_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_manifest_t* m = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_create(&alloc, &m));
    TEST_ASSERT_NOT_NULL(m);

    TEST_ASSERT_EQ(1, tl_manifest_version(m));
    TEST_ASSERT_EQ(0, tl_manifest_l0_count(m));
    TEST_ASSERT_EQ(0, tl_manifest_l1_count(m));
    TEST_ASSERT_EQ(1, tl_manifest_refcnt(m));

    tl_manifest_release(m);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_add_l0) {
    /*
     * Tests internal manifest builder and refcount behavior.
     * These are implementation details not exposed in public API.
     */
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create a segment */
    tl_record_t records[3] = {{10, 0}, {20, 0}, {30, 0}};
    tl_segment_t* seg = NULL;
    tl_segment_build_l0(&alloc, records, 3, NULL, 0,
                        TL_DEFAULT_TARGET_PAGE_BYTES, 1, &seg);

    /* Build manifest with segment */
    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l0(&mb, seg));

    tl_manifest_t* m = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_build(&mb, &m));

    TEST_ASSERT_EQ(1, tl_manifest_l0_count(m));
    TEST_ASSERT_EQ(0, tl_manifest_l1_count(m));
    TEST_ASSERT_EQ(seg, tl_manifest_l0_get(m, 0));

    /* Segment refcnt: 1 (builder) + 1 (manifest) = 2 */
    TEST_ASSERT_EQ(2, tl_segment_refcnt(seg));

    tl_manifest_builder_destroy(&mb);
    tl_manifest_release(m);  /* Releases segment ref */
    /* Segment refcnt now 1 (builder's original ref) */
    tl_segment_release(seg); /* Destroys */

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_destroy_resets_lengths) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create a segment to allocate builder arrays */
    tl_record_t records[1] = {{10, 0}};
    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, records, 1,
                                                   NULL, 0,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l0(&mb, seg));
    TEST_ASSERT_EQ(1u, mb.add_l0_len);
    TEST_ASSERT(mb.add_l0_cap >= 1u);

    tl_manifest_builder_destroy(&mb);

    TEST_ASSERT_EQ(NULL, mb.add_l0);
    TEST_ASSERT_EQ(NULL, mb.add_l1);
    TEST_ASSERT_EQ(NULL, mb.remove_l0);
    TEST_ASSERT_EQ(NULL, mb.remove_l1);

    TEST_ASSERT_EQ(0u, mb.add_l0_len);
    TEST_ASSERT_EQ(0u, mb.add_l0_cap);
    TEST_ASSERT_EQ(0u, mb.add_l1_len);
    TEST_ASSERT_EQ(0u, mb.add_l1_cap);
    TEST_ASSERT_EQ(0u, mb.remove_l0_len);
    TEST_ASSERT_EQ(0u, mb.remove_l0_cap);
    TEST_ASSERT_EQ(0u, mb.remove_l1_len);
    TEST_ASSERT_EQ(0u, mb.remove_l1_cap);

    TEST_ASSERT_EQ(NULL, mb.alloc);
    TEST_ASSERT_EQ(NULL, mb.base);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l0_record_tomb_bounds) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{10, 1}, {20, 2}};
    tl_interval_t tombs[1] = {{100, 110, false, 1}}; /* [100, 110) */

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc,
                                                   records, 2,
                                                   tombs, 1,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));
    TEST_ASSERT_NOT_NULL(seg);

    TEST_ASSERT_EQ(10, seg->record_min_ts);
    TEST_ASSERT_EQ(20, seg->record_max_ts);
    TEST_ASSERT_EQ(100, seg->tomb_min_ts);
    TEST_ASSERT_EQ(109, seg->tomb_max_ts);
    TEST_ASSERT_EQ(10, seg->min_ts);
    TEST_ASSERT_EQ(109, seg->max_ts);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_rejects_wrong_level) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{10, 0}, {20, 0}};

    tl_segment_t* l0 = NULL;
    tl_segment_t* l1 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, records, 2,
                                                   NULL, 0,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &l0));
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, records, 2,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   0, 100, false, 1, &l1));

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    TEST_ASSERT_STATUS(TL_EINVAL, tl_manifest_builder_add_l0(&mb, l1));
    TEST_ASSERT_STATUS(TL_EINVAL, tl_manifest_builder_add_l1(&mb, l0));
    tl_manifest_builder_destroy(&mb);

    tl_segment_release(l0);
    tl_segment_release(l1);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_rejects_duplicate_adds) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{10, 0}, {20, 0}};
    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, records, 2,
                                                   NULL, 0,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l0(&mb, seg));
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l0(&mb, seg));

    tl_manifest_t* m = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_manifest_builder_build(&mb, &m));
    TEST_ASSERT_NULL(m);
    tl_manifest_builder_destroy(&mb);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_rejects_add_existing_in_base) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{10, 0}, {20, 0}};
    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, records, 2,
                                                   NULL, 0,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));

    /* Base manifest with seg */
    tl_manifest_builder_t mb1;
    tl_manifest_builder_init(&mb1, &alloc, NULL);
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l0(&mb1, seg));
    tl_manifest_t* base = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_build(&mb1, &base));
    tl_manifest_builder_destroy(&mb1);

    /* Attempt to add same seg again */
    tl_manifest_builder_t mb2;
    tl_manifest_builder_init(&mb2, &alloc, base);
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l0(&mb2, seg));
    tl_manifest_t* m2 = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_manifest_builder_build(&mb2, &m2));
    TEST_ASSERT_NULL(m2);
    tl_manifest_builder_destroy(&mb2);

    tl_manifest_release(base);
    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_rejects_add_and_remove_same_segment) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{10, 0}, {20, 0}};
    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, records, 2,
                                                   NULL, 0,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   1, &seg));

    /* Base manifest with seg */
    tl_manifest_builder_t mb1;
    tl_manifest_builder_init(&mb1, &alloc, NULL);
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l0(&mb1, seg));
    tl_manifest_t* base = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_build(&mb1, &base));
    tl_manifest_builder_destroy(&mb1);

    /* Add and remove same seg in new builder */
    tl_manifest_builder_t mb2;
    tl_manifest_builder_init(&mb2, &alloc, base);
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_remove_l0(&mb2, seg));
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l0(&mb2, seg));
    tl_manifest_t* m2 = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_manifest_builder_build(&mb2, &m2));
    TEST_ASSERT_NULL(m2);
    tl_manifest_builder_destroy(&mb2);

    tl_manifest_release(base);
    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_add_l1_sorted) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create L1 segments with different windows (added in reverse order) */
    tl_record_t r1[2] = {{100, 0}, {150, 0}};
    tl_record_t r2[2] = {{200, 0}, {250, 0}};
    tl_record_t r3[2] = {{0, 0}, {50, 0}};

    tl_segment_t *s1 = NULL, *s2 = NULL, *s3 = NULL;
    tl_segment_build_l1(&alloc, r1, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 100, 200, false, 1, &s1);
    tl_segment_build_l1(&alloc, r2, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 200, 300, false, 1, &s2);
    tl_segment_build_l1(&alloc, r3, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 0, 100, false, 1, &s3);

    /* Add in reverse window order */
    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    tl_manifest_builder_add_l1(&mb, s2); /* window [200, 300) */
    tl_manifest_builder_add_l1(&mb, s1); /* window [100, 200) */
    tl_manifest_builder_add_l1(&mb, s3); /* window [0, 100) */

    tl_manifest_t* m = NULL;
    tl_manifest_builder_build(&mb, &m);

    /* Should be sorted by window_start */
    TEST_ASSERT_EQ(3, tl_manifest_l1_count(m));
    TEST_ASSERT_EQ(0, tl_manifest_l1_get(m, 0)->window_start);
    TEST_ASSERT_EQ(100, tl_manifest_l1_get(m, 1)->window_start);
    TEST_ASSERT_EQ(200, tl_manifest_l1_get(m, 2)->window_start);

    tl_manifest_builder_destroy(&mb);
    tl_manifest_release(m);
    tl_segment_release(s1);
    tl_segment_release(s2);
    tl_segment_release(s3);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_rejects_overlapping_l1) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t r1[2] = {{0, 0}, {50, 0}};
    tl_record_t r2[2] = {{60, 0}, {90, 0}};

    tl_segment_t *s1 = NULL, *s2 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r1, 2,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   0, 100, false, 1, &s1));
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r2, 2,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   50, 150, false, 1, &s2));

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    tl_manifest_builder_add_l1(&mb, s1);
    tl_manifest_builder_add_l1(&mb, s2);

    tl_manifest_t* m = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_manifest_builder_build(&mb, &m));
    TEST_ASSERT_NULL(m);
    tl_manifest_builder_destroy(&mb);

    tl_segment_release(s1);
    tl_segment_release(s2);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_l1_adjacent_windows_allowed) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t r1[2] = {{0, 0}, {50, 0}};
    tl_record_t r2[2] = {{100, 0}, {150, 0}};

    tl_segment_t *s1 = NULL, *s2 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r1, 2,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   0, 100, false, 1, &s1));
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r2, 2,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   100, 200, false, 1, &s2));

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    tl_manifest_builder_add_l1(&mb, s1);
    tl_manifest_builder_add_l1(&mb, s2);

    tl_manifest_t* m = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_build(&mb, &m));
    TEST_ASSERT_NOT_NULL(m);
    TEST_ASSERT_EQ(2, tl_manifest_l1_count(m));

    tl_manifest_builder_destroy(&mb);
    tl_manifest_release(m);
    tl_segment_release(s1);
    tl_segment_release(s2);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_l1_unbounded_rejects_subsequent) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t r1[2] = {{0, 0}, {50, 0}};
    tl_record_t r2[2] = {{200, 0}, {250, 0}};

    tl_segment_t *s1 = NULL, *s2 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r1, 2,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   0, TL_TS_MAX, true, 1, &s1));
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r2, 2,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   200, 300, false, 1, &s2));

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    tl_manifest_builder_add_l1(&mb, s1);
    tl_manifest_builder_add_l1(&mb, s2);

    tl_manifest_t* m = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_manifest_builder_build(&mb, &m));
    TEST_ASSERT_NULL(m);
    tl_manifest_builder_destroy(&mb);

    tl_segment_release(s1);
    tl_segment_release(s2);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_remove_l0) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create segments */
    tl_record_t r1[2] = {{10, 0}, {20, 0}};
    tl_record_t r2[2] = {{30, 0}, {40, 0}};
    tl_segment_t *s1 = NULL, *s2 = NULL;
    tl_segment_build_l0(&alloc, r1, 2, NULL, 0, TL_DEFAULT_TARGET_PAGE_BYTES, 1, &s1);
    tl_segment_build_l0(&alloc, r2, 2, NULL, 0, TL_DEFAULT_TARGET_PAGE_BYTES, 2, &s2);

    /* Create manifest with both */
    tl_manifest_builder_t mb1;
    tl_manifest_builder_init(&mb1, &alloc, NULL);
    tl_manifest_builder_add_l0(&mb1, s1);
    tl_manifest_builder_add_l0(&mb1, s2);
    tl_manifest_t* m1 = NULL;
    tl_manifest_builder_build(&mb1, &m1);
    tl_manifest_builder_destroy(&mb1);

    TEST_ASSERT_EQ(2, tl_manifest_l0_count(m1));

    /* Create new manifest removing s1 */
    tl_manifest_builder_t mb2;
    tl_manifest_builder_init(&mb2, &alloc, m1);
    tl_manifest_builder_remove_l0(&mb2, s1);
    tl_manifest_t* m2 = NULL;
    tl_manifest_builder_build(&mb2, &m2);
    tl_manifest_builder_destroy(&mb2);

    TEST_ASSERT_EQ(1, tl_manifest_l0_count(m2));
    TEST_ASSERT_EQ(s2, tl_manifest_l0_get(m2, 0));
    TEST_ASSERT_EQ(2, tl_manifest_version(m2));

    tl_manifest_release(m1);
    tl_manifest_release(m2);
    tl_segment_release(s1);
    tl_segment_release(s2);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_l1_find_first_overlap) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create L1 segments: [0,100), [100,200), [200,300) */
    tl_record_t r1[2] = {{10, 0}, {90, 0}};
    tl_record_t r2[2] = {{110, 0}, {190, 0}};
    tl_record_t r3[2] = {{210, 0}, {290, 0}};

    tl_segment_t *s1 = NULL, *s2 = NULL, *s3 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r1, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 0, 100, false, 1, &s1));
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r2, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 100, 200, false, 1, &s2));
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r3, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 200, 300, false, 1, &s3));

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l1(&mb, s1));
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l1(&mb, s2));
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l1(&mb, s3));
    tl_manifest_t* m = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_build(&mb, &m));
    TEST_ASSERT_NOT_NULL(m);
    tl_manifest_builder_destroy(&mb);

    /* Find first segment with max_ts >= ts */
    TEST_ASSERT_EQ(0, tl_manifest_l1_find_first_overlap(m, 50));   /* In s1 */
    TEST_ASSERT_EQ(1, tl_manifest_l1_find_first_overlap(m, 100));  /* Starts in s2 */
    TEST_ASSERT_EQ(2, tl_manifest_l1_find_first_overlap(m, 200));  /* Starts in s3 */
    TEST_ASSERT_EQ(3, tl_manifest_l1_find_first_overlap(m, 500));  /* After all */

    tl_manifest_release(m);
    tl_segment_release(s1);
    tl_segment_release(s2);
    tl_segment_release(s3);
    tl__alloc_destroy(&alloc);
}

/**
 * Test L1 overlap search behavior with sparse segments.
 *
 * IMPORTANT: tl_manifest_l1_find_first_overlap uses RECORD-BASED bounds (max_ts),
 * NOT window bounds. This is correct behavior because:
 * - If max_ts < query_ts, segment has no records at or after query_ts
 * - Window bounds enforce L1 non-overlap invariant, not query routing
 *
 * This test documents the actual (correct) behavior.
 */
TEST_DECLARE(storage_manifest_l1_find_first_overlap_sparse) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /*
     * Create sparse L1 segments:
     * - s1: window [0,100) but only record at ts=0 (max_ts=0)
     * - s2: window [100,200) with record at ts=150 (max_ts=150)
     */
    tl_record_t r1[1] = {{0, 1}};   /* Single record at ts=0 */
    tl_record_t r2[1] = {{150, 2}}; /* Single record at ts=150 */

    tl_segment_t *s1 = NULL, *s2 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r1, 1, TL_DEFAULT_TARGET_PAGE_BYTES, 0, 100, false, 1, &s1));
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, r2, 1, TL_DEFAULT_TARGET_PAGE_BYTES, 100, 200, false, 2, &s2));

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l1(&mb, s1));
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_add_l1(&mb, s2));
    tl_manifest_t* m = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_manifest_builder_build(&mb, &m));
    TEST_ASSERT_NOT_NULL(m);
    tl_manifest_builder_destroy(&mb);

    /*
     * Binary search: "first L1 segment where max_ts >= t1"
     *
     * ts=0: s1.max_ts=0 >= 0, return index 0
     * ts=1: s1.max_ts=0 < 1, skip; s2.max_ts=150 >= 1, return index 1
     * ts=50: s1.max_ts=0 < 50, skip; s2.max_ts=150 >= 50, return index 1
     * ts=100: s1.max_ts=0 < 100, skip; s2.max_ts=150 >= 100, return index 1
     * ts=150: s1.max_ts=0 < 150, skip; s2.max_ts=150 >= 150, return index 1
     * ts=151: s1 and s2 both have max_ts < 151, return n_l1=2 (past end)
     */
    TEST_ASSERT_EQ(0, tl_manifest_l1_find_first_overlap(m, 0));   /* s1.max_ts >= 0 */
    TEST_ASSERT_EQ(1, tl_manifest_l1_find_first_overlap(m, 1));   /* s1.max_ts < 1, s2.max_ts >= 1 */
    TEST_ASSERT_EQ(1, tl_manifest_l1_find_first_overlap(m, 50));  /* s1.max_ts < 50, s2.max_ts >= 50 */
    TEST_ASSERT_EQ(1, tl_manifest_l1_find_first_overlap(m, 100)); /* s1.max_ts < 100, s2.max_ts >= 100 */
    TEST_ASSERT_EQ(1, tl_manifest_l1_find_first_overlap(m, 150)); /* s1.max_ts < 150, s2.max_ts >= 150 */
    TEST_ASSERT_EQ(2, tl_manifest_l1_find_first_overlap(m, 151)); /* Both max_ts < 151, past end */

    tl_manifest_release(m);
    tl_segment_release(s1);
    tl_segment_release(s2);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_bounds_cached) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t r1[2] = {{10, 0}, {50, 0}};
    tl_record_t r2[2] = {{100, 0}, {200, 0}};

    tl_segment_t *s1 = NULL, *s2 = NULL;
    tl_segment_build_l0(&alloc, r1, 2, NULL, 0, TL_DEFAULT_TARGET_PAGE_BYTES, 1, &s1);
    tl_segment_build_l0(&alloc, r2, 2, NULL, 0, TL_DEFAULT_TARGET_PAGE_BYTES, 2, &s2);

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    tl_manifest_builder_add_l0(&mb, s1);
    tl_manifest_builder_add_l0(&mb, s2);
    tl_manifest_t* m = NULL;
    tl_manifest_builder_build(&mb, &m);
    tl_manifest_builder_destroy(&mb);

    TEST_ASSERT(m->has_bounds);
    TEST_ASSERT_EQ(10, m->min_ts);
    TEST_ASSERT_EQ(200, m->max_ts);

    tl_manifest_release(m);
    tl_segment_release(s1);
    tl_segment_release(s2);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Manifest Edge Case Tests (Internal API)
 *===========================================================================*/

TEST_DECLARE(storage_manifest_builder_remove_nonexistent) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create two segments */
    tl_record_t r1[2] = {{10, 0}, {20, 0}};
    tl_record_t r2[2] = {{30, 0}, {40, 0}};
    tl_segment_t *s1 = NULL, *s2 = NULL;
    tl_segment_build_l0(&alloc, r1, 2, NULL, 0, TL_DEFAULT_TARGET_PAGE_BYTES, 1, &s1);
    tl_segment_build_l0(&alloc, r2, 2, NULL, 0, TL_DEFAULT_TARGET_PAGE_BYTES, 2, &s2);

    /* Create manifest with only s1 */
    tl_manifest_builder_t mb1;
    tl_manifest_builder_init(&mb1, &alloc, NULL);
    tl_manifest_builder_add_l0(&mb1, s1);
    tl_manifest_t* m1 = NULL;
    tl_manifest_builder_build(&mb1, &m1);
    tl_manifest_builder_destroy(&mb1);

    /* Try to remove s2 (not in manifest) => should fail */
    tl_manifest_builder_t mb2;
    tl_manifest_builder_init(&mb2, &alloc, m1);
    tl_manifest_builder_remove_l0(&mb2, s2);
    tl_manifest_t* m2 = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_manifest_builder_build(&mb2, &m2));
    TEST_ASSERT_NULL(m2);
    tl_manifest_builder_destroy(&mb2);

    tl_manifest_release(m1);
    tl_segment_release(s1);
    tl_segment_release(s2);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_builder_remove_duplicate) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create segments */
    tl_record_t r1[2] = {{10, 0}, {20, 0}};
    tl_record_t r2[2] = {{30, 0}, {40, 0}};
    tl_segment_t *s1 = NULL, *s2 = NULL;
    tl_segment_build_l0(&alloc, r1, 2, NULL, 0, TL_DEFAULT_TARGET_PAGE_BYTES, 1, &s1);
    tl_segment_build_l0(&alloc, r2, 2, NULL, 0, TL_DEFAULT_TARGET_PAGE_BYTES, 2, &s2);

    /* Create manifest with both */
    tl_manifest_builder_t mb1;
    tl_manifest_builder_init(&mb1, &alloc, NULL);
    tl_manifest_builder_add_l0(&mb1, s1);
    tl_manifest_builder_add_l0(&mb1, s2);
    tl_manifest_t* m1 = NULL;
    tl_manifest_builder_build(&mb1, &m1);
    tl_manifest_builder_destroy(&mb1);

    /* Try to remove s1 twice => should fail */
    tl_manifest_builder_t mb2;
    tl_manifest_builder_init(&mb2, &alloc, m1);
    tl_manifest_builder_remove_l0(&mb2, s1);
    tl_manifest_builder_remove_l0(&mb2, s1); /* Duplicate removal */
    tl_manifest_t* m2 = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_manifest_builder_build(&mb2, &m2));
    TEST_ASSERT_NULL(m2);
    tl_manifest_builder_destroy(&mb2);

    tl_manifest_release(m1);
    tl_segment_release(s1);
    tl_segment_release(s2);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Edge Case Tests (T-03, T-08)
 *===========================================================================*/

/**
 * T-03: Invalid tombstone interval (end <= start) should be rejected.
 * Tombstone canonicalization requires half-open [start, end) with start < end.
 * Passing an invalid interval violates invariant #5.
 */
TEST_DECLARE(storage_segment_build_l0_invalid_tombstone_interval) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[2] = {{10, 1}, {20, 2}};

    /* Case 1: end < start (inverted interval) */
    tl_interval_t tombs_inverted[1] = {{100, 50, false, 1}};
    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l0(&alloc, records, 2,
                                                       tombs_inverted, 1,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       1, &seg));
    TEST_ASSERT_NULL(seg);

    /* Case 2: end == start (empty interval) */
    tl_interval_t tombs_empty[1] = {{100, 100, false, 1}};
    seg = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l0(&alloc, records, 2,
                                                       tombs_empty, 1,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       1, &seg));
    TEST_ASSERT_NULL(seg);

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l0_invalid_tombstone_seq_contract) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[1] = {{10, 1}};
    tl_segment_t* seg = NULL;

    /* max_seq must be > 0 */
    tl_interval_t zero_seq[1] = {{20, 30, false, 0}};
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l0(&alloc, records, 1,
                                                       zero_seq, 1,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       1, &seg));
    TEST_ASSERT_NULL(seg);

    /* max_seq must be <= applied_seq (wrapper maps generation->applied_seq) */
    tl_interval_t over_seq[1] = {{20, 30, false, 2}};
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l0(&alloc, records, 1,
                                                       over_seq, 1,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       1, &seg));
    TEST_ASSERT_NULL(seg);

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_build_l0_invalid_tombstone_order_contract) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[1] = {{10, 1}};
    tl_segment_t* seg = NULL;

    /* Unsorted intervals must be rejected */
    tl_interval_t unsorted[2] = {
        {30, 40, false, 1},
        {20, 25, false, 1}
    };
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l0(&alloc, records, 1,
                                                       unsorted, 2,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       1, &seg));
    TEST_ASSERT_NULL(seg);

    /* Adjacent same-seq intervals must be coalesced before build */
    tl_interval_t not_coalesced[2] = {
        {20, 30, false, 1},
        {30, 40, false, 1}
    };
    TEST_ASSERT_STATUS(TL_EINVAL, tl_segment_build_l0(&alloc, records, 1,
                                                       not_coalesced, 2,
                                                       TL_DEFAULT_TARGET_PAGE_BYTES,
                                                       1, &seg));
    TEST_ASSERT_NULL(seg);

    tl__alloc_destroy(&alloc);
}

/**
 * T-08: Very small target_page_bytes should clamp to minimum page rows.
 * Building a segment with target_page_bytes=1 should still produce valid
 * pages with at least TL_MIN_PAGE_ROWS records each.
 */
TEST_DECLARE(storage_segment_build_small_page_bytes_clamped) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create enough records to fill more than one minimum page */
    size_t n = TL_MIN_PAGE_ROWS * 3;
    tl_record_t* records = TL_NEW_ARRAY(&alloc, tl_record_t, n);
    TEST_ASSERT_NOT_NULL(records);

    for (size_t i = 0; i < n; i++) {
        records[i].ts = (tl_ts_t)(i * 10);
        records[i].handle = (tl_handle_t)(i + 1);
    }

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l0(&alloc, records, n,
                                                    NULL, 0,
                                                    1, /* tiny target_page_bytes */
                                                    1, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    TEST_ASSERT_EQ(n, seg->record_count);

    /* Verify pages were created (should have multiple pages due to minimum) */
    TEST_ASSERT(seg->page_count >= 1);

    /* Each page should have at least TL_MIN_PAGE_ROWS
     * (except possibly the last page which may have fewer) */
    for (uint32_t p = 0; p + 1 < seg->page_count; p++) {
        const tl_page_meta_t* meta = tl_page_catalog_get(&seg->catalog, p);
        TEST_ASSERT(meta->count >= TL_MIN_PAGE_ROWS);
    }

    tl_segment_release(seg);
    TL_FREE(&alloc, records);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Debug Validation Tests (Internal API)
 *
 * These validation functions are only available in debug builds.
 * They test internal invariants that may change with implementation.
 *===========================================================================*/

#ifdef TL_DEBUG

TEST_DECLARE(storage_page_validate_correct) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    tl_record_t records[5] = {
        {10, 0}, {20, 0}, {30, 0}, {40, 0}, {50, 0}
    };

    tl_page_t* page = NULL;
    tl_page_builder_build(&pb, records, 5, &page);

    TEST_ASSERT(tl_page_validate(page));

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_catalog_validate_correct) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    tl_record_t r1[2] = {{10, 0}, {20, 0}};
    tl_record_t r2[2] = {{30, 0}, {40, 0}};

    tl_page_t *p1 = NULL, *p2 = NULL;
    tl_page_builder_build(&pb, r1, 2, &p1);
    tl_page_builder_build(&pb, r2, 2, &p2);

    tl_page_catalog_t cat;
    tl_page_catalog_init(&cat, &alloc);
    tl_page_catalog_push(&cat, p1);
    tl_page_catalog_push(&cat, p2);

    TEST_ASSERT(tl_page_catalog_validate(&cat));

    tl_page_destroy(p1, &alloc);
    tl_page_destroy(p2, &alloc);
    tl_page_catalog_destroy(&cat);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_validate_l0) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[3] = {{10, 0}, {20, 0}, {30, 0}};
    tl_segment_t* seg = NULL;
    tl_segment_build_l0(&alloc, records, 3, NULL, 0,
                        TL_DEFAULT_TARGET_PAGE_BYTES, 1, &seg);

    TEST_ASSERT(tl_segment_validate(seg));

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_segment_validate_l1) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[3] = {{100, 0}, {150, 0}, {199, 0}};
    tl_segment_t* seg = NULL;
    tl_segment_build_l1(&alloc, records, 3, TL_DEFAULT_TARGET_PAGE_BYTES,
                        100, 200, false, 1, &seg);

    TEST_ASSERT(tl_segment_validate(seg));

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(storage_manifest_validate_correct) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t r1[2] = {{10, 0}, {90, 0}};
    tl_record_t r2[2] = {{110, 0}, {190, 0}};

    tl_segment_t *s1 = NULL, *s2 = NULL;
    tl_segment_build_l1(&alloc, r1, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 0, 100, false, 1, &s1);
    tl_segment_build_l1(&alloc, r2, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 100, 200, false, 1, &s2);

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    tl_manifest_builder_add_l1(&mb, s1);
    tl_manifest_builder_add_l1(&mb, s2);
    tl_manifest_t* m = NULL;
    tl_manifest_builder_build(&mb, &m);
    tl_manifest_builder_destroy(&mb);

    TEST_ASSERT(tl_manifest_validate(m));

    tl_manifest_release(m);
    tl_segment_release(s1);
    tl_segment_release(s2);
    tl__alloc_destroy(&alloc);
}

#endif /* TL_DEBUG */

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_storage_internal_tests(void) {
    /* Window mapping tests (15 tests) */
    RUN_TEST(storage_window_default_size);
    RUN_TEST(storage_window_default_size_unknown_enum);  /* M-06 fix test */
    RUN_TEST(storage_window_id_positive);
    RUN_TEST(storage_window_id_negative);
    RUN_TEST(storage_window_id_negative_exact);
    RUN_TEST(storage_window_id_negative_past);
    RUN_TEST(storage_window_id_at_origin);
    RUN_TEST(storage_window_bounds_basic);
    RUN_TEST(storage_window_bounds_negative_id);
    RUN_TEST(storage_window_bounds_for_ts);
    RUN_TEST(storage_window_contains);
    RUN_TEST(storage_window_contains_unbounded);
    RUN_TEST(storage_window_ts_max_unbounded);
    RUN_TEST(storage_window_id_overflow_underflow);
    RUN_TEST(storage_window_bounds_for_ts_overflow);
    RUN_TEST(storage_window_id_zero_size_invalid);
    RUN_TEST(storage_window_id_negative_size_invalid);
    RUN_TEST(storage_window_bounds_zero_size_degenerate);
    RUN_TEST(storage_window_bounds_negative_size_degenerate);
    RUN_TEST(storage_window_bounds_for_ts_zero_size_invalid);
    RUN_TEST(storage_floor_div_zero_divisor_safe);
    RUN_TEST(storage_floor_div_negative_divisor_safe);

    /* Page tests (9 tests) */
    RUN_TEST(storage_page_builder_single_page);
    RUN_TEST(storage_page_builder_count_zero);
    RUN_TEST(storage_page_builder_null_records_nonzero_count);  /* M-07 fix test */
    RUN_TEST(storage_page_capacity_tiny_target);
    RUN_TEST(storage_page_capacity_zero_target);
    RUN_TEST(storage_page_lower_bound_found);
    RUN_TEST(storage_page_upper_bound);
    RUN_TEST(storage_page_get_record);
    RUN_TEST(storage_page_destroy_null);

    /* Catalog tests (3 tests) */
    RUN_TEST(storage_catalog_init_empty);
    RUN_TEST(storage_catalog_push_single);
    RUN_TEST(storage_catalog_find_first_ge);

    /* Segment tests (14 tests) */
    RUN_TEST(storage_segment_build_l0_records_only);
    RUN_TEST(storage_segment_build_l0_with_tombstones);
    RUN_TEST(storage_segment_build_l0_record_tomb_bounds);
    RUN_TEST(storage_segment_build_l0_tombstone_only);
    RUN_TEST(storage_segment_build_l0_empty_invalid);
    RUN_TEST(storage_segment_build_l0_null_tombstones_invalid);
    RUN_TEST(storage_segment_build_l0_null_records_invalid);
    RUN_TEST(storage_segment_build_l0_null_records_no_tombstones_invalid);
    RUN_TEST(storage_segment_build_l0_unbounded_tombstone);
    RUN_TEST(storage_segment_build_l1);
    RUN_TEST(storage_segment_build_l1_min_below_window_start_einval);
    RUN_TEST(storage_segment_build_l1_max_at_or_above_window_end_einval);
    RUN_TEST(storage_segment_build_l1_exact_window_boundaries_ok);
    RUN_TEST(storage_segment_build_pages_rejects_cross_page_out_of_order);
    RUN_TEST(storage_segment_build_l1_unbounded_mismatch_invalid);
    RUN_TEST(storage_segment_build_l1_unbounded_valid);
    RUN_TEST(storage_segment_refcnt_acquire_release);
    RUN_TEST(storage_segment_tombstones_imm);
    RUN_TEST(storage_segment_l0_bounds_include_tombstones);
    RUN_TEST(storage_segment_l0_bounds_tombstones_extend_max);

    /* Manifest tests (15 tests) */
    RUN_TEST(storage_manifest_create_empty);
    RUN_TEST(storage_manifest_builder_add_l0);
    RUN_TEST(storage_manifest_builder_destroy_resets_lengths);
    RUN_TEST(storage_manifest_builder_rejects_wrong_level);
    RUN_TEST(storage_manifest_builder_rejects_duplicate_adds);
    RUN_TEST(storage_manifest_builder_rejects_add_existing_in_base);
    RUN_TEST(storage_manifest_builder_rejects_add_and_remove_same_segment);
    RUN_TEST(storage_manifest_builder_add_l1_sorted);
    RUN_TEST(storage_manifest_builder_rejects_overlapping_l1);
    RUN_TEST(storage_manifest_builder_l1_adjacent_windows_allowed);
    RUN_TEST(storage_manifest_builder_l1_unbounded_rejects_subsequent);
    RUN_TEST(storage_manifest_builder_remove_l0);
    RUN_TEST(storage_manifest_l1_find_first_overlap);
    RUN_TEST(storage_manifest_l1_find_first_overlap_sparse);
    RUN_TEST(storage_manifest_bounds_cached);
    RUN_TEST(storage_manifest_builder_remove_nonexistent);
    RUN_TEST(storage_manifest_builder_remove_duplicate);

    /* Edge case tests (T-03, T-08) */
    RUN_TEST(storage_segment_build_l0_invalid_tombstone_interval);
    RUN_TEST(storage_segment_build_l0_invalid_tombstone_seq_contract);
    RUN_TEST(storage_segment_build_l0_invalid_tombstone_order_contract);
    RUN_TEST(storage_segment_build_small_page_bytes_clamped);

#ifdef TL_DEBUG
    /* Debug validation tests (5 tests) */
    RUN_TEST(storage_page_validate_correct);
    RUN_TEST(storage_catalog_validate_correct);
    RUN_TEST(storage_segment_validate_l0);
    RUN_TEST(storage_segment_validate_l1);
    RUN_TEST(storage_manifest_validate_correct);
#endif
}
