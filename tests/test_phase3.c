#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_alloc.h"
#include "tl_window.h"
#include "tl_page.h"
#include "tl_segment.h"
#include "tl_manifest.h"

/*===========================================================================
 * Window Mapping Tests
 *===========================================================================*/

TEST_DECLARE(window_default_size) {
    TEST_ASSERT_EQ(TL_WINDOW_1H_S, tl_window_default_size(TL_TIME_S));
    TEST_ASSERT_EQ(TL_WINDOW_1H_MS, tl_window_default_size(TL_TIME_MS));
    TEST_ASSERT_EQ(TL_WINDOW_1H_US, tl_window_default_size(TL_TIME_US));
    TEST_ASSERT_EQ(TL_WINDOW_1H_NS, tl_window_default_size(TL_TIME_NS));
}

TEST_DECLARE(window_id_positive) {
    /* ts = 25, size = 10, origin = 0 => window_id = 2 */
    int64_t id;
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(25, 10, 0, &id));
    TEST_ASSERT_EQ(2, id);
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(5, 10, 0, &id));
    TEST_ASSERT_EQ(0, id);
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(10, 10, 0, &id));
    TEST_ASSERT_EQ(1, id);
}

TEST_DECLARE(window_id_negative) {
    /* Floor division is required for negative timestamps */
    /* ts = -1, size = 10, origin = 0 => floor(-1/10) = -1 */
    int64_t id;
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(-1, 10, 0, &id));
    TEST_ASSERT_EQ(-1, id);
}

TEST_DECLARE(window_id_negative_exact) {
    /* ts = -10, size = 10, origin = 0 => floor(-10/10) = -1 */
    int64_t id;
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(-10, 10, 0, &id));
    TEST_ASSERT_EQ(-1, id);
}

TEST_DECLARE(window_id_negative_past) {
    /* ts = -11, size = 10, origin = 0 => floor(-11/10) = -2 (C would give -1) */
    int64_t id;
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(-11, 10, 0, &id));
    TEST_ASSERT_EQ(-2, id);
}

TEST_DECLARE(window_id_at_origin) {
    int64_t id;
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(0, 10, 0, &id));
    TEST_ASSERT_EQ(0, id);
    TEST_ASSERT_STATUS(TL_OK, tl_window_id_for_ts(100, 10, 100, &id));
    TEST_ASSERT_EQ(0, id);
}

TEST_DECLARE(window_bounds_basic) {
    tl_ts_t start, end;
    bool unbounded;
    tl_window_bounds(2, 10, 0, &start, &end, &unbounded);
    TEST_ASSERT_EQ(20, start);
    TEST_ASSERT_EQ(30, end);
    TEST_ASSERT(!unbounded);
}

TEST_DECLARE(window_bounds_negative_id) {
    tl_ts_t start, end;
    bool unbounded;
    tl_window_bounds(-1, 10, 0, &start, &end, &unbounded);
    TEST_ASSERT_EQ(-10, start);
    TEST_ASSERT_EQ(0, end);
    TEST_ASSERT(!unbounded);
}

TEST_DECLARE(window_bounds_for_ts) {
    tl_ts_t start, end;
    bool unbounded;
    TEST_ASSERT_STATUS(TL_OK, tl_window_bounds_for_ts(25, 10, 0, &start, &end, &unbounded));
    TEST_ASSERT_EQ(20, start);
    TEST_ASSERT_EQ(30, end);
    TEST_ASSERT(!unbounded);
}

TEST_DECLARE(window_contains) {
    TEST_ASSERT(tl_window_contains(20, 30, false, 20));
    TEST_ASSERT(tl_window_contains(20, 30, false, 25));
    TEST_ASSERT(!tl_window_contains(20, 30, false, 30)); /* Half-open: end is exclusive */
    TEST_ASSERT(!tl_window_contains(20, 30, false, 19));
}

TEST_DECLARE(window_contains_unbounded) {
    /* Unbounded windows include everything >= start */
    TEST_ASSERT(tl_window_contains(20, TL_TS_MAX, true, 20));
    TEST_ASSERT(tl_window_contains(20, TL_TS_MAX, true, TL_TS_MAX));
    TEST_ASSERT(!tl_window_contains(20, TL_TS_MAX, true, 19));
}

TEST_DECLARE(window_ts_max_unbounded) {
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

TEST_DECLARE(window_id_overflow_underflow) {
    /*
     * Test TL_EOVERFLOW when ts - window_origin overflows.
     * Case 1: ts near INT64_MAX, origin negative => would overflow
     * Case 2: ts near INT64_MIN, origin positive => would underflow
     */
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

TEST_DECLARE(window_bounds_for_ts_overflow) {
    /*
     * Test TL_EOVERFLOW propagation through tl_window_bounds_for_ts.
     */
    tl_ts_t start, end;
    bool unbounded;

    /* Overflow in window_id computation */
    TEST_ASSERT_STATUS(TL_EOVERFLOW,
        tl_window_bounds_for_ts(INT64_MAX, 1000, INT64_MIN, &start, &end, &unbounded));
}

/*===========================================================================
 * Page Tests
 *===========================================================================*/

TEST_DECLARE(page_builder_single_page) {
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
    TEST_ASSERT_EQ(TL_PAGE_FULLY_LIVE, page->flags);

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(page_builder_count_zero) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    tl_page_t* page = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_page_builder_build(&pb, NULL, 0, &page));
    TEST_ASSERT_NULL(page);

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(page_capacity_tiny_target) {
    /* target_page_bytes < sizeof(tl_page_t) => returns TL_MIN_PAGE_ROWS */
    size_t cap = tl_page_builder_compute_capacity(1);
    TEST_ASSERT_EQ(TL_MIN_PAGE_ROWS, cap);
}

TEST_DECLARE(page_capacity_zero_target) {
    size_t cap = tl_page_builder_compute_capacity(0);
    TEST_ASSERT_EQ(TL_MIN_PAGE_ROWS, cap);
}

TEST_DECLARE(page_lower_bound_found) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    tl_record_t records[5] = {
        {10, 0}, {20, 0}, {30, 0}, {40, 0}, {50, 0}
    };

    tl_page_t* page = NULL;
    tl_page_builder_build(&pb, records, 5, &page);

    TEST_ASSERT_EQ(0, tl_page_lower_bound(page, 5));   /* Before all */
    TEST_ASSERT_EQ(0, tl_page_lower_bound(page, 10));  /* Exact match */
    TEST_ASSERT_EQ(1, tl_page_lower_bound(page, 15));  /* Between */
    TEST_ASSERT_EQ(2, tl_page_lower_bound(page, 30));  /* Exact match */
    TEST_ASSERT_EQ(5, tl_page_lower_bound(page, 100)); /* After all */

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(page_upper_bound) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    /* Records with duplicates: 10, 20, 20, 20, 30 */
    tl_record_t records[5] = {
        {10, 0}, {20, 1}, {20, 2}, {20, 3}, {30, 0}
    };

    tl_page_t* page = NULL;
    tl_page_builder_build(&pb, records, 5, &page);

    TEST_ASSERT_EQ(0, tl_page_upper_bound(page, 5));
    TEST_ASSERT_EQ(1, tl_page_upper_bound(page, 10));
    TEST_ASSERT_EQ(4, tl_page_upper_bound(page, 20)); /* After all 20s */
    TEST_ASSERT_EQ(5, tl_page_upper_bound(page, 30));

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(page_get_record) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_builder_t pb;
    tl_page_builder_init(&pb, &alloc, TL_DEFAULT_TARGET_PAGE_BYTES);

    tl_record_t records[3] = {
        {100, 0xDEAD}, {200, 0xBEEF}, {300, 0xCAFE}
    };

    tl_page_t* page = NULL;
    tl_page_builder_build(&pb, records, 3, &page);

    tl_record_t out;
    tl_page_get_record(page, 1, &out);
    TEST_ASSERT_EQ(200, out.ts);
    TEST_ASSERT_EQ(0xBEEF, out.handle);

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(page_destroy_null) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Should be safe to call on NULL */
    tl_page_destroy(NULL, &alloc);

    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Page Catalog Tests
 *===========================================================================*/

TEST_DECLARE(catalog_init_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_catalog_t cat;
    tl_page_catalog_init(&cat, &alloc);

    TEST_ASSERT_EQ(0, tl_page_catalog_count(&cat));
    TEST_ASSERT_NULL(cat.pages);

    tl_page_catalog_destroy(&cat);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(catalog_push_single) {
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

TEST_DECLARE(catalog_find_first_ge) {
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
 * Segment Tests
 *===========================================================================*/

TEST_DECLARE(segment_build_l0_records_only) {
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

TEST_DECLARE(segment_build_l0_with_tombstones) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[5] = {
        {10, 0}, {20, 0}, {30, 0}, {40, 0}, {50, 0}
    };
    tl_interval_t tombs[1] = {{100, 200, false}};

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

TEST_DECLARE(segment_build_l0_tombstone_only) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_interval_t tombs[1] = {{100, 200, false}};

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

TEST_DECLARE(segment_build_l0_empty_invalid) {
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

TEST_DECLARE(segment_build_l0_unbounded_tombstone) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Unbounded interval [100, +inf) */
    tl_interval_t tombs[1] = {{100, 0, true}};

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

TEST_DECLARE(segment_build_l1) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[5] = {
        {100, 0}, {110, 0}, {120, 0}, {130, 0}, {140, 0}
    };

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_segment_build_l1(&alloc, records, 5,
                                                   TL_DEFAULT_TARGET_PAGE_BYTES,
                                                   100, 200, 1, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    TEST_ASSERT(tl_segment_is_l1(seg));
    TEST_ASSERT_EQ(100, seg->window_start);
    TEST_ASSERT_EQ(200, seg->window_end);
    TEST_ASSERT_NULL(seg->tombstones);

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(segment_refcnt_acquire_release) {
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

TEST_DECLARE(segment_tombstones_imm) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_interval_t tombs[2] = {{10, 20, false}, {30, 40, false}};
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

/*===========================================================================
 * Manifest Tests
 *===========================================================================*/

TEST_DECLARE(manifest_create_empty) {
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

TEST_DECLARE(manifest_builder_add_l0) {
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

TEST_DECLARE(manifest_builder_add_l1_sorted) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create L1 segments with different windows (added in reverse order) */
    tl_record_t r1[2] = {{100, 0}, {150, 0}};
    tl_record_t r2[2] = {{200, 0}, {250, 0}};
    tl_record_t r3[2] = {{0, 0}, {50, 0}};

    tl_segment_t *s1 = NULL, *s2 = NULL, *s3 = NULL;
    tl_segment_build_l1(&alloc, r1, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 100, 200, 1, &s1);
    tl_segment_build_l1(&alloc, r2, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 200, 300, 1, &s2);
    tl_segment_build_l1(&alloc, r3, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 0, 100, 1, &s3);

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

TEST_DECLARE(manifest_builder_remove_l0) {
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

TEST_DECLARE(manifest_l1_find_first_overlap) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create L1 segments: [0,100), [100,200), [200,300) */
    tl_record_t r1[2] = {{10, 0}, {90, 0}};
    tl_record_t r2[2] = {{110, 0}, {190, 0}};
    tl_record_t r3[2] = {{210, 0}, {290, 0}};

    tl_segment_t *s1 = NULL, *s2 = NULL, *s3 = NULL;
    tl_segment_build_l1(&alloc, r1, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 0, 100, 1, &s1);
    tl_segment_build_l1(&alloc, r2, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 100, 200, 1, &s2);
    tl_segment_build_l1(&alloc, r3, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 200, 300, 1, &s3);

    tl_manifest_builder_t mb;
    tl_manifest_builder_init(&mb, &alloc, NULL);
    tl_manifest_builder_add_l1(&mb, s1);
    tl_manifest_builder_add_l1(&mb, s2);
    tl_manifest_builder_add_l1(&mb, s3);
    tl_manifest_t* m = NULL;
    tl_manifest_builder_build(&mb, &m);
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

TEST_DECLARE(manifest_bounds_cached) {
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
 * Edge Case Tests - Manifest Removal Validation
 *===========================================================================*/

TEST_DECLARE(manifest_builder_remove_nonexistent) {
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

TEST_DECLARE(manifest_builder_remove_duplicate) {
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
 * Edge Case Tests - L0 Bounds Cover Tombstones
 *===========================================================================*/

TEST_DECLARE(segment_l0_bounds_include_tombstones) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Records in range [100, 200] */
    tl_record_t records[3] = {{100, 0}, {150, 0}, {200, 0}};

    /* Tombstones in range [50, 80) and [300, 400) - outside records */
    tl_interval_t tombs[2] = {
        {50, 80, false},   /* Earlier than records */
        {300, 400, false}  /* Later than records */
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

TEST_DECLARE(segment_l0_bounds_tombstones_extend_max) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Records in range [100, 200] */
    tl_record_t records[2] = {{100, 0}, {200, 0}};

    /* Unbounded tombstone starting after records */
    tl_interval_t tombs[1] = {{300, 0, true}};  /* [300, +inf) */

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
 * Debug Validation Tests
 *===========================================================================*/

#ifdef TL_DEBUG

TEST_DECLARE(page_validate_correct) {
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

TEST_DECLARE(catalog_validate_correct) {
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

TEST_DECLARE(segment_validate_l0) {
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

TEST_DECLARE(segment_validate_l1) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t records[3] = {{100, 0}, {150, 0}, {199, 0}};
    tl_segment_t* seg = NULL;
    tl_segment_build_l1(&alloc, records, 3, TL_DEFAULT_TARGET_PAGE_BYTES,
                        100, 200, 1, &seg);

    TEST_ASSERT(tl_segment_validate(seg));

    tl_segment_release(seg);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(manifest_validate_correct) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t r1[2] = {{10, 0}, {90, 0}};
    tl_record_t r2[2] = {{110, 0}, {190, 0}};

    tl_segment_t *s1 = NULL, *s2 = NULL;
    tl_segment_build_l1(&alloc, r1, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 0, 100, 1, &s1);
    tl_segment_build_l1(&alloc, r2, 2, TL_DEFAULT_TARGET_PAGE_BYTES, 100, 200, 1, &s2);

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

void run_phase3_tests(void) {
    /* Window tests */
    RUN_TEST(window_default_size);
    RUN_TEST(window_id_positive);
    RUN_TEST(window_id_negative);
    RUN_TEST(window_id_negative_exact);
    RUN_TEST(window_id_negative_past);
    RUN_TEST(window_id_at_origin);
    RUN_TEST(window_bounds_basic);
    RUN_TEST(window_bounds_negative_id);
    RUN_TEST(window_bounds_for_ts);
    RUN_TEST(window_contains);
    RUN_TEST(window_contains_unbounded);
    RUN_TEST(window_ts_max_unbounded);
    RUN_TEST(window_id_overflow_underflow);
    RUN_TEST(window_bounds_for_ts_overflow);

    /* Page tests */
    RUN_TEST(page_builder_single_page);
    RUN_TEST(page_builder_count_zero);
    RUN_TEST(page_capacity_tiny_target);
    RUN_TEST(page_capacity_zero_target);
    RUN_TEST(page_lower_bound_found);
    RUN_TEST(page_upper_bound);
    RUN_TEST(page_get_record);
    RUN_TEST(page_destroy_null);

    /* Catalog tests */
    RUN_TEST(catalog_init_empty);
    RUN_TEST(catalog_push_single);
    RUN_TEST(catalog_find_first_ge);

    /* Segment tests */
    RUN_TEST(segment_build_l0_records_only);
    RUN_TEST(segment_build_l0_with_tombstones);
    RUN_TEST(segment_build_l0_tombstone_only);
    RUN_TEST(segment_build_l0_empty_invalid);
    RUN_TEST(segment_build_l0_unbounded_tombstone);
    RUN_TEST(segment_build_l1);
    RUN_TEST(segment_refcnt_acquire_release);
    RUN_TEST(segment_tombstones_imm);

    /* Manifest tests */
    RUN_TEST(manifest_create_empty);
    RUN_TEST(manifest_builder_add_l0);
    RUN_TEST(manifest_builder_add_l1_sorted);
    RUN_TEST(manifest_builder_remove_l0);
    RUN_TEST(manifest_l1_find_first_overlap);
    RUN_TEST(manifest_bounds_cached);
    RUN_TEST(manifest_builder_remove_nonexistent);
    RUN_TEST(manifest_builder_remove_duplicate);

    /* L0 bounds edge case tests */
    RUN_TEST(segment_l0_bounds_include_tombstones);
    RUN_TEST(segment_l0_bounds_tombstones_extend_max);

#ifdef TL_DEBUG
    /* Debug validation tests */
    RUN_TEST(page_validate_correct);
    RUN_TEST(catalog_validate_correct);
    RUN_TEST(segment_validate_l0);
    RUN_TEST(segment_validate_l1);
    RUN_TEST(manifest_validate_correct);
#endif
}
