/*===========================================================================
 * test_internal_data_structures.c - Internal Data Structure Tests
 *
 * Tests for fundamental data structures:
 * - Record Vector (recvec): Dynamic array of (ts, handle) pairs
 * - Intervals: Tombstone interval set with coalescing
 * - Heap: Min-heap for k-way merge iteration
 *
 * These tests validate the building blocks used by storage,
 * query, and maintenance subsystems.
 *
 * Part of Phase 10: Integration Testing and Hardening
 *
 * Migration Status: COMPLETE (migrated from test_phase2.c)
 * Note: Test names prefixed with "ds_" to avoid conflicts during migration.
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_alloc.h"
#include "internal/tl_recvec.h"
#include "internal/tl_intervals.h"
#include "internal/tl_heap.h"
#include "internal/tl_math.h"

#include <string.h>

static tl_status_t intervals_insert_seq(tl_intervals_t* iv,
                                        tl_ts_t t1,
                                        tl_ts_t t2,
                                        tl_seq_t seq) {
    return tl_intervals_insert(iv, t1, t2, seq);
}

static tl_status_t intervals_insert_unbounded_seq(tl_intervals_t* iv,
                                                  tl_ts_t t1,
                                                  tl_seq_t seq) {
    return tl_intervals_insert_unbounded(iv, t1, seq);
}

static tl_status_t test_intervals_insert(tl_intervals_t* iv,
                                          tl_ts_t t1,
                                          tl_ts_t t2) {
    return tl_intervals_insert(iv, t1, t2, 1);
}

static tl_status_t test_intervals_insert_unbounded(tl_intervals_t* iv,
                                                    tl_ts_t t1) {
    return tl_intervals_insert_unbounded(iv, t1, 1);
}

#define tl_intervals_insert test_intervals_insert
#define tl_intervals_insert_unbounded test_intervals_insert_unbounded

static bool tl_intervals_cursor_is_deleted(tl_intervals_cursor_t* cur, tl_ts_t ts) {
    return tl_intervals_cursor_max_seq(cur, ts) > 0;
}

/*===========================================================================
 * Record Vector Tests (16 tests)
 *===========================================================================*/

TEST_DECLARE(ds_recvec_init_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    TEST_ASSERT_EQ(0, tl_recvec_len(&rv));
    TEST_ASSERT(tl_recvec_is_empty(&rv));
    TEST_ASSERT_NULL(tl_recvec_data(&rv));

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_push_single) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    tl_status_t s = tl_recvec_push(&rv, 100, 0xDEADBEEF);
    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_EQ(1, tl_recvec_len(&rv));

    const tl_record_t* r = tl_recvec_get(&rv, 0);
    TEST_ASSERT_EQ(100, r->ts);
    TEST_ASSERT_EQ(0xDEADBEEF, r->handle);

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_push_growth) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    /* Push enough to trigger growth */
    for (size_t i = 0; i < 1000; i++) {
        tl_status_t s = tl_recvec_push(&rv, (tl_ts_t)i, i);
        TEST_ASSERT_STATUS(TL_OK, s);
    }
    TEST_ASSERT_EQ(1000, tl_recvec_len(&rv));

    /* Verify data */
    for (size_t i = 0; i < 1000; i++) {
        const tl_record_t* r = tl_recvec_get(&rv, i);
        TEST_ASSERT_EQ((tl_ts_t)i, r->ts);
    }

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_lower_bound_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    TEST_ASSERT_EQ(0, tl_recvec_lower_bound(&rv, 50));

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_lower_bound_found) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    /* Push sorted: 10, 20, 30, 40, 50 */
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, 10, 0));
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, 20, 0));
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, 30, 0));
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, 40, 0));
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, 50, 0));

    TEST_ASSERT_EQ(0, tl_recvec_lower_bound(&rv, 5));   /* Before all */
    TEST_ASSERT_EQ(0, tl_recvec_lower_bound(&rv, 10));  /* Exact match */
    TEST_ASSERT_EQ(1, tl_recvec_lower_bound(&rv, 15));  /* Between */
    TEST_ASSERT_EQ(2, tl_recvec_lower_bound(&rv, 30));  /* Exact match */
    TEST_ASSERT_EQ(5, tl_recvec_lower_bound(&rv, 100)); /* After all */

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Math Helper Tests
 *===========================================================================*/

TEST_DECLARE(ds_math_overflow_i64) {
    int64_t out = 0;

    /* Addition */
    TEST_ASSERT(!tl_add_overflow_i64(10, -3, &out));
    TEST_ASSERT_EQ(7, out);
    TEST_ASSERT(tl_add_overflow_i64(INT64_MAX, 1, &out));
    TEST_ASSERT(tl_add_overflow_i64(INT64_MIN, -1, &out));

    /* Subtraction */
    TEST_ASSERT(!tl_sub_overflow_i64(5, 7, &out));
    TEST_ASSERT_EQ(-2, out);
    TEST_ASSERT(tl_sub_overflow_i64(INT64_MIN, 1, &out));
    TEST_ASSERT(tl_sub_overflow_i64(INT64_MAX, -1, &out));

    /* Multiplication */
    TEST_ASSERT(!tl_mul_overflow_i64(6, -7, &out));
    TEST_ASSERT_EQ(-42, out);
    TEST_ASSERT(tl_mul_overflow_i64(INT64_MAX, 2, &out));
    TEST_ASSERT(tl_mul_overflow_i64(INT64_MIN, -1, &out));
    TEST_ASSERT(!tl_mul_overflow_i64(0, INT64_MIN, &out));
    TEST_ASSERT_EQ(0, out);
}

TEST_DECLARE(ds_recvec_upper_bound) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    /* Push with duplicates: 10, 20, 20, 20, 30 */
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, 10, 0));
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, 20, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, 20, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, 30, 0));

    TEST_ASSERT_EQ(0, tl_recvec_upper_bound(&rv, 5));
    TEST_ASSERT_EQ(1, tl_recvec_upper_bound(&rv, 10));
    TEST_ASSERT_EQ(4, tl_recvec_upper_bound(&rv, 20)); /* After all 20s */
    TEST_ASSERT_EQ(5, tl_recvec_upper_bound(&rv, 30));

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_range_bounds) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    /* 10, 20, 30, 40, 50 */
    for (tl_ts_t ts = 10; ts <= 50; ts += 10) {
        TEST_ASSERT_STATUS(TL_OK, tl_recvec_push(&rv, ts, 0));
    }

    size_t lo, hi;

    /* [15, 35) => indices 1..3 (records 20, 30) */
    tl_recvec_range_bounds(&rv, 15, 35, &lo, &hi);
    TEST_ASSERT_EQ(1, lo);
    TEST_ASSERT_EQ(3, hi);

    /* [10, 50) => indices 0..4 */
    tl_recvec_range_bounds(&rv, 10, 50, &lo, &hi);
    TEST_ASSERT_EQ(0, lo);
    TEST_ASSERT_EQ(4, hi);

    /* [100, 200) => empty */
    tl_recvec_range_bounds(&rv, 100, 200, &lo, &hi);
    TEST_ASSERT_EQ(5, lo);
    TEST_ASSERT_EQ(5, hi);

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_insert_middle) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    tl_recvec_push(&rv, 10, 0);
    tl_recvec_push(&rv, 30, 0);

    /* Insert 20 at index 1 */
    tl_status_t s = tl_recvec_insert(&rv, 1, 20, 0);
    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_EQ(3, tl_recvec_len(&rv));

    TEST_ASSERT_EQ(10, tl_recvec_get(&rv, 0)->ts);
    TEST_ASSERT_EQ(20, tl_recvec_get(&rv, 1)->ts);
    TEST_ASSERT_EQ(30, tl_recvec_get(&rv, 2)->ts);

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_clear_and_reuse) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    for (size_t i = 0; i < 100; i++) {
        tl_recvec_push(&rv, (tl_ts_t)i, 0);
    }
    TEST_ASSERT_EQ(100, tl_recvec_len(&rv));

    tl_recvec_clear(&rv);
    TEST_ASSERT_EQ(0, tl_recvec_len(&rv));
    TEST_ASSERT(rv.cap >= 100); /* Capacity preserved */

    /* Reuse */
    tl_recvec_push(&rv, 999, 0);
    TEST_ASSERT_EQ(1, tl_recvec_len(&rv));

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_take_ownership) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    tl_recvec_push(&rv, 100, 42);
    tl_recvec_push(&rv, 200, 43);

    size_t len;
    tl_record_t* arr = tl_recvec_take(&rv, &len);

    TEST_ASSERT_NOT_NULL(arr);
    TEST_ASSERT_EQ(2, len);
    TEST_ASSERT_EQ(100, arr[0].ts);
    TEST_ASSERT_EQ(200, arr[1].ts);

    /* Vector is now empty */
    TEST_ASSERT_EQ(0, tl_recvec_len(&rv));
    TEST_ASSERT_NULL(tl_recvec_data(&rv));

    /* Caller must free */
    tl__free(&alloc, arr);
    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_take_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    size_t len;
    tl_record_t* arr = tl_recvec_take(&rv, &len);

    TEST_ASSERT_NULL(arr);
    TEST_ASSERT_EQ(0, len);

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_reserve_zero) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    /* reserve(0) should be no-op */
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_reserve(&rv, 0));
    TEST_ASSERT_EQ(0, rv.cap);
    TEST_ASSERT_NULL(rv.data);

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_push_n_zero) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    /* push_n with n=0 should be no-op */
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_push_n(&rv, NULL, 0));
    TEST_ASSERT_EQ(0, tl_recvec_len(&rv));

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_insert_invalid_idx) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    tl_recvec_push(&rv, 10, 0);
    TEST_ASSERT_EQ(1, tl_recvec_len(&rv));

    /* idx > len should fail */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_recvec_insert(&rv, 5, 20, 0));
    TEST_ASSERT_EQ(1, tl_recvec_len(&rv)); /* Unchanged */

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_shrink_to_fit_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    /* Add and remove to get capacity without length */
    for (size_t i = 0; i < 100; i++) {
        tl_recvec_push(&rv, (tl_ts_t)i, 0);
    }
    tl_recvec_clear(&rv);
    TEST_ASSERT(rv.cap >= 100);

    /* shrink_to_fit when len=0 should free storage */
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_shrink_to_fit(&rv));
    TEST_ASSERT_EQ(0, rv.cap);
    TEST_ASSERT_NULL(rv.data);

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_recvec_destroy_idempotent) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    tl_recvec_push(&rv, 100, 0);
    tl_recvec_destroy(&rv);

    /* Second destroy should be safe */
    tl_recvec_destroy(&rv);

    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Interval Set Tests (24 tests, 1 debug-only)
 *===========================================================================*/

TEST_DECLARE(ds_intervals_init_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_EQ(0, tl_intervals_len(&iv));
    TEST_ASSERT(tl_intervals_is_empty(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_insert_single) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_status_t s = tl_intervals_insert(&iv, 10, 20);
    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));

    const tl_interval_t* i = tl_intervals_get(&iv, 0);
    TEST_ASSERT_EQ(10, i->start);
    TEST_ASSERT_EQ(20, i->end);
    TEST_ASSERT(!i->end_unbounded);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_insert_empty_is_noop) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* t1 == t2 is a no-op (Write Path LLD Section 3.8) */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 10));
    TEST_ASSERT_EQ(0, tl_intervals_len(&iv)); /* Nothing stored */

    /* t1 > t2 is invalid */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_intervals_insert(&iv, 20, 10));
    TEST_ASSERT_EQ(0, tl_intervals_len(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_coalesce_overlapping) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Insert [10, 30), then [20, 40) => should coalesce to [10, 40) */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 30));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 20, 40));

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(10, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(40, tl_intervals_get(&iv, 0)->end);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_coalesce_adjacent) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* [10, 20) and [20, 30) are adjacent => [10, 30) */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 20, 30));

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(10, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(30, tl_intervals_get(&iv, 0)->end);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_piecewise_max_overlap) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, intervals_insert_seq(&iv, 0, 100, 5));
    TEST_ASSERT_STATUS(TL_OK, intervals_insert_seq(&iv, 50, 200, 10));

    TEST_ASSERT_EQ(2, iv.len);
    TEST_ASSERT_EQ(0, iv.data[0].start);
    TEST_ASSERT_EQ(50, iv.data[0].end);
    TEST_ASSERT_EQ(5, iv.data[0].max_seq);

    TEST_ASSERT_EQ(50, iv.data[1].start);
    TEST_ASSERT_EQ(200, iv.data[1].end);
    TEST_ASSERT_EQ(10, iv.data[1].max_seq);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_max_seq_cursor_mixed) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, intervals_insert_seq(&iv, 0, 100, 5));
    TEST_ASSERT_STATUS(TL_OK, intervals_insert_seq(&iv, 20, 40, 8));

    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, tl_intervals_as_imm(&iv));

    TEST_ASSERT_EQ(5, tl_intervals_cursor_max_seq(&cur, 10));
    TEST_ASSERT_EQ(8, tl_intervals_cursor_max_seq(&cur, 30));
    TEST_ASSERT_EQ(5, tl_intervals_cursor_max_seq(&cur, 50));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_no_coalesce_gap) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* [10, 20) and [30, 40) have gap => remain separate */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 30, 40));

    TEST_ASSERT_EQ(2, tl_intervals_len(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_coalesce_multi) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Three intervals, then one that spans all */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 30, 40));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 50, 60));
    TEST_ASSERT_EQ(3, tl_intervals_len(&iv));

    /* Insert [15, 55) => merges all three into [10, 60) */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 15, 55));
    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(10, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(60, tl_intervals_get(&iv, 0)->end);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_contains_basic) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 30, 40));

    /* In first interval */
    TEST_ASSERT(tl_intervals_contains(&iv, 10));
    TEST_ASSERT(tl_intervals_contains(&iv, 15));
    TEST_ASSERT(!tl_intervals_contains(&iv, 20)); /* Exclusive end */

    /* In gap */
    TEST_ASSERT(!tl_intervals_contains(&iv, 25));

    /* In second interval */
    TEST_ASSERT(tl_intervals_contains(&iv, 30));
    TEST_ASSERT(tl_intervals_contains(&iv, 39));
    TEST_ASSERT(!tl_intervals_contains(&iv, 40));

    /* Outside all */
    TEST_ASSERT(!tl_intervals_contains(&iv, 5));
    TEST_ASSERT(!tl_intervals_contains(&iv, 100));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, intervals_insert_unbounded_seq(&iv, 50, 2));

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT(tl_intervals_get(&iv, 0)->end_unbounded);
    TEST_ASSERT_EQ(2, tl_intervals_get(&iv, 0)->max_seq);

    TEST_ASSERT(!tl_intervals_contains(&iv, 49));
    TEST_ASSERT(tl_intervals_contains(&iv, 50));
    TEST_ASSERT(tl_intervals_contains(&iv, TL_TS_MAX));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_union_basic) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_intervals_t a, b, out;
    tl_intervals_init(&a, &alloc);
    tl_intervals_init(&b, &alloc);
    tl_intervals_init(&out, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&a, 10, 30));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&b, 20, 40));

    tl_status_t s = tl_intervals_union(&out, &a, &b);
    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_EQ(1, tl_intervals_len(&out));
    TEST_ASSERT_EQ(10, tl_intervals_get(&out, 0)->start);
    TEST_ASSERT_EQ(40, tl_intervals_get(&out, 0)->end);

    tl_intervals_destroy(&out);
    tl_intervals_destroy(&b);
    tl_intervals_destroy(&a);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_union_max_seq) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_intervals_t a, b, out;
    tl_intervals_init(&a, &alloc);
    tl_intervals_init(&b, &alloc);
    tl_intervals_init(&out, &alloc);

    TEST_ASSERT_STATUS(TL_OK, intervals_insert_seq(&a, 0, 50, 3));
    TEST_ASSERT_STATUS(TL_OK, intervals_insert_seq(&b, 25, 75, 7));

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_union(&out, &a, &b));
    TEST_ASSERT_EQ(2, tl_intervals_len(&out));
    TEST_ASSERT_EQ(0, tl_intervals_get(&out, 0)->start);
    TEST_ASSERT_EQ(25, tl_intervals_get(&out, 0)->end);
    TEST_ASSERT_EQ(3, tl_intervals_get(&out, 0)->max_seq);
    TEST_ASSERT_EQ(25, tl_intervals_get(&out, 1)->start);
    TEST_ASSERT_EQ(75, tl_intervals_get(&out, 1)->end);
    TEST_ASSERT_EQ(7, tl_intervals_get(&out, 1)->max_seq);

    tl_intervals_destroy(&out);
    tl_intervals_destroy(&b);
    tl_intervals_destroy(&a);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_clip) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 0, 100));
    tl_intervals_clip(&iv, 25, 75);

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(25, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(75, tl_intervals_get(&iv, 0)->end);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_clip_removes_outside) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 30, 40));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 50, 60));

    /* Clip to [25, 55) => removes [10,20), keeps [30,40), clips [50,60) to [50,55) */
    tl_intervals_clip(&iv, 25, 55);

    TEST_ASSERT_EQ(2, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(30, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(40, tl_intervals_get(&iv, 0)->end);
    TEST_ASSERT_EQ(50, tl_intervals_get(&iv, 1)->start);
    TEST_ASSERT_EQ(55, tl_intervals_get(&iv, 1)->end);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

/*---------------------------------------------------------------------------
 * clip_lower tests - Added for coverage (Phase 10)
 *---------------------------------------------------------------------------*/

TEST_DECLARE(ds_intervals_clip_lower_removes_before) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Insert [10, 20), [30, 40), [50, 60) */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 30, 40));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 50, 60));
    TEST_ASSERT_EQ(3, tl_intervals_len(&iv));

    /* clip_lower(35) removes [10,20), truncates [30,40) to [35,40), keeps [50,60) */
    tl_intervals_clip_lower(&iv, 35);

    TEST_ASSERT_EQ(2, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(35, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(40, tl_intervals_get(&iv, 0)->end);
    TEST_ASSERT_EQ(50, tl_intervals_get(&iv, 1)->start);
    TEST_ASSERT_EQ(60, tl_intervals_get(&iv, 1)->end);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_clip_lower_truncates_overlapping) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Insert [10, 50) */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 50));

    /* clip_lower(25) truncates to [25, 50) */
    tl_intervals_clip_lower(&iv, 25);

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(25, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(50, tl_intervals_get(&iv, 0)->end);
    TEST_ASSERT(!tl_intervals_get(&iv, 0)->end_unbounded);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_clip_lower_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Insert bounded [10, 30) and unbounded [50, +inf) */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 30));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert_unbounded(&iv, 50));
    TEST_ASSERT_EQ(2, tl_intervals_len(&iv));

    /* clip_lower(40) removes [10,30), truncates unbounded to [50,+inf) unchanged */
    tl_intervals_clip_lower(&iv, 40);

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(50, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT(tl_intervals_get(&iv, 0)->end_unbounded);

    /* Now test with clip_lower inside unbounded range */
    tl_intervals_clip_lower(&iv, 75);

    /* Unbounded [50, +inf) truncated to [75, +inf) */
    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(75, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT(tl_intervals_get(&iv, 0)->end_unbounded);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_unbounded_merge_with_bounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Insert bounded [10, 30), then overlapping unbounded [20, +inf) */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 30));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert_unbounded(&iv, 20));

    /* Should merge to [10, +inf) */
    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(10, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT(tl_intervals_get(&iv, 0)->end_unbounded);

    /* Verify containment */
    TEST_ASSERT(!tl_intervals_contains(&iv, 9));
    TEST_ASSERT(tl_intervals_contains(&iv, 10));
    TEST_ASSERT(tl_intervals_contains(&iv, TL_TS_MAX));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_unbounded_absorbs_successors) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Insert multiple bounded intervals */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 30, 40));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 50, 60));
    TEST_ASSERT_EQ(3, tl_intervals_len(&iv));

    /* Insert unbounded that overlaps first - should absorb all */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert_unbounded(&iv, 15));

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(10, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT(tl_intervals_get(&iv, 0)->end_unbounded);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_union_with_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_intervals_t a, b, out;
    tl_intervals_init(&a, &alloc);
    tl_intervals_init(&b, &alloc);
    tl_intervals_init(&out, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&a, 10, 30));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert_unbounded(&b, 20));

    tl_status_t s = tl_intervals_union(&out, &a, &b);
    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_EQ(1, tl_intervals_len(&out));
    TEST_ASSERT_EQ(10, tl_intervals_get(&out, 0)->start);
    TEST_ASSERT(tl_intervals_get(&out, 0)->end_unbounded);

    tl_intervals_destroy(&out);
    tl_intervals_destroy(&b);
    tl_intervals_destroy(&a);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_clip_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert_unbounded(&iv, 50));
    tl_intervals_clip(&iv, 25, 75);

    /* Unbounded [50, +inf) clipped to [25, 75) => [50, 75) bounded */
    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(50, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(75, tl_intervals_get(&iv, 0)->end);
    TEST_ASSERT(!tl_intervals_get(&iv, 0)->end_unbounded);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_covered_span_bounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 30)); /* span = 20 */
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 50, 70)); /* span = 20 */

    TEST_ASSERT_EQ(40, tl_intervals_covered_span(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_covered_span_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 30));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert_unbounded(&iv, 50));

    /* Unbounded => returns TL_TS_MAX (saturated) */
    TEST_ASSERT_EQ(TL_TS_MAX, tl_intervals_covered_span(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_cursor_basic) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 30, 40));

    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, tl_intervals_as_imm(&iv));

    /* Before first interval */
    TEST_ASSERT(!tl_intervals_cursor_is_deleted(&cur, 5));
    /* In first interval */
    TEST_ASSERT(tl_intervals_cursor_is_deleted(&cur, 10));
    TEST_ASSERT(tl_intervals_cursor_is_deleted(&cur, 15));
    /* Between intervals */
    TEST_ASSERT(!tl_intervals_cursor_is_deleted(&cur, 25));
    /* In second interval */
    TEST_ASSERT(tl_intervals_cursor_is_deleted(&cur, 35));
    /* After all */
    TEST_ASSERT(!tl_intervals_cursor_is_deleted(&cur, 50));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_cursor_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert_unbounded(&iv, 50));

    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, tl_intervals_as_imm(&iv));

    TEST_ASSERT(!tl_intervals_cursor_is_deleted(&cur, 49));
    TEST_ASSERT(tl_intervals_cursor_is_deleted(&cur, 50));
    TEST_ASSERT(tl_intervals_cursor_is_deleted(&cur, TL_TS_MAX));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_cursor_skip_to) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 30));

    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, tl_intervals_as_imm(&iv));

    tl_ts_t out;

    /* Not covered - returns ts unchanged */
    TEST_ASSERT(tl_intervals_cursor_skip_to(&cur, 5, &out));
    TEST_ASSERT_EQ(5, out);

    /* Covered - returns end of interval */
    TEST_ASSERT(tl_intervals_cursor_skip_to(&cur, 15, &out));
    TEST_ASSERT_EQ(30, out);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_cursor_skip_to_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert_unbounded(&iv, 50));

    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, tl_intervals_as_imm(&iv));

    tl_ts_t out;

    /* Not covered */
    TEST_ASSERT(tl_intervals_cursor_skip_to(&cur, 40, &out));
    TEST_ASSERT_EQ(40, out);

    /* Covered by unbounded - returns false (no more uncovered timestamps) */
    TEST_ASSERT(!tl_intervals_cursor_skip_to(&cur, 60, &out));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_intervals_destroy_idempotent) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 20));
    tl_intervals_destroy(&iv);

    /* Second destroy should be safe */
    tl_intervals_destroy(&iv);

    tl__alloc_destroy(&alloc);
}

#ifdef TL_DEBUG
TEST_DECLARE(ds_intervals_validate_correct) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 10, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_intervals_insert(&iv, 30, 40));

    TEST_ASSERT(tl_intervals_validate(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}
#endif

/*===========================================================================
 * Min-Heap Tests (11 tests)
 *===========================================================================*/

TEST_DECLARE(ds_heap_init_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    TEST_ASSERT_EQ(0, tl_heap_len(&h));
    TEST_ASSERT(tl_heap_is_empty(&h));
    TEST_ASSERT_NULL(tl_heap_peek(&h));

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_heap_push_pop_single) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    tl_heap_entry_t e = { .ts = 100, .tie_break_key = 0, .handle = 42, .iter = NULL };
    TEST_ASSERT_STATUS(TL_OK, tl_heap_push(&h, &e));
    TEST_ASSERT_EQ(1, tl_heap_len(&h));

    const tl_heap_entry_t* top = tl_heap_peek(&h);
    TEST_ASSERT_NOT_NULL(top);
    TEST_ASSERT_EQ(100, top->ts);

    tl_heap_entry_t out;
    TEST_ASSERT_STATUS(TL_OK, tl_heap_pop(&h, &out));
    TEST_ASSERT_EQ(100, out.ts);
    TEST_ASSERT_EQ(42, out.handle);
    TEST_ASSERT(tl_heap_is_empty(&h));

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_heap_pop_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    tl_heap_entry_t out;
    TEST_ASSERT_STATUS(TL_EOF, tl_heap_pop(&h, &out));

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_heap_ordering) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    /* Push in reverse order */
    tl_heap_entry_t e;
    e.iter = NULL;
    e.tie_break_key = 0;
    for (tl_ts_t ts = 50; ts >= 10; ts -= 10) {
        e.ts = ts;
        e.handle = (tl_handle_t)ts;
        TEST_ASSERT_STATUS(TL_OK, tl_heap_push(&h, &e));
    }
    TEST_ASSERT_EQ(5, tl_heap_len(&h));

    /* Pop should be in order */
    tl_heap_entry_t out;
    for (tl_ts_t expected = 10; expected <= 50; expected += 10) {
        TEST_ASSERT_STATUS(TL_OK, tl_heap_pop(&h, &out));
        TEST_ASSERT_EQ(expected, out.ts);
    }
    TEST_ASSERT(tl_heap_is_empty(&h));

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_heap_tie_break_by_component) {
    /*
     * NOTE: This test verifies a DOCUMENTED INVARIANT, not an implementation
     * detail. The K-way merge relies on deterministic tie-breaking by
     * tie_break_key to ensure stable, reproducible iteration order when
     * multiple components have records at the same timestamp.
     *
     * If tie-breaking order changes, update both the implementation AND
     * this test intentionally - don't just remove the test.
     */
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    /* Same ts, different tie_break_key */
    tl_heap_entry_t e1 = { .ts = 100, .tie_break_key = 5, .handle = 1, .iter = NULL };
    tl_heap_entry_t e2 = { .ts = 100, .tie_break_key = 2, .handle = 2, .iter = NULL };
    tl_heap_entry_t e3 = { .ts = 100, .tie_break_key = 8, .handle = 3, .iter = NULL };

    TEST_ASSERT_STATUS(TL_OK, tl_heap_push(&h, &e1));
    TEST_ASSERT_STATUS(TL_OK, tl_heap_push(&h, &e2));
    TEST_ASSERT_STATUS(TL_OK, tl_heap_push(&h, &e3));

    /* Should pop in ascending tie_break_key order (documented tie-breaker) */
    tl_heap_entry_t out;
    TEST_ASSERT_STATUS(TL_OK, tl_heap_pop(&h, &out));
    TEST_ASSERT_EQ(2, out.tie_break_key);
    TEST_ASSERT_STATUS(TL_OK, tl_heap_pop(&h, &out));
    TEST_ASSERT_EQ(5, out.tie_break_key);
    TEST_ASSERT_STATUS(TL_OK, tl_heap_pop(&h, &out));
    TEST_ASSERT_EQ(8, out.tie_break_key);

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_heap_build_heapify) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    tl_heap_entry_t entries[5] = {
        { .ts = 30, .tie_break_key = 0, .handle = 0, .iter = NULL },
        { .ts = 10, .tie_break_key = 1, .handle = 0, .iter = NULL },
        { .ts = 50, .tie_break_key = 2, .handle = 0, .iter = NULL },
        { .ts = 20, .tie_break_key = 3, .handle = 0, .iter = NULL },
        { .ts = 40, .tie_break_key = 4, .handle = 0, .iter = NULL },
    };

    TEST_ASSERT_STATUS(TL_OK, tl_heap_build(&h, entries, 5));
    TEST_ASSERT_EQ(5, tl_heap_len(&h));

    /* Verify min is 10 */
    TEST_ASSERT_EQ(10, tl_heap_peek(&h)->ts);

    /* Pop all and verify order */
    tl_heap_entry_t out;
    tl_ts_t prev = INT64_MIN;
    while (tl_heap_pop(&h, &out) == TL_OK) {
        TEST_ASSERT(out.ts >= prev);
        prev = out.ts;
    }

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_heap_replace_top) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    tl_heap_entry_t e;
    e.iter = NULL;
    e.tie_break_key = 0;
    e.handle = 0;
    for (tl_ts_t ts = 10; ts <= 50; ts += 10) {
        e.ts = ts;
        TEST_ASSERT_STATUS(TL_OK, tl_heap_push(&h, &e));
    }

    /* Replace top (10) with 25 */
    tl_heap_entry_t new_top = { .ts = 25, .tie_break_key = 0, .handle = 0, .iter = NULL };
    tl_heap_replace_top(&h, &new_top);

    /* New min should be 20 */
    TEST_ASSERT_EQ(20, tl_heap_peek(&h)->ts);

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_heap_stress) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    /* Push 1000 entries in pseudo-random order */
    tl_heap_entry_t e;
    e.iter = NULL;
    e.tie_break_key = 0;
    for (int i = 0; i < 1000; i++) {
        /* Simple pseudo-random: (i * 7 + 13) % 1000 */
        e.ts = (tl_ts_t)((i * 7 + 13) % 1000);
        e.handle = (tl_handle_t)i;
        TEST_ASSERT_STATUS(TL_OK, tl_heap_push(&h, &e));
    }

    TEST_ASSERT_EQ(1000, tl_heap_len(&h));

    /* Pop all and verify sorted */
    tl_heap_entry_t out;
    tl_ts_t prev = INT64_MIN;
    size_t count = 0;
    while (tl_heap_pop(&h, &out) == TL_OK) {
        TEST_ASSERT(out.ts >= prev);
        prev = out.ts;
        count++;
    }
    TEST_ASSERT_EQ(1000, count);

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_heap_build_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    /* Build with n=0 should produce empty heap */
    TEST_ASSERT_STATUS(TL_OK, tl_heap_build(&h, NULL, 0));
    TEST_ASSERT(tl_heap_is_empty(&h));
    TEST_ASSERT_NULL(tl_heap_peek(&h));

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_heap_destroy_idempotent) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    tl_heap_entry_t e = { .ts = 100, .tie_break_key = 0, .handle = 0, .iter = NULL };
    tl_heap_push(&h, &e);
    tl_heap_destroy(&h);

    /* Second destroy should be safe */
    tl_heap_destroy(&h);

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(ds_heap_replace_top_becomes_smallest) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    /* Heap with entries: 20, 30, 40 */
    tl_heap_entry_t e;
    e.iter = NULL;
    e.tie_break_key = 0;
    e.handle = 0;
    for (tl_ts_t ts = 20; ts <= 40; ts += 10) {
        e.ts = ts;
        tl_heap_push(&h, &e);
    }

    /* Replace top (20) with 5 - new entry becomes smallest */
    tl_heap_entry_t new_top = { .ts = 5, .tie_break_key = 0, .handle = 0, .iter = NULL };
    tl_heap_replace_top(&h, &new_top);

    TEST_ASSERT_EQ(5, tl_heap_peek(&h)->ts);

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_internal_data_structures_tests(void) {
    /* Record Vector tests (16 tests) */
    RUN_TEST(ds_recvec_init_empty);
    RUN_TEST(ds_recvec_push_single);
    RUN_TEST(ds_recvec_push_growth);
    RUN_TEST(ds_recvec_lower_bound_empty);
    RUN_TEST(ds_recvec_lower_bound_found);
    RUN_TEST(ds_recvec_upper_bound);
    RUN_TEST(ds_recvec_range_bounds);
    RUN_TEST(ds_recvec_insert_middle);
    RUN_TEST(ds_recvec_clear_and_reuse);
    RUN_TEST(ds_recvec_take_ownership);
    RUN_TEST(ds_recvec_take_empty);
    RUN_TEST(ds_recvec_reserve_zero);
    RUN_TEST(ds_recvec_push_n_zero);
    RUN_TEST(ds_recvec_insert_invalid_idx);
    RUN_TEST(ds_recvec_shrink_to_fit_empty);
    RUN_TEST(ds_recvec_destroy_idempotent);

    /* Math helper tests */
    RUN_TEST(ds_math_overflow_i64);

    /* Interval Set tests (30 tests, 1 debug-only) */
    RUN_TEST(ds_intervals_init_empty);
    RUN_TEST(ds_intervals_insert_single);
    RUN_TEST(ds_intervals_insert_empty_is_noop);
    RUN_TEST(ds_intervals_coalesce_overlapping);
    RUN_TEST(ds_intervals_coalesce_adjacent);
    RUN_TEST(ds_intervals_piecewise_max_overlap);
    RUN_TEST(ds_intervals_max_seq_cursor_mixed);
    RUN_TEST(ds_intervals_no_coalesce_gap);
    RUN_TEST(ds_intervals_coalesce_multi);
    RUN_TEST(ds_intervals_contains_basic);
    RUN_TEST(ds_intervals_unbounded);
    RUN_TEST(ds_intervals_union_basic);
    RUN_TEST(ds_intervals_union_max_seq);
    RUN_TEST(ds_intervals_clip);
    RUN_TEST(ds_intervals_clip_removes_outside);
    RUN_TEST(ds_intervals_clip_lower_removes_before);
    RUN_TEST(ds_intervals_clip_lower_truncates_overlapping);
    RUN_TEST(ds_intervals_clip_lower_unbounded);
    RUN_TEST(ds_intervals_unbounded_merge_with_bounded);
    RUN_TEST(ds_intervals_unbounded_absorbs_successors);
    RUN_TEST(ds_intervals_union_with_unbounded);
    RUN_TEST(ds_intervals_clip_unbounded);
    RUN_TEST(ds_intervals_covered_span_bounded);
    RUN_TEST(ds_intervals_covered_span_unbounded);
    RUN_TEST(ds_intervals_cursor_basic);
    RUN_TEST(ds_intervals_cursor_unbounded);
    RUN_TEST(ds_intervals_cursor_skip_to);
    RUN_TEST(ds_intervals_cursor_skip_to_unbounded);
    RUN_TEST(ds_intervals_destroy_idempotent);
#ifdef TL_DEBUG
    RUN_TEST(ds_intervals_validate_correct);
#endif

    /* Min-Heap tests (11 tests) */
    RUN_TEST(ds_heap_init_empty);
    RUN_TEST(ds_heap_push_pop_single);
    RUN_TEST(ds_heap_pop_empty);
    RUN_TEST(ds_heap_ordering);
    RUN_TEST(ds_heap_tie_break_by_component);
    RUN_TEST(ds_heap_build_heapify);
    RUN_TEST(ds_heap_replace_top);
    RUN_TEST(ds_heap_stress);
    RUN_TEST(ds_heap_build_empty);
    RUN_TEST(ds_heap_destroy_idempotent);
    RUN_TEST(ds_heap_replace_top_becomes_smallest);

    /* Total: 54 tests in release, 55 in debug */
}
