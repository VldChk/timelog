#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_alloc.h"
#include "internal/tl_recvec.h"
#include "internal/tl_intervals.h"
#include "internal/tl_heap.h"

/*===========================================================================
 * Record Vector Tests
 *===========================================================================*/

TEST_DECLARE(recvec_init_empty) {
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

TEST_DECLARE(recvec_push_single) {
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

TEST_DECLARE(recvec_push_growth) {
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

TEST_DECLARE(recvec_lower_bound_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    TEST_ASSERT_EQ(0, tl_recvec_lower_bound(&rv, 50));

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(recvec_lower_bound_found) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    /* Push sorted: 10, 20, 30, 40, 50 */
    tl_recvec_push(&rv, 10, 0);
    tl_recvec_push(&rv, 20, 0);
    tl_recvec_push(&rv, 30, 0);
    tl_recvec_push(&rv, 40, 0);
    tl_recvec_push(&rv, 50, 0);

    TEST_ASSERT_EQ(0, tl_recvec_lower_bound(&rv, 5));   /* Before all */
    TEST_ASSERT_EQ(0, tl_recvec_lower_bound(&rv, 10));  /* Exact match */
    TEST_ASSERT_EQ(1, tl_recvec_lower_bound(&rv, 15));  /* Between */
    TEST_ASSERT_EQ(2, tl_recvec_lower_bound(&rv, 30));  /* Exact match */
    TEST_ASSERT_EQ(5, tl_recvec_lower_bound(&rv, 100)); /* After all */

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(recvec_upper_bound) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    /* Push with duplicates: 10, 20, 20, 20, 30 */
    tl_recvec_push(&rv, 10, 0);
    tl_recvec_push(&rv, 20, 1);
    tl_recvec_push(&rv, 20, 2);
    tl_recvec_push(&rv, 20, 3);
    tl_recvec_push(&rv, 30, 0);

    TEST_ASSERT_EQ(0, tl_recvec_upper_bound(&rv, 5));
    TEST_ASSERT_EQ(1, tl_recvec_upper_bound(&rv, 10));
    TEST_ASSERT_EQ(4, tl_recvec_upper_bound(&rv, 20)); /* After all 20s */
    TEST_ASSERT_EQ(5, tl_recvec_upper_bound(&rv, 30));

    tl_recvec_destroy(&rv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(recvec_range_bounds) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_recvec_t rv;
    tl_recvec_init(&rv, &alloc);

    /* 10, 20, 30, 40, 50 */
    for (tl_ts_t ts = 10; ts <= 50; ts += 10) {
        tl_recvec_push(&rv, ts, 0);
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

TEST_DECLARE(recvec_insert_middle) {
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

TEST_DECLARE(recvec_clear_and_reuse) {
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

TEST_DECLARE(recvec_take_ownership) {
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

TEST_DECLARE(recvec_take_empty) {
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

TEST_DECLARE(recvec_reserve_zero) {
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

TEST_DECLARE(recvec_push_n_zero) {
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

TEST_DECLARE(recvec_insert_invalid_idx) {
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

TEST_DECLARE(recvec_shrink_to_fit_empty) {
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

TEST_DECLARE(recvec_destroy_idempotent) {
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
 * Interval Set Tests
 *===========================================================================*/

TEST_DECLARE(intervals_init_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    TEST_ASSERT_EQ(0, tl_intervals_len(&iv));
    TEST_ASSERT(tl_intervals_is_empty(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_insert_single) {
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

TEST_DECLARE(intervals_insert_empty_is_noop) {
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

TEST_DECLARE(intervals_coalesce_overlapping) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Insert [10, 30), then [20, 40) => should coalesce to [10, 40) */
    tl_intervals_insert(&iv, 10, 30);
    tl_intervals_insert(&iv, 20, 40);

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(10, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(40, tl_intervals_get(&iv, 0)->end);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_coalesce_adjacent) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* [10, 20) and [20, 30) are adjacent => [10, 30) */
    tl_intervals_insert(&iv, 10, 20);
    tl_intervals_insert(&iv, 20, 30);

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(10, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(30, tl_intervals_get(&iv, 0)->end);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_no_coalesce_gap) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* [10, 20) and [30, 40) have gap => remain separate */
    tl_intervals_insert(&iv, 10, 20);
    tl_intervals_insert(&iv, 30, 40);

    TEST_ASSERT_EQ(2, tl_intervals_len(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_coalesce_multi) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Three intervals, then one that spans all */
    tl_intervals_insert(&iv, 10, 20);
    tl_intervals_insert(&iv, 30, 40);
    tl_intervals_insert(&iv, 50, 60);
    TEST_ASSERT_EQ(3, tl_intervals_len(&iv));

    /* Insert [15, 55) => merges all three into [10, 60) */
    tl_intervals_insert(&iv, 15, 55);
    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(10, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(60, tl_intervals_get(&iv, 0)->end);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_contains_basic) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert(&iv, 10, 20);
    tl_intervals_insert(&iv, 30, 40);

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

TEST_DECLARE(intervals_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert_unbounded(&iv, 50);

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT(tl_intervals_get(&iv, 0)->end_unbounded);

    TEST_ASSERT(!tl_intervals_contains(&iv, 49));
    TEST_ASSERT(tl_intervals_contains(&iv, 50));
    TEST_ASSERT(tl_intervals_contains(&iv, INT64_MAX));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_union_basic) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_intervals_t a, b, out;
    tl_intervals_init(&a, &alloc);
    tl_intervals_init(&b, &alloc);
    tl_intervals_init(&out, &alloc);

    tl_intervals_insert(&a, 10, 30);
    tl_intervals_insert(&b, 20, 40);

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

TEST_DECLARE(intervals_clip) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert(&iv, 0, 100);
    tl_intervals_clip(&iv, 25, 75);

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(25, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(75, tl_intervals_get(&iv, 0)->end);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_clip_removes_outside) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert(&iv, 10, 20);
    tl_intervals_insert(&iv, 30, 40);
    tl_intervals_insert(&iv, 50, 60);

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

TEST_DECLARE(intervals_unbounded_merge_with_bounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Insert bounded [10, 30), then overlapping unbounded [20, +inf) */
    tl_intervals_insert(&iv, 10, 30);
    tl_intervals_insert_unbounded(&iv, 20);

    /* Should merge to [10, +inf) */
    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(10, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT(tl_intervals_get(&iv, 0)->end_unbounded);

    /* Verify containment */
    TEST_ASSERT(!tl_intervals_contains(&iv, 9));
    TEST_ASSERT(tl_intervals_contains(&iv, 10));
    TEST_ASSERT(tl_intervals_contains(&iv, INT64_MAX));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_unbounded_absorbs_successors) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    /* Insert multiple bounded intervals */
    tl_intervals_insert(&iv, 10, 20);
    tl_intervals_insert(&iv, 30, 40);
    tl_intervals_insert(&iv, 50, 60);
    TEST_ASSERT_EQ(3, tl_intervals_len(&iv));

    /* Insert unbounded that overlaps first - should absorb all */
    tl_intervals_insert_unbounded(&iv, 15);

    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(10, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT(tl_intervals_get(&iv, 0)->end_unbounded);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_union_with_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_intervals_t a, b, out;
    tl_intervals_init(&a, &alloc);
    tl_intervals_init(&b, &alloc);
    tl_intervals_init(&out, &alloc);

    tl_intervals_insert(&a, 10, 30);
    tl_intervals_insert_unbounded(&b, 20);

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

TEST_DECLARE(intervals_clip_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert_unbounded(&iv, 50);
    tl_intervals_clip(&iv, 25, 75);

    /* Unbounded [50, +inf) clipped to [25, 75) => [50, 75) bounded */
    TEST_ASSERT_EQ(1, tl_intervals_len(&iv));
    TEST_ASSERT_EQ(50, tl_intervals_get(&iv, 0)->start);
    TEST_ASSERT_EQ(75, tl_intervals_get(&iv, 0)->end);
    TEST_ASSERT(!tl_intervals_get(&iv, 0)->end_unbounded);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_covered_span_bounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert(&iv, 10, 30); /* span = 20 */
    tl_intervals_insert(&iv, 50, 70); /* span = 20 */

    TEST_ASSERT_EQ(40, tl_intervals_covered_span(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_covered_span_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert(&iv, 10, 30);
    tl_intervals_insert_unbounded(&iv, 50);

    /* Unbounded => returns TL_TS_MAX (saturated) */
    TEST_ASSERT_EQ(TL_TS_MAX, tl_intervals_covered_span(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_cursor_basic) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert(&iv, 10, 20);
    tl_intervals_insert(&iv, 30, 40);

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

TEST_DECLARE(intervals_cursor_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert_unbounded(&iv, 50);

    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, tl_intervals_as_imm(&iv));

    TEST_ASSERT(!tl_intervals_cursor_is_deleted(&cur, 49));
    TEST_ASSERT(tl_intervals_cursor_is_deleted(&cur, 50));
    TEST_ASSERT(tl_intervals_cursor_is_deleted(&cur, INT64_MAX));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_cursor_skip_to) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert(&iv, 10, 30);

    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, tl_intervals_as_imm(&iv));

    /* Not covered - returns ts unchanged */
    TEST_ASSERT_EQ(5, tl_intervals_cursor_skip_to(&cur, 5));

    /* Covered - returns end of interval */
    TEST_ASSERT_EQ(30, tl_intervals_cursor_skip_to(&cur, 15));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_cursor_skip_to_unbounded) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert_unbounded(&iv, 50);

    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, tl_intervals_as_imm(&iv));

    /* Not covered */
    TEST_ASSERT_EQ(40, tl_intervals_cursor_skip_to(&cur, 40));

    /* Covered by unbounded - returns TL_TS_MAX as SENTINEL */
    tl_ts_t skip_result = tl_intervals_cursor_skip_to(&cur, 60);
    TEST_ASSERT_EQ(TL_TS_MAX, skip_result);

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(intervals_destroy_idempotent) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert(&iv, 10, 20);
    tl_intervals_destroy(&iv);

    /* Second destroy should be safe */
    tl_intervals_destroy(&iv);

    tl__alloc_destroy(&alloc);
}

#ifdef TL_DEBUG
TEST_DECLARE(intervals_validate_correct) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    tl_intervals_insert(&iv, 10, 20);
    tl_intervals_insert(&iv, 30, 40);

    TEST_ASSERT(tl_intervals_validate(&iv));

    tl_intervals_destroy(&iv);
    tl__alloc_destroy(&alloc);
}
#endif

/*===========================================================================
 * Min-Heap Tests
 *===========================================================================*/

TEST_DECLARE(heap_init_empty) {
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

TEST_DECLARE(heap_push_pop_single) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    tl_heap_entry_t e = { .ts = 100, .component_id = 0, .handle = 42, .iter = NULL };
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

TEST_DECLARE(heap_pop_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    tl_heap_entry_t out;
    TEST_ASSERT_STATUS(TL_EOF, tl_heap_pop(&h, &out));

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(heap_ordering) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    /* Push in reverse order */
    tl_heap_entry_t e;
    e.iter = NULL;
    e.component_id = 0;
    for (tl_ts_t ts = 50; ts >= 10; ts -= 10) {
        e.ts = ts;
        e.handle = (tl_handle_t)ts;
        tl_heap_push(&h, &e);
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

TEST_DECLARE(heap_tie_break_by_component) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    /* Same ts, different component_id */
    tl_heap_entry_t e1 = { .ts = 100, .component_id = 5, .handle = 1, .iter = NULL };
    tl_heap_entry_t e2 = { .ts = 100, .component_id = 2, .handle = 2, .iter = NULL };
    tl_heap_entry_t e3 = { .ts = 100, .component_id = 8, .handle = 3, .iter = NULL };

    tl_heap_push(&h, &e1);
    tl_heap_push(&h, &e2);
    tl_heap_push(&h, &e3);

    /* Should pop in component_id order */
    tl_heap_entry_t out;
    tl_heap_pop(&h, &out);
    TEST_ASSERT_EQ(2, out.component_id);
    tl_heap_pop(&h, &out);
    TEST_ASSERT_EQ(5, out.component_id);
    tl_heap_pop(&h, &out);
    TEST_ASSERT_EQ(8, out.component_id);

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(heap_build_heapify) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    tl_heap_entry_t entries[5] = {
        { .ts = 30, .component_id = 0, .handle = 0, .iter = NULL },
        { .ts = 10, .component_id = 1, .handle = 0, .iter = NULL },
        { .ts = 50, .component_id = 2, .handle = 0, .iter = NULL },
        { .ts = 20, .component_id = 3, .handle = 0, .iter = NULL },
        { .ts = 40, .component_id = 4, .handle = 0, .iter = NULL },
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

TEST_DECLARE(heap_replace_top) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    tl_heap_entry_t e;
    e.iter = NULL;
    e.component_id = 0;
    e.handle = 0;
    for (tl_ts_t ts = 10; ts <= 50; ts += 10) {
        e.ts = ts;
        tl_heap_push(&h, &e);
    }

    /* Replace top (10) with 25 */
    tl_heap_entry_t new_top = { .ts = 25, .component_id = 0, .handle = 0, .iter = NULL };
    tl_heap_replace_top(&h, &new_top);

    /* New min should be 20 */
    TEST_ASSERT_EQ(20, tl_heap_peek(&h)->ts);

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(heap_stress) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    /* Push 1000 entries in pseudo-random order */
    tl_heap_entry_t e;
    e.iter = NULL;
    e.component_id = 0;
    for (int i = 0; i < 1000; i++) {
        /* Simple pseudo-random: (i * 7 + 13) % 1000 */
        e.ts = (tl_ts_t)((i * 7 + 13) % 1000);
        e.handle = (tl_handle_t)i;
        tl_heap_push(&h, &e);
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

TEST_DECLARE(heap_build_empty) {
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

TEST_DECLARE(heap_destroy_idempotent) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    tl_heap_entry_t e = { .ts = 100, .component_id = 0, .handle = 0, .iter = NULL };
    tl_heap_push(&h, &e);
    tl_heap_destroy(&h);

    /* Second destroy should be safe */
    tl_heap_destroy(&h);

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(heap_replace_top_becomes_smallest) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);
    tl_heap_t h;
    tl_heap_init(&h, &alloc);

    /* Heap with entries: 20, 30, 40 */
    tl_heap_entry_t e;
    e.iter = NULL;
    e.component_id = 0;
    e.handle = 0;
    for (tl_ts_t ts = 20; ts <= 40; ts += 10) {
        e.ts = ts;
        tl_heap_push(&h, &e);
    }

    /* Replace top (20) with 5 - new entry becomes smallest */
    tl_heap_entry_t new_top = { .ts = 5, .component_id = 0, .handle = 0, .iter = NULL };
    tl_heap_replace_top(&h, &new_top);

    TEST_ASSERT_EQ(5, tl_heap_peek(&h)->ts);

    tl_heap_destroy(&h);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_phase2_tests(void) {
    /* Record Vector tests */
    RUN_TEST(recvec_init_empty);
    RUN_TEST(recvec_push_single);
    RUN_TEST(recvec_push_growth);
    RUN_TEST(recvec_lower_bound_empty);
    RUN_TEST(recvec_lower_bound_found);
    RUN_TEST(recvec_upper_bound);
    RUN_TEST(recvec_range_bounds);
    RUN_TEST(recvec_insert_middle);
    RUN_TEST(recvec_clear_and_reuse);
    RUN_TEST(recvec_take_ownership);
    RUN_TEST(recvec_take_empty);
    RUN_TEST(recvec_reserve_zero);
    RUN_TEST(recvec_push_n_zero);
    RUN_TEST(recvec_insert_invalid_idx);
    RUN_TEST(recvec_shrink_to_fit_empty);
    RUN_TEST(recvec_destroy_idempotent);

    /* Interval Set tests */
    RUN_TEST(intervals_init_empty);
    RUN_TEST(intervals_insert_single);
    RUN_TEST(intervals_insert_empty_is_noop);
    RUN_TEST(intervals_coalesce_overlapping);
    RUN_TEST(intervals_coalesce_adjacent);
    RUN_TEST(intervals_no_coalesce_gap);
    RUN_TEST(intervals_coalesce_multi);
    RUN_TEST(intervals_contains_basic);
    RUN_TEST(intervals_unbounded);
    RUN_TEST(intervals_union_basic);
    RUN_TEST(intervals_clip);
    RUN_TEST(intervals_clip_removes_outside);
    RUN_TEST(intervals_unbounded_merge_with_bounded);
    RUN_TEST(intervals_unbounded_absorbs_successors);
    RUN_TEST(intervals_union_with_unbounded);
    RUN_TEST(intervals_clip_unbounded);
    RUN_TEST(intervals_covered_span_bounded);
    RUN_TEST(intervals_covered_span_unbounded);
    RUN_TEST(intervals_cursor_basic);
    RUN_TEST(intervals_cursor_unbounded);
    RUN_TEST(intervals_cursor_skip_to);
    RUN_TEST(intervals_cursor_skip_to_unbounded);
    RUN_TEST(intervals_destroy_idempotent);
#ifdef TL_DEBUG
    RUN_TEST(intervals_validate_correct);
#endif

    /* Min-Heap tests */
    RUN_TEST(heap_init_empty);
    RUN_TEST(heap_push_pop_single);
    RUN_TEST(heap_pop_empty);
    RUN_TEST(heap_ordering);
    RUN_TEST(heap_tie_break_by_component);
    RUN_TEST(heap_build_heapify);
    RUN_TEST(heap_replace_top);
    RUN_TEST(heap_stress);
    RUN_TEST(heap_build_empty);
    RUN_TEST(heap_destroy_idempotent);
    RUN_TEST(heap_replace_top_becomes_smallest);
}
