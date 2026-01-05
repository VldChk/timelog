#include "test_harness.h"
#include "timelog/timelog.h"
#include <stdint.h>

/*===========================================================================
 * Snapshot Tests
 *===========================================================================*/

TEST_DECLARE(snapshot_acquire_release_empty) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));
    TEST_ASSERT_NOT_NULL(tl);

    /* Acquire snapshot on empty timelog */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_NOT_NULL(snap);

    /* Release snapshot */
    tl_snapshot_release(snap);

    tl_close(tl);
}

TEST_DECLARE(snapshot_acquire_with_data) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert some records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));

    /* Acquire snapshot */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_NOT_NULL(snap);

    /* Verify min/max timestamps */
    tl_ts_t min_ts, max_ts;
    TEST_ASSERT_STATUS(TL_OK, tl_min_ts(snap, &min_ts));
    TEST_ASSERT_STATUS(TL_OK, tl_max_ts(snap, &max_ts));
    TEST_ASSERT_EQ(100, min_ts);
    TEST_ASSERT_EQ(300, max_ts);

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Iterator Range Tests
 *===========================================================================*/

TEST_DECLARE(iter_range_basic) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records at various timestamps */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 40, 4));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 50, 5));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Query range [20, 40) should return ts=20 and ts=30 */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, 20, 40, &it));
    TEST_ASSERT_NOT_NULL(it);

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(20, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(30, rec.ts);
    TEST_ASSERT_EQ(3, rec.handle);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(iter_range_empty) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Query non-overlapping range [300, 400) */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, 300, 400, &it));
    TEST_ASSERT_NOT_NULL(it);

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(iter_range_invalid) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Invalid range t1 >= t2 should return empty iterator */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, 200, 100, &it));
    TEST_ASSERT_NOT_NULL(it);

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Iterator Since/Until Tests
 *===========================================================================*/

TEST_DECLARE(iter_since_basic) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Query [20, +inf) should return ts=20, 30 */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 20, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(20, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(30, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(iter_until_basic) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Query [MIN, 25) should return ts=10, 20 */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_until(snap, 25, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(10, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(20, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Point/Equal Lookup Tests
 *===========================================================================*/

TEST_DECLARE(iter_equal_basic) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 2)); /* Duplicate timestamp */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 3));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Query exactly ts=100 should return both records */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_equal(snap, 100, &it));

    tl_record_t rec;
    int count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(100, rec.ts);
        count++;
    }
    TEST_ASSERT_EQ(2, count);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(iter_point_not_found) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Query ts=150 should return empty */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_point(snap, 150, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Tombstone (Delete) Tests
 *===========================================================================*/

TEST_DECLARE(iter_with_tombstone) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 40, 4));

    /* Delete range [15, 35) - should hide ts=20 and ts=30 */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 15, 35));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Iterate all - should only see ts=10 and ts=40 */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(10, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(40, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(iter_delete_before) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));

    /* Delete before 25 - should hide ts=10 and ts=20 */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_before(tl, 25));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(30, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Scan API Tests
 *===========================================================================*/

typedef struct {
    tl_record_t records[100];
    int count;
    int stop_at;
} scan_ctx_t;

static tl_scan_decision_t scan_callback(void* ctx, const tl_record_t* rec) {
    scan_ctx_t* scan = (scan_ctx_t*)ctx;
    if (scan->count < 100) {
        scan->records[scan->count] = *rec;
    }
    scan->count++;

    if (scan->stop_at > 0 && scan->count >= scan->stop_at) {
        return TL_SCAN_STOP;
    }
    return TL_SCAN_CONTINUE;
}

TEST_DECLARE(scan_range_basic) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    scan_ctx_t ctx = {0};
    TEST_ASSERT_STATUS(TL_OK, tl_scan_range(snap, 0, 100, scan_callback, &ctx));
    TEST_ASSERT_EQ(3, ctx.count);
    TEST_ASSERT_EQ(10, ctx.records[0].ts);
    TEST_ASSERT_EQ(20, ctx.records[1].ts);
    TEST_ASSERT_EQ(30, ctx.records[2].ts);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(scan_range_early_stop) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 40, 4));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    scan_ctx_t ctx = {0};
    ctx.stop_at = 2; /* Stop after 2 records */
    TEST_ASSERT_STATUS(TL_OK, tl_scan_range(snap, 0, 100, scan_callback, &ctx));
    TEST_ASSERT_EQ(2, ctx.count);

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Timestamp Navigation Tests
 *===========================================================================*/

TEST_DECLARE(min_max_ts_basic) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 50, 2));  /* OOO insert */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 3));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_ts_t ts;
    TEST_ASSERT_STATUS(TL_OK, tl_min_ts(snap, &ts));
    TEST_ASSERT_EQ(50, ts);

    TEST_ASSERT_STATUS(TL_OK, tl_max_ts(snap, &ts));
    TEST_ASSERT_EQ(200, ts);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(min_max_ts_empty) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_ts_t ts;
    TEST_ASSERT_STATUS(TL_EOF, tl_min_ts(snap, &ts));
    TEST_ASSERT_STATUS(TL_EOF, tl_max_ts(snap, &ts));

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(next_prev_ts_basic) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_ts_t ts;

    /* Next after 10 should be 20 */
    TEST_ASSERT_STATUS(TL_OK, tl_next_ts(snap, 10, &ts));
    TEST_ASSERT_EQ(20, ts);

    /* Next after 15 should be 20 */
    TEST_ASSERT_STATUS(TL_OK, tl_next_ts(snap, 15, &ts));
    TEST_ASSERT_EQ(20, ts);

    /* Next after 30 should be EOF */
    TEST_ASSERT_STATUS(TL_EOF, tl_next_ts(snap, 30, &ts));

    /* Prev before 30 should be 20 */
    TEST_ASSERT_STATUS(TL_OK, tl_prev_ts(snap, 30, &ts));
    TEST_ASSERT_EQ(20, ts);

    /* Prev before 10 should be EOF */
    TEST_ASSERT_STATUS(TL_EOF, tl_prev_ts(snap, 10, &ts));

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Post-Flush Read Tests
 *===========================================================================*/

TEST_DECLARE(iter_after_flush) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));

    /* Flush to L0 segment */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Add more records to active memtable */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 40, 4));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 50, 5));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Should see all 5 records from both segment and active */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it));

    int count = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        count++;
    }
    TEST_ASSERT_EQ(5, count);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(iter_tombstone_after_flush) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));

    /* Flush to L0 */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Delete middle record */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 15, 25));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Should see ts=10 and ts=30, not ts=20 */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(10, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(30, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Edge Case Tests (INT64_MAX, tombstones affecting min/max)
 *===========================================================================*/

TEST_DECLARE(iter_at_ts_max) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert record at INT64_MAX - this is a valid timestamp */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, INT64_MAX, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 2));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Query should find the INT64_MAX record */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_equal(snap, INT64_MAX, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(INT64_MAX, rec.ts);
    TEST_ASSERT_EQ(1, rec.handle);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(min_max_with_tombstones) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 40, 4));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 50, 5));

    /* Delete first and last records */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 0, 15));   /* Deletes ts=10 */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 45, 100)); /* Deletes ts=50 */

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* min should be 20 (not 10), max should be 40 (not 50) */
    tl_ts_t ts;
    TEST_ASSERT_STATUS(TL_OK, tl_min_ts(snap, &ts));
    TEST_ASSERT_EQ(20, ts);

    TEST_ASSERT_STATUS(TL_OK, tl_max_ts(snap, &ts));
    TEST_ASSERT_EQ(40, ts);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(min_max_all_deleted) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));

    /* Delete ALL records */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 0, 100));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* min/max should return EOF since all are deleted */
    tl_ts_t ts;
    TEST_ASSERT_STATUS(TL_EOF, tl_min_ts(snap, &ts));
    TEST_ASSERT_STATUS(TL_EOF, tl_max_ts(snap, &ts));

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(iter_unbounded_range) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, INT64_MAX - 1, 3)); /* Near max */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, INT64_MAX, 4));     /* At max */

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Unbounded since should get all records including INT64_MAX */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 100, &it));

    int count = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        count++;
    }
    TEST_ASSERT_EQ(4, count);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(tombstone_coalescing) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    for (int i = 0; i < 10; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, (tl_ts_t)(i * 10), (tl_handle_t)i));
    }

    /* Insert overlapping tombstones that should coalesce:
     * [10, 30) and [20, 50) should become [10, 50) */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 10, 30));
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 20, 50));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Should only see ts=0, 50, 60, 70, 80, 90 */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it));

    tl_record_t rec;
    int count = 0;
    tl_ts_t expected[] = {0, 50, 60, 70, 80, 90};
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT(count < 6);
        TEST_ASSERT_EQ(expected[count], rec.ts);
        count++;
    }
    TEST_ASSERT_EQ(6, count);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Point Fast Path Tests
 *===========================================================================*/

TEST_DECLARE(iter_point_fast_path) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert multiple records with duplicates at same timestamp */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 3));  /* Duplicate ts */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 4));  /* Duplicate ts */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 5));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Point lookup should find all duplicates */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_point(snap, 200, &it));
    TEST_ASSERT_NOT_NULL(it);

    int count = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(200, rec.ts);
        count++;
    }
    TEST_ASSERT_EQ(3, count);  /* Three records with ts=200 */

    tl_iter_destroy(it);

    /* Point lookup at non-existent ts */
    TEST_ASSERT_STATUS(TL_OK, tl_iter_point(snap, 150, &it));
    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));
    tl_iter_destroy(it);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(iter_point_with_tombstone) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));

    /* Delete ts=200 */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 195, 205));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Point lookup at deleted ts should return empty */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_point(snap, 200, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(iter_point_at_ts_max) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert record at INT64_MAX */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, INT64_MAX, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 2));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Point lookup at INT64_MAX should work (no overflow) */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_point(snap, INT64_MAX, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(INT64_MAX, rec.ts);
    TEST_ASSERT_EQ(1, rec.handle);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_phase5_tests(void) {
    /* Snapshot tests */
    RUN_TEST(snapshot_acquire_release_empty);
    RUN_TEST(snapshot_acquire_with_data);

    /* Iterator range tests */
    RUN_TEST(iter_range_basic);
    RUN_TEST(iter_range_empty);
    RUN_TEST(iter_range_invalid);

    /* Since/Until tests */
    RUN_TEST(iter_since_basic);
    RUN_TEST(iter_until_basic);

    /* Point lookup tests */
    RUN_TEST(iter_equal_basic);
    RUN_TEST(iter_point_not_found);

    /* Point fast path tests */
    RUN_TEST(iter_point_fast_path);
    RUN_TEST(iter_point_with_tombstone);
    RUN_TEST(iter_point_at_ts_max);

    /* Tombstone tests */
    RUN_TEST(iter_with_tombstone);
    RUN_TEST(iter_delete_before);

    /* Scan tests */
    RUN_TEST(scan_range_basic);
    RUN_TEST(scan_range_early_stop);

    /* Timestamp navigation tests */
    RUN_TEST(min_max_ts_basic);
    RUN_TEST(min_max_ts_empty);
    RUN_TEST(next_prev_ts_basic);

    /* Post-flush tests */
    RUN_TEST(iter_after_flush);
    RUN_TEST(iter_tombstone_after_flush);

    /* Edge case tests */
    RUN_TEST(iter_at_ts_max);
    RUN_TEST(min_max_with_tombstones);
    RUN_TEST(min_max_all_deleted);
    RUN_TEST(iter_unbounded_range);
    RUN_TEST(tombstone_coalescing);
}
