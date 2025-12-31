#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/timelog/timelog.h"
#include "../src/internal/tl_snapshot.h"
#include "../src/internal/tl_memtable.h"
#include "../src/internal/tl_manifest.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))
#define TEST_ASSERT_GE(a, b) TEST_ASSERT((a) >= (b))
#define TEST_ASSERT_LE(a, b) TEST_ASSERT((a) <= (b))

int test_diagnostics(void) {
    tl_timelog_t* tl = NULL;
    tl_snapshot_t* snap = NULL;
    tl_stats_t stats;
    tl_status_t st;

    printf("  [diagnostics] Testing validation and stats infrastructure...\n");

    /*=======================================================================
     * Test 1: Empty timelog validation
     *=======================================================================*/
    printf("    Test 1: Empty timelog validation...\n");

    st = tl_open(NULL, &tl);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(tl, NULL);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(snap, NULL);

    /* Validation should pass for empty timelog */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Stats should reflect empty state */
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.segments_main, 0);
    TEST_ASSERT_EQ(stats.segments_delta, 0);
    TEST_ASSERT_EQ(stats.pages_total, 0);
    TEST_ASSERT_EQ(stats.records_estimate, 0);
    TEST_ASSERT_EQ(stats.tombstone_count, 0);

    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 2: Validation after appends (data in memview)
     *=======================================================================*/
    printf("    Test 2: Validation after appends...\n");

    for (int i = 0; i < 100; i++) {
        st = tl_append(tl, 1000 + i * 10, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Validation should pass */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Stats should reflect records */
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.records_estimate, 100);
    TEST_ASSERT_EQ(stats.min_ts, 1000);
    TEST_ASSERT_EQ(stats.max_ts, 1990);

    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 3: Validation after flush (data in segments)
     *=======================================================================*/
    printf("    Test 3: Validation after flush...\n");

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Validation should still pass */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Stats should show delta segment */
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_GE(stats.segments_delta, 1);
    TEST_ASSERT_GE(stats.pages_total, 1);
    TEST_ASSERT_EQ(stats.records_estimate, 100);

    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 4: Validation after delete_range (tombstones present)
     *=======================================================================*/
    printf("    Test 4: Validation with tombstones...\n");

    /* Add more records */
    for (int i = 0; i < 50; i++) {
        st = tl_append(tl, 2000 + i * 10, 3000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    /* Add a tombstone range */
    st = tl_delete_range(tl, 1200, 1500);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Validation should pass with tombstones in memview */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Stats should show tombstone */
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_GE(stats.tombstone_count, 1);

    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 5: Validation after flush with tombstones (tombstones in segment)
     *=======================================================================*/
    printf("    Test 5: Validation after flush with tombstones...\n");

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Validation should pass with tombstones in segment */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 6: Out-of-order appends validation
     *=======================================================================*/
    printf("    Test 6: Out-of-order appends validation...\n");

    /* Add OOO records */
    st = tl_append(tl, 500, 4001);   /* Before existing data */
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 3000, 4002);  /* After existing data */
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 600, 4003);   /* OOO again */
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Validation should pass - OOO is sorted in memview */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 7: Merged output monotonicity via iterator
     *=======================================================================*/
    printf("    Test 7: Merged output monotonicity...\n");

    /* Flush OOO data */
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Create iterator and verify monotonicity manually */
    tl_iter_t* it = NULL;
    st = tl_iter_range(snap, TL_TS_MIN, TL_TS_MAX, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(it, NULL);

    tl_record_t prev_rec = {TL_TS_MIN, 0};
    tl_record_t cur_rec;
    int record_count = 0;
    bool has_prev = false;

    while ((st = tl_iter_next(it, &cur_rec)) == TL_OK) {
        if (has_prev) {
            /* Verify monotonicity: current ts >= previous ts */
            TEST_ASSERT_GE(cur_rec.ts, prev_rec.ts);
        }
        prev_rec = cur_rec;
        has_prev = true;
        record_count++;
    }
    TEST_ASSERT_EQ(st, TL_EOF);
    TEST_ASSERT(record_count > 0);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 8: Multiple flushes create multiple segments
     *=======================================================================*/
    printf("    Test 8: Multiple segments validation...\n");

    /* Add more data and flush multiple times */
    for (int batch = 0; batch < 3; batch++) {
        for (int i = 0; i < 20; i++) {
            st = tl_append(tl, 4000 + batch * 1000 + i * 10, 5000 + batch * 100 + i);
            TEST_ASSERT_EQ(st, TL_OK);
        }
        st = tl_flush(tl);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Validation should pass with multiple segments */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Stats should show multiple delta segments */
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_GE(stats.segments_delta, 4);  /* At least 4 flushes */

    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 9: Multiple tombstone ranges
     *=======================================================================*/
    printf("    Test 9: Multiple tombstone ranges...\n");

    /* Add multiple non-overlapping tombstones */
    st = tl_delete_range(tl, 4100, 4200);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_delete_range(tl, 5100, 5200);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_delete_range(tl, 6100, 6200);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Validation should pass - tombstones should be canonical */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 10: Adjacent tombstones should be coalesced
     *=======================================================================*/
    printf("    Test 10: Adjacent tombstone coalescing...\n");

    /* Add adjacent tombstones (should be merged) */
    st = tl_delete_range(tl, 7000, 7100);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_delete_range(tl, 7100, 7200);  /* Adjacent */
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Validation should pass - adjacent should be coalesced */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 11: Adjacent tombstones should fail validation if invariants broken
     *=======================================================================*/
    printf("    Test 11: Adjacent tombstone validation...\n");

    tl_timelog_t* tl_bad = NULL;
    st = tl_open(NULL, &tl_bad);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Create two disjoint tombstones */
    st = tl_delete_range(tl_bad, 100, 200);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_delete_range(tl_bad, 300, 400);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl_bad, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(snap->memview, NULL);
    TEST_ASSERT_EQ(snap->memview->active_tombs_len, 2);

    /* Corrupt tombstones to be adjacent */
    tl_interval_t* bad = snap->memview->active_tombs;
    bad[1].start = bad[0].end;
    bad[1].end = bad[0].end + 50;
    bad[1].end_unbounded = false;

    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_EINTERNAL);

    tl_snapshot_release(snap);
    snap = NULL;
    tl_close(tl_bad);
    tl_bad = NULL;

    /*=======================================================================
     * Test 12: Null safety for diagnostics APIs
     *=======================================================================*/
    printf("    Test 12: Null safety...\n");

    TEST_ASSERT_EQ(tl_validate(NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_stats(NULL, &stats), TL_EINVAL);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_stats(snap, NULL), TL_EINVAL);
    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Test 13: Stats bounds match query results
     *=======================================================================*/
    printf("    Test 13: Stats bounds accuracy...\n");

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);

    if (stats.records_estimate > 0) {
        /* min_ts should be <= any record timestamp */
        tl_ts_t actual_min = TL_TS_MAX;
        st = tl_min_ts(snap, &actual_min);
        if (st == TL_OK) {
            TEST_ASSERT_LE(stats.min_ts, actual_min);
        }

        /* max_ts should be >= any record timestamp */
        tl_ts_t actual_max = TL_TS_MIN;
        st = tl_max_ts(snap, &actual_max);
        if (st == TL_OK) {
            TEST_ASSERT_GE(stats.max_ts, actual_max);
        }
    }

    tl_snapshot_release(snap);
    snap = NULL;

    /*=======================================================================
     * Cleanup
     *=======================================================================*/
    tl_close(tl);

    printf("  [diagnostics] All diagnostics tests passed.\n");
    return 0;
}
