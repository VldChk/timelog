#include "test_harness.h"
#include "timelog/timelog.h"
#include <stdint.h>

/*===========================================================================
 * tl_stats() Tests
 *===========================================================================*/

TEST_DECLARE(stats_empty_timelog) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));

    /* Empty timelog should have zero counts */
    TEST_ASSERT_EQ(0, stats.segments_l0);
    TEST_ASSERT_EQ(0, stats.segments_l1);
    TEST_ASSERT_EQ(0, stats.pages_total);
    TEST_ASSERT_EQ(0, stats.records_estimate);
    TEST_ASSERT_EQ(0, stats.tombstone_count);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(stats_with_records) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert some records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));

    /* Records in memview, not yet flushed */
    TEST_ASSERT_EQ(0, stats.segments_l0);
    TEST_ASSERT_EQ(0, stats.segments_l1);
    TEST_ASSERT_EQ(0, stats.pages_total);
    TEST_ASSERT_EQ(3, stats.records_estimate);
    TEST_ASSERT_EQ(0, stats.tombstone_count);

    /* Bounds should be set */
    TEST_ASSERT_EQ(100, stats.min_ts);
    TEST_ASSERT_EQ(300, stats.max_ts);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(stats_with_tombstones) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records and delete some */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 150, 250));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));

    /* Should have 3 RAW records and 1 tombstone */
    TEST_ASSERT_EQ(3, stats.records_estimate);
    TEST_ASSERT_EQ(1, stats.tombstone_count);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(stats_after_flush) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));

    /* Flush to create L0 segment */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));

    /* Now should have L0 segment with pages */
    TEST_ASSERT_EQ(1, stats.segments_l0);
    TEST_ASSERT_EQ(0, stats.segments_l1);
    TEST_ASSERT(stats.pages_total >= 1);
    TEST_ASSERT_EQ(3, stats.records_estimate);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(stats_null_checks) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_stats_t stats;

    /* NULL snapshot */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_stats(NULL, &stats));

    /* NULL output */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_stats(snap, NULL));

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * tl_validate() Tests
 *===========================================================================*/

TEST_DECLARE(validate_empty_timelog) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Empty timelog should validate successfully */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(validate_with_records) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Should validate successfully */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(validate_with_ooo_records) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert out-of-order records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Should validate successfully (ooo is sorted during seal) */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(validate_with_tombstones) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records and tombstones */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 50, 150));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Should validate successfully */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(validate_after_flush) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records and flush */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Should validate successfully with L0 segment */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(validate_after_flush_with_tombstones) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records, add tombstone, then flush */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 50, 150));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Should validate successfully with L0 segment containing tombstones */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * TL_TS_MAX Edge Case Tests
 *
 * These tests verify that validation handles TL_TS_MAX correctly. The
 * validator must use explicit has_content flags rather than sentinel checks.
 *===========================================================================*/

TEST_DECLARE(validate_record_at_ts_max) {
    /*
     * A segment with a single record at TL_TS_MAX must validate correctly.
     * This catches the bug where (required_min != TL_TS_MAX) was used as
     * a sentinel for "has content".
     */
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert record at INT64_MAX */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, INT64_MAX, 1));

    /* Flush to create L0 segment */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Must validate successfully - the record at TL_TS_MAX is valid content */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    /* Verify stats show the record */
    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    TEST_ASSERT_EQ(1, stats.records_estimate);
    TEST_ASSERT_EQ(INT64_MAX, stats.min_ts);
    TEST_ASSERT_EQ(INT64_MAX, stats.max_ts);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(validate_tombstone_at_ts_max) {
    /*
     * A segment with a tombstone starting at TL_TS_MAX must validate correctly.
     * This ensures the explicit has_content flag works for tombstone-only cases.
     */
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert a record, then delete from TL_TS_MAX onward */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_delete_before(tl, INT64_MAX));

    /* Flush to create L0 segment with tombstone */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Must validate successfully */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(validate_null_snapshot) {
    /* NULL snapshot should return EINVAL */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_validate(NULL));
}

TEST_DECLARE(validate_multiple_flushes) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Multiple flush cycles */
    for (int i = 0; i < 3; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, (i + 1) * 100, (tl_handle_t)(i + 1)));
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, (i + 1) * 100 + 50, (tl_handle_t)(i + 10)));
        TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));
    }

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Validate with multiple L0 segments */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    /* Also verify stats */
    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    TEST_ASSERT_EQ(3, stats.segments_l0);
    TEST_ASSERT_EQ(6, stats.records_estimate);

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Test Runner for Phase 6
 *===========================================================================*/

void run_phase6_tests(void) {
    /* tl_stats() tests */
    RUN_TEST(stats_empty_timelog);
    RUN_TEST(stats_with_records);
    RUN_TEST(stats_with_tombstones);
    RUN_TEST(stats_after_flush);
    RUN_TEST(stats_null_checks);

    /* tl_validate() tests */
    RUN_TEST(validate_empty_timelog);
    RUN_TEST(validate_with_records);
    RUN_TEST(validate_with_ooo_records);
    RUN_TEST(validate_with_tombstones);
    RUN_TEST(validate_after_flush);
    RUN_TEST(validate_after_flush_with_tombstones);
    RUN_TEST(validate_null_snapshot);
    RUN_TEST(validate_multiple_flushes);

    /* TL_TS_MAX edge case tests */
    RUN_TEST(validate_record_at_ts_max);
    RUN_TEST(validate_tombstone_at_ts_max);
}
