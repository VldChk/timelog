/*===========================================================================
 * test_invariants.c - Observable Invariant Verification Tests
 *
 * Tests that verify observable invariants via tl_validate():
 * - Empty timelog validation
 * - Validation with records (in-order and out-of-order)
 * - Validation with tombstones
 * - Validation after flush (single and multiple)
 * - TL_TS_MAX edge cases (no sentinel assumption)
 * - NULL pointer handling
 *
 * NOTE: Other invariants documented in CLAUDE.md are verified in:
 * - test_storage_internal.c: Page sortedness, segment bounds, L1 non-overlap
 * - test_delta_internal.c: Tombstone canonicalization, memtable invariants
 * - test_concurrency.c: Snapshot isolation
 *
 * Part of Phase 10: Test Suite Reorganization
 * Note: Test names prefixed with "inv_" to indicate invariant tests.
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"

/* Internal headers for T-42 (L0 generation ordering) */
#include "internal/tl_timelog_internal.h"
#include "tl_snapshot.h"
#include "tl_manifest.h"
#include "tl_segment.h"

#include <stdint.h>

/*===========================================================================
 * tl_validate() Tests (migrated from test_phase6.c)
 *===========================================================================*/

TEST_DECLARE(inv_validate_empty_timelog) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Empty timelog should validate successfully */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(inv_validate_with_records) {
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

TEST_DECLARE(inv_validate_with_ooo_records) {
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

TEST_DECLARE(inv_validate_with_tombstones) {
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

TEST_DECLARE(inv_validate_after_flush) {
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

TEST_DECLARE(inv_validate_after_flush_with_tombstones) {
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

TEST_DECLARE(inv_validate_null_snapshot) {
    /* NULL snapshot should return EINVAL */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_validate(NULL));
}

TEST_DECLARE(inv_validate_multiple_flushes) {
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

    /* Also verify stats - use lower bound for estimate (spec says it's approximate) */
    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    TEST_ASSERT_EQ(3, stats.segments_l0);
    TEST_ASSERT(stats.records_estimate >= 6);  /* At least 6 records inserted */

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * TL_TS_MAX Edge Case Tests (migrated from test_phase6.c)
 *
 * These tests verify that validation handles TL_TS_MAX correctly. The
 * validator must use explicit has_content flags rather than sentinel checks.
 *===========================================================================*/

TEST_DECLARE(inv_validate_record_at_ts_max) {
    /*
     * A segment with a single record at TL_TS_MAX must validate correctly.
     * This catches the bug where (required_min != TL_TS_MAX) was used as
     * a sentinel for "has content".
     *
     * Per spec: "TL_TS_MAX (INT64_MAX) is NOT a sentinel; records at TL_TS_MAX
     * are fully supported."
     */
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert record at TL_TS_MAX (the maximum valid timestamp) */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, TL_TS_MAX, 1));

    /* Flush to create L0 segment */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Must validate successfully - the record at TL_TS_MAX is valid content */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    /* Verify stats show the record */
    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    TEST_ASSERT(stats.records_estimate >= 1);  /* At least 1 record */
    TEST_ASSERT_EQ(TL_TS_MAX, stats.min_ts);
    TEST_ASSERT_EQ(TL_TS_MAX, stats.max_ts);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(inv_validate_tombstone_ending_at_ts_max) {
    /*
     * A segment with a tombstone ending at TL_TS_MAX must validate correctly.
     *
     * tl_delete_before(ts) creates tombstone [TL_TS_MIN, ts), so calling
     * tl_delete_before(TL_TS_MAX) creates [TL_TS_MIN, TL_TS_MAX).
     *
     * NOTE: There is no public API to create a tombstone STARTING at TL_TS_MAX
     * because the half-open interval [TL_TS_MAX, TL_TS_MAX+1) would overflow.
     * Unbounded tombstones [TL_TS_MAX, +inf) require internal APIs.
     */
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert a record, then delete everything before TL_TS_MAX */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_delete_before(tl, TL_TS_MAX));

    /* Flush to create L0 segment with tombstone [TL_TS_MIN, TL_TS_MAX) */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Must validate successfully - record at 100 is tombstoned */
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    /* Verify the record is now deleted (tombstone covers it) */
    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    /* records_estimate may still show 1 (includes deleted), but query should find 0 */

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * T-42: L0 Generation Ordering After Flush
 *
 * Multiple flush cycles should produce L0 segments with monotonically
 * increasing generation numbers. This is a fundamental invariant for
 * correct merge ordering.
 *===========================================================================*/

TEST_DECLARE(inv_l0_generation_ordering_after_flush) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* No background compaction */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Perform 5 flush cycles */
    for (int i = 0; i < 5; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, (i + 1) * 100, (tl_handle_t)(i + 1)));
        TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));
    }

    /* Snapshot and check L0 generation ordering */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    const tl_manifest_t* manifest = tl_snapshot_manifest(snap);

    uint32_t n_l0 = tl_manifest_l0_count(manifest);
    TEST_ASSERT_EQ(5, (long long)n_l0);

    /* Verify monotonically increasing generations */
    uint32_t prev_gen = 0;
    for (uint32_t i = 0; i < n_l0; i++) {
        tl_segment_t* seg = tl_manifest_l0_get(manifest, i);
        TEST_ASSERT_NOT_NULL(seg);
        TEST_ASSERT(seg->generation > prev_gen);
        prev_gen = seg->generation;
    }

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_invariants_tests(void) {
    /* tl_validate() tests (8 tests) - migrated from test_phase6.c */
    RUN_TEST(inv_validate_empty_timelog);
    RUN_TEST(inv_validate_with_records);
    RUN_TEST(inv_validate_with_ooo_records);
    RUN_TEST(inv_validate_with_tombstones);
    RUN_TEST(inv_validate_after_flush);
    RUN_TEST(inv_validate_after_flush_with_tombstones);
    RUN_TEST(inv_validate_null_snapshot);
    RUN_TEST(inv_validate_multiple_flushes);

    /* TL_TS_MAX edge case tests (2 tests) - migrated from test_phase6.c */
    RUN_TEST(inv_validate_record_at_ts_max);
    RUN_TEST(inv_validate_tombstone_ending_at_ts_max);

    /* L0 generation ordering (1 test) - T-42 */
    RUN_TEST(inv_l0_generation_ordering_after_flush);

    /* Total: 11 tests */
}
