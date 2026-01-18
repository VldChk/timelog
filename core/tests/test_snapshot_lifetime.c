/*===========================================================================
 * test_snapshot_lifetime.c - Snapshot Lifetime Enforcement Tests
 *
 * P0 CRITICAL: Tests for snapshot and iterator lifetime management.
 *
 * These tests verify correct behavior when:
 * - Iterators outlive their parent snapshot
 * - Snapshots are released with outstanding iterators
 * - Multiple iterators share a snapshot
 * - Snapshots are reacquired after release
 *
 * In debug builds (TL_DEBUG), these conditions trigger assertions.
 * Tests use the tl__test_assert_hook mechanism to intercept assertions
 * without terminating the process.
 *
 * Part of Phase 10: Integration Testing and Hardening
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_defs.h"
#include "internal/tl_alloc.h"

#include <string.h>
#include <stdint.h>

/*===========================================================================
 * Assert Hook Infrastructure
 *
 * In TL_DEBUG builds, TL_ASSERT can be configured to call a test hook
 * instead of aborting. This allows testing assertion conditions.
 *
 * The hook is set via tl__test_set_assert_hook() and cleared after test.
 * Hook signature: void hook(const char* file, int line, const char* expr)
 *===========================================================================*/

#if defined(TL_DEBUG) && defined(TL_TEST_HOOKS)

#include "internal/tl_platform.h"

/* Thread-local flag to track if assertion was triggered */
static TL_THREAD_LOCAL bool g_assert_triggered = false;
static TL_THREAD_LOCAL const char* g_assert_file = NULL;
static TL_THREAD_LOCAL int g_assert_line = 0;
static TL_THREAD_LOCAL const char* g_assert_expr = NULL;

/* Test assert hook - sets flags instead of aborting */
static void lifetime_test_assert_hook(const char* file, int line, const char* expr) {
    g_assert_triggered = true;
    g_assert_file = file;
    g_assert_line = line;
    g_assert_expr = expr;
    /* Return instead of abort - test will check flags */
}

/* Helper macros for assert hook tests */
#define EXPECT_ASSERT_BEGIN() \
    do { \
        g_assert_triggered = false; \
        g_assert_file = NULL; \
        g_assert_line = 0; \
        g_assert_expr = NULL; \
        tl__test_set_assert_hook(lifetime_test_assert_hook); \
    } while (0)

#define EXPECT_ASSERT_END() \
    do { \
        tl__test_set_assert_hook(NULL); \
    } while (0)

#define EXPECT_ASSERT_TRIGGERED() (g_assert_triggered)
#define EXPECT_ASSERT_FILE() (g_assert_file)
#define EXPECT_ASSERT_LINE() (g_assert_line)
#define EXPECT_ASSERT_EXPR() (g_assert_expr)

#endif /* TL_DEBUG && TL_TEST_HOOKS */

/*===========================================================================
 * Snapshot Lifetime Tests (Phase 10 - P0 CRITICAL)
 *
 * These tests verify proper snapshot and iterator lifetime management.
 *===========================================================================*/

/*---------------------------------------------------------------------------
 * Test: lifetime_iter_outlive_snapshot_debug_assert
 *
 * Purpose: Verify debug assertion fires when iterator outlives snapshot.
 *
 * In TL_DEBUG builds, releasing a snapshot with outstanding iterators
 * triggers TL_ASSERT(snap->iter_count == 0). This test verifies that
 * behavior using the assert hook mechanism.
 *---------------------------------------------------------------------------*/
#if defined(TL_DEBUG) && defined(TL_TEST_HOOKS)
TEST_DECLARE(lifetime_iter_outlive_snapshot_debug_assert) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));

    /* Acquire snapshot */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Create iterator on snapshot */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it));

    /* Install assert hook */
    EXPECT_ASSERT_BEGIN();

    /*
     * Release snapshot WITHOUT closing iterator.
     * This should trigger assertion: snap->iter_count == 0
     */
    tl_snapshot_release(snap);

    /* Verify assertion was triggered */
    TEST_ASSERT(EXPECT_ASSERT_TRIGGERED());
    TEST_ASSERT(EXPECT_ASSERT_EXPR() != NULL);
    /* The assertion message should mention iter_count */

    /* Clear hook */
    EXPECT_ASSERT_END();

    /*
     * INTENTIONAL MEMORY LEAK (iterator 'it'):
     *
     * We do NOT call tl_iter_destroy(it) here because it would cause UAF:
     *   - tl_snapshot_release() already freed the snapshot memory
     *   - tl_iter_destroy() dereferences it->snapshot in TL_DEBUG mode
     *   - The iterator holds a raw pointer, NOT a reference - iter_count is
     *     a debug counter for detecting misuse, not a refcount
     *
     * This leak is acceptable because:
     *   1. This test specifically verifies misuse detection (releasing
     *      snapshot with outstanding iterators)
     *   2. The assertion would abort() in production, so this path is
     *      only reachable in test builds with hook suppression
     *   3. A few hundred bytes of leaked test memory is preferable to UAF
     */
    (void)it;  /* Suppress unused warning - intentionally leaked */

    /*
     * Clean up timelog. tl_close() will trigger assertion due to
     * snapshot_count being wrong (we suppressed the abort, but the
     * snapshot was still freed, leaving the count in a bad state).
     */
    EXPECT_ASSERT_BEGIN();
    tl_close(tl);
    EXPECT_ASSERT_END();
}
#endif /* TL_DEBUG && TL_TEST_HOOKS */

/*---------------------------------------------------------------------------
 * Test: lifetime_close_with_outstanding_debug_assert
 *
 * Purpose: Verify debug assertion fires when closing with outstanding snapshot.
 *
 * In TL_DEBUG builds, calling tl_close() with unreleased snapshots
 * triggers TL_ASSERT_MSG(outstanding == 0, ...). This test verifies
 * that behavior using the assert hook mechanism.
 *---------------------------------------------------------------------------*/
#if defined(TL_DEBUG) && defined(TL_TEST_HOOKS)
TEST_DECLARE(lifetime_close_with_outstanding_debug_assert) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));

    /* Acquire snapshot (do NOT release) */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Install assert hook */
    EXPECT_ASSERT_BEGIN();

    /*
     * Close timelog WITHOUT releasing snapshot.
     * This should trigger assertion: outstanding == 0
     */
    tl_close(tl);

    /* Verify assertion was triggered */
    TEST_ASSERT(EXPECT_ASSERT_TRIGGERED());
    TEST_ASSERT(EXPECT_ASSERT_EXPR() != NULL);
    /* The assertion message should mention outstanding snapshots */

    /* Clear hook */
    EXPECT_ASSERT_END();

    /*
     * Note: After tl_close, the snapshot is in an invalid state.
     * We cannot safely release it since the timelog is closed.
     * In production, this would be a memory leak - which is why
     * the assertion exists to catch this bug early.
     */
}
#endif /* TL_DEBUG && TL_TEST_HOOKS */

/*---------------------------------------------------------------------------
 * Test: lifetime_multiple_iterators_lifecycle
 *
 * Purpose: Verify multiple iterators can share a snapshot safely.
 *
 * This test verifies that:
 * - Multiple iterators can be created on the same snapshot
 * - Iterators can be closed in any order
 * - Snapshot can be released after all iterators are closed
 * - No assertions fire (proper lifecycle management)
 *---------------------------------------------------------------------------*/
TEST_DECLARE(lifetime_multiple_iterators_lifecycle) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 400, 4));

    /* Acquire snapshot */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Create 3 iterators on the same snapshot */
    tl_iter_t* it1 = NULL;
    tl_iter_t* it2 = NULL;
    tl_iter_t* it3 = NULL;

    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it1));
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, 150, 350, &it2));
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 200, &it3));

    /* Use all iterators to verify they work independently */
    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it1, &rec)); /* 100 */
    TEST_ASSERT_EQ(100, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it2, &rec)); /* 200 (first in range 150-350) */
    TEST_ASSERT_EQ(200, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it3, &rec)); /* 200 (first >= 200) */
    TEST_ASSERT_EQ(200, rec.ts);

    /* Close iterators in reverse order (should not affect correctness) */
    tl_iter_destroy(it3);
    tl_iter_destroy(it1);
    tl_iter_destroy(it2);

    /* Release snapshot - should succeed without assertion */
    tl_snapshot_release(snap);

    /* Close timelog */
    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: lifetime_reacquire_after_release
 *
 * Purpose: Verify snapshot reacquisition after release works correctly.
 *
 * This test verifies that:
 * - Releasing a snapshot doesn't affect data
 * - New snapshot can be acquired after release
 * - New snapshot sees the same data
 * - No stale references or corruption
 *---------------------------------------------------------------------------*/
/*
 * Helper: Count records via iterator.
 */
static size_t lifetime_count_records(const tl_snapshot_t* snap) {
    tl_iter_t* it = NULL;
    if (tl_iter_since(snap, TL_TS_MIN, &it) != TL_OK) {
        return 0;
    }
    size_t count = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        count++;
    }
    tl_iter_destroy(it);
    return count;
}

TEST_DECLARE(lifetime_reacquire_after_release) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));

    /* Acquire first snapshot and verify data */
    tl_snapshot_t* snap1 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap1));

    TEST_ASSERT_EQ(3, lifetime_count_records(snap1));

    /* Release first snapshot */
    tl_snapshot_release(snap1);
    snap1 = NULL;

    /* Acquire second snapshot - should see same data */
    tl_snapshot_t* snap2 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap2));

    TEST_ASSERT_EQ(3, lifetime_count_records(snap2));

    /* Verify data with iterator */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap2, 0, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);
    TEST_ASSERT_EQ(1, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(200, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(300, rec.ts);
    TEST_ASSERT_EQ(3, rec.handle);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec)); /* End of data */

    tl_iter_destroy(it);
    tl_snapshot_release(snap2);

    /* Add more data after release */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 400, 4));

    /* Third snapshot should see new data */
    tl_snapshot_t* snap3 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap3));

    TEST_ASSERT_EQ(4, lifetime_count_records(snap3));

    tl_snapshot_release(snap3);
    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_snapshot_lifetime_tests(void) {
    /* Debug-only assertion tests (require TL_DEBUG + TL_TEST_HOOKS) */
#if defined(TL_DEBUG) && defined(TL_TEST_HOOKS)
    RUN_TEST(lifetime_iter_outlive_snapshot_debug_assert);
    RUN_TEST(lifetime_close_with_outstanding_debug_assert);
#else
    printf("  [SKIP] lifetime_iter_outlive_snapshot_debug_assert (requires TL_DEBUG + TL_TEST_HOOKS)\n");
    printf("  [SKIP] lifetime_close_with_outstanding_debug_assert (requires TL_DEBUG + TL_TEST_HOOKS)\n");
#endif

    /* These tests run in all builds */
    RUN_TEST(lifetime_multiple_iterators_lifecycle);
    RUN_TEST(lifetime_reacquire_after_release);
}
