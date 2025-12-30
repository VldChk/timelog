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

int test_snapshot(void) {
    tl_timelog_t* tl = NULL;
    tl_status_t st;

    /* Test: Create timelog */
    st = tl_open(NULL, &tl);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(tl, NULL);

    /* Test: Acquire snapshot on empty timelog */
    tl_snapshot_t* snap = NULL;
    st = tl_snapshot_acquire_internal(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(snap, NULL);

    /* Empty snapshot should have no bounds */
    TEST_ASSERT(tl_snapshot_empty(snap));
    TEST_ASSERT_EQ(tl_snapshot_min_ts(snap), TL_TS_MAX);
    TEST_ASSERT_EQ(tl_snapshot_max_ts(snap), TL_TS_MIN);

    /* Manifest should be pinned (non-NULL) */
    TEST_ASSERT_NE(snap->manifest, NULL);

    /* Memview should be captured */
    TEST_ASSERT_NE(snap->memview, NULL);

    tl_snapshot_release_internal(snap);
    snap = NULL;

    /* Test: Acquire snapshot after appending data */
    st = tl_append(tl, 100, 1001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 200, 1002);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 300, 1003);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire_internal(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(snap, NULL);

    /* Snapshot should have bounds now (from memview) */
    TEST_ASSERT(!tl_snapshot_empty(snap));
    TEST_ASSERT(snap->has_bounds);
    TEST_ASSERT_EQ(snap->min_ts, 100);
    TEST_ASSERT_EQ(snap->max_ts, 300);
    TEST_ASSERT_EQ(tl_snapshot_min_ts(snap), 100);
    TEST_ASSERT_EQ(tl_snapshot_max_ts(snap), 300);

    /* Memview should have records */
    TEST_ASSERT_NE(snap->memview, NULL);
    TEST_ASSERT(!tl_memview_empty(snap->memview));

    tl_snapshot_release_internal(snap);
    snap = NULL;

    /* Test: Acquire snapshot after flush (data in manifest) */
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire_internal(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(snap, NULL);

    /* Snapshot should still have bounds (now from manifest) */
    TEST_ASSERT(!tl_snapshot_empty(snap));
    TEST_ASSERT(snap->has_bounds);
    TEST_ASSERT_EQ(snap->min_ts, 100);
    TEST_ASSERT_EQ(snap->max_ts, 300);

    /* Manifest should have delta segments now */
    TEST_ASSERT_NE(snap->manifest, NULL);
    TEST_ASSERT(snap->manifest->n_delta > 0 || snap->manifest->n_main > 0);

    /* Memview should be empty (after flush) */
    TEST_ASSERT(tl_memview_empty(snap->memview));

    tl_snapshot_release_internal(snap);
    snap = NULL;

    /* Test: Multiple snapshots can coexist */
    tl_snapshot_t* snap1 = NULL;
    tl_snapshot_t* snap2 = NULL;

    /* Append more data */
    st = tl_append(tl, 400, 1004);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire_internal(tl, &snap1);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Append even more data */
    st = tl_append(tl, 500, 1005);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire_internal(tl, &snap2);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Both snapshots should be valid */
    TEST_ASSERT_NE(snap1, NULL);
    TEST_ASSERT_NE(snap2, NULL);

    /* Snap1 should have older bounds (didn't see 500) */
    TEST_ASSERT_EQ(snap1->max_ts, 400);

    /* Snap2 should have newer bounds */
    TEST_ASSERT_EQ(snap2->max_ts, 500);

    tl_snapshot_release_internal(snap1);
    tl_snapshot_release_internal(snap2);

    /* Test: Snapshot with tombstones */
    st = tl_append(tl, 600, 1006);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_delete_range(tl, 150, 250);  /* Delete middle range */
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire_internal(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Tombstones should be visible in memview */
    TEST_ASSERT_NE(snap->memview, NULL);
    TEST_ASSERT(snap->memview->active_tombs_len > 0 ||
                snap->memview->sealed_len > 0);  /* Tombs in active or sealed */

    tl_snapshot_release_internal(snap);

    /* Test: Snapshot acquisition is wait-free in stable state */
    /* (We can't easily test the seqlock retry without concurrent access,
       but we can verify it succeeds under normal conditions) */
    for (int i = 0; i < 100; i++) {
        st = tl_snapshot_acquire_internal(tl, &snap);
        TEST_ASSERT_EQ(st, TL_OK);
        TEST_ASSERT_NE(snap, NULL);
        tl_snapshot_release_internal(snap);
    }

    /* Test: Null safety */
    TEST_ASSERT_EQ(tl_snapshot_acquire_internal(NULL, &snap), TL_EINVAL);
    TEST_ASSERT_EQ(tl_snapshot_acquire_internal(tl, NULL), TL_EINVAL);
    TEST_ASSERT(tl_snapshot_empty(NULL));
    TEST_ASSERT_EQ(tl_snapshot_min_ts(NULL), TL_TS_MAX);
    TEST_ASSERT_EQ(tl_snapshot_max_ts(NULL), TL_TS_MIN);
    tl_snapshot_release_internal(NULL);  /* Should not crash */

    /* Cleanup */
    tl_close(tl);

    return 0;
}
