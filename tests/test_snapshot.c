#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/timelog/timelog.h"

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
    tl_config_t cfg;

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Test: Create timelog */
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(tl, NULL);

    /* Test: Acquire snapshot on empty timelog */
    tl_snapshot_t* snap = NULL;
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(snap, NULL);

    /* Empty snapshot should return EOF on bounds */
    tl_ts_t ts;
    st = tl_min_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_EOF);
    st = tl_max_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_iter_t* it = NULL;
    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    tl_record_t rec;
    st = tl_iter_next(it, &rec);
    TEST_ASSERT_EQ(st, TL_EOF);
    tl_iter_destroy(it);

    tl_snapshot_release(snap);
    snap = NULL;

    /* Test: Acquire snapshot after appending data */
    st = tl_append(tl, 100, 1001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 200, 1002);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 300, 1003);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_min_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 100);

    st = tl_max_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 300);

    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    int count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        count++;
    }
    TEST_ASSERT_EQ(count, 3);
    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    snap = NULL;

    /* Test: Acquire snapshot after flush (data in manifest) */
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_min_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 100);
    st = tl_max_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 300);

    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        count++;
    }
    TEST_ASSERT_EQ(count, 3);
    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    snap = NULL;

    /* Test: Multiple snapshots can coexist */
    tl_snapshot_t* snap1 = NULL;
    tl_snapshot_t* snap2 = NULL;

    st = tl_append(tl, 400, 1004);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_snapshot_acquire(tl, &snap1);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_append(tl, 500, 1005);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap2);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_max_ts(snap1, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 400);
    st = tl_max_ts(snap2, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 500);

    tl_snapshot_release(snap1);
    tl_snapshot_release(snap2);

    /* Test: Tombstones are visible in snapshot */
    st = tl_append(tl, 600, 1006);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_delete_range(tl, 150, 250);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT(rec.ts < 150 || rec.ts >= 250);
    }
    tl_iter_destroy(it);
    tl_snapshot_release(snap);

    /* Test: Snapshot acquisition is stable in steady state */
    for (int i = 0; i < 100; i++) {
        st = tl_snapshot_acquire(tl, &snap);
        TEST_ASSERT_EQ(st, TL_OK);
        tl_snapshot_release(snap);
    }

    /* Test: Null safety */
    TEST_ASSERT_EQ(tl_snapshot_acquire(NULL, &snap), TL_EINVAL);
    TEST_ASSERT_EQ(tl_snapshot_acquire(tl, NULL), TL_EINVAL);
    tl_snapshot_release(NULL);

    /* Cleanup */
    tl_close(tl);

    return 0;
}
