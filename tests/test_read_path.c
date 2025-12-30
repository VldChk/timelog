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

/* Scan visitor context types */
typedef struct {
    int count;
    tl_ts_t sum;
} scan_ctx_t;

/* Scan visitor that counts records and sums timestamps */
static tl_scan_decision_t count_visitor(void* ctx, const tl_record_t* r) {
    scan_ctx_t* sctx = (scan_ctx_t*)ctx;
    sctx->count++;
    sctx->sum += r->ts;
    return TL_SCAN_CONTINUE;
}

/* Scan visitor that stops after 2 records */
static tl_scan_decision_t stop_visitor(void* ctx, const tl_record_t* r) {
    (void)r;  /* unused */
    int* cnt = (int*)ctx;
    (*cnt)++;
    if (*cnt >= 2) return TL_SCAN_STOP;
    return TL_SCAN_CONTINUE;
}

int test_read_path(void) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    /* Use small but valid sizes for testing */
    cfg.memtable_max_bytes = 16 * 1024;  /* min 16 KiB */
    cfg.target_page_bytes = 1024;         /* min 1 KiB */

    tl_timelog_t* tl = NULL;
    tl_status_t st;

    /*=======================================================================
     * Basic Read Path Tests
     *=======================================================================*/

    /* Test: Empty timelog iteration */
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_snapshot_t* snap = NULL;
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(snap, NULL);

    /* Empty snapshot should return EOF on min/max */
    tl_ts_t ts;
    st = tl_min_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_EOF);

    st = tl_max_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_EOF);

    /* Empty range should return no records */
    tl_iter_t* it = NULL;
    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(it, NULL);

    tl_record_t rec;
    st = tl_iter_next(it, &rec);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * Read From Memtable (Before Flush)
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Append some records */
    st = tl_append(tl, 100, 1001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 200, 1002);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 300, 1003);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Acquire snapshot (should see memtable data) */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Check bounds */
    st = tl_min_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 100);

    st = tl_max_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 300);

    /* Iterate all records */
    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_iter_next(it, &rec);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(rec.ts, 100);
    TEST_ASSERT_EQ(rec.handle, 1001);

    st = tl_iter_next(it, &rec);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(rec.ts, 200);
    TEST_ASSERT_EQ(rec.handle, 1002);

    st = tl_iter_next(it, &rec);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(rec.ts, 300);
    TEST_ASSERT_EQ(rec.handle, 1003);

    st = tl_iter_next(it, &rec);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * Read After Flush (From Segment)
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Append and flush */
    st = tl_append(tl, 100, 1001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 200, 1002);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 300, 1003);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Acquire snapshot (should see flushed data) */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Iterate and verify */
    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    int count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        count++;
    }
    TEST_ASSERT_EQ(count, 3);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * Range Query Tests
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Append records: 100, 200, 300, 400, 500 */
    for (int i = 1; i <= 5; i++) {
        st = tl_append(tl, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Test: iter_since(250) should return 300, 400, 500 */
    st = tl_iter_since(snap, 250, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    count = 0;
    tl_ts_t first_ts = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        if (count == 0) first_ts = rec.ts;
        count++;
    }
    TEST_ASSERT_EQ(count, 3);
    TEST_ASSERT_EQ(first_ts, 300);
    tl_iter_destroy(it);

    /* Test: iter_until(350) should return 100, 200, 300 */
    st = tl_iter_until(snap, 350, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    count = 0;
    tl_ts_t last_ts = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        last_ts = rec.ts;
        count++;
    }
    TEST_ASSERT_EQ(count, 3);
    TEST_ASSERT_EQ(last_ts, 300);
    tl_iter_destroy(it);

    /* Test: iter_equal(300) should return exactly one record */
    st = tl_iter_equal(snap, 300, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, 300);
        count++;
    }
    TEST_ASSERT_EQ(count, 1);
    tl_iter_destroy(it);

    /* Test: iter_range(200, 400) should return 200, 300 */
    st = tl_iter_range(snap, 200, 400, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        count++;
    }
    TEST_ASSERT_EQ(count, 2);
    tl_iter_destroy(it);

    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * Tombstone Filtering Tests
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Append records: 100, 200, 300, 400, 500 */
    for (int i = 1; i <= 5; i++) {
        st = tl_append(tl, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    /* Delete range [200, 400) */
    st = tl_delete_range(tl, 200, 400);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Should return 100, 400, 500 (200 and 300 are deleted) */
    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_ts_t expected[] = {100, 400, 500};
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, expected[count]);
        count++;
    }
    TEST_ASSERT_EQ(count, 3);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * Out-of-Order Insertion Tests
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Insert out of order: 300, 100, 500, 200, 400 */
    st = tl_append(tl, 300, 3000);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 100, 1000);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 500, 5000);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 200, 2000);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, 400, 4000);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Should return records in sorted order */
    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_ts_t sorted_expected[] = {100, 200, 300, 400, 500};
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, sorted_expected[count]);
        count++;
    }
    TEST_ASSERT_EQ(count, 5);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * Scan API Tests
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 1; i <= 5; i++) {
        st = tl_append(tl, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Scan with counter visitor */
    scan_ctx_t sctx = {0, 0};
    st = tl_scan_range(snap, 0, 1000, count_visitor, &sctx);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(sctx.count, 5);
    TEST_ASSERT_EQ(sctx.sum, 1500);  /* 100+200+300+400+500 */

    /* Scan with early stop */
    int stop_count = 0;
    st = tl_scan_range(snap, 0, 1000, stop_visitor, &stop_count);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stop_count, 2);

    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * Timestamp Navigation Tests
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 1; i <= 5; i++) {
        st = tl_append(tl, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Test: tl_next_ts */
    st = tl_next_ts(snap, 200, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 300);

    st = tl_next_ts(snap, 500, &ts);
    TEST_ASSERT_EQ(st, TL_EOF);  /* No timestamp after 500 */

    st = tl_next_ts(snap, 50, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 100);

    /* Test: tl_prev_ts */
    st = tl_prev_ts(snap, 300, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 200);

    st = tl_prev_ts(snap, 100, &ts);
    TEST_ASSERT_EQ(st, TL_EOF);  /* No timestamp before 100 */

    st = tl_prev_ts(snap, 600, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 500);

    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * Statistics and Validation Tests
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 1; i <= 10; i++) {
        st = tl_append(tl, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    st = tl_delete_range(tl, 400, 600);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Test statistics */
    tl_stats_t stats;
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.records_estimate, 10);
    TEST_ASSERT(stats.tombstone_count >= 1);
    TEST_ASSERT_EQ(stats.min_ts, 100);
    TEST_ASSERT_EQ(stats.max_ts, 1000);

    /* Test validation */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * Multiple Snapshot Isolation Tests
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Create first set of data */
    for (int i = 1; i <= 3; i++) {
        st = tl_append(tl, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Take first snapshot */
    tl_snapshot_t* snap1 = NULL;
    st = tl_snapshot_acquire(tl, &snap1);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add more data */
    for (int i = 4; i <= 6; i++) {
        st = tl_append(tl, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Take second snapshot */
    tl_snapshot_t* snap2 = NULL;
    st = tl_snapshot_acquire(tl, &snap2);
    TEST_ASSERT_EQ(st, TL_OK);

    /* First snapshot should see 3 records */
    st = tl_iter_range(snap1, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) count++;
    TEST_ASSERT_EQ(count, 3);
    tl_iter_destroy(it);

    /* Second snapshot should see 6 records */
    st = tl_iter_range(snap2, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) count++;
    TEST_ASSERT_EQ(count, 6);
    tl_iter_destroy(it);

    tl_snapshot_release(snap1);
    tl_snapshot_release(snap2);
    tl_close(tl);

    /*=======================================================================
     * Null Safety Tests
     *=======================================================================*/

    TEST_ASSERT_EQ(tl_snapshot_acquire(NULL, NULL), TL_EINVAL);
    tl_snapshot_release(NULL);  /* Should not crash */

    TEST_ASSERT_EQ(tl_iter_range(NULL, 0, 100, NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_iter_next(NULL, NULL), TL_EINVAL);
    tl_iter_destroy(NULL);  /* Should not crash */

    TEST_ASSERT_EQ(tl_min_ts(NULL, NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_max_ts(NULL, NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_next_ts(NULL, 100, NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_prev_ts(NULL, 100, NULL), TL_EINVAL);

    TEST_ASSERT_EQ(tl_stats(NULL, NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_validate(NULL), TL_EINVAL);

    return 0;
}
