#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/timelog/timelog.h"
#include "../src/internal/tl_defs.h"

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
     * Tombstone-Only Segment Suppression Tests
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Append records and flush to create data segment */
    for (int i = 1; i <= 5; i++) {
        st = tl_append(tl, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Delete range and flush with no new records -> tombstone-only segment */
    st = tl_delete_range(tl, 200, 400);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_ts_t expected_tomb_only[] = {100, 400, 500};
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, expected_tomb_only[count]);
        count++;
    }
    TEST_ASSERT_EQ(count, 3);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * Delete-Before Tests
     *=======================================================================*/

    /* delete_before should suppress records across segments and memview */
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 1; i <= 3; i++) {
        st = tl_append(tl, i * 100, i * 1000);  /* 100, 200, 300 */
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 4; i <= 5; i++) {
        st = tl_append(tl, i * 100, i * 1000);  /* 400, 500 (active) */
        TEST_ASSERT_EQ(st, TL_OK);
    }

    st = tl_delete_before(tl, 300);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_ts_t expected_cutoff[] = {300, 400, 500};
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, expected_cutoff[count]);
        count++;
    }
    TEST_ASSERT_EQ(count, 3);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);

    /* delete_before equivalence to delete_range(TL_TS_MIN, cutoff) */
    tl_timelog_t* tl_a = NULL;
    tl_timelog_t* tl_b = NULL;
    tl_snapshot_t* snap_a = NULL;
    tl_snapshot_t* snap_b = NULL;
    tl_iter_t* it_a = NULL;
    tl_iter_t* it_b = NULL;

    st = tl_open(&cfg, &tl_a);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_open(&cfg, &tl_b);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 1; i <= 5; i++) {
        st = tl_append(tl_a, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
        st = tl_append(tl_b, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl_a);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_flush(tl_b);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_delete_before(tl_a, 300);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_delete_range(tl_b, TL_TS_MIN, 300);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_flush(tl_a);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_flush(tl_b);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl_a, &snap_a);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_snapshot_acquire(tl_b, &snap_b);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_iter_since(snap_a, TL_TS_MIN, &it_a);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_iter_since(snap_b, TL_TS_MIN, &it_b);
    TEST_ASSERT_EQ(st, TL_OK);

    while (1) {
        tl_record_t rec_a;
        tl_record_t rec_b;
        tl_status_t sta = tl_iter_next(it_a, &rec_a);
        tl_status_t stb = tl_iter_next(it_b, &rec_b);
        TEST_ASSERT_EQ(sta, stb);
        if (sta == TL_EOF) break;
        TEST_ASSERT_EQ(rec_a.ts, rec_b.ts);
        TEST_ASSERT_EQ(rec_a.handle, rec_b.handle);
    }

    tl_iter_destroy(it_a);
    tl_iter_destroy(it_b);
    tl_snapshot_release(snap_a);
    tl_snapshot_release(snap_b);
    tl_close(tl_a);
    tl_close(tl_b);

    /*=======================================================================
     * Min/Max With Tombstones (Head/Tail)
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

    /* Delete head and tail */
    st = tl_delete_range(tl, 100, 200);  /* delete 100 */
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_delete_range(tl, 500, 600);  /* delete 500 */
    TEST_ASSERT_EQ(st, TL_OK);

    /* Tombstones in memview */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_min_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 200);

    st = tl_max_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 400);

    tl_snapshot_release(snap);
    snap = NULL;

    /* Flush tombstones to segments and re-check */
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_min_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 200);

    st = tl_max_ts(snap, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, 400);

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
     * Batch Append Tests
     *=======================================================================*/

    /* Sorted batch with hint */
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_record_t batch_sorted[] = {
        {100, 1001}, {200, 1002}, {300, 1003}, {400, 1004}, {500, 1005}
    };
    st = tl_append_batch(tl, batch_sorted, 5, TL_APPEND_HINT_MOSTLY_ORDER);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_ts_t expected_batch1[] = {100, 200, 300, 400, 500};
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, expected_batch1[count]);
        count++;
    }
    TEST_ASSERT_EQ(count, 5);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);

    /* Mostly ordered batch with one late out-of-order record */
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_record_t batch_late[] = {
        {100, 1}, {200, 2}, {400, 4}, {300, 3}, {500, 5}
    };
    st = tl_append_batch(tl, batch_late, 5, TL_APPEND_HINT_MOSTLY_ORDER);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_ts_t expected_batch2[] = {100, 200, 300, 400, 500};
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, expected_batch2[count]);
        count++;
    }
    TEST_ASSERT_EQ(count, 5);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);

    /* Unsorted batch without hint */
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_record_t batch_unsorted[] = {
        {300, 3}, {100, 1}, {200, 2}
    };
    st = tl_append_batch(tl, batch_unsorted, 3, 0);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_iter_range(snap, 0, 1000, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_ts_t expected_batch3[] = {100, 200, 300};
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, expected_batch3[count]);
        count++;
    }
    TEST_ASSERT_EQ(count, 3);

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
     * TL_TS_MIN Edge Case Tests
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_append(tl, TL_TS_MIN, 8001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, TL_TS_MIN + 1, 8002);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* iter_since should include TL_TS_MIN */
    st = tl_iter_since(snap, TL_TS_MIN, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    count = 0;
    tl_ts_t first_seen = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        if (count == 0) first_seen = rec.ts;
        count++;
    }
    TEST_ASSERT_EQ(count, 2);
    TEST_ASSERT_EQ(first_seen, TL_TS_MIN);
    tl_iter_destroy(it);

    /* iter_equal should return TL_TS_MIN */
    st = tl_iter_equal(snap, TL_TS_MIN, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, TL_TS_MIN);
        count++;
    }
    TEST_ASSERT_EQ(count, 1);
    tl_iter_destroy(it);

    /* iter_until should return only TL_TS_MIN */
    st = tl_iter_until(snap, TL_TS_MIN + 1, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, TL_TS_MIN);
        count++;
    }
    TEST_ASSERT_EQ(count, 1);
    tl_iter_destroy(it);

    /* next/prev ts around TL_TS_MIN */
    st = tl_next_ts(snap, TL_TS_MIN, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, TL_TS_MIN + 1);

    st = tl_prev_ts(snap, TL_TS_MIN, &ts);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_snapshot_release(snap);
    tl_close(tl);

    /*=======================================================================
     * TL_TS_MAX Edge Case Tests
     *=======================================================================*/

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_append(tl, TL_TS_MAX - 1, 9001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_append(tl, TL_TS_MAX, 9002);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* iter_since should include TL_TS_MAX */
    st = tl_iter_since(snap, TL_TS_MAX - 1, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    count = 0;
    tl_ts_t last_seen = TL_TS_MIN;
    while (tl_iter_next(it, &rec) == TL_OK) {
        last_seen = rec.ts;
        count++;
    }
    TEST_ASSERT_EQ(count, 2);
    TEST_ASSERT_EQ(last_seen, TL_TS_MAX);
    tl_iter_destroy(it);

    /* iter_equal should return TL_TS_MAX */
    st = tl_iter_equal(snap, TL_TS_MAX, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, TL_TS_MAX);
        count++;
    }
    TEST_ASSERT_EQ(count, 1);
    tl_iter_destroy(it);

    /* iter_until should stop before TL_TS_MAX */
    st = tl_iter_until(snap, TL_TS_MAX, &it);
    TEST_ASSERT_EQ(st, TL_OK);
    count = 0;
    while (tl_iter_next(it, &rec) == TL_OK) {
        TEST_ASSERT_EQ(rec.ts, TL_TS_MAX - 1);
        count++;
    }
    TEST_ASSERT_EQ(count, 1);
    tl_iter_destroy(it);

    /* next_ts should reach TL_TS_MAX */
    st = tl_next_ts(snap, TL_TS_MAX - 1, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, TL_TS_MAX);

    st = tl_next_ts(snap, TL_TS_MAX, &ts);
    TEST_ASSERT_EQ(st, TL_EOF);

    /* prev_ts should reach TL_TS_MAX - 1 */
    st = tl_prev_ts(snap, TL_TS_MAX, &ts);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(ts, TL_TS_MAX - 1);

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
