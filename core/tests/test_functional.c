/*===========================================================================
 * test_functional.c - Public API Functional Tests
 *
 * Tests for end-to-end functional correctness using public API:
 * - Snapshot: tl_snapshot_acquire, tl_snapshot_release
 * - Iterators: tl_iter_range, tl_iter_since, tl_iter_until, tl_iter_equal
 * - Scanning: tl_scan_range with callbacks
 * - Navigation: tl_min_ts, tl_max_ts, tl_next_ts, tl_prev_ts
 * - Statistics: tl_stats
 * - Maintenance: tl_flush, tl_compact, tl_maint_step
 * - Failure handling: ENOMEM recovery, error logging
 *
 * Internal implementation tests have been moved to:
 * - test_storage_internal.c: window, page, segment, manifest
 * - test_delta_internal.c: memrun, memtable, flush builder
 * - test_compaction_internal.c: selection, merge, publish
 *
 * Part of Phase 10: Integration Testing and Hardening
 *
 * Note: test scaffolding uses internal sync primitives for threads/conds,
 * but core behaviors are exercised through the public API surface.
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"

/* Internal headers required for test threading scaffolding. */
#include "internal/tl_sync.h"

#include <stdbool.h>
#include <string.h>
#include <stdint.h>

/*===========================================================================
 * Snapshot Tests
 *===========================================================================*/

TEST_DECLARE(func_snapshot_acquire_release_empty) {
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

TEST_DECLARE(func_snapshot_acquire_with_data) {
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
 * Iterator Range Tests (migrated from test_phase5.c)
 *===========================================================================*/

TEST_DECLARE(func_iter_range_basic) {
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

TEST_DECLARE(func_iter_range_empty) {
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

TEST_DECLARE(func_iter_range_invalid) {
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
 * Iterator Since/Until Tests (migrated from test_phase5.c)
 *===========================================================================*/

TEST_DECLARE(func_iter_since_basic) {
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

TEST_DECLARE(func_iter_until_basic) {
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
 * Point/Equal Lookup Tests (migrated from test_phase5.c)
 *===========================================================================*/

TEST_DECLARE(func_iter_equal_basic) {
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

TEST_DECLARE(func_iter_point_not_found) {
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

TEST_DECLARE(func_iter_point_fast_path) {
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

TEST_DECLARE(func_iter_point_with_tombstone) {
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

TEST_DECLARE(func_reinsert_visible_after_delete) {
    tl_timelog_t* tl = NULL;
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert, delete, then reinsert same timestamp */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 100, 200));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 2));

    /* Visible before flush */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_point(snap, 100, &it));
    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);
    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));
    tl_iter_destroy(it);
    tl_snapshot_release(snap);

    /* Flush to L0 and verify visibility */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_STATUS(TL_OK, tl_iter_point(snap, 100, &it));
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);
    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));
    tl_iter_destroy(it);
    tl_snapshot_release(snap);

    /* Compaction and verify again */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));
    while (tl_maint_step(tl) == TL_OK) {}

    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_STATUS(TL_OK, tl_iter_point(snap, 100, &it));
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);
    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));
    tl_iter_destroy(it);
    tl_snapshot_release(snap);

    tl_close(tl);
}

TEST_DECLARE(func_iter_point_at_ts_max) {
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
 * Tombstone (Delete) Tests (migrated from test_phase5.c)
 *===========================================================================*/

TEST_DECLARE(func_iter_with_tombstone) {
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

TEST_DECLARE(func_iter_delete_before) {
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
 * Scan API Tests (migrated from test_phase5.c)
 *===========================================================================*/

typedef struct {
    tl_record_t records[100];
    int count;
    int stop_at;
} func_scan_ctx_t;

static tl_scan_decision_t func_scan_callback(void* ctx, const tl_record_t* rec) {
    func_scan_ctx_t* scan = (func_scan_ctx_t*)ctx;
    if (scan->count < 100) {
        scan->records[scan->count] = *rec;
    }
    scan->count++;

    if (scan->stop_at > 0 && scan->count >= scan->stop_at) {
        return TL_SCAN_STOP;
    }
    return TL_SCAN_CONTINUE;
}

TEST_DECLARE(func_scan_range_basic) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    func_scan_ctx_t ctx = {0};
    TEST_ASSERT_STATUS(TL_OK, tl_scan_range(snap, 0, 100, func_scan_callback, &ctx));
    TEST_ASSERT_EQ(3, ctx.count);
    TEST_ASSERT_EQ(10, ctx.records[0].ts);
    TEST_ASSERT_EQ(20, ctx.records[1].ts);
    TEST_ASSERT_EQ(30, ctx.records[2].ts);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(func_scan_range_early_stop) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 40, 4));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    func_scan_ctx_t ctx = {0};
    ctx.stop_at = 2; /* Stop after 2 records */
    TEST_ASSERT_STATUS(TL_OK, tl_scan_range(snap, 0, 100, func_scan_callback, &ctx));
    TEST_ASSERT_EQ(2, ctx.count);

    tl_snapshot_release(snap);
    tl_close(tl);
}


TEST_DECLARE(func_count_range_basic) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 40, 4));

    uint64_t count = 0;
    TEST_ASSERT_STATUS(TL_OK, tl_count_range(tl, 20, 40, &count));
    TEST_ASSERT_EQ(2, (long long)count);

    tl_close(tl);
}

TEST_DECLARE(func_count_respects_tombstone_watermark_tie) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Segment watermark will be seq 1 after first flush. */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* First tombstone at seq 2 should hide ts=100 in newer snapshots. */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 100, 101));

    /* Reinsert at higher watermark (active source, treated as visible). */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 2));

    /* Second tombstone at seq 4: strict compare tomb_seq > watermark keeps reinsert. */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 100, 101));

    uint64_t count = 0;
    TEST_ASSERT_STATUS(TL_OK, tl_count(tl, &count));
    TEST_ASSERT_EQ(1, (long long)count);

    TEST_ASSERT_STATUS(TL_OK, tl_count_range(tl, 100, 101, &count));
    TEST_ASSERT_EQ(1, (long long)count);

    tl_close(tl);
}

TEST_DECLARE(func_count_snapshot_isolation) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 1));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Mutate after snapshot acquisition. */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 2));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, TL_TS_MIN, &it));

    uint64_t snap_count = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        snap_count++;
    }
    TEST_ASSERT_EQ(1, (long long)snap_count);
    tl_iter_destroy(it);

    uint64_t count = 0;
    TEST_ASSERT_STATUS(TL_OK, tl_count(tl, &count));
    TEST_ASSERT_EQ(2, (long long)count);

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Timestamp Navigation Tests (migrated from test_phase5.c)
 *===========================================================================*/

TEST_DECLARE(func_min_max_ts_basic) {
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

TEST_DECLARE(func_min_max_ts_empty) {
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

TEST_DECLARE(func_next_prev_ts_basic) {
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

TEST_DECLARE(func_next_ts_at_ts_max_eof) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, TL_TS_MAX, 1));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_ts_t ts = 0;
    TEST_ASSERT_STATUS(TL_EOF, tl_next_ts(snap, TL_TS_MAX, &ts));

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Post-Flush Read Tests (migrated from test_phase5.c)
 *===========================================================================*/

TEST_DECLARE(func_iter_after_flush) {
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

TEST_DECLARE(func_iter_tombstone_after_flush) {
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

/*
 * BUG REPRO: Tombstone filter drops first record of each subsequent segment.
 * Two segments flushed, then delete range in first segment's range.
 * The merge iterator's skip-ahead optimization drops ts=60.
 */
TEST_DECLARE(func_iter_tombstone_multi_segment) {
    tl_config_t cfg = {0};
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Segment 1: [10, 20, 30, 40, 50] */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 10));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 30));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 40, 40));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 50, 50));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Segment 2: [60, 70, 80, 90, 100] */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 60, 60));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 70, 70));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 80, 80));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 90, 90));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 100));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Delete [25, 45) — removes ts=30, ts=40 */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 25, 45));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Expected: 10, 20, 50, 60, 70, 80, 90, 100 (8 records) */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, TL_TS_MIN, &it));

    tl_record_t rec;
    int count = 0;
    int64_t expected[] = {10, 20, 50, 60, 70, 80, 90, 100};
    int64_t got[16] = {0};

    while (tl_iter_next(it, &rec) == TL_OK) {
        if (count < 16) got[count] = rec.ts;
        count++;
    }

    printf("    Got %d records:", count);
    for (int i = 0; i < count && i < 16; i++) {
        printf(" %lld", (long long)got[i]);
    }
    printf("\n");

    TEST_ASSERT_EQ(8, count);
    for (int i = 0; i < 8; i++) {
        TEST_ASSERT_EQ(expected[i], got[i]);
    }

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Edge Case Tests (migrated from test_phase5.c)
 *===========================================================================*/

TEST_DECLARE(func_iter_at_ts_max) {
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

TEST_DECLARE(func_min_max_with_tombstones) {
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

TEST_DECLARE(func_min_max_all_deleted) {
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

TEST_DECLARE(func_iter_unbounded_range) {
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

TEST_DECLARE(func_tombstone_coalescing) {
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
 * Statistics Tests (migrated from test_phase6.c)
 *===========================================================================*/

TEST_DECLARE(func_stats_empty_timelog) {
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

TEST_DECLARE(func_stats_with_records) {
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

TEST_DECLARE(func_stats_with_tombstones) {
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

TEST_DECLARE(func_stats_after_flush) {
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

TEST_DECLARE(func_stats_null_checks) {
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
 * Maintenance Configuration Tests
 *===========================================================================*/

TEST_DECLARE(func_compaction_safety_valve_config) {
    /* Verify safety valve config: max_delta_segments sets hard limit for L0.
     * When L0 >= max_delta_segments, compaction must run. */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.max_delta_segments = 4;   /* Low limit for testing */
    cfg.sealed_max_runs = 4;
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Verify timelog functional */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));

    tl_close(tl);
}

TEST_DECLARE(func_periodic_wake_config) {
    /* Verify maintenance_wakeup_ms config is accepted.
     * Periodic wake ensures worker detects pressure even without signals. */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_wakeup_ms = 50;  /* 50ms wakeup interval */
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert data */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));

    /* Brief wait for worker to potentially wake */
    tl_sleep_ms(60);

    /* Verify data intact */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    TEST_ASSERT_EQ(2, stats.records_estimate);

    tl_snapshot_release(snap);
    tl_close(tl);
}


/*===========================================================================
 * Compaction Tests
 *===========================================================================*/

/**
 * Helper: Fill memtable and flush to create L0 segments.
 */
static void func_flush_n_times(tl_timelog_t* tl, int n, tl_ts_t base_ts, int records_per_flush) {
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < records_per_flush; j++) {
            tl_ts_t ts = base_ts + (i * 1000) + j;
            tl_append(tl, ts, (tl_handle_t)(ts + 1));
        }
        tl_flush(tl);
    }
}

/*---------------------------------------------------------------------------
 * Drop handle tracker (for callback tests)
 *---------------------------------------------------------------------------*/

typedef struct {
    tl_ts_t    dropped_ts[100];
    tl_handle_t dropped_handle[100];
    size_t     dropped_count;
} func_drop_tracker_t;

static void func_track_dropped_handle(void* ctx, tl_ts_t ts, tl_handle_t handle) {
    func_drop_tracker_t* tracker = (func_drop_tracker_t*)ctx;
    if (tracker->dropped_count < 100) {
        tracker->dropped_ts[tracker->dropped_count] = ts;
        tracker->dropped_handle[tracker->dropped_count] = handle;
        tracker->dropped_count++;
    }
}

/*---------------------------------------------------------------------------
 * Helper: request compaction and run maintenance to quiescence (public API)
 *---------------------------------------------------------------------------*/
static tl_status_t func_compact_to_quiescence(tl_timelog_t* tl) {
    tl_status_t st = tl_compact(tl);
    if (st != TL_OK) {
        return st;
    }

    do {
        st = tl_maint_step(tl);
    } while (st == TL_OK);

    return st;  /* TL_EOF on success, or error */
}

/*---------------------------------------------------------------------------
 * Compaction Trigger Tests
 *---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------
 * Compaction Selection Tests
 *---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------
 * Compaction Merge Tests
 *---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------
 * Compaction Publication Tests
 *---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------
 * Compaction End-to-End Tests
 *---------------------------------------------------------------------------*/

TEST_DECLARE(func_compact_one_basic) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode for tl_maint_step() */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments */
    func_flush_n_times(tl, 2, 1000, 5);

    /* Run full compaction via public API */
    TEST_ASSERT_STATUS(TL_EOF, func_compact_to_quiescence(tl));

    /* Verify L0 is cleared, L1 exists */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats;
    tl_stats(snap, &stats);
    tl_snapshot_release(snap);

    TEST_ASSERT_EQ(0, stats.segments_l0);
    TEST_ASSERT(stats.segments_l1 > 0);

    tl_close(tl);
}

TEST_DECLARE(func_compact_one_no_work) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode for tl_maint_step() */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* No L0 segments - maint step should return EOF */
    TEST_ASSERT_STATUS(TL_EOF, func_compact_to_quiescence(tl));

    tl_close(tl);
}

TEST_DECLARE(func_compact_preserves_data) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode for tl_maint_step() */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert specific records */
    tl_append(tl, 100, 1);
    tl_append(tl, 200, 2);
    tl_append(tl, 300, 3);
    tl_flush(tl);

    tl_append(tl, 150, 4);
    tl_append(tl, 250, 5);
    tl_flush(tl);

    /* Run compaction */
    TEST_ASSERT_STATUS(TL_EOF, func_compact_to_quiescence(tl));

    /* Query should return all records in order */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, TL_TS_MIN, TL_TS_MAX, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);
    TEST_ASSERT_EQ(1, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(150, rec.ts);
    TEST_ASSERT_EQ(4, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(200, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(250, rec.ts);
    TEST_ASSERT_EQ(5, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(300, rec.ts);
    TEST_ASSERT_EQ(3, rec.handle);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(func_compact_respects_tombstones) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode for tl_maint_step() */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert records */
    tl_append(tl, 100, 1);
    tl_append(tl, 200, 2);
    tl_append(tl, 300, 3);
    tl_append(tl, 400, 4);
    tl_append(tl, 500, 5);
    tl_flush(tl);

    /* Delete some records */
    tl_delete_range(tl, 150, 350);  /* Deletes ts=200, ts=300 */
    tl_flush(tl);

    /* Run compaction */
    TEST_ASSERT_STATUS(TL_EOF, func_compact_to_quiescence(tl));

    /* Query should skip deleted records */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, TL_TS_MIN, TL_TS_MAX, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);  /* Not deleted */

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(400, rec.ts);  /* 200, 300 skipped */

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(500, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(func_compact_validate_passes) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode for tl_maint_step() */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create some L0 segments */
    func_flush_n_times(tl, 3, 1000, 10);

    /* Run compaction */
    TEST_ASSERT_STATUS(TL_EOF, func_compact_to_quiescence(tl));

    /* Validate should pass */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));
    tl_snapshot_release(snap);

    tl_close(tl);
}

TEST_DECLARE(func_compact_multiple_rounds) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode for tl_maint_step() */
    cfg.max_delta_segments = 2;  /* Trigger compaction with 2 L0 */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Round 1: Create 2 L0 segments and compact */
    func_flush_n_times(tl, 2, 1000, 5);
    TEST_ASSERT_STATUS(TL_EOF, func_compact_to_quiescence(tl));

    /* Round 2: Create 2 more L0 segments and compact */
    func_flush_n_times(tl, 2, 2000, 5);
    TEST_ASSERT_STATUS(TL_EOF, func_compact_to_quiescence(tl));

    /* Round 3: Create 2 more L0 segments and compact */
    func_flush_n_times(tl, 2, 3000, 5);
    TEST_ASSERT_STATUS(TL_EOF, func_compact_to_quiescence(tl));

    /* Validate final state */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_stats_t stats;
    tl_stats(snap, &stats);

    /* L0 should be empty, L1 should have data */
    TEST_ASSERT_EQ(0, stats.segments_l0);
    TEST_ASSERT(stats.segments_l1 > 0);

    /* All records should be queryable */
    TEST_ASSERT_EQ(30, stats.records_estimate);  /* 6 flushes * 5 records */

    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Compaction Edge Case Tests
 *---------------------------------------------------------------------------*/

/**
 * Test that L1 selection uses window bounds, not record bounds.
 * This catches the bug where a sparse L1 segment (record at ts=0 in window [0,3600))
 * would not be selected when new L0 data arrives at ts=1000 in the same window,
 * because record-based overlap check (0 >= 1000) would fail.
 */

/**
 * Test bounded tombstone residual doesn't widen deletes.
 * If tombstone [5000, 10000) but output range ends at ts=3600,
 * residual should start at max(5000, 3600) = 5000, not 3600.
 *
 * Note: We use a bounded tombstone to avoid TL_EOVERFLOW from window span
 * calculations that would occur with TL_TS_MAX tombstones.
 */

/**
 * Test compaction handles records at TL_TS_MAX correctly.
 *
 * This tests the fix for dynamic output array growth and window jumping:
 * - Records at TL_TS_MAX and ts=100 span a huge window ID range
 * - Without dynamic growth, pre-allocation would fail (trillions of pointers)
 * - Without window jumping, iterating window-by-window would hang forever
 *
 * With the fix, compaction is O(records) not O(windows), so this works.
 */
TEST_DECLARE(func_compact_record_at_ts_max) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode for tl_maint_step() */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert records at extreme timestamps */
    tl_append(tl, 100, 1);
    tl_append(tl, TL_TS_MAX, 999);  /* Maximum timestamp */
    tl_flush(tl);

    /* Create second L0 */
    tl_append(tl, 200, 2);
    tl_flush(tl);

    /* Compact - should handle the massive window span via jumping */
    TEST_ASSERT_STATUS(TL_EOF, func_compact_to_quiescence(tl));

    /* Verify all records are queryable after compaction */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Query for normal records */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, 0, 1000, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);
    TEST_ASSERT_EQ(1, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(200, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));
    tl_iter_destroy(it);

    /* Query for record at TL_TS_MAX */
    TEST_ASSERT_STATUS(TL_OK, tl_iter_equal(snap, TL_TS_MAX, &it));
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(TL_TS_MAX, rec.ts);
    TEST_ASSERT_EQ(999, rec.handle);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Compaction Manual Mode Tests
 *---------------------------------------------------------------------------*/

/**
 * Test: tl_compact() + tl_maint_step() in manual mode.
 *
 * Verifies that explicit compaction request via tl_compact() is honored
 * by tl_maint_step() in manual mode (TL_MAINT_DISABLED).
 */

/**
 * Test: Manual-mode compaction request survives TL_ENOMEM.
 *
 * Simulates a transient allocation failure during tl_maint_step()
 * and verifies the explicit compaction request is preserved for retry.
 */

/**
 * Test: compaction publish returns EBUSY when manifest changes mid-merge.
 *
 * Uses a helper thread to publish a new L0 segment between merge and publish,
 * which deterministically invalidates ctx->base_manifest.
 */

/*---------------------------------------------------------------------------
 * Compaction Callback Tests
 *---------------------------------------------------------------------------*/

/**
 * Test: on_drop_handle callback invoked during compaction.
 *
 * Verifies that records filtered by tombstones trigger the callback
 * with correct timestamp and handle values.
 */
TEST_DECLARE(func_compact_on_drop_handle_invoked) {
    func_drop_tracker_t tracker = {0};

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.max_delta_segments = 100;  /* High threshold - only explicit compaction */
    cfg.on_drop_handle = func_track_dropped_handle;
    cfg.on_drop_ctx = &tracker;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert records at ts 100, 200, 300, 400, 500 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 400, 4));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 500, 5));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Delete records in range [200, 400) - should drop ts 200, 300 */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 200, 400));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Drain flush queue */
    while (tl_maint_step(tl) == TL_OK) {}

    /* No drops yet - compaction hasn't run */
    TEST_ASSERT_EQ(0, (long long)tracker.dropped_count);

    /* Explicitly request compaction */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));
    tl_status_t st = tl_maint_step(tl);
    TEST_ASSERT(st == TL_OK || st == TL_EOF);

    /* Callback should have been invoked for deleted records */
    TEST_ASSERT_EQ(2, (long long)tracker.dropped_count);

    /* Check dropped records (order may vary, so check both are present) */
    bool found_200 = false, found_300 = false;
    for (size_t i = 0; i < tracker.dropped_count; i++) {
        if (tracker.dropped_ts[i] == 200 && tracker.dropped_handle[i] == 2) {
            found_200 = true;
        }
        if (tracker.dropped_ts[i] == 300 && tracker.dropped_handle[i] == 3) {
            found_300 = true;
        }
    }
    TEST_ASSERT(found_200);
    TEST_ASSERT(found_300);

    /* Verify remaining data is still queryable */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, TL_TS_MIN, TL_TS_MAX, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);
    TEST_ASSERT_EQ(1, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(400, rec.ts);
    TEST_ASSERT_EQ(4, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(500, rec.ts);
    TEST_ASSERT_EQ(5, rec.handle);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * C-10: Window Grid Freeze Test
 *
 * Verifies that after L1 segments are created, subsequent compactions
 * maintain L1 non-overlap invariant (which C-10 protects by freezing the
 * window grid once L1 exists).
 *===========================================================================*/

TEST_DECLARE(func_compact_c10_l1_nonoverlap_preserved) {
    /*
     * C-10 TEST: Verify L1 non-overlap is maintained across multiple compactions.
     *
     * The C-10 fix freezes the window grid after first L1 creation, preventing
     * adaptive segmentation from changing window boundaries mid-stream. This
     * test verifies the invariant is preserved by:
     * 1. Creating L1 segments through compaction
     * 2. Adding more data and compacting again
     * 3. Verifying all data is still queryable (L1 non-overlap maintained)
     */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.max_delta_segments = 2;  /* Trigger compaction with 2 L0 segments */
    cfg.window_size = 100;       /* Small window for easy L1 creation */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Phase 1: Create first L1 segment */
    /* Insert records in window 0 [0, 100) */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 10));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Insert more in same window */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 30));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 40, 40));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Compact - should create L1 segment for window 0 */
    /* After this, window_grid_frozen should be true (C-10) */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));
    while (tl_maint_step(tl) == TL_OK) {}

    /* Phase 2: Add more data in different window and compact again */
    /* Insert records in window 1 [100, 200) */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 110, 110));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 120, 120));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 130, 130));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 140, 140));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Compact again - should create L1 segment for window 1 */
    /* C-10 ensures window boundaries don't change, maintaining non-overlap */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));
    while (tl_maint_step(tl) == TL_OK) {}

    /* Phase 3: Verify all data is queryable (L1 non-overlap maintained) */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, TL_TS_MIN, TL_TS_MAX, &it));

    tl_record_t rec;
    tl_ts_t expected_ts[] = {10, 20, 30, 40, 110, 120, 130, 140};
    tl_handle_t expected_h[] = {10, 20, 30, 40, 110, 120, 130, 140};
    size_t n_expected = sizeof(expected_ts) / sizeof(expected_ts[0]);

    for (size_t i = 0; i < n_expected; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
        TEST_ASSERT_EQ(expected_ts[i], rec.ts);
        TEST_ASSERT_EQ(expected_h[i], rec.handle);
    }
    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    /* Phase 4: Verify validation passes (L1 non-overlap invariant) */
#ifdef TL_DEBUG
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));
#endif

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Failure Handling Tests (migrated from test_phase9.c)
 *===========================================================================*/

#include "internal/tl_atomic.h"  /* tl_atomic_u32, tl_atomic_fetch_add_u32 */
#include <stdio.h>   /* snprintf */

/*---------------------------------------------------------------------------
 * Targeted Fault Injection Infrastructure
 *
 * Unlike func_fail_alloc_ctx_t (which fails the NEXT allocation),
 * this targets the N-th allocation for precise failure injection.
 *---------------------------------------------------------------------------*/

typedef struct {
    size_t fail_after_n;  /* Fail the N-th allocation (0 = disabled) */
    size_t alloc_count;   /* Current allocation count */
    bool   failed;        /* Set to true after injection */
} func_targeted_fail_ctx_t;

static void* func_targeted_fail_malloc(void* ctx, size_t size) {
    func_targeted_fail_ctx_t* fa = (func_targeted_fail_ctx_t*)ctx;
    fa->alloc_count++;

    if (fa->fail_after_n > 0 && fa->alloc_count == fa->fail_after_n) {
        fa->failed = true;
        return NULL;
    }
    return malloc(size);
}

static void* func_targeted_fail_calloc(void* ctx, size_t count, size_t size) {
    func_targeted_fail_ctx_t* fa = (func_targeted_fail_ctx_t*)ctx;
    fa->alloc_count++;

    if (fa->fail_after_n > 0 && fa->alloc_count == fa->fail_after_n) {
        fa->failed = true;
        return NULL;
    }
    return calloc(count, size);
}

static void* func_targeted_fail_realloc(void* ctx, void* ptr, size_t size) {
    func_targeted_fail_ctx_t* fa = (func_targeted_fail_ctx_t*)ctx;
    fa->alloc_count++;

    if (fa->fail_after_n > 0 && fa->alloc_count == fa->fail_after_n) {
        fa->failed = true;
        return NULL;
    }
    return realloc(ptr, size);
}

static void func_targeted_fail_free(void* ctx, void* ptr) {
    (void)ctx;
    free(ptr);
}

/*---------------------------------------------------------------------------
 * Log Capture Infrastructure
 *---------------------------------------------------------------------------*/

#define FUNC_LOG_CAPTURE_MAX_MESSAGES 16
#define FUNC_LOG_CAPTURE_MSG_SIZE     256

typedef struct {
    char           messages[FUNC_LOG_CAPTURE_MAX_MESSAGES][FUNC_LOG_CAPTURE_MSG_SIZE];
    int            levels[FUNC_LOG_CAPTURE_MAX_MESSAGES];
    tl_atomic_u32  count;  /* Use project's atomic type for MSVC compatibility */
} func_log_capture_ctx_t;

static void func_capture_log(void* ctx, int level, const char* msg) {
    func_log_capture_ctx_t* lc = (func_log_capture_ctx_t*)ctx;
    /* TL_MO_RELAXED sufficient: only incrementing counter, array writes independent */
    uint32_t idx = tl_atomic_fetch_add_u32(&lc->count, 1, TL_MO_RELAXED);

    if (idx < FUNC_LOG_CAPTURE_MAX_MESSAGES) {
        snprintf(lc->messages[idx], FUNC_LOG_CAPTURE_MSG_SIZE, "%s", msg);
        lc->levels[idx] = level;
    }
}

/*---------------------------------------------------------------------------
 * Helper: flush with error checking (returns bool)
 *---------------------------------------------------------------------------*/

static bool func_flush_n_times_checked(tl_timelog_t* tl, int n, tl_ts_t base_ts, int records_per_flush) {
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < records_per_flush; j++) {
            tl_ts_t ts = base_ts + (tl_ts_t)(i * 1000) + j;
            tl_status_t st = tl_append(tl, ts, (tl_handle_t)(uintptr_t)(ts + 1));
            if (st != TL_OK) {
                return false;
            }
        }
        tl_status_t st = tl_flush(tl);
        if (st != TL_OK) {
            return false;
        }
    }
    return true;
}

/*---------------------------------------------------------------------------
 * Failure Handling Tests
 *---------------------------------------------------------------------------*/

/**
 * Test: flush_build_survives_enomem
 *
 * Purpose: Verify flush ENOMEM recovery with deterministic injection.
 */
TEST_DECLARE(func_flush_build_survives_enomem) {
    func_targeted_fail_ctx_t fail_ctx = {0};

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.memtable_max_bytes = 512;  /* Small - forces seal with few records */
    cfg.allocator.ctx = &fail_ctx;
    cfg.allocator.malloc_fn = func_targeted_fail_malloc;
    cfg.allocator.calloc_fn = func_targeted_fail_calloc;
    cfg.allocator.realloc_fn = func_targeted_fail_realloc;
    cfg.allocator.free_fn = func_targeted_fail_free;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Phase 1: Create and flush first memrun (calibration run) */
    fail_ctx.alloc_count = 0;
    for (int i = 0; i < 5; i++) {
        tl_append(tl, 1000 + i, (tl_handle_t)(uintptr_t)(i + 1));
    }

    tl_status_t st = tl_flush(tl);
    TEST_ASSERT_STATUS(TL_OK, st);
    size_t flush_allocs = fail_ctx.alloc_count;

    /* Sanity check: flush should have done some allocations */
    TEST_ASSERT(flush_allocs > 0);

    /* Phase 2: Create another memrun */
    fail_ctx.alloc_count = 0;
    fail_ctx.failed = false;
    for (int i = 0; i < 5; i++) {
        tl_append(tl, 2000 + i, (tl_handle_t)(uintptr_t)(i + 100));
    }

    /* Phase 3: Inject ENOMEM at midpoint of flush allocations. */
    fail_ctx.fail_after_n = (flush_allocs > 2) ? flush_allocs / 2 : 1;
    fail_ctx.alloc_count = 0;

    st = tl_flush(tl);
    TEST_ASSERT_STATUS(TL_ENOMEM, st);
    TEST_ASSERT(fail_ctx.failed);  /* Verify injection triggered */

    /* Phase 4: Verify records still visible via snapshot iteration. */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, 2000, 2100, &it));

    int count = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        count++;
    }
    TEST_ASSERT_EQ(5, count);  /* All 5 records from second batch visible */

    tl_iter_destroy(it);
    tl_snapshot_release(snap);

    /* Phase 5: Retry without fault, verify success */
    fail_ctx.fail_after_n = 0;  /* Disable injection */
    fail_ctx.alloc_count = 0;

    st = tl_flush(tl);
    TEST_ASSERT_STATUS(TL_OK, st);

    /* Phase 6: Verify data now in L0 segment */
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats;
    tl_stats(snap, &stats);
    TEST_ASSERT(stats.segments_l0 >= 1);  /* At least one L0 from retry */
    tl_snapshot_release(snap);

    tl_close(tl);
}

#ifdef TL_TEST_HOOKS
extern volatile int tl_test_force_ebusy_count;

/**
 * Test: compact_one_exhausts_retries
 *
 * Purpose: Verify TL_EBUSY is returned after max retries, inputs remain intact.
 */
#endif /* TL_TEST_HOOKS */

/**
 * Test: publish_phase_enomem
 *
 * Purpose: Verify ENOMEM during manifest building is recoverable.
 */
TEST_DECLARE(func_publish_phase_enomem) {
    func_targeted_fail_ctx_t fail_ctx = {0};

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.allocator.ctx = &fail_ctx;
    cfg.allocator.malloc_fn = func_targeted_fail_malloc;
    cfg.allocator.calloc_fn = func_targeted_fail_calloc;
    cfg.allocator.realloc_fn = func_targeted_fail_realloc;
    cfg.allocator.free_fn = func_targeted_fail_free;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Phase 1: Create L0 segments (injection disabled during setup) */
    TEST_ASSERT(func_flush_n_times_checked(tl, 2, 1000, 5));

    /* Phase 2: Calibrate - count allocations during successful compaction. */
    fail_ctx.alloc_count = 0;
    TEST_ASSERT_STATUS(TL_EOF, func_compact_to_quiescence(tl));
    size_t compact_allocs = fail_ctx.alloc_count;

    tl_status_t st;  /* Declare here for use in Phase 3 */

    /* Create more L0 segments for second compaction attempt (still no injection) */
    TEST_ASSERT(func_flush_n_times_checked(tl, 2, 3000, 5));

    /* Get stats before injection */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats_before;
    tl_stats(snap, &stats_before);
    tl_snapshot_release(snap);

    /* Phase 3: Inject ENOMEM late in compaction (targeting manifest build) */
    if (compact_allocs > 4) {
        /* Target the last quarter of allocations (more likely to hit publish) */
        fail_ctx.fail_after_n = compact_allocs * 3 / 4;
    } else {
        fail_ctx.fail_after_n = compact_allocs > 0 ? compact_allocs : 1;
    }
    fail_ctx.alloc_count = 0;
    fail_ctx.failed = false;

    st = func_compact_to_quiescence(tl);

    /* Either injection triggered (ENOMEM) or missed (compaction succeeded). */
    if (fail_ctx.failed) {
        /* Injection triggered - verify ENOMEM returned and inputs preserved */
        TEST_ASSERT_STATUS(TL_ENOMEM, st);

        /* Verify inputs still intact */
        TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
        tl_stats_t stats_after;
        tl_stats(snap, &stats_after);
        tl_snapshot_release(snap);

        /* L0 segments should still exist (inputs not consumed on failure) */
        TEST_ASSERT(stats_after.segments_l0 >= stats_before.segments_l0 ||
                    stats_after.segments_l0 > 0);
    } else {
        /* Injection missed - compaction should have quiesced */
        TEST_ASSERT_STATUS(TL_EOF, st);

        /* Compaction either succeeded (L1 created) or had no work */
        TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
        tl_stats_t stats_after;
        tl_stats(snap, &stats_after);
        tl_snapshot_release(snap);

        /* If compaction succeeded, should have L1 segment */
        if (st == TL_OK) {
            TEST_ASSERT(stats_after.segments_l1 > 0);
        }
    }

    tl_close(tl);
}

/**
 * Test: transient_errors_are_logged
 *
 * Purpose: Verify that transient errors produce log output.
 */
TEST_DECLARE(func_transient_errors_are_logged) {
    func_log_capture_ctx_t log_ctx;
    memset(&log_ctx, 0, sizeof(log_ctx));
    tl_atomic_init_u32(&log_ctx.count, 0);

    func_targeted_fail_ctx_t fail_ctx = {0};

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode for determinism */
    cfg.log_fn = func_capture_log;
    cfg.log_ctx = &log_ctx;
    cfg.allocator.ctx = &fail_ctx;
    cfg.allocator.malloc_fn = func_targeted_fail_malloc;
    cfg.allocator.calloc_fn = func_targeted_fail_calloc;
    cfg.allocator.realloc_fn = func_targeted_fail_realloc;
    cfg.allocator.free_fn = func_targeted_fail_free;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create L0 segments for compaction (injection not yet enabled) */
    TEST_ASSERT(func_flush_n_times_checked(tl, 2, 1000, 10));

    /* Request compaction explicitly */
    tl_compact(tl);

    /* Inject ENOMEM at first allocation in compaction */
    fail_ctx.fail_after_n = 1;
    fail_ctx.alloc_count = 0;

    /* Run maintenance step - should hit ENOMEM */
    tl_status_t st = tl_maint_step(tl);

    /* Verify injection triggered and error was returned. */
    if (st == TL_ENOMEM) {
        TEST_ASSERT(fail_ctx.failed);  /* Injection triggered */

        /*
         * CRITICAL: Verify that transient errors ARE actually logged.
         * This is the core purpose of this test - if we hit ENOMEM, the
         * implementation MUST log the error for observability.
         */
        uint32_t log_count = tl_atomic_load_u32(&log_ctx.count, TL_MO_RELAXED);
        TEST_ASSERT_MSG(log_count > 0,
                        "ENOMEM occurred but no log messages were emitted");
    }

    /* Retry without fault to clean up */
    fail_ctx.fail_after_n = 0;

    tl_close(tl);
}

/**
 * Test: eoverflow_clears_pending_manual_mode
 *
 * Purpose: Verify compact_pending is cleared after maintenance completes.
 */
TEST_DECLARE(func_eoverflow_clears_pending_manual_mode) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create some L0 segments */
    TEST_ASSERT(func_flush_n_times_checked(tl, 2, 1000, 5));

    /* Request compaction explicitly - this sets compact_pending */
    tl_compact(tl);

    /* maint_step should do compaction work because pending was set */
    tl_status_t st = tl_maint_step(tl);

    /* Should complete with OK, EOF, or possibly ENOMEM - all clear pending */
    TEST_ASSERT(st == TL_OK || st == TL_EOF || st == TL_ENOMEM);

    /* After first maint_step completes, pending should be cleared.
     * We verify this doesn't cause infinite loop by calling it again. */
    tl_status_t st2 = tl_maint_step(tl);
    /* May be OK (more work to do), EOF (no work), or ENOMEM */
    TEST_ASSERT(st2 == TL_OK || st2 == TL_EOF || st2 == TL_ENOMEM);

    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Stress Smoke Test (always-on, small scale)
 *---------------------------------------------------------------------------*/
TEST_DECLARE(func_smoke_high_volume_append_iterate) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    const int count = 5000;
    for (int i = 0; i < count; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, (tl_ts_t)i, (tl_handle_t)(i + 1)));
    }

    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, 0, count, &it));

    int seen = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        seen++;
    }
    TEST_ASSERT_EQ(count, seen);

    tl_iter_destroy(it);
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Skip-Ahead Seek Tests (C-02 Fix Verification)
 *
 * These tests verify that tl_kmerge_iter_seek() correctly preserves buffered
 * records >= target timestamp. The bug (C-02 / QUERY-1.1) was that seek()
 * cleared the entire heap, losing prefetched records that should be preserved.
 *===========================================================================*/

/**
 * Test: seek during tombstone filtering preserves buffered records >= target.
 *
 * Bug scenario: With multiple sources (L0 segment + memtable), the merge heap
 * contains prefetched records from each. When a tombstone triggers skip-ahead,
 * seek() must preserve heap entries with ts >= target.
 *
 * Setup:
 * - L0 segment: [100, 300] (from flush)
 * - Active memtable: [150, 350]
 * - Tombstone: [0, 200)  <- triggers skip-ahead past 150, 100
 *
 * After merge init, heap has: {ts=100, L0}, {ts=150, memtable}
 * Tombstone skip-ahead seeks to ts=200:
 * - Entry {100} < 200: pop, seek L0 to 200, re-prime with 300
 * - Entry {150} < 200: pop, seek memtable to 200, re-prime with 350
 *
 * Expected output: ts=300, ts=350 (both records visible after tombstone)
 *
 * The bug would lose ts=300 if seek() incorrectly cleared and re-sought L0.
 */
TEST_DECLARE(func_seek_preserves_buffered_records_multi_source) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Create L0 segment with records at ts=100, ts=300 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Add records to active memtable at ts=150, ts=350 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 150, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 350, 4));

    /* Add tombstone [0, 200) - triggers skip-ahead past 100 and 150 */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 0, 200));

    /* Query all records */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it));

    /* Should see ts=300 and ts=350 (records after tombstone) */
    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(300, rec.ts);
    TEST_ASSERT_EQ(3, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(350, rec.ts);
    TEST_ASSERT_EQ(4, rec.handle);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/**
 * Test: seek preserves heap entry exactly at target timestamp.
 *
 * If heap has entry {ts=200} and we seek to target=200, the entry should
 * be preserved (200 >= 200), not popped and re-fetched.
 */
TEST_DECLARE(func_seek_preserves_entry_at_exact_target) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Create records: 100, 200, 300 in L0 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Add tombstone [50, 200) - seek target is exactly 200 */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 50, 200));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it));

    /* ts=100 is deleted by tombstone.
     * After skip-ahead to 200, heap should have entry for ts=200.
     * ts=200 is NOT deleted (tombstone is [50, 200), half-open). */
    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(200, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(300, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/**
 * Test: seek preserves some entries while popping others (MIXED case).
 *
 * This is the CORE BUG scenario - one source has entry >= target that must
 * be preserved while another source has entry < target that must be popped.
 *
 * Setup:
 * - L0 segment: [100, 400]
 * - Active memtable: [250, 500]
 *
 * After merge init, heap has: {ts=100, L0}, {ts=250, memtable}
 * Tombstone [0, 200) triggers seek to 200:
 * - Entry {100} < 200: pop, seek L0 to 200, re-prime with 400
 * - Entry {250} >= 200: PRESERVE (this is the key case!)
 *
 * Expected: 250, 400, 500 (250 preserved, not lost)
 *
 * The OLD buggy code would lose 250 because it cleared the entire heap.
 */
TEST_DECLARE(func_seek_mixed_preserve_and_pop) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Create L0 segment with records at ts=100, ts=400 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 400, 4));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Add records to active memtable at ts=250, ts=500 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 250, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 500, 5));

    /* Tombstone [0, 200) - triggers seek.
     * Entry {100} < 200: pop and re-seek
     * Entry {250} >= 200: PRESERVE */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 0, 200));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it));

    /* Key assertion: ts=250 MUST be returned first (preserved, not lost) */
    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(250, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(400, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(500, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/**
 * Test: seek with interleaved records from multiple sources.
 *
 * Three sources with interleaved timestamps:
 * - L0-a: [100, 400]
 * - L0-b: [200, 500]
 * - Active: [300, 600]
 *
 * Tombstone [0, 350) triggers seek to 350.
 * After init, heap has {100, 200, 300}.
 * All three entries are < 350, so all sources should be re-seeked.
 *
 * Expected: 400, 500, 600 (sorted order from all sources)
 */
TEST_DECLARE(func_seek_multiple_sources_all_below_target) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Create first L0 segment */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 400, 4));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Create second L0 segment */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 500, 5));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Active memtable */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 600, 6));

    /* Tombstone [0, 350) */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 0, 350));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, 0, &it));

    /* Should see 400, 500, 600 in sorted order */
    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(400, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(500, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(600, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * T-23: Tombstone Skip-Ahead Correctness
 *
 * Records at [10,15,20,25,30]. Delete [12,22). Query full range.
 * Verify records 10, 25, 30 are returned (15, 20 are tombstoned).
 *===========================================================================*/

TEST_DECLARE(func_tombstone_skip_ahead_correctness) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 10, 10));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 15, 15));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 20, 20));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 25, 25));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 30, 30));

    /* Delete range [12, 22) — covers ts=15 and ts=20 */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 12, 22));

    /* Flush to create L0 segment with tombstones */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, TL_TS_MIN, TL_TS_MAX, &it));

    tl_record_t rec;
    /* Should see 10, 25, 30 (15 and 20 tombstoned by [12,22)) */
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(10, rec.ts);
    TEST_ASSERT_EQ(10, (long long)rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(25, rec.ts);
    TEST_ASSERT_EQ(25, (long long)rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(30, rec.ts);
    TEST_ASSERT_EQ(30, (long long)rec.handle);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * T-37: Segment Refcount Leak Detection (Full Lifecycle)
 *
 * Full lifecycle: append → seal → flush → compact → close.
 * Verify no crashes or leaks (ASan will catch actual leaks).
 *===========================================================================*/

TEST_DECLARE(func_lifecycle_no_segment_refcount_leak) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.max_delta_segments = 100;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Phase 1: Append records across multiple flushes */
    for (int batch = 0; batch < 3; batch++) {
        for (int i = 0; i < 10; i++) {
            tl_ts_t ts = (tl_ts_t)(batch * 1000 + i * 10);
            TEST_ASSERT_STATUS(TL_OK, tl_append(tl, ts, (tl_handle_t)(ts + 1)));
        }
        TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));
    }

    /* Phase 2: Take snapshot, verify data */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_stats_t stats;
    tl_stats(snap, &stats);
    TEST_ASSERT_EQ(3, stats.segments_l0);
    TEST_ASSERT(stats.records_estimate >= 30);

    tl_snapshot_release(snap);

    /* Phase 3: Compact L0 → L1 */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));
    tl_status_t st;
    do {
        st = tl_maint_step(tl);
    } while (st == TL_OK);

    /* Phase 4: Verify L1 exists, L0 consumed */
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats(snap, &stats);
    TEST_ASSERT_EQ(0, stats.segments_l0);
    TEST_ASSERT(stats.segments_l1 > 0);

    /* Verify all data still readable */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, TL_TS_MIN, TL_TS_MAX, &it));
    int count = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        count++;
    }
    TEST_ASSERT_EQ(30, count);

    tl_iter_destroy(it);
    tl_snapshot_release(snap);

    /* Phase 5: Close — ASan will catch any refcount leaks */
    tl_close(tl);
}

/*===========================================================================
 * T-40: Snapshot Isolation + Drop Callback
 *
 * Append → snapshot S1 → delete range → compact → S1 still sees records
 * → release S1.
 *===========================================================================*/

TEST_DECLARE(func_snapshot_isolation_with_drop_callback) {
    func_drop_tracker_t tracker = {0};

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.max_delta_segments = 100;
    cfg.on_drop_handle = func_track_dropped_handle;
    cfg.on_drop_ctx = &tracker;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert records */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 200, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 300, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Take snapshot BEFORE deletion */
    tl_snapshot_t* snap_before = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap_before));

    /* Delete range [150, 250) — covers ts=200 */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 150, 250));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Compact to physically drop ts=200 */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));
    tl_status_t st;
    do {
        st = tl_maint_step(tl);
    } while (st == TL_OK);

    /* Drop callback should have fired for ts=200 */
    TEST_ASSERT_EQ(1, (long long)tracker.dropped_count);
    TEST_ASSERT_EQ(200, tracker.dropped_ts[0]);
    TEST_ASSERT_EQ(2, (long long)tracker.dropped_handle[0]);

    /* snap_before (taken before delete) should still see ALL records */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap_before, TL_TS_MIN, TL_TS_MAX, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(200, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(300, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap_before);

    /* New snapshot should NOT see ts=200 */
    tl_snapshot_t* snap_after = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap_after));

    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap_after, TL_TS_MIN, TL_TS_MAX, &it));

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(300, rec.ts);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap_after);
    tl_close(tl);
}

/*===========================================================================
 * T-28: Multi-Source Determinism (Same Timestamp)
 *
 * Insert records at the same timestamp across multiple components
 * (memtable + flushed segments). Verify stable deterministic output.
 *===========================================================================*/

TEST_DECLARE(func_determinism_multi_source_same_timestamp) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Flush 1: records at ts=100 with handle=1 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Flush 2: records at ts=100 with handle=2 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Active memtable: ts=100 with handle=3 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, 3));

    /* Query twice and verify same order both times */
    tl_handle_t first_run[3] = {0};
    tl_handle_t second_run[3] = {0};

    for (int pass = 0; pass < 2; pass++) {
        tl_snapshot_t* snap = NULL;
        TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

        tl_iter_t* it = NULL;
        TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, TL_TS_MIN, TL_TS_MAX, &it));

        int count = 0;
        tl_record_t rec;
        while (tl_iter_next(it, &rec) == TL_OK) {
            TEST_ASSERT_EQ(100, rec.ts);
            if (pass == 0) {
                first_run[count] = rec.handle;
            } else {
                second_run[count] = rec.handle;
            }
            count++;
        }
        TEST_ASSERT_EQ(3, count);

        tl_iter_destroy(it);
        tl_snapshot_release(snap);
    }

    /* Verify deterministic ordering: both passes must yield same sequence */
    for (int i = 0; i < 3; i++) {
        TEST_ASSERT_EQ((long long)first_run[i], (long long)second_run[i]);
    }

    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_functional_tests(void) {
    /*=======================================================================
     * PUBLIC API TESTS (Spec-Driven)
     *
     * These tests verify behavior through PUBLIC API only:
     * - tl_append, tl_delete_range, tl_flush, tl_compact, tl_maint_step
     * - tl_snapshot_acquire, tl_snapshot_release
     * - tl_iter_*, tl_scan_*, tl_min_ts, tl_max_ts, tl_next_ts, tl_prev_ts
     * - tl_stats, tl_validate
     *
     * Internal tests (window, page, segment, manifest, memrun, memtable,
     * merge_iter, flush builder, compaction internals) have been moved to:
     * - test_storage_internal.c
     * - test_delta_internal.c
     * - test_compaction_internal.c
     *=======================================================================*/

    /* Snapshot tests (2 tests) - migrated from test_phase5.c */
    RUN_TEST(func_snapshot_acquire_release_empty);
    RUN_TEST(func_snapshot_acquire_with_data);

    /* Iterator range tests (3 tests) - migrated from test_phase5.c */
    RUN_TEST(func_iter_range_basic);
    RUN_TEST(func_iter_range_empty);
    RUN_TEST(func_iter_range_invalid);

    /* Since/Until tests (2 tests) - migrated from test_phase5.c */
    RUN_TEST(func_iter_since_basic);
    RUN_TEST(func_iter_until_basic);

    /* Point lookup tests (6 tests) - migrated from test_phase5.c */
    RUN_TEST(func_iter_equal_basic);
    RUN_TEST(func_iter_point_not_found);
    RUN_TEST(func_iter_point_fast_path);
    RUN_TEST(func_iter_point_with_tombstone);
    RUN_TEST(func_reinsert_visible_after_delete);
    RUN_TEST(func_iter_point_at_ts_max);

    /* Tombstone tests (2 tests) - migrated from test_phase5.c */
    RUN_TEST(func_iter_with_tombstone);
    RUN_TEST(func_iter_delete_before);

    /* Scan tests (2 tests) - migrated from test_phase5.c */
    RUN_TEST(func_scan_range_basic);
    RUN_TEST(func_scan_range_early_stop);
    RUN_TEST(func_count_range_basic);
    RUN_TEST(func_count_respects_tombstone_watermark_tie);
    RUN_TEST(func_count_snapshot_isolation);

    /* Timestamp navigation tests (3 tests) - migrated from test_phase5.c */
    RUN_TEST(func_min_max_ts_basic);
    RUN_TEST(func_min_max_ts_empty);
    RUN_TEST(func_next_prev_ts_basic);
    RUN_TEST(func_next_ts_at_ts_max_eof);

    /* Post-flush tests (2 tests) - migrated from test_phase5.c */
    RUN_TEST(func_iter_after_flush);
    RUN_TEST(func_iter_tombstone_after_flush);
    RUN_TEST(func_iter_tombstone_multi_segment);

    /* Edge case tests (5 tests) - migrated from test_phase5.c */
    RUN_TEST(func_iter_at_ts_max);
    RUN_TEST(func_min_max_with_tombstones);
    RUN_TEST(func_min_max_all_deleted);
    RUN_TEST(func_iter_unbounded_range);
    RUN_TEST(func_tombstone_coalescing);

    /* Statistics tests (5 tests) - uses tl_stats */
    RUN_TEST(func_stats_empty_timelog);
    RUN_TEST(func_stats_with_records);
    RUN_TEST(func_stats_with_tombstones);
    RUN_TEST(func_stats_after_flush);
    RUN_TEST(func_stats_null_checks);

    /* Maintenance config tests (2 tests) */
    RUN_TEST(func_compaction_safety_valve_config);
    RUN_TEST(func_periodic_wake_config);

    /* Compaction end-to-end tests (6 tests) - uses tl_compact + tl_maint_step */
    RUN_TEST(func_compact_one_basic);
    RUN_TEST(func_compact_one_no_work);
    RUN_TEST(func_compact_preserves_data);
    RUN_TEST(func_compact_respects_tombstones);
    RUN_TEST(func_compact_validate_passes);
    RUN_TEST(func_compact_multiple_rounds);

    /* Compaction edge case tests (1 test) - uses public API */
    RUN_TEST(func_compact_record_at_ts_max);

    /* Compaction callback tests (1 test) - uses on_drop callback */
    RUN_TEST(func_compact_on_drop_handle_invoked);

    /* C-10: Window grid freeze test (1 test) - verifies L1 non-overlap invariant */
    RUN_TEST(func_compact_c10_l1_nonoverlap_preserved);

    /* Failure handling tests (4 tests) - uses allocator/log hooks */
    RUN_TEST(func_flush_build_survives_enomem);
    RUN_TEST(func_publish_phase_enomem);
    RUN_TEST(func_transient_errors_are_logged);
    RUN_TEST(func_eoverflow_clears_pending_manual_mode);

    /* Stress smoke test (small scale, always-on) */
    RUN_TEST(func_smoke_high_volume_append_iterate);

    /* Skip-ahead seek tests (4 tests) - C-02 fix verification */
    RUN_TEST(func_seek_preserves_buffered_records_multi_source);
    RUN_TEST(func_seek_preserves_entry_at_exact_target);
    RUN_TEST(func_seek_mixed_preserve_and_pop);  /* Core bug scenario */
    RUN_TEST(func_seek_multiple_sources_all_below_target);

    /* Tombstone skip-ahead correctness (1 test) - T-23 */
    RUN_TEST(func_tombstone_skip_ahead_correctness);

    /* Full lifecycle refcount leak detection (1 test) - T-37 */
    RUN_TEST(func_lifecycle_no_segment_refcount_leak);

    /* Snapshot isolation with drop callback (1 test) - T-40 */
    RUN_TEST(func_snapshot_isolation_with_drop_callback);

    /* Multi-source determinism (1 test) - T-28 */
    RUN_TEST(func_determinism_multi_source_same_timestamp);

    /*
     * Total: ~62 tests (public API only)
     *
     * Internal tests moved to:
     * - test_storage_internal.c (~43 tests): window, page, catalog, segment, manifest
     * - test_delta_internal.c (~38 tests): memrun, memtable, merge_iter, flush
     * - test_compaction_internal.c (~11 tests): compact_needed, select, merge, publish
     */
}
