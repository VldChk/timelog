#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_timelog_internal.h"
#include "internal/tl_sync.h"
#include "storage/tl_manifest.h"
#include "query/tl_snapshot.h"
#include "maint/tl_compaction.h"
#include <stdint.h>

/*===========================================================================
 * Helper Functions
 *===========================================================================*/

/**
 * Helper: Fill memtable and flush to create L0 segments.
 */
static void flush_n_times(tl_timelog_t* tl, int n, tl_ts_t base_ts, int records_per_flush) {
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < records_per_flush; j++) {
            tl_ts_t ts = base_ts + (i * 1000) + j;
            tl_append(tl, ts, (tl_handle_t)(ts + 1));
        }
        tl_flush(tl);
    }
}

/*===========================================================================
 * Fault-Injection Allocator (for ENOMEM tests)
 *===========================================================================*/

typedef struct {
    bool   fail_next;
    size_t alloc_calls;
} fail_alloc_ctx_t;

static void* fail_malloc(void* ctx, size_t size) {
    fail_alloc_ctx_t* fa = (fail_alloc_ctx_t*)ctx;
    fa->alloc_calls++;
    if (fa->fail_next) {
        fa->fail_next = false;
        return NULL;
    }
    return malloc(size);
}

static void* fail_calloc(void* ctx, size_t count, size_t size) {
    fail_alloc_ctx_t* fa = (fail_alloc_ctx_t*)ctx;
    fa->alloc_calls++;
    if (fa->fail_next) {
        fa->fail_next = false;
        return NULL;
    }
    return calloc(count, size);
}

static void* fail_realloc(void* ctx, void* ptr, size_t size) {
    fail_alloc_ctx_t* fa = (fail_alloc_ctx_t*)ctx;
    if (fa->fail_next) {
        fa->fail_next = false;
        return NULL;
    }
    return realloc(ptr, size);
}

static void fail_free(void* ctx, void* ptr) {
    (void)ctx;
    free(ptr);
}

/*===========================================================================
 * Threaded Helpers (for EBUSY publish test)
 *===========================================================================*/

typedef struct {
    tl_timelog_t* tl;
    tl_mutex_t    mu;
    tl_cond_t     cond;
    bool          start;
    bool          done;
} flush_thread_ctx_t;

static void* flush_thread_entry(void* arg) {
    flush_thread_ctx_t* ctx = (flush_thread_ctx_t*)arg;

    tl_mutex_lock(&ctx->mu);
    while (!ctx->start) {
        tl_cond_wait(&ctx->cond, &ctx->mu);
    }
    tl_mutex_unlock(&ctx->mu);

    /* Publish a new L0 to change the manifest */
    tl_append(ctx->tl, 9999, 42);
    tl_flush(ctx->tl);

    tl_mutex_lock(&ctx->mu);
    ctx->done = true;
    tl_cond_signal(&ctx->cond);
    tl_mutex_unlock(&ctx->mu);

    return NULL;
}

/*===========================================================================
 * Trigger Tests
 *===========================================================================*/

TEST_DECLARE(compact_needed_empty) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Empty timelog should not need compaction */
    TEST_ASSERT(!tl_compact_needed(tl));

    tl_close(tl);
}

TEST_DECLARE(compact_needed_below_threshold) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.max_delta_segments = 4;  /* Require 4 L0 segments to trigger */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments (below threshold) */
    flush_n_times(tl, 2, 1000, 10);

    /* Should NOT need compaction yet */
    TEST_ASSERT(!tl_compact_needed(tl));

    tl_close(tl);
}

TEST_DECLARE(compact_needed_at_threshold) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.max_delta_segments = 2;  /* Low threshold for testing */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments (at threshold) */
    flush_n_times(tl, 2, 1000, 10);

    /* Should need compaction now */
    TEST_ASSERT(tl_compact_needed(tl));

    tl_close(tl);
}

/*===========================================================================
 * Selection Tests
 *===========================================================================*/

TEST_DECLARE(compact_select_no_l0) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);

    /* Should return EOF when no L0 segments exist */
    TEST_ASSERT_STATUS(TL_EOF, tl_compact_select(&ctx));

    tl_compact_ctx_destroy(&ctx);
    tl_close(tl);
}

TEST_DECLARE(compact_select_selects_all_l0) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 3 L0 segments */
    flush_n_times(tl, 3, 1000, 10);

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_compact_select(&ctx));

    /* Should have selected all 3 L0 segments */
    TEST_ASSERT_EQ(3, ctx.input_l0_len);

    /* Should have no L1 inputs (none exist) */
    TEST_ASSERT_EQ(0, ctx.input_l1_len);

    tl_compact_ctx_destroy(&ctx);
    tl_close(tl);
}

/*===========================================================================
 * Merge Tests
 *===========================================================================*/

TEST_DECLARE(compact_merge_basic) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments with non-overlapping records */
    flush_n_times(tl, 2, 1000, 5);

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_compact_select(&ctx));
    TEST_ASSERT_STATUS(TL_OK, tl_compact_merge(&ctx));

    /* Should have at least 1 output L1 segment */
    TEST_ASSERT(ctx.output_l1_len > 0);

    /* Verify output L1 segments are valid */
    for (size_t i = 0; i < ctx.output_l1_len; i++) {
        TEST_ASSERT_NOT_NULL(ctx.output_l1[i]);
        TEST_ASSERT(tl_segment_is_l1(ctx.output_l1[i]));
        /* L1 segments must have no tombstones */
        TEST_ASSERT(!tl_segment_has_tombstones(ctx.output_l1[i]));
    }

    tl_compact_ctx_destroy(&ctx);
    tl_close(tl);
}

TEST_DECLARE(compact_merge_with_tombstones) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert records */
    for (int i = 0; i < 10; i++) {
        tl_append(tl, 100 + i * 10, i + 1);
    }

    /* Delete some records in the middle */
    tl_delete_range(tl, 130, 170);

    tl_flush(tl);

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_compact_select(&ctx));
    TEST_ASSERT_STATUS(TL_OK, tl_compact_merge(&ctx));

    /* Should have output L1 segments */
    TEST_ASSERT(ctx.output_l1_len > 0);

    /* L1 segments must be tombstone-free */
    for (size_t i = 0; i < ctx.output_l1_len; i++) {
        TEST_ASSERT(!tl_segment_has_tombstones(ctx.output_l1[i]));
    }

    tl_compact_ctx_destroy(&ctx);
    tl_close(tl);
}

/*===========================================================================
 * Publication Tests
 *===========================================================================*/

TEST_DECLARE(compact_publish_basic) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments */
    flush_n_times(tl, 2, 1000, 5);

    /* Get initial L0/L1 counts */
    tl_snapshot_t* snap_before = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap_before));
    tl_stats_t stats_before;
    tl_stats(snap_before, &stats_before);
    tl_snapshot_release(snap_before);

    TEST_ASSERT_EQ(2, stats_before.segments_l0);
    TEST_ASSERT_EQ(0, stats_before.segments_l1);

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_compact_select(&ctx));
    TEST_ASSERT_STATUS(TL_OK, tl_compact_merge(&ctx));
    TEST_ASSERT_STATUS(TL_OK, tl_compact_publish(&ctx));

    /* Get counts after compaction */
    tl_snapshot_t* snap_after = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap_after));
    tl_stats_t stats_after;
    tl_stats(snap_after, &stats_after);
    tl_snapshot_release(snap_after);

    /* L0 should be reduced, L1 should have segments */
    TEST_ASSERT_EQ(0, stats_after.segments_l0);
    TEST_ASSERT(stats_after.segments_l1 > 0);

    tl_compact_ctx_destroy(&ctx);
    tl_close(tl);
}

/*===========================================================================
 * End-to-End Tests
 *===========================================================================*/

TEST_DECLARE(compact_one_basic) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments */
    flush_n_times(tl, 2, 1000, 5);

    /* Run full compaction */
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

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

TEST_DECLARE(compact_one_no_work) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* No L0 segments - should return EOF */
    TEST_ASSERT_STATUS(TL_EOF, tl_compact_one(tl, 3));

    tl_close(tl);
}

TEST_DECLARE(compact_preserves_data) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

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
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

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

TEST_DECLARE(compact_respects_tombstones) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

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
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

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

TEST_DECLARE(compact_validate_passes) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create some L0 segments */
    flush_n_times(tl, 3, 1000, 10);

    /* Run compaction */
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

    /* Validate should pass */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));
    tl_snapshot_release(snap);

    tl_close(tl);
}

TEST_DECLARE(compact_multiple_rounds) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.max_delta_segments = 2;  /* Trigger compaction with 2 L0 */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Round 1: Create 2 L0 segments and compact */
    flush_n_times(tl, 2, 1000, 5);
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

    /* Round 2: Create 2 more L0 segments and compact */
    flush_n_times(tl, 2, 2000, 5);
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

    /* Round 3: Create 2 more L0 segments and compact */
    flush_n_times(tl, 2, 3000, 5);
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

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

/*===========================================================================
 * Edge Case Tests
 *===========================================================================*/

/**
 * Test that L1 selection uses window bounds, not record bounds.
 * This catches the bug where a sparse L1 segment (record at ts=0 in window [0,3600))
 * would not be selected when new L0 data arrives at ts=1000 in the same window,
 * because record-based overlap check (0 >= 1000) would fail.
 */
TEST_DECLARE(compact_l1_selection_uses_window_bounds) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.window_size = 3600;  /* 1 hour window */
    cfg.window_origin = 0;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create first L0 with single record at ts=0 (start of window [0,3600)) */
    tl_append(tl, 0, 1);
    tl_flush(tl);

    /* Compact to create L1 segment for window [0,3600) with single record */
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

    /* Verify we have 1 L1 segment */
    tl_snapshot_t* snap1 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap1));
    tl_stats_t stats1;
    tl_stats(snap1, &stats1);
    TEST_ASSERT_EQ(1, stats1.segments_l1);
    TEST_ASSERT_EQ(0, stats1.segments_l0);
    tl_snapshot_release(snap1);

    /* Create second L0 with record at ts=1000 (same window [0,3600)) */
    tl_append(tl, 1000, 2);
    tl_flush(tl);

    /* Compact again - must select the existing L1 segment for window [0,3600) */
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

    /* After compaction: should still have exactly 1 L1 segment (merged) */
    tl_snapshot_t* snap2 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap2));
    tl_stats_t stats2;
    tl_stats(snap2, &stats2);

    /* CRITICAL: If this fails with segments_l1=2, the L1 selection bug exists */
    TEST_ASSERT_EQ(1, stats2.segments_l1);
    TEST_ASSERT_EQ(0, stats2.segments_l0);

    /* Both records should be queryable */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap2, TL_TS_MIN, TL_TS_MAX, &it));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(0, rec.ts);
    TEST_ASSERT_EQ(1, rec.handle);

    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(1000, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);

    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap2);
    tl_close(tl);
}

/**
 * Test bounded tombstone residual doesn't widen deletes.
 * If tombstone [5000, 10000) but output range ends at ts=3600,
 * residual should start at max(5000, 3600) = 5000, not 3600.
 *
 * Note: We use a bounded tombstone to avoid TL_EOVERFLOW from window span
 * calculations that would occur with TL_TS_MAX tombstones.
 */
TEST_DECLARE(compact_bounded_tomb_residual_correct_start) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.window_size = 3600;
    cfg.window_origin = 0;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert records in window [0, 3600) */
    tl_append(tl, 100, 1);
    tl_append(tl, 200, 2);
    tl_flush(tl);

    /* Insert bounded tombstone [5000, 10000) starting AFTER the record range.
     * Residual should preserve [5000, 10000), not widen to [3600, 10000). */
    tl_delete_range(tl, 5000, 10000);
    tl_flush(tl);

    /* Compact - should process all and create residual for [5000, 10000) */
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

    /* Verify records in [3600, 5000) are NOT deleted */
    tl_append(tl, 4000, 3);  /* Record at ts=4000, should NOT be deleted */
    tl_flush(tl);

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    /* Query for record at ts=4000 - it should exist */
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_equal(snap, 4000, &it));
    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_next(it, &rec));
    TEST_ASSERT_EQ(4000, rec.ts);
    TEST_ASSERT_EQ(3, rec.handle);

    /* Record at ts=6000 should be deleted by residual tombstone */
    tl_iter_destroy(it);
    TEST_ASSERT_STATUS(TL_OK, tl_iter_equal(snap, 6000, &it));
    TEST_ASSERT_STATUS(TL_EOF, tl_iter_next(it, &rec));

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

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
TEST_DECLARE(compact_record_at_ts_max) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

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
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

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

/**
 * Test: tl_compact() + tl_maint_step() in manual mode.
 *
 * Verifies that explicit compaction request via tl_compact() is honored
 * by tl_maint_step() in manual mode (TL_MAINT_DISABLED).
 */
TEST_DECLARE(compact_manual_mode_explicit_request) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode */
    cfg.max_delta_segments = 100;  /* High threshold - won't trigger automatically */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments */
    for (int i = 0; i < 10; i++) {
        tl_append(tl, 1000 + i, (tl_handle_t)(i + 1));
    }
    tl_flush(tl);

    for (int i = 0; i < 10; i++) {
        tl_append(tl, 2000 + i, (tl_handle_t)(100 + i));
    }
    tl_flush(tl);

    /* Drain the flush queue */
    while (tl_maint_step(tl) == TL_OK) {}

    /* Snapshot should show 2 L0 segments */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    const tl_manifest_t* manifest = tl_snapshot_manifest(snap);
    size_t l0_before = manifest->n_l0;
    tl_snapshot_release(snap);

    TEST_ASSERT_EQ(2, (long long)l0_before);

    /* maint_step should return EOF - no automatic work needed (high threshold) */
    TEST_ASSERT_STATUS(TL_EOF, tl_maint_step(tl));

    /* Explicitly request compaction */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));

    /* maint_step should now perform compaction (honoring the explicit request) */
    tl_status_t st = tl_maint_step(tl);
    TEST_ASSERT(st == TL_OK || st == TL_EOF);  /* OK = did work, EOF = nothing selected */

    /* After compaction, L0 should be empty (all merged to L1) */
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    manifest = tl_snapshot_manifest(snap);
    size_t l0_after = manifest->n_l0;
    tl_snapshot_release(snap);

    /* L0 should be reduced (ideally 0 if compaction completed) */
    TEST_ASSERT(l0_after < l0_before || l0_before == 0);

    /* Verify data is still readable */
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_range(snap, TL_TS_MIN, TL_TS_MAX, &it));

    int count = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        count++;
    }
    TEST_ASSERT_EQ(20, count);  /* 10 + 10 records */

    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    tl_close(tl);
}

/**
 * Test: Manual-mode compaction request survives TL_ENOMEM.
 *
 * Simulates a transient allocation failure during tl_maint_step()
 * and verifies the explicit compaction request is preserved for retry.
 */
TEST_DECLARE(compact_manual_mode_request_survives_enomem) {
    fail_alloc_ctx_t fail_ctx = {0};

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode */
    cfg.max_delta_segments = 100;  /* Avoid auto compaction */

    cfg.allocator.ctx = &fail_ctx;
    cfg.allocator.malloc_fn = fail_malloc;
    cfg.allocator.calloc_fn = fail_calloc;
    cfg.allocator.realloc_fn = fail_realloc;
    cfg.allocator.free_fn = fail_free;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments */
    for (int i = 0; i < 5; i++) {
        tl_append(tl, 1000 + i, (tl_handle_t)(i + 1));
    }
    tl_flush(tl);

    for (int i = 0; i < 5; i++) {
        tl_append(tl, 2000 + i, (tl_handle_t)(100 + i));
    }
    tl_flush(tl);

    /* Drain flush queue */
    while (tl_maint_step(tl) == TL_OK) {}

    /* Confirm we have L0 segments before compaction */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    size_t l0_before = tl_snapshot_manifest(snap)->n_l0;
    tl_snapshot_release(snap);
    TEST_ASSERT(l0_before > 0);

    /* Request compaction explicitly */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));

    /* Fail the next allocation during compaction */
    fail_ctx.fail_next = true;
    TEST_ASSERT_STATUS(TL_ENOMEM, tl_maint_step(tl));

    /* Retry without failures - compaction should now succeed */
    tl_status_t st;
    do {
        st = tl_maint_step(tl);
    } while (st == TL_OK);
    TEST_ASSERT(st == TL_EOF || st == TL_ENOMEM);

    /* L0 should be reduced after successful retry */
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    size_t l0_after = tl_snapshot_manifest(snap)->n_l0;
    tl_snapshot_release(snap);
    TEST_ASSERT(l0_after < l0_before);

    tl_close(tl);
}

/**
 * Test: compaction publish returns EBUSY when manifest changes mid-merge.
 *
 * Uses a helper thread to publish a new L0 segment between merge and publish,
 * which deterministically invalidates ctx->base_manifest.
 */
TEST_DECLARE(compact_publish_ebusy_on_manifest_change) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create L0 segments to compact */
    flush_n_times(tl, 2, 1000, 10);

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);
    TEST_ASSERT_STATUS(TL_OK, tl_compact_select(&ctx));
    TEST_ASSERT_STATUS(TL_OK, tl_compact_merge(&ctx));

    /* Start helper thread that will change the manifest */
    flush_thread_ctx_t fctx = {0};
    fctx.tl = tl;
    TEST_ASSERT_STATUS(TL_OK, tl_mutex_init(&fctx.mu));
    TEST_ASSERT_STATUS(TL_OK, tl_cond_init(&fctx.cond));

    tl_thread_t th;
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&th, flush_thread_entry, &fctx));

    tl_mutex_lock(&fctx.mu);
    fctx.start = true;
    tl_cond_signal(&fctx.cond);
    while (!fctx.done) {
        tl_cond_wait(&fctx.cond, &fctx.mu);
    }
    tl_mutex_unlock(&fctx.mu);

    TEST_ASSERT_STATUS(TL_OK, tl_thread_join(&th, NULL));

    /* Publish should see manifest changed and return EBUSY */
    TEST_ASSERT_STATUS(TL_EBUSY, tl_compact_publish(&ctx));

    tl_compact_ctx_destroy(&ctx);
    tl_cond_destroy(&fctx.cond);
    tl_mutex_destroy(&fctx.mu);
    tl_close(tl);
}

/*===========================================================================
 * on_drop_handle Callback Tests
 *===========================================================================*/

/* Test context for tracking dropped handles */
typedef struct {
    tl_ts_t    dropped_ts[100];
    tl_handle_t dropped_handle[100];
    size_t     dropped_count;
} drop_tracker_t;

static void track_dropped_handle(void* ctx, tl_ts_t ts, tl_handle_t handle) {
    drop_tracker_t* tracker = (drop_tracker_t*)ctx;
    if (tracker->dropped_count < 100) {
        tracker->dropped_ts[tracker->dropped_count] = ts;
        tracker->dropped_handle[tracker->dropped_count] = handle;
        tracker->dropped_count++;
    }
}

/**
 * Test: on_drop_handle callback invoked during compaction.
 *
 * Verifies that records filtered by tombstones trigger the callback
 * with correct timestamp and handle values.
 */
TEST_DECLARE(compact_on_drop_handle_invoked) {
    drop_tracker_t tracker = {0};

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.max_delta_segments = 100;  /* High threshold - only explicit compaction */
    cfg.on_drop_handle = track_dropped_handle;
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
 * Run All Phase 8 Tests
 *===========================================================================*/

void run_phase8_tests(void) {
    /* Trigger tests */
    RUN_TEST(compact_needed_empty);
    RUN_TEST(compact_needed_below_threshold);
    RUN_TEST(compact_needed_at_threshold);

    /* Selection tests */
    RUN_TEST(compact_select_no_l0);
    RUN_TEST(compact_select_selects_all_l0);

    /* Merge tests */
    RUN_TEST(compact_merge_basic);
    RUN_TEST(compact_merge_with_tombstones);

    /* Publication tests */
    RUN_TEST(compact_publish_basic);

    /* End-to-end tests */
    RUN_TEST(compact_one_basic);
    RUN_TEST(compact_one_no_work);
    RUN_TEST(compact_preserves_data);
    RUN_TEST(compact_respects_tombstones);
    RUN_TEST(compact_validate_passes);
    RUN_TEST(compact_multiple_rounds);

    /* Edge case tests */
    RUN_TEST(compact_l1_selection_uses_window_bounds);
    RUN_TEST(compact_bounded_tomb_residual_correct_start);
    RUN_TEST(compact_record_at_ts_max);

    /* Manual mode tests */
    RUN_TEST(compact_manual_mode_explicit_request);
    RUN_TEST(compact_manual_mode_request_survives_enomem);
    RUN_TEST(compact_publish_ebusy_on_manifest_change);

    /* Callback tests */
    RUN_TEST(compact_on_drop_handle_invoked);
}
