/*===========================================================================
 * test_compaction_internal.c - Compaction Internal Tests
 *
 * These tests verify LLD-level invariants and internal API behavior for
 * the compaction subsystem: selection, merge, publication, and retry logic.
 *
 * CLASSIFICATION: Internal (LLD-Driven)
 * These are IMPLEMENTATION tests, not SPEC tests.
 *
 * If these tests fail, the cause could be:
 * 1. A bug in the implementation (likely)
 * 2. An intentional internal refactor (update test accordingly)
 *
 * These tests do NOT verify public API contracts - see test_functional.c.
 *
 * Part of Phase 10: Test Suite Reorganization
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"

/* Internal headers - NOT public API */
#include "internal/tl_alloc.h"
#include "internal/tl_sync.h"
#include "internal/tl_timelog_internal.h"  /* For tl->alloc access */
#include "tl_compaction.h"
#include "tl_segment.h"
#include "tl_manifest.h"
#include "tl_snapshot.h"  /* For tl_snapshot_manifest */

#include <string.h>
#include <stdint.h>
#include <stdbool.h>

/*===========================================================================
 * Helper Functions
 *===========================================================================*/

/**
 * Helper to flush N times with specified base timestamp and records per flush.
 * Creates a deterministic pattern of L0 segments for testing.
 *
 * NOTE: Asserts on status to catch silent failures under backpressure/fault injection.
 */
static void compact_flush_n_times(tl_timelog_t* tl, int n, tl_ts_t base_ts, int records_per_flush) {
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < records_per_flush; j++) {
            tl_ts_t ts = base_ts + (tl_ts_t)(i * 1000) + j;
            tl_status_t st = tl_append(tl, ts, (tl_handle_t)(ts + 1));
            TEST_ASSERT_STATUS(TL_OK, st);
        }
        tl_status_t st = tl_flush(tl);
        TEST_ASSERT_STATUS(TL_OK, st);
    }
}

/*===========================================================================
 * Compaction Trigger Tests (Internal API)
 *
 * These test the internal tl_compact_needed() function which determines
 * if compaction should be triggered based on L0 segment count.
 *===========================================================================*/

TEST_DECLARE(cint_needed_empty) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Empty timelog should not need compaction */
    TEST_ASSERT(!tl_compact_needed(tl));

    tl_close(tl);
}

TEST_DECLARE(cint_needed_below_threshold) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.max_delta_segments = 4;  /* Require 4 L0 segments to trigger */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments (below threshold) */
    compact_flush_n_times(tl, 2, 1000, 10);

    /* Should NOT need compaction yet */
    TEST_ASSERT(!tl_compact_needed(tl));

    tl_close(tl);
}

TEST_DECLARE(cint_needed_at_threshold) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.max_delta_segments = 2;  /* Low threshold for testing */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments (at threshold) */
    compact_flush_n_times(tl, 2, 1000, 10);

    /* Should need compaction now */
    TEST_ASSERT(tl_compact_needed(tl));

    tl_close(tl);
}

/*===========================================================================
 * Compaction Selection Tests (Internal API)
 *
 * These test the internal tl_compact_select() function which determines
 * which L0 and L1 segments to include in a compaction round.
 *===========================================================================*/

TEST_DECLARE(cint_select_no_l0) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);

    /* Should return EOF when no L0 segments exist */
    TEST_ASSERT_STATUS(TL_EOF, tl_compact_select(&ctx));

    tl_compact_ctx_destroy(&ctx);
    tl_close(tl);
}

TEST_DECLARE(cint_select_selects_all_l0) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 3 L0 segments */
    compact_flush_n_times(tl, 3, 1000, 10);

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
 * Compaction Merge Tests (Internal API)
 *
 * These test the internal tl_compact_merge() function which performs the
 * actual merge of L0 segments into L1 output segments.
 *===========================================================================*/

TEST_DECLARE(cint_merge_basic) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments with non-overlapping records */
    compact_flush_n_times(tl, 2, 1000, 5);

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

TEST_DECLARE(cint_merge_with_tombstones) {
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

/**
 * Test compaction with multi-window output.
 *
 * This test verifies that compaction correctly handles inputs spanning
 * multiple windows and produces properly aligned L1 outputs with correct
 * window_start/window_end values.
 *
 * This catches regressions in window alignment or residual tombstone emission.
 */
TEST_DECLARE(cint_merge_multi_window) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.window_size = 1000;  /* Small windows for testing */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /*
     * Insert records spanning 3 windows:
     * - Window 0: [0, 1000) - records at 100, 200, 300
     * - Window 1: [1000, 2000) - records at 1100, 1200, 1300
     * - Window 2: [2000, 3000) - records at 2100, 2200, 2300
     */
    for (int w = 0; w < 3; w++) {
        for (int i = 0; i < 3; i++) {
            tl_ts_t ts = (tl_ts_t)(w * 1000 + 100 + i * 100);
            tl_status_t st = tl_append(tl, ts, (tl_handle_t)(ts + 1));
            TEST_ASSERT_STATUS(TL_OK, st);
        }
    }

    /* Add a tombstone spanning windows 0-1 boundary */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 800, 1200));

    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);

    TEST_ASSERT_STATUS(TL_OK, tl_compact_select(&ctx));
    TEST_ASSERT_STATUS(TL_OK, tl_compact_merge(&ctx));

    /* Should produce multiple L1 segments (one per window with data) */
    TEST_ASSERT(ctx.output_l1_len >= 2);  /* At least 2 windows have surviving data */

    /* Verify L1 segments have correct window alignment and are sorted */
    tl_ts_t prev_window_end = TL_TS_MIN;
    for (size_t i = 0; i < ctx.output_l1_len; i++) {
        tl_segment_t* seg = ctx.output_l1[i];
        TEST_ASSERT_NOT_NULL(seg);
        TEST_ASSERT(tl_segment_is_l1(seg));
        TEST_ASSERT(!tl_segment_has_tombstones(seg));  /* L1 is tombstone-free */

        /* Windows should be non-overlapping and sorted */
        TEST_ASSERT(seg->window_start >= prev_window_end);
        TEST_ASSERT(seg->window_start < seg->window_end);
        prev_window_end = seg->window_end;
    }

    tl_compact_ctx_destroy(&ctx);
    tl_close(tl);
}

/*===========================================================================
 * Compaction Publication Tests (Internal API)
 *
 * These test the internal tl_compact_publish() function which atomically
 * updates the manifest with compaction results.
 *===========================================================================*/

TEST_DECLARE(cint_publish_basic) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments */
    compact_flush_n_times(tl, 2, 1000, 5);

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
 * Compaction EBUSY Handling Tests (Internal API)
 *
 * These test the internal retry logic when manifest changes mid-compaction.
 *===========================================================================*/

/* Helper thread context for EBUSY test */
typedef struct {
    tl_timelog_t* tl;
    tl_mutex_t    mu;
    tl_cond_t     cond;
    bool          start;
    bool          done;
} compact_flush_thread_ctx_t;

/* Helper thread that performs a flush to change the manifest */
static void* compact_flush_thread_entry(void* arg) {
    compact_flush_thread_ctx_t* ctx = (compact_flush_thread_ctx_t*)arg;

    tl_mutex_lock(&ctx->mu);
    while (!ctx->start) {
        tl_cond_wait(&ctx->cond, &ctx->mu);
    }
    tl_mutex_unlock(&ctx->mu);

    /* Insert and flush to change the manifest */
    for (int i = 0; i < 5; i++) {
        tl_append(ctx->tl, 9000 + i, (tl_handle_t)(uintptr_t)(9000 + i));
    }
    tl_flush(ctx->tl);

    tl_mutex_lock(&ctx->mu);
    ctx->done = true;
    tl_cond_signal(&ctx->cond);
    tl_mutex_unlock(&ctx->mu);

    return NULL;
}

/**
 * Test: compaction publish succeeds via rebase when manifest changes mid-merge.
 *
 * Uses a helper thread to publish a new L0 segment between merge and publish,
 * which changes ctx->base_manifest. With rebase publish (Phase 2 OOO Scaling),
 * publish now succeeds because:
 * 1. All input segments are still present in the new manifest
 * 2. The new L0 from flush doesn't conflict with our L1 outputs
 *
 * Pre-Phase 2: Would return TL_EBUSY and require full retry
 * Post-Phase 2: Returns TL_OK via rebase (rebuilds manifest off-lock)
 */
TEST_DECLARE(cint_publish_ebusy_on_manifest_change) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create L0 segments to compact */
    compact_flush_n_times(tl, 2, 1000, 10);

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);
    TEST_ASSERT_STATUS(TL_OK, tl_compact_select(&ctx));
    TEST_ASSERT_STATUS(TL_OK, tl_compact_merge(&ctx));

    /* Start helper thread that will change the manifest */
    compact_flush_thread_ctx_t fctx = {0};
    fctx.tl = tl;
    TEST_ASSERT_STATUS(TL_OK, tl_mutex_init(&fctx.mu));
    TEST_ASSERT_STATUS(TL_OK, tl_cond_init(&fctx.cond));

    tl_thread_t th;
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&th, compact_flush_thread_entry, &fctx));

    tl_mutex_lock(&fctx.mu);
    fctx.start = true;
    tl_cond_signal(&fctx.cond);
    while (!fctx.done) {
        tl_cond_wait(&fctx.cond, &fctx.mu);
    }
    tl_mutex_unlock(&fctx.mu);

    TEST_ASSERT_STATUS(TL_OK, tl_thread_join(&th, NULL));

    /* With rebase publish (Phase 2), publish succeeds even with manifest change.
     * Inputs still present + no L1 conflict = rebase succeeds. */
    TEST_ASSERT_STATUS(TL_OK, tl_compact_publish(&ctx));

    tl_compact_ctx_destroy(&ctx);
    tl_cond_destroy(&fctx.cond);
    tl_mutex_destroy(&fctx.mu);
    tl_close(tl);
}

/*===========================================================================
 * Compaction Manual Mode Tests (Internal API)
 *
 * These test the internal compaction behavior in manual mode, including
 * how explicit compaction requests interact with the maintenance scheduler.
 *===========================================================================*/

/**
 * Test: tl_compact() + tl_maint_step() in manual mode.
 *
 * Verifies that explicit compaction request via tl_compact() is honored
 * by tl_maint_step() in manual mode (TL_MAINT_DISABLED).
 *
 * NOTE: This test uses tl_snapshot_manifest() which is an internal API.
 */
TEST_DECLARE(cint_manual_mode_explicit_request) {
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

/*===========================================================================
 * Compaction Retry Limit Tests (Internal API)
 *
 * These test the internal retry behavior when TL_EBUSY occurs repeatedly.
 * Requires TL_TEST_HOOKS to be defined for fault injection.
 *===========================================================================*/

#ifdef TL_TEST_HOOKS
extern volatile int tl_test_force_ebusy_count;

/**
 * Test: compact_one_exhausts_retries
 *
 * Purpose: Verify TL_EBUSY is returned after max retries, inputs remain intact.
 */
TEST_DECLARE(cint_one_exhausts_retries) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create L0 segments to compact */
    compact_flush_n_times(tl, 2, 1000, 10);

    /* Get L0 count before compaction attempt */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats_before;
    tl_stats(snap, &stats_before);
    tl_snapshot_release(snap);

    TEST_ASSERT(stats_before.segments_l0 >= 2);

    /* Force EBUSY for more than max_retries (default is 3) */
    tl_test_force_ebusy_count = 5;

    /* Should exhaust retries and return EBUSY */
    tl_status_t st = tl_compact_one(tl, 3);
    TEST_ASSERT_STATUS(TL_EBUSY, st);

    /* Verify inputs remain intact (L0 segments not consumed) */
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats_after;
    tl_stats(snap, &stats_after);
    tl_snapshot_release(snap);

    TEST_ASSERT_EQ((long long)stats_before.segments_l0,
                   (long long)stats_after.segments_l0);
    TEST_ASSERT_EQ((long long)stats_before.records_estimate,
                   (long long)stats_after.records_estimate);

    /* Reset hook and verify compaction now succeeds */
    tl_test_force_ebusy_count = 0;
    st = tl_compact_one(tl, 3);
    TEST_ASSERT_STATUS(TL_OK, st);

    /* Verify compaction actually happened (L1 created) */
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats(snap, &stats_after);
    tl_snapshot_release(snap);
    TEST_ASSERT(stats_after.segments_l1 > 0);

    tl_close(tl);
}
#endif /* TL_TEST_HOOKS */

/*===========================================================================
 * Phase 2 OOO Scaling Tests (Window-Bounded Selection + Rebase + Reshape)
 *
 * These tests verify the Phase 2 OOO Scaling implementation:
 * - Window-bounded L0 selection (max_compaction_windows cap)
 * - Rebase publish (succeed when inputs present despite manifest change)
 * - Reshape compaction (L0→L0 window-splitting)
 *===========================================================================*/

/**
 * Test: window-bounded selection caps L0 by window range.
 *
 * With max_compaction_windows=2, L0 segments spanning >2 windows should
 * trigger the window_bound_exceeded counter and still be selected (forward
 * progress guarantee).
 */
TEST_DECLARE(cint_window_bounded_selection_basic) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.max_compaction_windows = 2;  /* Tight window bound */
    cfg.window_size = 1000;          /* Windows at [0,1000), [1000,2000), etc */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create L0 spanning multiple windows */
    /* Window 0: ts 0-999 */
    for (int i = 0; i < 10; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100 + i, (tl_handle_t)(i + 1)));
    }
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Window 3: ts 3000-3999 (skips windows 1,2) */
    for (int i = 0; i < 10; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 3000 + i, (tl_handle_t)(i + 100)));
    }
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Selection should bound by target windows */
    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);

    tl_status_t st = tl_compact_select(&ctx);
    TEST_ASSERT_STATUS(TL_OK, st);

    /* With bounded selection, some L0s should be selected */
    TEST_ASSERT(ctx.input_l0_len > 0);

    /* The wide L0 spans 4 windows (0-3), exceeding our cap of 2.
     * Window-bounded selection should still work (forward progress). */

    tl_compact_ctx_destroy(&ctx);
    tl_close(tl);
}

/**
 * Test: window_bound_exceeded stat incremented for wide L0 segments.
 *
 * When a single L0 segment spans more windows than max_compaction_windows,
 * the window_bound_exceeded counter should be incremented for observability.
 */
TEST_DECLARE(cint_window_bound_exceeded_stat) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.max_compaction_windows = 1;  /* Very tight: single window */
    cfg.window_size = 100;           /* Small windows */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create single L0 spanning 5 windows [0,100), [100,200), ... [400,500) */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 50, (tl_handle_t)1));    /* Window 0 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 450, (tl_handle_t)2));   /* Window 4 */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Get initial stat */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats_before;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats_before));
    tl_snapshot_release(snap);

    /* Run selection which should detect wide L0 */
    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);
    tl_status_t st = tl_compact_select(&ctx);
    TEST_ASSERT_STATUS(TL_OK, st);
    tl_compact_ctx_destroy(&ctx);

    /* Get updated stat - window_bound_exceeded should have incremented */
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats_after;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats_after));
    tl_snapshot_release(snap);

    /* L0 spans 5 windows but cap is 1: should trigger exceeded */
    TEST_ASSERT(stats_after.window_bound_exceeded > stats_before.window_bound_exceeded);

    tl_close(tl);
}

/**
 * Test: window-bounded selection disabled when max_compaction_windows=0.
 *
 * Setting max_compaction_windows=0 means unlimited (legacy behavior).
 * All L0 segments should be selected regardless of span.
 */
TEST_DECLARE(cint_window_bounded_disabled_when_zero) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.max_compaction_windows = 0;  /* Disabled = unlimited */
    cfg.window_size = 100;
    cfg.max_compaction_inputs = 100; /* High cap to allow all */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 3 L0 segments spanning many windows */
    for (int seg = 0; seg < 3; seg++) {
        for (int i = 0; i < 5; i++) {
            tl_ts_t ts = (tl_ts_t)(seg * 1000 + i * 100);
            TEST_ASSERT_STATUS(TL_OK, tl_append(tl, ts, (tl_handle_t)(ts + 1)));
        }
        TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));
    }

    /* Selection should use greedy (all L0s selected) */
    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);
    TEST_ASSERT_STATUS(TL_OK, tl_compact_select(&ctx));

    /* All 3 L0 segments should be selected (greedy mode) */
    TEST_ASSERT_EQ(3, (long long)ctx.input_l0_len);

    tl_compact_ctx_destroy(&ctx);
    tl_close(tl);
}

/**
 * Test: rebase publish fallback when input removed by concurrent compaction.
 *
 * When inputs have been removed from manifest (by another compaction),
 * rebase cannot succeed and must return TL_EBUSY.
 */
TEST_DECLARE(cint_rebase_fallback_input_removed) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 4 L0 segments */
    compact_flush_n_times(tl, 4, 1000, 10);

    /* First compaction: select & merge (but don't publish yet) */
    tl_compact_ctx_t ctx1;
    tl_compact_ctx_init(&ctx1, tl, &tl->alloc);
    TEST_ASSERT_STATUS(TL_OK, tl_compact_select(&ctx1));
    TEST_ASSERT_STATUS(TL_OK, tl_compact_merge(&ctx1));

    /* Second compaction: runs to completion, removes the same L0s */
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

    /* Now try to publish first compaction - inputs are gone */
    tl_status_t st = tl_compact_publish(&ctx1);

    /* Rebase should fail because inputs no longer exist */
    TEST_ASSERT_STATUS(TL_EBUSY, st);

    /* Verify fallback counter was incremented */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    tl_snapshot_release(snap);

    TEST_ASSERT(stats.rebase_publish_fallback > 0);

    tl_compact_ctx_destroy(&ctx1);
    tl_close(tl);
}

/**
 * Test: rebase_publish_success stat incremented on successful rebase.
 *
 * When manifest changes but inputs still exist and no L1 conflict,
 * rebase succeeds and increments rebase_publish_success.
 */
TEST_DECLARE(cint_rebase_success_stat) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments for compaction */
    compact_flush_n_times(tl, 2, 1000, 10);

    /* Start compaction: select & merge */
    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);
    TEST_ASSERT_STATUS(TL_OK, tl_compact_select(&ctx));
    TEST_ASSERT_STATUS(TL_OK, tl_compact_merge(&ctx));

    /* Add a new L0 via flush (changes manifest but doesn't remove inputs) */
    for (int i = 0; i < 5; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 5000 + i, (tl_handle_t)(i + 1)));
    }
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Publish should succeed via rebase */
    TEST_ASSERT_STATUS(TL_OK, tl_compact_publish(&ctx));

    /* Verify success counter incremented */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    tl_snapshot_release(snap);

    TEST_ASSERT(stats.rebase_publish_success > 0);

    tl_compact_ctx_destroy(&ctx);
    tl_close(tl);
}

/**
 * Test: reshape config defaults are applied correctly.
 *
 * Verifies reshape_l0_threshold, reshape_max_inputs, and reshape_cooldown_max
 * are initialized to their documented defaults.
 */
TEST_DECLARE(cint_reshape_config_defaults) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    /* Verify Phase 2 reshape defaults from LLD */
    TEST_ASSERT_EQ(12, (long long)cfg.reshape_l0_threshold);
    TEST_ASSERT_EQ(4, (long long)cfg.reshape_max_inputs);
    TEST_ASSERT_EQ(3, (long long)cfg.reshape_cooldown_max);
    TEST_ASSERT_EQ(TL_COMPACT_AUTO, (int)cfg.compaction_strategy);
}

/**
 * Test: reshape compaction produces window-contained L0 outputs.
 *
 * When reshape is forced via TL_COMPACT_RESHAPE strategy, wide L0 segments
 * should be split into smaller, window-contained L0 segments.
 */
TEST_DECLARE(cint_reshape_outputs_window_contained) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.compaction_strategy = TL_COMPACT_RESHAPE;  /* Force reshape */
    cfg.window_size = 1000;
    cfg.reshape_max_inputs = 2;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create 2 L0 segments spanning multiple windows */
    /* First L0: windows 0 and 2 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100, (tl_handle_t)1));   /* Window 0 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 2100, (tl_handle_t)2));  /* Window 2 */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Second L0: windows 1 and 3 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 1100, (tl_handle_t)3));  /* Window 1 */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 3100, (tl_handle_t)4));  /* Window 3 */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Get pre-reshape stats */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats_before;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats_before));
    tl_snapshot_release(snap);

    TEST_ASSERT_EQ(2, (long long)stats_before.segments_l0);

    /* Run reshape compaction */
    TEST_ASSERT_STATUS(TL_OK, tl_compact_one(tl, 3));

    /* Get post-reshape stats */
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats_after;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats_after));
    tl_snapshot_release(snap);

    /* Reshape should produce multiple L0s (one per window with records).
     * We had 4 windows with records (0, 1, 2, 3), so expect 4 L0s. */
    TEST_ASSERT(stats_after.segments_l0 >= 4);
    TEST_ASSERT_EQ(0, (long long)stats_after.segments_l1);  /* No L1 from reshape */

    /* Verify reshape counter incremented */
    TEST_ASSERT(stats_after.reshape_compactions_total > 0);

    /* Verify all records still accessible */
    TEST_ASSERT_EQ(4, (long long)stats_after.records_estimate);

    tl_close(tl);
}

/**
 * Test: reshape cooldown prevents infinite reshape loops.
 *
 * After reshape_cooldown_max consecutive reshapes, AUTO mode should
 * fall back to L0→L1 compaction even if reshape trigger conditions are met.
 */
TEST_DECLARE(cint_reshape_cooldown_prevents_loops) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.compaction_strategy = TL_COMPACT_AUTO;
    cfg.reshape_cooldown_max = 2;    /* Low cooldown for testing */
    cfg.reshape_l0_threshold = 2;    /* Trigger reshape easily */
    cfg.window_size = 1000;
    cfg.max_delta_segments = 100;    /* High to avoid triggering L0->L1 */

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Create wide L0s that would normally trigger reshape */
    for (int round = 0; round < 3; round++) {
        /* Create 2 wide L0s (exceeds reshape_l0_threshold) */
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 100 + round * 10000, (tl_handle_t)1));
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 5100 + round * 10000, (tl_handle_t)2));
        TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 2100 + round * 10000, (tl_handle_t)3));
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 7100 + round * 10000, (tl_handle_t)4));
        TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

        /* Run compaction (AUTO mode will choose reshape or L0->L1) */
        tl_status_t st = tl_compact_one(tl, 3);
        /* May return TL_OK or TL_EOF depending on state */
        (void)st;
    }

    /* After cooldown_max (2) consecutive reshapes, L0->L1 should run.
     * This is verified by checking that L1 segments exist. */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    tl_snapshot_release(snap);

    /* After multiple rounds with cooldown, should have done at least one L0->L1 */
    /* Note: This test may be flaky depending on exact segment counts */
    TEST_ASSERT(stats.reshape_compactions_total <= cfg.reshape_cooldown_max ||
                stats.segments_l1 > 0);

    tl_close(tl);
}

/**
 * Test: Phase 2 stats fields initialized to zero.
 *
 * Verifies all new Phase 2 stats fields are present and zeroed initially.
 */
TEST_DECLARE(cint_phase2_stats_initialized) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));

    /* All Phase 2 counters should be zero initially */
    TEST_ASSERT_EQ(0, (long long)stats.reshape_compactions_total);
    TEST_ASSERT_EQ(0, (long long)stats.rebase_publish_success);
    TEST_ASSERT_EQ(0, (long long)stats.rebase_publish_fallback);
    TEST_ASSERT_EQ(0, (long long)stats.window_bound_exceeded);
    TEST_ASSERT_EQ(0, (long long)stats.rebase_l1_conflict);

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_compaction_internal_tests(void) {
    /* Compaction trigger tests (3 tests) */
    RUN_TEST(cint_needed_empty);
    RUN_TEST(cint_needed_below_threshold);
    RUN_TEST(cint_needed_at_threshold);

    /* Compaction selection tests (2 tests) */
    RUN_TEST(cint_select_no_l0);
    RUN_TEST(cint_select_selects_all_l0);

    /* Compaction merge tests (2 tests) */
    RUN_TEST(cint_merge_basic);
    RUN_TEST(cint_merge_with_tombstones);
    RUN_TEST(cint_merge_multi_window);

    /* Compaction publication tests (1 test) */
    RUN_TEST(cint_publish_basic);

    /* Compaction EBUSY handling tests (1 test) */
    RUN_TEST(cint_publish_ebusy_on_manifest_change);

    /* Compaction manual mode tests (1 test) */
    RUN_TEST(cint_manual_mode_explicit_request);

    /* Phase 2 OOO Scaling Tests - Window-Bounded Selection (3 tests) */
    RUN_TEST(cint_window_bounded_selection_basic);
    RUN_TEST(cint_window_bound_exceeded_stat);
    RUN_TEST(cint_window_bounded_disabled_when_zero);

    /* Phase 2 OOO Scaling Tests - Rebase Publish (2 tests) */
    RUN_TEST(cint_rebase_fallback_input_removed);
    RUN_TEST(cint_rebase_success_stat);

    /* Phase 2 OOO Scaling Tests - Reshape Compaction (4 tests) */
    RUN_TEST(cint_reshape_config_defaults);
    RUN_TEST(cint_reshape_outputs_window_contained);
    RUN_TEST(cint_reshape_cooldown_prevents_loops);
    RUN_TEST(cint_phase2_stats_initialized);

#ifdef TL_TEST_HOOKS
    /* Compaction retry limit tests (1 test) */
    RUN_TEST(cint_one_exhausts_retries);
#endif
}
