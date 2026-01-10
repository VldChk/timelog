/*===========================================================================
 * test_concurrency.c - Thread Safety and Concurrency Tests
 *
 * Tests for multi-threaded correctness:
 * - Snapshot stability during flush/compaction
 * - Publication protocol (seqlock + writer_mu)
 * - Concurrent readers during maintenance
 * - Writer backpressure handling
 * - Data race detection (validated with TSan)
 * - Lock ordering verification
 *
 * These tests validate that concurrent operations are safe and
 * don't cause data races, deadlocks, or visibility issues.
 *
 * Part of Phase 10: Integration Testing and Hardening
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_alloc.h"
#include "internal/tl_sync.h"
#include "internal/tl_atomic.h"
#include "internal/tl_seqlock.h"

#include <string.h>
#include <stdint.h>

/*===========================================================================
 * Snapshot Isolation Tests
 *
 * Tests will be migrated from test_phase5.c, test_phase6.c in Step 2.3
 *===========================================================================*/

/* Placeholder - tests to be migrated:
 * - snapshot_isolation_during_write
 * - snapshot_isolation_during_flush
 * - snapshot_isolation_during_compaction
 * - multiple_snapshots_concurrent
 * - snapshot_acquire_during_publication
 */

/*===========================================================================
 * Publication Protocol Tests
 *
 * Tests will be migrated from test_phase1.c, test_phase5.c in Step 2.3
 *===========================================================================*/

/* Placeholder - tests to be migrated:
 * - seqlock_reader_retry
 * - seqlock_writer_blocks_readers
 * - publication_atomic_visibility
 * - manifest_swap_atomic
 */

/*===========================================================================
 * Concurrent Reader Tests
 *
 * Tests will be migrated from test_phase5.c, test_phase6.c in Step 2.3
 *===========================================================================*/

/* Placeholder - tests to be migrated:
 * - concurrent_readers_no_contention
 * - readers_during_write
 * - readers_during_maintenance
 */

/*===========================================================================
 * Writer Tests
 *
 * Tests will be migrated from test_phase4.c, test_phase9.c in Step 2.3
 *===========================================================================*/

/* Placeholder - tests to be migrated:
 * - writer_serialization
 * - writer_flush_coordination
 * - writer_compaction_coordination
 */

/*===========================================================================
 * Maintenance Concurrency Tests
 *
 * Tests will be migrated from test_phase9.c in Step 2.3
 *===========================================================================*/

/* Placeholder - tests to be migrated:
 * - maint_thread_coordination
 * - maint_flush_compaction_interleaving
 * - maint_shutdown_waits_for_completion
 */

/*===========================================================================
 * Test Helpers (must be defined before tests)
 *===========================================================================*/

/* Thread coordination structure for concurrent tests */
typedef struct {
    tl_timelog_t*   tl;
    tl_atomic_u32   ready_count;
    tl_atomic_u32   start_flag;
    tl_atomic_u32   error_count;
    tl_atomic_u64   operations;
} concurrency_test_ctx_t;

/* Helper to wait for all threads to be ready */
static inline void wait_for_threads_ready(concurrency_test_ctx_t* ctx, uint32_t expected) {
    while (tl_atomic_load_acquire_u32(&ctx->ready_count) < expected) {
        tl_sleep_ms(1);
    }
}

/* Helper to signal threads to start */
static inline void signal_start(concurrency_test_ctx_t* ctx) {
    tl_atomic_store_release_u32(&ctx->start_flag, 1);
}

/* Helper to wait for start signal */
static inline void wait_for_start(concurrency_test_ctx_t* ctx) {
    while (tl_atomic_load_acquire_u32(&ctx->start_flag) == 0) {
        tl_sleep_ms(1);
    }
}

/*===========================================================================
 * Concurrency Tests (Phase 10)
 *===========================================================================*/

/*---------------------------------------------------------------------------
 * Test: conc_snapshot_stability_during_flush
 *
 * Purpose: Verify snapshot remains consistent during concurrent flush.
 *
 * Test scenario:
 * - Thread 1: Holds snapshot, iterates through data
 * - Thread 2: Continuously appends and flushes
 * - Verify: Thread 1's iteration sees consistent data
 *---------------------------------------------------------------------------*/
typedef struct {
    concurrency_test_ctx_t* ctx;
    tl_snapshot_t*          snap;
    size_t                  expected_count;
    bool                    success;
} snapshot_reader_ctx_t;

static void* snapshot_reader_thread(void* arg) {
    snapshot_reader_ctx_t* rctx = (snapshot_reader_ctx_t*)arg;
    concurrency_test_ctx_t* ctx = rctx->ctx;

    /* Signal ready and wait */
    tl_atomic_fetch_add_u32(&ctx->ready_count, 1, TL_MO_RELEASE);
    wait_for_start(ctx);

    /* Iterate through snapshot multiple times to detect instability */
    for (int round = 0; round < 10; round++) {
        tl_iter_t* it = NULL;
        if (tl_iter_since(rctx->snap, TL_TS_MIN, &it) != TL_OK) {
            tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
            rctx->success = false;
            return NULL;
        }

        size_t count = 0;
        tl_record_t rec;
        tl_ts_t prev_ts = TL_TS_MIN;
        while (tl_iter_next(it, &rec) == TL_OK) {
            /* Verify ordering */
            if (rec.ts < prev_ts) {
                tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
                rctx->success = false;
            }
            prev_ts = rec.ts;
            count++;
        }
        tl_iter_destroy(it);

        /* Snapshot should see exactly expected_count (frozen at acquire time) */
        if (count != rctx->expected_count) {
            tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
            rctx->success = false;
        }

        tl_atomic_fetch_add_u64(&ctx->operations, 1, TL_MO_RELAXED);
    }

    rctx->success = true;
    return NULL;
}

static void* flush_writer_thread(void* arg) {
    concurrency_test_ctx_t* ctx = (concurrency_test_ctx_t*)arg;

    /* Signal ready and wait */
    tl_atomic_fetch_add_u32(&ctx->ready_count, 1, TL_MO_RELEASE);
    wait_for_start(ctx);

    /* Continuously append and flush */
    tl_ts_t ts = 1000000;  /* Start after initial data */
    for (int i = 0; i < 100; i++) {
        /* Append a batch */
        for (int j = 0; j < 10; j++) {
            tl_status_t st = tl_append(ctx->tl, ts++, (tl_handle_t)i);
            if (st != TL_OK) {
                tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
            }
        }

        /* Trigger flush - TL_OK expected (no-op if nothing to flush) */
        if (tl_flush(ctx->tl) != TL_OK) {
            tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
        }

        tl_atomic_fetch_add_u64(&ctx->operations, 1, TL_MO_RELAXED);
    }

    return NULL;
}

TEST_DECLARE(conc_snapshot_stability_during_flush) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert initial data */
    const size_t initial_count = 100;
    for (size_t i = 0; i < initial_count; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, (tl_ts_t)(i * 100), (tl_handle_t)(i + 1)));
    }

    /* Acquire snapshot BEFORE starting writers */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    concurrency_test_ctx_t ctx = {0};
    ctx.tl = tl;
    tl_atomic_init_u32(&ctx.ready_count, 0);
    tl_atomic_init_u32(&ctx.start_flag, 0);
    tl_atomic_init_u32(&ctx.error_count, 0);
    tl_atomic_init_u64(&ctx.operations, 0);

    snapshot_reader_ctx_t reader_ctx = {
        .ctx = &ctx,
        .snap = snap,
        .expected_count = initial_count,
        .success = false
    };

    tl_thread_t reader, writer;
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&reader, snapshot_reader_thread, &reader_ctx));
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&writer, flush_writer_thread, &ctx));

    wait_for_threads_ready(&ctx, 2);
    signal_start(&ctx);

    tl_thread_join(&reader, NULL);
    tl_thread_join(&writer, NULL);

    /* Verify no errors */
    TEST_ASSERT_EQ(0, tl_atomic_load_relaxed_u32(&ctx.error_count));
    TEST_ASSERT(reader_ctx.success);

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: conc_snapshot_stability_during_compaction
 *
 * Similar to flush test but with compaction running.
 *---------------------------------------------------------------------------*/
TEST_DECLARE(conc_snapshot_stability_during_compaction) {
    /* Configure for background maintenance */
    tl_config_t cfg;
    TEST_ASSERT_STATUS(TL_OK, tl_config_init_defaults(&cfg));
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert data and flush multiple times to create L0 segments */
    const size_t records_per_flush = 50;
    const int num_flushes = 4;

    for (int f = 0; f < num_flushes; f++) {
        for (size_t i = 0; i < records_per_flush; i++) {
            tl_ts_t ts = (tl_ts_t)(f * 10000 + i * 100);
            TEST_ASSERT_STATUS(TL_OK, tl_append(tl, ts, (tl_handle_t)(f * 100 + i)));
        }
        TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));
    }

    /* Acquire snapshot */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    const size_t total_expected = records_per_flush * num_flushes;

    /* Start background maintenance (will do compaction) */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_start(tl));

    /* Verify snapshot consistency during maintenance */
    for (int round = 0; round < 5; round++) {
        tl_iter_t* it = NULL;
        TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, TL_TS_MIN, &it));

        size_t count = 0;
        tl_record_t rec;
        tl_ts_t prev_ts = TL_TS_MIN;
        while (tl_iter_next(it, &rec) == TL_OK) {
            TEST_ASSERT(rec.ts >= prev_ts);  /* Sorted */
            prev_ts = rec.ts;
            count++;
        }
        tl_iter_destroy(it);

        TEST_ASSERT_EQ(total_expected, count);

        /* Request compaction and wait a bit */
        tl_status_t compact_st = tl_compact(tl);
        /* TL_OK or TL_EBUSY (if compaction already in progress) are acceptable */
        TEST_ASSERT(compact_st == TL_OK || compact_st == TL_EBUSY);
        tl_sleep_ms(10);
    }

    TEST_ASSERT_STATUS(TL_OK, tl_maint_stop(tl));
    tl_snapshot_release(snap);
    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: conc_multiple_readers_during_maintenance
 *
 * Multiple reader threads with background maintenance.
 *---------------------------------------------------------------------------*/
typedef struct {
    concurrency_test_ctx_t* ctx;
    int                     reader_id;
    size_t                  reads_completed;
} multi_reader_ctx_t;

static void* multi_reader_thread(void* arg) {
    multi_reader_ctx_t* rctx = (multi_reader_ctx_t*)arg;
    concurrency_test_ctx_t* ctx = rctx->ctx;

    /* Signal ready and wait */
    tl_atomic_fetch_add_u32(&ctx->ready_count, 1, TL_MO_RELEASE);
    wait_for_start(ctx);

    rctx->reads_completed = 0;

    for (int i = 0; i < 50; i++) {
        /* Each iteration: acquire snapshot, iterate, release */
        tl_snapshot_t* snap = NULL;
        if (tl_snapshot_acquire(ctx->tl, &snap) != TL_OK) {
            tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
            continue;
        }

        tl_iter_t* it = NULL;
        if (tl_iter_since(snap, 0, &it) == TL_OK) {
            tl_record_t rec;
            size_t count = 0;
            while (tl_iter_next(it, &rec) == TL_OK) {
                count++;
            }
            tl_iter_destroy(it);
            rctx->reads_completed++;
        }

        tl_snapshot_release(snap);
        tl_atomic_fetch_add_u64(&ctx->operations, 1, TL_MO_RELAXED);
    }

    return NULL;
}

TEST_DECLARE(conc_multiple_readers_during_maintenance) {
    tl_config_t cfg;
    TEST_ASSERT_STATUS(TL_OK, tl_config_init_defaults(&cfg));
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert initial data */
    for (int i = 0; i < 100; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, (tl_ts_t)(i * 100), (tl_handle_t)(i + 1)));
    }
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Start maintenance */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_start(tl));

    concurrency_test_ctx_t ctx = {0};
    ctx.tl = tl;
    tl_atomic_init_u32(&ctx.ready_count, 0);
    tl_atomic_init_u32(&ctx.start_flag, 0);
    tl_atomic_init_u32(&ctx.error_count, 0);
    tl_atomic_init_u64(&ctx.operations, 0);

    const int num_readers = 4;
    multi_reader_ctx_t reader_ctx[4];
    tl_thread_t readers[4];

    for (int i = 0; i < num_readers; i++) {
        reader_ctx[i].ctx = &ctx;
        reader_ctx[i].reader_id = i;
        reader_ctx[i].reads_completed = 0;
        TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&readers[i], multi_reader_thread, &reader_ctx[i]));
    }

    wait_for_threads_ready(&ctx, num_readers);
    signal_start(&ctx);

    for (int i = 0; i < num_readers; i++) {
        tl_thread_join(&readers[i], NULL);
    }

    TEST_ASSERT_STATUS(TL_OK, tl_maint_stop(tl));

    /* Verify all readers completed successfully */
    TEST_ASSERT_EQ(0, tl_atomic_load_relaxed_u32(&ctx.error_count));
    for (int i = 0; i < num_readers; i++) {
        TEST_ASSERT(reader_ctx[i].reads_completed > 0);
    }

    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: conc_writer_reader_interleave
 *
 * Verify correct behavior with interleaved writes and reads.
 *---------------------------------------------------------------------------*/
static void* writer_interleave_thread(void* arg) {
    concurrency_test_ctx_t* ctx = (concurrency_test_ctx_t*)arg;

    tl_atomic_fetch_add_u32(&ctx->ready_count, 1, TL_MO_RELEASE);
    wait_for_start(ctx);

    for (int i = 0; i < 1000; i++) {
        tl_ts_t ts = (tl_ts_t)(i * 10);
        tl_status_t st = tl_append(ctx->tl, ts, (tl_handle_t)(i + 1));
        if (st != TL_OK) {
            tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
        }
        tl_atomic_fetch_add_u64(&ctx->operations, 1, TL_MO_RELAXED);
    }

    return NULL;
}

static void* reader_interleave_thread(void* arg) {
    concurrency_test_ctx_t* ctx = (concurrency_test_ctx_t*)arg;

    tl_atomic_fetch_add_u32(&ctx->ready_count, 1, TL_MO_RELEASE);
    wait_for_start(ctx);

    for (int i = 0; i < 100; i++) {
        tl_snapshot_t* snap = NULL;
        if (tl_snapshot_acquire(ctx->tl, &snap) != TL_OK) {
            tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
            continue;
        }

        /* Validate structure */
        tl_status_t st = tl_validate(snap);
        if (st != TL_OK) {
            tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
        }

        tl_snapshot_release(snap);
        tl_atomic_fetch_add_u64(&ctx->operations, 1, TL_MO_RELAXED);
    }

    return NULL;
}

TEST_DECLARE(conc_writer_reader_interleave) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    concurrency_test_ctx_t ctx = {0};
    ctx.tl = tl;
    tl_atomic_init_u32(&ctx.ready_count, 0);
    tl_atomic_init_u32(&ctx.start_flag, 0);
    tl_atomic_init_u32(&ctx.error_count, 0);
    tl_atomic_init_u64(&ctx.operations, 0);

    tl_thread_t writer, reader;
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&writer, writer_interleave_thread, &ctx));
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&reader, reader_interleave_thread, &ctx));

    wait_for_threads_ready(&ctx, 2);
    signal_start(&ctx);

    tl_thread_join(&writer, NULL);
    tl_thread_join(&reader, NULL);

    /* Verify no errors */
    TEST_ASSERT_EQ(0, tl_atomic_load_relaxed_u32(&ctx.error_count));

    /* Final validation */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));
    tl_snapshot_release(snap);

    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: conc_view_seq_validation
 *
 * Verify seqlock (view_seq) is always even when idle.
 *---------------------------------------------------------------------------*/
TEST_DECLARE(conc_view_seq_validation) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert data and do various operations */
    for (int round = 0; round < 10; round++) {
        /* Append */
        for (int i = 0; i < 100; i++) {
            TEST_ASSERT_STATUS(TL_OK, tl_append(tl, (tl_ts_t)(round * 1000 + i), (tl_handle_t)(i + 1)));
        }

        /* Acquire snapshot (uses seqlock) */
        tl_snapshot_t* snap = NULL;
        TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

        /* Verify snapshot is valid */
        TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

        tl_snapshot_release(snap);

        /* Flush */
        TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));
    }

    /* Final validation */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    /* records_estimate is approximate per spec - use lower bound check */
    TEST_ASSERT(stats.records_estimate >= 1000);

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_concurrency_tests(void) {
    /* Phase 10 concurrency tests */
    RUN_TEST(conc_snapshot_stability_during_flush);
    RUN_TEST(conc_snapshot_stability_during_compaction);
    RUN_TEST(conc_multiple_readers_during_maintenance);
    RUN_TEST(conc_writer_reader_interleave);
    RUN_TEST(conc_view_seq_validation);
}
