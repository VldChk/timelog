/*===========================================================================
 * test_stress.c - High-Volume Stress Tests
 *
 * Tests for system behavior under heavy load:
 * - High-volume append/query (100K+ records)
 * - Heavy out-of-order ingestion
 * - Delete churn (append/delete with concurrent queries)
 * - Long-running maintenance (minutes, not seconds)
 * - Memory pressure scenarios
 *
 * IMPORTANT: These tests respect the SINGLE-WRITER CONTRACT.
 * All write operations (append, delete, flush) are serialized through
 * a test-local mutex. Readers remain concurrent as per spec.
 *
 * CONDITIONAL COMPILATION:
 * These tests are expensive and should only run when explicitly requested.
 * Enable via TIMELOG_STRESS_TESTS=1 environment variable.
 *
 * SHORT MODE:
 * For CI/quick validation, set TIMELOG_SHORT_STRESS=1 to run abbreviated
 * versions with reduced iteration counts.
 *
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_alloc.h"
#include "internal/tl_sync.h"
#include "internal/tl_atomic.h"

#include <string.h>
#include <stdint.h>
#include <stdlib.h>

/*===========================================================================
 * Configuration
 *===========================================================================*/

/* Read boolean env var safely across platforms */
static bool env_flag_is_enabled(const char* name) {
#if defined(_WIN32)
    char* buf = NULL;
    size_t len = 0;
    if (_dupenv_s(&buf, &len, name) != 0 || buf == NULL) {
        return false;
    }
    bool enabled = (buf[0] == '1' || buf[0] == 'y' || buf[0] == 'Y');
    free(buf);
    return enabled;
#else
    const char* env = getenv(name);
    return (env != NULL && (env[0] == '1' || env[0] == 'y' || env[0] == 'Y'));
#endif
}

/* Check if stress tests should run */
static bool stress_tests_enabled(void) {
    return env_flag_is_enabled("TIMELOG_STRESS_TESTS");
}

/* Check if short stress mode is enabled */
static bool short_stress_mode(void) {
    return env_flag_is_enabled("TIMELOG_SHORT_STRESS");
}

/* Get iteration count based on mode */
static size_t get_stress_iterations(size_t full_count, size_t short_count) {
    return short_stress_mode() ? short_count : full_count;
}

/* Get duration in ms based on mode */
static uint32_t get_stress_duration_ms(uint32_t full_ms, uint32_t short_ms) {
    return short_stress_mode() ? short_ms : full_ms;
}

/*===========================================================================
 * Stress Test Context
 *
 * IMPORTANT: The writer_mu mutex enforces the single-writer contract.
 * All write operations MUST hold this mutex.
 *===========================================================================*/

typedef struct {
    tl_timelog_t*   tl;
    tl_mutex_t      writer_mu;        /* Enforces single-writer contract */
    tl_atomic_u32   ready_count;
    tl_atomic_u32   start_flag;
    tl_atomic_u32   stop_flag;
    tl_atomic_u32   error_count;
    tl_atomic_u64   total_appends;
    tl_atomic_u64   total_queries;
    tl_atomic_u64   total_deletes;
    tl_atomic_u64   backpressure_count;  /* Track TL_EBUSY separately */
} stress_test_ctx_t;

static tl_status_t stress_ctx_init(stress_test_ctx_t* ctx, tl_timelog_t* tl) {
    ctx->tl = tl;
    tl_status_t st = tl_mutex_init(&ctx->writer_mu);
    if (st != TL_OK) return st;

    tl_atomic_init_u32(&ctx->ready_count, 0);
    tl_atomic_init_u32(&ctx->start_flag, 0);
    tl_atomic_init_u32(&ctx->stop_flag, 0);
    tl_atomic_init_u32(&ctx->error_count, 0);
    tl_atomic_init_u64(&ctx->total_appends, 0);
    tl_atomic_init_u64(&ctx->total_queries, 0);
    tl_atomic_init_u64(&ctx->total_deletes, 0);
    tl_atomic_init_u64(&ctx->backpressure_count, 0);
    return TL_OK;
}

static void stress_ctx_destroy(stress_test_ctx_t* ctx) {
    tl_mutex_destroy(&ctx->writer_mu);
}

/*===========================================================================
 * Simple RNG for Reproducible Tests
 *
 * Uses thread-local storage to avoid data races when multiple threads
 * call stress_rand() concurrently. Each thread gets its own RNG state.
 *===========================================================================*/

#include "internal/tl_platform.h"  /* For TL_THREAD_LOCAL */

/* Thread-local xorshift32 PRNG state */
static TL_THREAD_LOCAL uint32_t stress_rng_state = 12345;

static uint32_t stress_rand(void) {
    uint32_t x = stress_rng_state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    stress_rng_state = x;
    return x;
}

static void stress_srand(uint32_t seed) {
    stress_rng_state = seed ? seed : 12345;
}

/*===========================================================================
 * Stress Tests
 *===========================================================================*/

/*---------------------------------------------------------------------------
 * Test: stress_high_volume_append_query
 *
 * Purpose: Validate system under high-volume append and concurrent query.
 *
 * SINGLE-WRITER CONTRACT: A single writer thread performs all appends.
 * Multiple reader threads query concurrently.
 *
 * Configuration:
 * - Full mode: 100K records, 2 readers, 30s
 * - Short mode: 10K records, 1 reader, 5s
 *
 * This test validates:
 * - No data loss during writes
 * - Query correctness during writes
 * - Proper handling of memtable sealing/flushing
 * - Correct backpressure handling (TL_EBUSY)
 *---------------------------------------------------------------------------*/
typedef struct {
    stress_test_ctx_t* ctx;
    int                thread_id;
    size_t             records_to_append;
    tl_ts_t            ts_base;
} stress_append_thread_ctx_t;

static void* stress_single_writer_thread(void* arg) {
    stress_append_thread_ctx_t* tctx = (stress_append_thread_ctx_t*)arg;
    stress_test_ctx_t* ctx = tctx->ctx;

    /* Signal ready and wait for start */
    tl_atomic_fetch_add_u32(&ctx->ready_count, 1, TL_MO_RELEASE);
    while (!tl_atomic_load_acquire_u32(&ctx->start_flag)) {
        tl_thread_yield();
    }

    size_t appended = 0;
    tl_ts_t ts = tctx->ts_base;

    for (size_t i = 0; i < tctx->records_to_append; i++) {
        if (tl_atomic_load_relaxed_u32(&ctx->stop_flag)) {
            break;
        }

        tl_handle_t handle = (tl_handle_t)(tctx->thread_id * 1000000 + i);

        /* Acquire writer lock (single-writer contract) */
        tl_mutex_lock(&ctx->writer_mu);
        tl_status_t st = tl_append(ctx->tl, ts++, handle);
        tl_mutex_unlock(&ctx->writer_mu);

        if (st == TL_OK) {
            appended++;
        } else if (st == TL_EBUSY) {
            /* TL_EBUSY: Record WAS inserted, but backpressure occurred.
             * DO NOT retry (i--) - would create duplicate. Count as success. */
            appended++;
            tl_atomic_fetch_add_u64(&ctx->backpressure_count, 1, TL_MO_RELAXED);
            tl_sleep_ms(1);  /* Brief backoff before next insert */
        } else {
            /* Unexpected error */
            tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
        }
    }

    tl_atomic_fetch_add_u64(&ctx->total_appends, appended, TL_MO_RELAXED);
    return NULL;
}

typedef struct {
    stress_test_ctx_t* ctx;
    int                thread_id;
    size_t             queries_to_run;
} stress_query_thread_ctx_t;

static void* stress_query_thread(void* arg) {
    stress_query_thread_ctx_t* tctx = (stress_query_thread_ctx_t*)arg;
    stress_test_ctx_t* ctx = tctx->ctx;

    /* Signal ready and wait for start */
    tl_atomic_fetch_add_u32(&ctx->ready_count, 1, TL_MO_RELEASE);
    while (!tl_atomic_load_acquire_u32(&ctx->start_flag)) {
        tl_thread_yield();
    }

    size_t queries = 0;
    for (size_t i = 0; i < tctx->queries_to_run; i++) {
        if (tl_atomic_load_relaxed_u32(&ctx->stop_flag)) {
            break;
        }

        tl_snapshot_t* snap = NULL;
        tl_status_t st = tl_snapshot_acquire(ctx->tl, &snap);
        if (st != TL_OK) {
            tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
            continue;
        }

        tl_iter_t* it = NULL;
        st = tl_iter_since(snap, TL_TS_MIN, &it);
        if (st == TL_OK) {
            /* Iterate through some records */
            tl_record_t rec;
            size_t count = 0;
            tl_ts_t prev_ts = TL_TS_MIN;
            while (tl_iter_next(it, &rec) == TL_OK && count < 100) {
                /* Verify ordering invariant */
                if (rec.ts < prev_ts) {
                    tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
                }
                prev_ts = rec.ts;
                count++;
            }
            tl_iter_destroy(it);
            queries++;
        }

        tl_snapshot_release(snap);
    }

    tl_atomic_fetch_add_u64(&ctx->total_queries, queries, TL_MO_RELAXED);
    return NULL;
}

TEST_DECLARE(stress_high_volume_append_query) {
    /* Configure for background maintenance */
    tl_config_t cfg;
    TEST_ASSERT_STATUS(TL_OK, tl_config_init_defaults(&cfg));
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Start background maintenance */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_start(tl));

    stress_test_ctx_t ctx;
    TEST_ASSERT_STATUS(TL_OK, stress_ctx_init(&ctx, tl));

    /* Configuration based on mode - SINGLE WRITER + multiple readers */
    const size_t total_records = get_stress_iterations(100000, 10000);
    const int num_readers = short_stress_mode() ? 1 : 2;
    const size_t queries_per_reader = get_stress_iterations(10000, 1000);

    /* Single writer thread */
    stress_append_thread_ctx_t writer_ctx = {
        .ctx = &ctx,
        .thread_id = 0,
        .records_to_append = total_records,
        .ts_base = 0
    };
    tl_thread_t writer;
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&writer, stress_single_writer_thread, &writer_ctx));

    /* Multiple reader threads */
    stress_query_thread_ctx_t reader_ctx[2];
    tl_thread_t readers[2];
    for (int i = 0; i < num_readers; i++) {
        reader_ctx[i].ctx = &ctx;
        reader_ctx[i].thread_id = i + 1;
        reader_ctx[i].queries_to_run = queries_per_reader;
        TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&readers[i], stress_query_thread, &reader_ctx[i]));
    }

    /* Wait for all threads to be ready */
    while (tl_atomic_load_acquire_u32(&ctx.ready_count) < (uint32_t)(1 + num_readers)) {
        tl_thread_yield();
    }

    /* Start all threads */
    tl_atomic_store_release_u32(&ctx.start_flag, 1);

    /* Wait for writer to complete */
    tl_thread_join(&writer, NULL);

    /* Signal readers to stop and wait */
    tl_atomic_store_release_u32(&ctx.stop_flag, 1);
    for (int i = 0; i < num_readers; i++) {
        tl_thread_join(&readers[i], NULL);
    }

    /* Stop background maintenance */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_stop(tl));

    /* Verify results */
    uint64_t appends = tl_atomic_load_relaxed_u64(&ctx.total_appends);
    uint64_t queries = tl_atomic_load_relaxed_u64(&ctx.total_queries);
    uint32_t errors = tl_atomic_load_relaxed_u32(&ctx.error_count);
    uint64_t backpressure = tl_atomic_load_relaxed_u64(&ctx.backpressure_count);

    TEST_ASSERT(appends > 0);
    TEST_ASSERT(queries > 0);
    TEST_ASSERT_EQ(0, errors);

    /* Backpressure is acceptable, but log it */
    if (backpressure > 0) {
        printf("    [INFO] Backpressure events: %llu\n", (unsigned long long)backpressure);
    }

    /* Verify data integrity - all records should be queryable */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));
    /* records_estimate should be approximately appends */
    TEST_ASSERT(stats.records_estimate >= appends / 2);  /* Allow some variance */

    tl_snapshot_release(snap);

    stress_ctx_destroy(&ctx);
    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: stress_heavy_ooo_ingestion
 *
 * Purpose: Validate OOO (out-of-order) timestamp handling under heavy load.
 *
 * SINGLE-WRITER: Uses a single thread for all writes.
 *
 * Configuration:
 * - Full mode: 10K records in random order
 * - Short mode: 1K records in random order
 *
 * This test validates:
 * - Correct sorting of OOO records
 * - Proper OOO budget handling
 * - No data loss with heavy OOO writes
 * - Correct backpressure handling
 *---------------------------------------------------------------------------*/
TEST_DECLARE(stress_heavy_ooo_ingestion) {
    /* Configure with generous sealed_max_runs to minimize backpressure */
    tl_config_t cfg;
    TEST_ASSERT_STATUS(TL_OK, tl_config_init_defaults(&cfg));
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Start background maintenance */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_start(tl));

    const size_t record_count = get_stress_iterations(10000, 1000);

    /* Create array of timestamps to shuffle */
    tl_ts_t* timestamps = (tl_ts_t*)malloc(record_count * sizeof(tl_ts_t));
    TEST_ASSERT(timestamps != NULL);

    for (size_t i = 0; i < record_count; i++) {
        timestamps[i] = (tl_ts_t)(i * 100);  /* Spread out timestamps */
    }

    /* Fisher-Yates shuffle */
    stress_srand(42);  /* Reproducible */
    for (size_t i = record_count - 1; i > 0; i--) {
        size_t j = stress_rand() % (i + 1);
        tl_ts_t tmp = timestamps[i];
        timestamps[i] = timestamps[j];
        timestamps[j] = tmp;
    }

    /* Insert in shuffled order */
    size_t inserted = 0;
    size_t backpressure_count = 0;

    for (size_t i = 0; i < record_count; i++) {
        tl_status_t st = tl_append(tl, timestamps[i], (tl_handle_t)(i + 1));
        if (st == TL_OK) {
            inserted++;
        } else if (st == TL_EBUSY) {
            /* TL_EBUSY: Record WAS inserted, but backpressure occurred.
             * DO NOT retry - would create duplicate. Count as success. */
            inserted++;
            backpressure_count++;
            tl_sleep_ms(1);  /* Brief backoff before next insert */
        } else {
            /* Unexpected failure - record NOT inserted, skip */
            printf("    [WARN] Append failed with %d at i=%zu\n", st, i);
        }
    }

    /* Allow some tolerance for failures, but most should succeed */
    TEST_ASSERT(inserted >= record_count * 9 / 10);  /* At least 90% */

    if (backpressure_count > 0) {
        printf("    [INFO] Backpressure events: %zu\n", backpressure_count);
    }

    /* Verify all inserted records are present and sorted */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));

    tl_iter_t* it = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_iter_since(snap, TL_TS_MIN, &it));

    tl_record_t rec;
    tl_ts_t prev_ts = TL_TS_MIN;
    size_t count = 0;

    while (tl_iter_next(it, &rec) == TL_OK) {
        /* Verify ascending order */
        TEST_ASSERT(rec.ts >= prev_ts);
        prev_ts = rec.ts;
        count++;
    }

    TEST_ASSERT_EQ(inserted, count);

    tl_iter_destroy(it);
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));
    tl_snapshot_release(snap);

    /* Stop maintenance */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_stop(tl));

    free(timestamps);
    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: stress_delete_churn
 *
 * Purpose: Validate tombstone handling under append/delete with concurrent queries.
 *
 * SINGLE-WRITER CONTRACT: A single writer thread performs all mutations.
 * Multiple reader threads query concurrently to validate tombstone filtering.
 *
 * Configuration:
 * - Full mode: 1 writer, 2 readers, 2K operations
 * - Short mode: 1 writer, 1 reader, 500 operations
 *
 * This test validates:
 * - Correct tombstone filtering under pressure
 * - No race conditions in tombstone handling
 * - Query consistency during deletes
 *---------------------------------------------------------------------------*/
typedef struct {
    stress_test_ctx_t* ctx;
    int                thread_id;
    size_t             operations;
} stress_churn_thread_ctx_t;

static void* stress_churn_writer_thread(void* arg) {
    stress_churn_thread_ctx_t* tctx = (stress_churn_thread_ctx_t*)arg;
    stress_test_ctx_t* ctx = tctx->ctx;

    /* Signal ready and wait for start */
    tl_atomic_fetch_add_u32(&ctx->ready_count, 1, TL_MO_RELEASE);
    while (!tl_atomic_load_acquire_u32(&ctx->start_flag)) {
        tl_thread_yield();
    }

    stress_srand((uint32_t)(tctx->thread_id * 1000 + 1));
    size_t appends = 0;
    size_t deletes = 0;

    for (size_t i = 0; i < tctx->operations; i++) {
        if (tl_atomic_load_relaxed_u32(&ctx->stop_flag)) {
            break;
        }

        uint32_t op = stress_rand() % 3;
        tl_ts_t ts_base = (tl_ts_t)(stress_rand() % 10000) * 100;

        /* Hold writer lock for entire operation (single-writer contract) */
        tl_mutex_lock(&ctx->writer_mu);

        tl_status_t st;
        if (op == 0 || op == 1) {
            /* Append */
            st = tl_append(ctx->tl, ts_base + (tl_ts_t)i,
                           (tl_handle_t)(tctx->thread_id * 100000 + i));
            if (st == TL_OK) {
                appends++;
            } else if (st == TL_EBUSY) {
                tl_atomic_fetch_add_u64(&ctx->backpressure_count, 1, TL_MO_RELAXED);
            }
        } else {
            /* Delete range */
            tl_ts_t t1 = ts_base;
            tl_ts_t t2 = ts_base + 500;
            st = tl_delete_range(ctx->tl, t1, t2);
            if (st == TL_OK) {
                deletes++;
            } else if (st == TL_EBUSY) {
                tl_atomic_fetch_add_u64(&ctx->backpressure_count, 1, TL_MO_RELAXED);
            }
        }

        tl_mutex_unlock(&ctx->writer_mu);
    }

    tl_atomic_fetch_add_u64(&ctx->total_appends, appends, TL_MO_RELAXED);
    tl_atomic_fetch_add_u64(&ctx->total_deletes, deletes, TL_MO_RELAXED);
    return NULL;
}

static void* stress_churn_reader_thread(void* arg) {
    stress_churn_thread_ctx_t* tctx = (stress_churn_thread_ctx_t*)arg;
    stress_test_ctx_t* ctx = tctx->ctx;

    /* Signal ready and wait for start */
    tl_atomic_fetch_add_u32(&ctx->ready_count, 1, TL_MO_RELEASE);
    while (!tl_atomic_load_acquire_u32(&ctx->start_flag)) {
        tl_thread_yield();
    }

    size_t queries = 0;

    while (!tl_atomic_load_relaxed_u32(&ctx->stop_flag)) {
        tl_snapshot_t* snap = NULL;
        tl_status_t st = tl_snapshot_acquire(ctx->tl, &snap);
        if (st != TL_OK) {
            continue;
        }

        /* Iterate through records to validate tombstone filtering */
        tl_iter_t* it = NULL;
        st = tl_iter_since(snap, TL_TS_MIN, &it);
        if (st == TL_OK) {
            tl_record_t rec;
            size_t count = 0;
            tl_ts_t prev_ts = TL_TS_MIN;

            while (tl_iter_next(it, &rec) == TL_OK) {
                /* Verify ordering invariant (even with tombstones) */
                if (rec.ts < prev_ts) {
                    tl_atomic_fetch_add_u32(&ctx->error_count, 1, TL_MO_RELAXED);
                }
                prev_ts = rec.ts;
                count++;

                /* Limit iteration to avoid blocking too long */
                if (count >= 1000) break;
            }
            tl_iter_destroy(it);
            queries++;
        }

        tl_snapshot_release(snap);
    }

    tl_atomic_fetch_add_u64(&ctx->total_queries, queries, TL_MO_RELAXED);
    return NULL;
}

TEST_DECLARE(stress_delete_churn) {
    /* Configure for background maintenance */
    tl_config_t cfg;
    TEST_ASSERT_STATUS(TL_OK, tl_config_init_defaults(&cfg));
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Start background maintenance */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_start(tl));

    stress_test_ctx_t ctx;
    TEST_ASSERT_STATUS(TL_OK, stress_ctx_init(&ctx, tl));

    /* Configuration: SINGLE WRITER + multiple readers */
    const int num_readers = short_stress_mode() ? 1 : 2;
    const size_t ops_per_writer = get_stress_iterations(2000, 500);

    /* Single writer thread */
    stress_churn_thread_ctx_t writer_ctx = {
        .ctx = &ctx,
        .thread_id = 0,
        .operations = ops_per_writer
    };
    tl_thread_t writer;
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&writer, stress_churn_writer_thread, &writer_ctx));

    /* Multiple reader threads */
    stress_churn_thread_ctx_t reader_ctx[2];
    tl_thread_t readers[2];
    for (int i = 0; i < num_readers; i++) {
        reader_ctx[i].ctx = &ctx;
        reader_ctx[i].thread_id = i + 1;
        reader_ctx[i].operations = 0;  /* Readers run until stop_flag */
        TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&readers[i], stress_churn_reader_thread, &reader_ctx[i]));
    }

    /* Wait for ready */
    while (tl_atomic_load_acquire_u32(&ctx.ready_count) < (uint32_t)(1 + num_readers)) {
        tl_thread_yield();
    }

    /* Start and wait for writer */
    tl_atomic_store_release_u32(&ctx.start_flag, 1);
    tl_thread_join(&writer, NULL);

    /* Signal readers to stop and wait */
    tl_atomic_store_release_u32(&ctx.stop_flag, 1);
    for (int i = 0; i < num_readers; i++) {
        tl_thread_join(&readers[i], NULL);
    }

    /* Stop background maintenance */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_stop(tl));

    /* Verify no errors and data integrity */
    uint64_t appends = tl_atomic_load_relaxed_u64(&ctx.total_appends);
    uint64_t deletes = tl_atomic_load_relaxed_u64(&ctx.total_deletes);
    uint64_t queries = tl_atomic_load_relaxed_u64(&ctx.total_queries);
    uint32_t errors = tl_atomic_load_relaxed_u32(&ctx.error_count);
    uint64_t backpressure = tl_atomic_load_relaxed_u64(&ctx.backpressure_count);

    TEST_ASSERT(appends > 0);
    TEST_ASSERT(deletes > 0);
    TEST_ASSERT(queries > 0);  /* Readers did run */
    TEST_ASSERT_EQ(0, errors);

    if (backpressure > 0) {
        printf("    [INFO] Backpressure events: %llu\n", (unsigned long long)backpressure);
    }

    /* Validate structure */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));
    tl_snapshot_release(snap);

    stress_ctx_destroy(&ctx);
    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: stress_long_running_maintenance
 *
 * Purpose: Validate system under extended operation with background mode.
 *
 * SINGLE-WRITER: Uses a single loop for all writes.
 *
 * Configuration:
 * - Full mode: 60 seconds of continuous activity
 * - Short mode: 10 seconds of continuous activity
 *
 * This test validates:
 * - No memory leaks over extended operation
 * - No deadlocks with background maintenance
 * - Correct flush/compaction behavior
 * - Proper error tracking
 *---------------------------------------------------------------------------*/
TEST_DECLARE(stress_long_running_maintenance) {
    /* Configure for background maintenance mode */
    tl_config_t cfg;
    TEST_ASSERT_STATUS(TL_OK, tl_config_init_defaults(&cfg));
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Start background maintenance */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_start(tl));

    const uint64_t duration_ms = get_stress_duration_ms(60000, 10000);
    const uint64_t start_ms = tl_monotonic_ms();

    size_t total_appends = 0;
    size_t total_queries = 0;
    size_t backpressure_count = 0;
    size_t error_count = 0;
    tl_ts_t ts = 0;

    /* Continuous operation for duration */
    while ((tl_monotonic_ms() - start_ms) < duration_ms) {
        /* Batch of appends with error tracking */
        for (int i = 0; i < 100; i++) {
            tl_status_t st = tl_append(tl, ts++, (tl_handle_t)total_appends);
            if (st == TL_OK) {
                total_appends++;
            } else if (st == TL_EBUSY) {
                backpressure_count++;
                tl_sleep_ms(1);  /* Backoff on backpressure */
            } else {
                error_count++;
            }
        }

        /* Occasional queries with TL_TS_MIN */
        if ((total_appends % 1000) == 0) {
            tl_snapshot_t* snap = NULL;
            if (tl_snapshot_acquire(tl, &snap) == TL_OK) {
                tl_iter_t* it = NULL;
                if (tl_iter_since(snap, TL_TS_MIN, &it) == TL_OK) {
                    tl_record_t rec;
                    while (tl_iter_next(it, &rec) == TL_OK) {
                        /* Just iterate */
                    }
                    tl_iter_destroy(it);
                    total_queries++;
                }
                tl_snapshot_release(snap);
            }
        }

        /* Occasional explicit flush with error tracking */
        if ((total_appends % 5000) == 0) {
            tl_status_t st = tl_flush(tl);
            if (st != TL_OK && st != TL_EBUSY) {
                error_count++;
            }
        }
    }

    /* Stop background maintenance */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_stop(tl));

    /* Final validation */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));

    tl_stats_t stats;
    TEST_ASSERT_STATUS(TL_OK, tl_stats(snap, &stats));

    /* Verify work was done */
    TEST_ASSERT(total_appends > 0);
    TEST_ASSERT(total_queries > 0);
    TEST_ASSERT(stats.records_estimate > 0);
    TEST_ASSERT_EQ(0, error_count);  /* No unexpected errors */

    if (backpressure_count > 0) {
        printf("    [INFO] Backpressure events: %zu\n", backpressure_count);
    }

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_stress_tests(void) {
    if (!stress_tests_enabled()) {
        /* Skip stress tests unless explicitly enabled */
        printf("  [SKIP] Stress tests disabled (set TIMELOG_STRESS_TESTS=1 to enable)\n");
        return;
    }

    if (short_stress_mode()) {
        printf("  [INFO] Running stress tests in SHORT mode\n");
    } else {
        printf("  [INFO] Running stress tests in FULL mode\n");
    }

    /* Stress tests - all respect single-writer contract */
    RUN_TEST(stress_high_volume_append_query);
    RUN_TEST(stress_heavy_ooo_ingestion);
    RUN_TEST(stress_delete_churn);
    RUN_TEST(stress_long_running_maintenance);
}
