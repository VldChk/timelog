/*===========================================================================
 * test_api_semantics.c - API Contract and Semantics Tests
 *
 * Tests for public API contracts:
 * - NULL parameter validation (EINVAL returns)
 * - Invalid parameter detection (EINVAL, ERANGE)
 * - State machine validation (ESTATE returns)
 * - Lifecycle correctness (init/destroy ordering)
 * - Idempotency guarantees
 * - Error code consistency
 *
 * These tests ensure the public API behaves predictably and safely
 * when given invalid inputs or called in invalid states.
 *
 * Part of Phase 10: Integration Testing and Hardening
 *
 * Migration Status: COMPLETE (migrated from test_phase0.c)
 * Note: Test names prefixed with "api_" to avoid conflicts during migration.
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"

#include <string.h>
#include <stdlib.h>
#include <stdint.h>

/*===========================================================================
 * Status Code Tests
 *===========================================================================*/

TEST_DECLARE(api_strerror_returns_non_null) {
    /* All defined status codes should return non-NULL */
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_OK));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_EOF));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_EINVAL));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_ESTATE));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_EBUSY));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_ENOMEM));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_EOVERFLOW));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_EINTERNAL));
}

TEST_DECLARE(api_strerror_unknown_code) {
    /* Unknown status codes should return non-NULL (fallback message) */
    const char* unknown = tl_strerror((tl_status_t)999);
    TEST_ASSERT_NOT_NULL(unknown);
}

/*===========================================================================
 * Configuration Tests
 *===========================================================================*/

TEST_DECLARE(api_config_defaults) {
    tl_config_t cfg;
    tl_status_t s = tl_config_init_defaults(&cfg);

    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_EQ(TL_TIME_MS, cfg.time_unit);
    TEST_ASSERT_EQ(64 * 1024, cfg.target_page_bytes);
    TEST_ASSERT_EQ(1024 * 1024, cfg.memtable_max_bytes);
    TEST_ASSERT_EQ(0, cfg.ooo_budget_bytes);  /* 0 means use default */
    TEST_ASSERT_EQ(4, cfg.sealed_max_runs);
    TEST_ASSERT_EQ(100, cfg.sealed_wait_ms);
    TEST_ASSERT_EQ(8, cfg.max_delta_segments);
    TEST_ASSERT_EQ(0, cfg.window_size);  /* 0 means use default */
    TEST_ASSERT_EQ(0, cfg.window_origin);

    /* Compaction policy fields (Phase 10 addition) */
    TEST_ASSERT(cfg.delete_debt_threshold == 0.0);  /* Disabled */
    TEST_ASSERT_EQ(0, cfg.compaction_target_bytes); /* Unlimited */
    TEST_ASSERT_EQ(0, cfg.max_compaction_inputs);   /* Unlimited */
    TEST_ASSERT_EQ(0, cfg.max_compaction_windows);  /* Unlimited */

    TEST_ASSERT_EQ(TL_MAINT_DISABLED, cfg.maintenance_mode);

    /* Allocator is zeroed (default system allocator) */
    TEST_ASSERT_NULL(cfg.allocator.malloc_fn);
    TEST_ASSERT_NULL(cfg.allocator.free_fn);
    TEST_ASSERT_NULL(cfg.allocator.realloc_fn);
    TEST_ASSERT_NULL(cfg.allocator.ctx);

    /* Logging and callbacks */
    TEST_ASSERT_NULL(cfg.log_fn);
    TEST_ASSERT_NULL(cfg.log_ctx);
    TEST_ASSERT_EQ(TL_LOG_INFO, cfg.log_level);     /* Explicit default per API docs */
    TEST_ASSERT_NULL(cfg.on_drop_handle);
    TEST_ASSERT_NULL(cfg.on_drop_ctx);
}

TEST_DECLARE(api_config_null_returns_einval) {
    tl_status_t s = tl_config_init_defaults(NULL);
    TEST_ASSERT_STATUS(TL_EINVAL, s);
}

/*===========================================================================
 * Lifecycle Tests
 *===========================================================================*/

TEST_DECLARE(api_open_null_out_returns_einval) {
    tl_status_t s = tl_open(NULL, NULL);
    TEST_ASSERT_STATUS(TL_EINVAL, s);
}

TEST_DECLARE(api_open_with_defaults) {
    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(NULL, &tl);

    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_NOT_NULL(tl);

    tl_close(tl);
}

TEST_DECLARE(api_open_with_explicit_config) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.time_unit = TL_TIME_US;
    cfg.target_page_bytes = 32 * 1024;

    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_NOT_NULL(tl);

    tl_close(tl);
}

TEST_DECLARE(api_close_null_is_safe) {
    tl_close(NULL);  /* Should not crash */
    TEST_ASSERT(1);  /* If we get here, test passed */
}

TEST_DECLARE(api_open_close_lifecycle) {
    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(NULL, &tl);
    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_NOT_NULL(tl);

    tl_close(tl);
    /* Instance is now freed. Caller is responsible for not reusing pointer.
     * A higher-level wrapper could NULL the pointer for safety. */
}

TEST_DECLARE(api_open_invalid_time_unit) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.time_unit = (tl_time_unit_t)99;  /* Invalid */

    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_EINVAL, s);
    TEST_ASSERT_NULL(tl);
}

TEST_DECLARE(api_open_invalid_maint_mode) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = (tl_maint_mode_t)99;  /* Invalid */

    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_EINVAL, s);
    TEST_ASSERT_NULL(tl);
}

TEST_DECLARE(api_open_negative_time_unit) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.time_unit = (tl_time_unit_t)-1;  /* Invalid negative */

    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_EINVAL, s);
    TEST_ASSERT_NULL(tl);
}

/*===========================================================================
 * Custom Allocator Tests
 *===========================================================================*/

static int api_alloc_call_count = 0;
static int api_free_call_count = 0;

static void* api_test_malloc(void* ctx, size_t size) {
    (void)ctx;
    api_alloc_call_count++;
    return malloc(size);
}

static void* api_test_calloc(void* ctx, size_t count, size_t size) {
    (void)ctx;
    api_alloc_call_count++;
    return calloc(count, size);
}

static void* api_test_realloc(void* ctx, void* ptr, size_t size) {
    (void)ctx;
    return realloc(ptr, size);
}

static void api_test_free(void* ctx, void* ptr) {
    (void)ctx;
    api_free_call_count++;
    free(ptr);
}

TEST_DECLARE(api_custom_allocator) {
    api_alloc_call_count = 0;
    api_free_call_count = 0;

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.allocator.ctx = NULL;
    cfg.allocator.malloc_fn = api_test_malloc;
    cfg.allocator.calloc_fn = api_test_calloc;
    cfg.allocator.realloc_fn = api_test_realloc;
    cfg.allocator.free_fn = api_test_free;

    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_NOT_NULL(tl);
    TEST_ASSERT(api_alloc_call_count > 0);  /* Should have allocated something */

    tl_close(tl);
    TEST_ASSERT(api_free_call_count > 0);   /* Should have freed something */
}

/*===========================================================================
 * Custom Logger Tests
 *===========================================================================*/

static int api_logger_call_count = 0;

static void api_test_log_fn(void* ctx, int level, const char* msg) {
    (void)ctx;
    (void)level;
    (void)msg;
    api_logger_call_count++;
}

TEST_DECLARE(api_custom_logger) {
    api_logger_call_count = 0;

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.log_fn = api_test_log_fn;
    cfg.log_ctx = NULL;

    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT(api_logger_call_count > 0);  /* Should have logged open message */

    tl_close(tl);
}

/*===========================================================================
 * Timestamp Type Tests
 *===========================================================================*/

TEST_DECLARE(api_timestamp_type_range) {
    /*
     * tl_ts_t should be able to represent full int64_t range.
     * Use TL_TS_MIN/TL_TS_MAX from public contract (not INT64_MIN/MAX).
     */
    tl_ts_t min_ts = TL_TS_MIN;
    tl_ts_t max_ts = TL_TS_MAX;

    TEST_ASSERT(min_ts < 0);
    TEST_ASSERT(max_ts > 0);
    TEST_ASSERT(min_ts < max_ts);

    /* Verify it's actually int64_t sized */
    TEST_ASSERT_EQ(8, sizeof(tl_ts_t));

    /* Verify TL_TS_MIN/MAX match documented values (INT64_MIN/MAX) */
    TEST_ASSERT_EQ(INT64_MIN, TL_TS_MIN);
    TEST_ASSERT_EQ(INT64_MAX, TL_TS_MAX);
}

/*===========================================================================
 * Write Path API Tests
 *===========================================================================*/

TEST_DECLARE(api_write_append_single) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));
    TEST_ASSERT_NOT_NULL(tl);

    /* Single append should succeed */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 1000, 42));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 2000, 43));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 3000, 44));

    tl_close(tl);
}

TEST_DECLARE(api_write_append_batch) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    tl_record_t batch[3] = {
        {.ts = 100, .handle = 1},
        {.ts = 200, .handle = 2},
        {.ts = 300, .handle = 3},
    };

    /* Batch append should succeed */
    TEST_ASSERT_STATUS(TL_OK, tl_append_batch(tl, batch, 3, 0));

    /* Empty batch with valid pointer is no-op */
    TEST_ASSERT_STATUS(TL_OK, tl_append_batch(tl, batch, 0, 0));

    /* Empty batch with NULL pointer should be allowed as no-op (n=0) */
    TEST_ASSERT_STATUS(TL_OK, tl_append_batch(tl, NULL, 0, 0));

    /* NULL pointer with n > 0 is invalid */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_append_batch(tl, NULL, 1, 0));

    tl_close(tl);
}

TEST_DECLARE(api_write_delete_range) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Delete range should succeed */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 100, 200));

    /* Empty range is no-op (t1 == t2) */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_range(tl, 100, 100));

    /* Invalid range (t1 > t2) should fail */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_delete_range(tl, 200, 100));

    tl_close(tl);
}

TEST_DECLARE(api_write_delete_before) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Delete before should succeed */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_before(tl, 1000));

    tl_close(tl);
}

TEST_DECLARE(api_write_flush) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Insert some data */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 1000, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 2000, 2));

    /* Flush should succeed (seals memtable) */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Flush empty is also OK */
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    tl_close(tl);
}

TEST_DECLARE(api_write_null_checks) {
    /* NULL timelog should return EINVAL */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_append(NULL, 1000, 1));
    TEST_ASSERT_STATUS(TL_EINVAL, tl_append_batch(NULL, NULL, 0, 0));
    TEST_ASSERT_STATUS(TL_EINVAL, tl_delete_range(NULL, 0, 100));
    TEST_ASSERT_STATUS(TL_EINVAL, tl_delete_before(NULL, 100));
    TEST_ASSERT_STATUS(TL_EINVAL, tl_flush(NULL));
}

/*===========================================================================
 * Maintenance API Mode Validation Tests (Phase 10)
 *
 * These tests verify the maintenance API behaves correctly w.r.t. mode.
 *===========================================================================*/

/*---------------------------------------------------------------------------
 * Test: api_maint_start_wrong_mode_estate
 *
 * Purpose: Verify maint_start returns ESTATE when mode is TL_MAINT_DISABLED.
 *
 * When timelog is opened with TL_MAINT_DISABLED (the default), calling
 * tl_maint_start() should return TL_ESTATE since background maintenance
 * is not enabled.
 *---------------------------------------------------------------------------*/
TEST_DECLARE(api_maint_start_wrong_mode_estate) {
    /* Open with default config (TL_MAINT_DISABLED) */
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* maint_start should return ESTATE - background mode not enabled */
    TEST_ASSERT_STATUS(TL_ESTATE, tl_maint_start(tl));

    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: api_maint_step_wrong_mode_estate
 *
 * Purpose: Verify maint_step returns ESTATE when mode is TL_MAINT_BACKGROUND.
 *
 * API semantics (per implementation):
 * - TL_MAINT_DISABLED: Manual mode - tl_maint_step() is the only way to
 *   perform maintenance work. Returns TL_OK/TL_EOF.
 * - TL_MAINT_BACKGROUND: Background thread does maintenance. Manual stepping
 *   is not allowed - tl_maint_step() returns TL_ESTATE.
 *---------------------------------------------------------------------------*/
TEST_DECLARE(api_maint_step_wrong_mode_estate) {
    /*
     * Test 1: DISABLED mode (manual mode) - maint_step should WORK
     * In this mode, maint_step is the intended way to do maintenance.
     * Returns TL_EOF if no work available, TL_OK if work done.
     */
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* maint_step should succeed (TL_EOF = no work to do) */
    tl_status_t st = tl_maint_step(tl);
    TEST_ASSERT(st == TL_OK || st == TL_EOF);

    tl_close(tl);

    /*
     * Test 2: BACKGROUND mode - maint_step should return ESTATE
     * In this mode, the background thread handles maintenance.
     * Manual stepping is not allowed.
     */
    tl_config_t cfg;
    TEST_ASSERT_STATUS(TL_OK, tl_config_init_defaults(&cfg));
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* In background mode, manual step is not allowed */
    TEST_ASSERT_STATUS(TL_ESTATE, tl_maint_step(tl));

    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: api_maint_start_idempotent
 *
 * Purpose: Verify calling maint_start twice is safe and idempotent.
 *
 * Starting maintenance when already started should be a no-op or return
 * a status indicating already started (not crash or corrupt state).
 *---------------------------------------------------------------------------*/
TEST_DECLARE(api_maint_start_idempotent) {
    tl_config_t cfg;
    TEST_ASSERT_STATUS(TL_OK, tl_config_init_defaults(&cfg));
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* First start should succeed */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_start(tl));

    /*
     * Second start should be idempotent - per API contract:
     * "Idempotency: If already running, returns TL_OK without action."
     */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_start(tl));

    TEST_ASSERT_STATUS(TL_OK, tl_maint_stop(tl));
    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: api_maint_stop_idempotent
 *
 * Purpose: Verify calling maint_stop when not started is safe.
 *
 * Stopping maintenance when not started should be a no-op.
 *---------------------------------------------------------------------------*/
TEST_DECLARE(api_maint_stop_idempotent) {
    tl_config_t cfg;
    TEST_ASSERT_STATUS(TL_OK, tl_config_init_defaults(&cfg));
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /*
     * Stop before start should be safe - per API contract:
     * "Idempotency: Returns TL_OK if already stopped..."
     */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_stop(tl));

    /* Start then stop */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_start(tl));
    TEST_ASSERT_STATUS(TL_OK, tl_maint_stop(tl));

    /* Double stop should also be safe - per API contract */
    TEST_ASSERT_STATUS(TL_OK, tl_maint_stop(tl));

    tl_close(tl);
}

/*---------------------------------------------------------------------------
 * Test: api_compact_sets_pending
 *
 * Purpose: Verify tl_compact() requests compaction (sets pending flag).
 *
 * Calling tl_compact() should signal that compaction should run.
 * This test verifies the call succeeds and doesn't corrupt state.
 *---------------------------------------------------------------------------*/
TEST_DECLARE(api_compact_sets_pending) {
    tl_config_t cfg;
    TEST_ASSERT_STATUS(TL_OK, tl_config_init_defaults(&cfg));
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(&cfg, &tl));

    /* Insert data and flush to create segments */
    for (int i = 0; i < 100; i++) {
        TEST_ASSERT_STATUS(TL_OK, tl_append(tl, (tl_ts_t)(i * 100), (tl_handle_t)(i + 1)));
    }
    TEST_ASSERT_STATUS(TL_OK, tl_flush(tl));

    /* Request compaction - should succeed */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));

    /* Multiple calls should be safe (idempotent) */
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));
    TEST_ASSERT_STATUS(TL_OK, tl_compact(tl));

    /* Verify state is still valid */
    tl_snapshot_t* snap = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_snapshot_acquire(tl, &snap));
    TEST_ASSERT_STATUS(TL_OK, tl_validate(snap));
    tl_snapshot_release(snap);

    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_api_semantics_tests(void) {
    /* Status codes (2 tests) */
    RUN_TEST(api_strerror_returns_non_null);
    RUN_TEST(api_strerror_unknown_code);

    /* Configuration (2 tests) */
    RUN_TEST(api_config_defaults);
    RUN_TEST(api_config_null_returns_einval);

    /* Lifecycle (7 tests) */
    RUN_TEST(api_open_null_out_returns_einval);
    RUN_TEST(api_open_with_defaults);
    RUN_TEST(api_open_with_explicit_config);
    RUN_TEST(api_close_null_is_safe);
    RUN_TEST(api_open_close_lifecycle);
    RUN_TEST(api_open_invalid_time_unit);
    RUN_TEST(api_open_invalid_maint_mode);
    RUN_TEST(api_open_negative_time_unit);

    /* Custom allocator (1 test) */
    RUN_TEST(api_custom_allocator);

    /* Custom logger (1 test) */
    RUN_TEST(api_custom_logger);

    /* Timestamp type (1 test) */
    RUN_TEST(api_timestamp_type_range);

    /* Write path API (6 tests) */
    RUN_TEST(api_write_append_single);
    RUN_TEST(api_write_append_batch);
    RUN_TEST(api_write_delete_range);
    RUN_TEST(api_write_delete_before);
    RUN_TEST(api_write_flush);
    RUN_TEST(api_write_null_checks);

    /* Maintenance API mode validation (5 tests - Phase 10) */
    RUN_TEST(api_maint_start_wrong_mode_estate);
    RUN_TEST(api_maint_step_wrong_mode_estate);
    RUN_TEST(api_maint_start_idempotent);
    RUN_TEST(api_maint_stop_idempotent);
    RUN_TEST(api_compact_sets_pending);

    /* Total: 27 tests */
}
