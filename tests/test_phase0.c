#include "test_harness.h"
#include "timelog/timelog.h"
#include <string.h>
#include <stdlib.h>
#include <stdint.h>

/*===========================================================================
 * Status Code Tests
 *
 * Note: We only assert tl_strerror returns non-NULL. The exact strings and
 * whether they are distinct are not part of the public contract.
 *===========================================================================*/

TEST_DECLARE(strerror_returns_non_null) {
    /* All defined status codes should return non-NULL */
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_OK));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_EOF));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_EINVAL));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_ESTATE));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_EBUSY));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_ENOMEM));
    TEST_ASSERT_NOT_NULL(tl_strerror(TL_EINTERNAL));
}

TEST_DECLARE(strerror_unknown_code) {
    /* Unknown status codes should return non-NULL (fallback message) */
    const char* unknown = tl_strerror((tl_status_t)999);
    TEST_ASSERT_NOT_NULL(unknown);
}

/*===========================================================================
 * Configuration Tests
 *===========================================================================*/

TEST_DECLARE(config_defaults) {
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
    TEST_ASSERT_EQ(TL_MAINT_DISABLED, cfg.maintenance_mode);
    TEST_ASSERT_NULL(cfg.log_fn);
    TEST_ASSERT_NULL(cfg.on_drop_handle);
}

TEST_DECLARE(config_null_returns_einval) {
    tl_status_t s = tl_config_init_defaults(NULL);
    TEST_ASSERT_STATUS(TL_EINVAL, s);
}

/*===========================================================================
 * Lifecycle Tests
 *===========================================================================*/

TEST_DECLARE(open_null_out_returns_einval) {
    tl_status_t s = tl_open(NULL, NULL);
    TEST_ASSERT_STATUS(TL_EINVAL, s);
}

TEST_DECLARE(open_with_defaults) {
    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(NULL, &tl);

    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_NOT_NULL(tl);

    tl_close(tl);
}

TEST_DECLARE(open_with_explicit_config) {
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

TEST_DECLARE(close_null_is_safe) {
    tl_close(NULL);  /* Should not crash */
    TEST_ASSERT(1);  /* If we get here, test passed */
}

TEST_DECLARE(open_close_lifecycle) {
    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(NULL, &tl);
    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_NOT_NULL(tl);

    tl_close(tl);
    /* Instance is now freed. Caller is responsible for not reusing pointer.
     * A higher-level wrapper could NULL the pointer for safety. */
}

TEST_DECLARE(open_invalid_time_unit) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.time_unit = (tl_time_unit_t)99;  /* Invalid */

    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_EINVAL, s);
    TEST_ASSERT_NULL(tl);
}

TEST_DECLARE(open_invalid_maint_mode) {
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = (tl_maint_mode_t)99;  /* Invalid */

    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_EINVAL, s);
    TEST_ASSERT_NULL(tl);
}

TEST_DECLARE(open_negative_time_unit) {
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

static int alloc_call_count = 0;
static int free_call_count = 0;

static void* test_malloc(void* ctx, size_t size) {
    (void)ctx;
    alloc_call_count++;
    return malloc(size);
}

static void* test_calloc(void* ctx, size_t count, size_t size) {
    (void)ctx;
    alloc_call_count++;
    return calloc(count, size);
}

static void* test_realloc(void* ctx, void* ptr, size_t size) {
    (void)ctx;
    return realloc(ptr, size);
}

static void test_free(void* ctx, void* ptr) {
    (void)ctx;
    free_call_count++;
    free(ptr);
}

TEST_DECLARE(custom_allocator) {
    alloc_call_count = 0;
    free_call_count = 0;

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.allocator.ctx = NULL;
    cfg.allocator.malloc_fn = test_malloc;
    cfg.allocator.calloc_fn = test_calloc;
    cfg.allocator.realloc_fn = test_realloc;
    cfg.allocator.free_fn = test_free;

    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_NOT_NULL(tl);
    TEST_ASSERT(alloc_call_count > 0);  /* Should have allocated something */

    tl_close(tl);
    TEST_ASSERT(free_call_count > 0);   /* Should have freed something */
}

/*===========================================================================
 * Custom Logger Tests
 *===========================================================================*/

static int logger_call_count = 0;

static void test_log_fn(void* ctx, int level, const char* msg) {
    (void)ctx;
    (void)level;
    (void)msg;
    logger_call_count++;
}

TEST_DECLARE(custom_logger) {
    logger_call_count = 0;

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.log_fn = test_log_fn;
    cfg.log_ctx = NULL;

    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT(logger_call_count > 0);  /* Should have logged open message */

    tl_close(tl);
}

/*===========================================================================
 * Timestamp Type Tests
 *
 * Note: tl_ts_t is int64_t per the public API. We verify it can hold
 * the full range of 64-bit signed integers.
 *===========================================================================*/

TEST_DECLARE(timestamp_type_range) {
    /* tl_ts_t should be able to represent full int64_t range */
    tl_ts_t min_ts = INT64_MIN;
    tl_ts_t max_ts = INT64_MAX;

    TEST_ASSERT(min_ts < 0);
    TEST_ASSERT(max_ts > 0);
    TEST_ASSERT(min_ts < max_ts);

    /* Verify it's actually int64_t sized */
    TEST_ASSERT_EQ(8, sizeof(tl_ts_t));
}

/*===========================================================================
 * Write Path API Tests (Phase 4 wiring)
 *===========================================================================*/

TEST_DECLARE(write_api_append_single) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));
    TEST_ASSERT_NOT_NULL(tl);

    /* Single append should succeed */
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 1000, 42));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 2000, 43));
    TEST_ASSERT_STATUS(TL_OK, tl_append(tl, 3000, 44));

    tl_close(tl);
}

TEST_DECLARE(write_api_append_batch) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    tl_record_t batch[3] = {
        {.ts = 100, .handle = 1},
        {.ts = 200, .handle = 2},
        {.ts = 300, .handle = 3},
    };

    /* Batch append should succeed */
    TEST_ASSERT_STATUS(TL_OK, tl_append_batch(tl, batch, 3, 0));

    /* Empty batch is no-op */
    TEST_ASSERT_STATUS(TL_OK, tl_append_batch(tl, batch, 0, 0));

    tl_close(tl);
}

TEST_DECLARE(write_api_delete_range) {
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

TEST_DECLARE(write_api_delete_before) {
    tl_timelog_t* tl = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_open(NULL, &tl));

    /* Delete before should succeed */
    TEST_ASSERT_STATUS(TL_OK, tl_delete_before(tl, 1000));

    tl_close(tl);
}

TEST_DECLARE(write_api_flush) {
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

TEST_DECLARE(write_api_null_checks) {
    /* NULL timelog should return EINVAL */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_append(NULL, 1000, 1));
    TEST_ASSERT_STATUS(TL_EINVAL, tl_append_batch(NULL, NULL, 0, 0));
    TEST_ASSERT_STATUS(TL_EINVAL, tl_delete_range(NULL, 0, 100));
    TEST_ASSERT_STATUS(TL_EINVAL, tl_delete_before(NULL, 100));
    TEST_ASSERT_STATUS(TL_EINVAL, tl_flush(NULL));
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_phase0_tests(void) {
    /* Status codes */
    RUN_TEST(strerror_returns_non_null);
    RUN_TEST(strerror_unknown_code);

    /* Configuration */
    RUN_TEST(config_defaults);
    RUN_TEST(config_null_returns_einval);

    /* Lifecycle */
    RUN_TEST(open_null_out_returns_einval);
    RUN_TEST(open_with_defaults);
    RUN_TEST(open_with_explicit_config);
    RUN_TEST(close_null_is_safe);
    RUN_TEST(open_close_lifecycle);
    RUN_TEST(open_invalid_time_unit);
    RUN_TEST(open_invalid_maint_mode);
    RUN_TEST(open_negative_time_unit);

    /* Custom allocator */
    RUN_TEST(custom_allocator);

    /* Custom logger */
    RUN_TEST(custom_logger);

    /* Timestamp type */
    RUN_TEST(timestamp_type_range);

    /* Write path API (Phase 4 wiring) */
    RUN_TEST(write_api_append_single);
    RUN_TEST(write_api_append_batch);
    RUN_TEST(write_api_delete_range);
    RUN_TEST(write_api_delete_before);
    RUN_TEST(write_api_flush);
    RUN_TEST(write_api_null_checks);
}
