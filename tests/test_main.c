#include "test_harness.h"
#include "timelog/timelog.h"
#include <inttypes.h>

/*===========================================================================
 * Global Test Context
 *===========================================================================*/

test_context_t g_test_ctx;

/*===========================================================================
 * Test Framework Implementation
 *===========================================================================*/

void test_init(void) {
    memset(&g_test_ctx, 0, sizeof(g_test_ctx));
}

void test_run(const char* name, test_fn fn) {
    g_test_ctx.current_test = name;
    printf("  Running: %s ... ", name);
    fflush(stdout);

    int prev_count = g_test_ctx.count;

    /* Run the test */
    fn();

    /* If we get here without failing, the test passed */
    if (g_test_ctx.count == prev_count) {
        /* No failure was recorded, so test passed */
        test_result_t* r = &g_test_ctx.results[g_test_ctx.count++];
        r->name = name;
        r->passed = 1;
        g_test_ctx.passed++;
        printf("PASSED\n");
    }
}

void test_fail(const char* file, int line, const char* msg) {
    test_result_t* r = &g_test_ctx.results[g_test_ctx.count++];
    r->name = g_test_ctx.current_test;
    r->file = file;
    r->line = line;
    r->passed = 0;
    snprintf(r->message, sizeof(r->message), "%s", msg);
    g_test_ctx.failed++;
    printf("FAILED\n");
    printf("    %s:%d: %s\n", file, line, msg);
}

void test_fail_eq(const char* file, int line,
                  const char* expected_expr, const char* actual_expr,
                  long long expected, long long actual) {
    char msg[512];
    snprintf(msg, sizeof(msg),
             "Expected %s == %s, got %lld != %lld",
             expected_expr, actual_expr, expected, actual);
    test_fail(file, line, msg);
}

void test_fail_eq_u64(const char* file, int line,
                      const char* expected_expr, const char* actual_expr,
                      uint64_t expected, uint64_t actual) {
    char msg[512];
    snprintf(msg, sizeof(msg),
             "Expected %s == %s, got %" PRIu64 " != %" PRIu64,
             expected_expr, actual_expr, expected, actual);
    test_fail(file, line, msg);
}

void test_fail_eq_size(const char* file, int line,
                       const char* expected_expr, const char* actual_expr,
                       size_t expected, size_t actual) {
    char msg[512];
    snprintf(msg, sizeof(msg),
             "Expected %s == %s, got %zu != %zu",
             expected_expr, actual_expr, expected, actual);
    test_fail(file, line, msg);
}

void test_fail_eq_ptr(const char* file, int line,
                      const char* expected_expr, const char* actual_expr,
                      const void* expected, const void* actual) {
    char msg[512];
    snprintf(msg, sizeof(msg),
             "Expected %s == %s, got %p != %p",
             expected_expr, actual_expr, expected, actual);
    test_fail(file, line, msg);
}

void test_fail_status(const char* file, int line,
                      tl_status_t expected, tl_status_t actual) {
    char msg[512];
    snprintf(msg, sizeof(msg),
             "Expected status %s (%d), got %s (%d)",
             tl_strerror(expected), expected,
             tl_strerror(actual), actual);
    test_fail(file, line, msg);
}

int test_report(void) {
    printf("\n");
    printf("========================================\n");
    printf("Test Results: %d passed, %d failed\n",
           g_test_ctx.passed, g_test_ctx.failed);
    printf("========================================\n");

    if (g_test_ctx.failed > 0) {
        printf("\nFailed tests:\n");
        for (int i = 0; i < g_test_ctx.count; i++) {
            if (!g_test_ctx.results[i].passed) {
                printf("  - %s: %s\n",
                       g_test_ctx.results[i].name,
                       g_test_ctx.results[i].message);
            }
        }
    }

    return g_test_ctx.failed > 0 ? 1 : 0;
}

/*===========================================================================
 * External Test Declarations
 *
 * Tests organized by category:
 * - Internal: Low-level primitives (sync, data structures, storage, delta)
 * - Functional: End-to-end behavior through public API
 * - API Semantics: Contract and error handling
 * - Concurrency/Stress: Thread safety and load testing
 * - Invariants: Structural correctness verification
 *===========================================================================*/

/* Internal synchronization primitives */
extern void run_internal_sync_tests(void);

/* Internal data structures */
extern void run_internal_data_structures_tests(void);

/* Core functional tests */
extern void run_functional_tests(void);

/* API semantics and contract tests */
extern void run_api_semantics_tests(void);

/* Concurrency and thread safety tests */
extern void run_concurrency_tests(void);

/* Structural invariant tests */
extern void run_invariants_tests(void);

/* Stress tests (conditional) */
extern void run_stress_tests(void);

/* Snapshot lifetime tests */
extern void run_snapshot_lifetime_tests(void);

/* Storage layer internal tests (LLD-driven) */
extern void run_storage_internal_tests(void);

/* Delta layer internal tests (LLD-driven) */
extern void run_delta_internal_tests(void);

/* Compaction internal tests (LLD-driven) */
extern void run_compaction_internal_tests(void);

/* PageSpan core API tests (V2 binding support) */
extern void run_pagespan_iter_tests(void);

/*===========================================================================
 * Main Entry Point
 *===========================================================================*/

int main(int argc, char* argv[]) {
    (void)argc;
    (void)argv;

    printf("Timelog V1 Test Suite\n");
    printf("========================================\n\n");

    test_init();

    /*-----------------------------------------------------------------------
     * Internal Tests (LLD-driven implementation verification)
     *-----------------------------------------------------------------------*/

    printf("[Internal] Sync Primitives\n");
    printf("----------------------------------------\n");
    run_internal_sync_tests();

    printf("\n[Internal] Data Structures\n");
    printf("----------------------------------------\n");
    run_internal_data_structures_tests();

    printf("\n[Internal] Storage Layer\n");
    printf("----------------------------------------\n");
    run_storage_internal_tests();

    printf("\n[Internal] Delta Layer\n");
    printf("----------------------------------------\n");
    run_delta_internal_tests();

    printf("\n[Internal] Compaction\n");
    printf("----------------------------------------\n");
    run_compaction_internal_tests();

    printf("\n[Internal] PageSpan Iterator\n");
    printf("----------------------------------------\n");
    run_pagespan_iter_tests();

    /*-----------------------------------------------------------------------
     * Functional Tests (Public API behavior)
     *-----------------------------------------------------------------------*/

    printf("\n[Functional] Core Operations\n");
    printf("----------------------------------------\n");
    run_functional_tests();

    printf("\n[Functional] API Semantics\n");
    printf("----------------------------------------\n");
    run_api_semantics_tests();

    printf("\n[Functional] Snapshot Lifetime\n");
    printf("----------------------------------------\n");
    run_snapshot_lifetime_tests();

    printf("\n[Functional] Invariants\n");
    printf("----------------------------------------\n");
    run_invariants_tests();

    /*-----------------------------------------------------------------------
     * Concurrency and Stress Tests
     *-----------------------------------------------------------------------*/

    printf("\n[Concurrency] Thread Safety\n");
    printf("----------------------------------------\n");
    run_concurrency_tests();

    printf("\n[Stress] Load Testing\n");
    printf("----------------------------------------\n");
    run_stress_tests();

    return test_report();
}
