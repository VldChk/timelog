#include "test_harness.h"
#include "timelog/timelog.h"

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
 *===========================================================================*/

/* Phase 0 tests */
extern void run_phase0_tests(void);

/* Phase 1 tests */
extern void run_phase1_tests(void);

/* Phase 2 tests */
extern void run_phase2_tests(void);

/* Phase 3 tests */
extern void run_phase3_tests(void);

/* Phase 4 tests */
extern void run_phase4_tests(void);

/* Phase 5 tests */
extern void run_phase5_tests(void);

/* Phase 6 tests */
extern void run_phase6_tests(void);

/*===========================================================================
 * Main Entry Point
 *===========================================================================*/

int main(int argc, char* argv[]) {
    (void)argc;
    (void)argv;

    printf("Timelog V1 Test Suite\n");
    printf("========================================\n\n");

    test_init();

    printf("Phase 0: Contract and Lifecycle\n");
    printf("----------------------------------------\n");
    run_phase0_tests();

    printf("\nPhase 1: Concurrency Primitives\n");
    printf("----------------------------------------\n");
    run_phase1_tests();

    printf("\nPhase 2: Shared Data Structures\n");
    printf("----------------------------------------\n");
    run_phase2_tests();

    printf("\nPhase 3: Immutable Storage Layer\n");
    printf("----------------------------------------\n");
    run_phase3_tests();

    printf("\nPhase 4: Memtable and Write Path\n");
    printf("----------------------------------------\n");
    run_phase4_tests();

    printf("\nPhase 5: Snapshot and Read Path\n");
    printf("----------------------------------------\n");
    run_phase5_tests();

    printf("\nPhase 6: Statistics and Diagnostics\n");
    printf("----------------------------------------\n");
    run_phase6_tests();

    return test_report();
}
