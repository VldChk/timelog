#include "test_harness.h"
#include "timelog/timelog.h"
#include <inttypes.h>
#include <stdbool.h>

/*===========================================================================
 * Global Test Context
 *===========================================================================*/

test_context_t g_test_ctx;
static const char* g_test_filter;
static bool test_name_enabled(const char* filter, const char* name);

/*===========================================================================
 * Test Framework Implementation
 *===========================================================================*/

void test_init(void) {
    memset(&g_test_ctx, 0, sizeof(g_test_ctx));
}

void test_run(const char* name, test_fn fn) {
    if (!test_name_enabled(g_test_filter, name)) {
        return;
    }

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
 * Optional Group Filter (Targeted Runs)
 *===========================================================================*/

static bool test_group_enabled(const char* groups, const char* name) {
    if (groups == NULL || *groups == '\0') {
        return true;
    }

    size_t name_len = strlen(name);
    const char* p = groups;

    while (*p != '\0') {
        while (*p == ' ' || *p == ',') {
            p++;
        }
        if (*p == '\0') {
            break;
        }

        const char* end = p;
        while (*end != '\0' && *end != ',') {
            end++;
        }

        size_t len = (size_t)(end - p);
        if (len == name_len && strncmp(p, name, len) == 0) {
            return true;
        }

        p = end;
    }

    return false;
}

/* Registered group names. Keep in sync with the test_group_enabled()
 * dispatch chain in main(); the guard below fails the run if TL_TEST_GROUPS
 * names a group that no longer exists (prevents silent test skips in CI). */
static const char* const k_test_groups[] = {
    "internal_sync", "internal_data", "storage", "delta", "compaction",
    "pagespan", "adaptive", "functional", "api_semantics",
    "snapshot_lifetime", "invariants", "concurrency", "stress",
};

/* Validate TL_TEST_GROUPS: every requested name must match a registered
 * group. Tokenization and comparison are identical to test_group_enabled().
 * Returns 0 if groups is NULL/empty or all names match; otherwise prints
 * the unmatched name(s) and returns nonzero. */
static int test_groups_validate(const char* groups) {
    if (groups == NULL || *groups == '\0') {
        return 0;
    }

    int unmatched = 0;
    int n_tokens = 0;
    const char* p = groups;

    while (*p != '\0') {
        while (*p == ' ' || *p == ',') {
            p++;
        }
        if (*p == '\0') {
            break;
        }

        const char* end = p;
        while (*end != '\0' && *end != ',') {
            end++;
        }

        size_t len = (size_t)(end - p);
        n_tokens++;
        bool matched = false;
        for (size_t i = 0;
             i < sizeof(k_test_groups) / sizeof(k_test_groups[0]); i++) {
            if (len == strlen(k_test_groups[i]) &&
                strncmp(p, k_test_groups[i], len) == 0) {
                matched = true;
                break;
            }
        }
        if (!matched) {
            fprintf(stderr,
                    "ERROR: TL_TEST_GROUPS names unknown group '%.*s'\n",
                    (int)len, p);
            unmatched = 1;
        }

        p = end;
    }

    /* A non-empty value made only of separators would otherwise select
     * nothing and "pass" with zero tests run — treat it as an error. */
    if (n_tokens == 0) {
        fprintf(stderr,
                "ERROR: TL_TEST_GROUPS is set but names no groups: '%s'\n",
                groups);
        return 1;
    }

    return unmatched;
}

static bool test_name_enabled(const char* filter, const char* name) {
    if (filter == NULL || *filter == '\0') {
        return true;
    }

    size_t name_len = strlen(name);
    const char* p = filter;

    while (*p != '\0') {
        while (*p == ' ' || *p == ',') {
            p++;
        }
        if (*p == '\0') {
            break;
        }

        const char* end = p;
        while (*end != '\0' && *end != ',') {
            end++;
        }

        size_t len = (size_t)(end - p);
        if (len == name_len && strncmp(p, name, len) == 0) {
            return true;
        }

        p = end;
    }

    return false;
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

/* Storage layer internal tests */
extern void run_storage_internal_tests(void);
extern void run_search_branchless_tests(void);

/* Delta layer internal tests */
extern void run_delta_internal_tests(void);

/* Compaction internal tests */
extern void run_compaction_internal_tests(void);

/* PageSpan core API tests */
extern void run_pagespan_iter_tests(void);

/* Adaptive Segmentation internal tests (V-Next) */
extern void run_adaptive_internal_tests(void);

/*===========================================================================
 * Main Entry Point
 *===========================================================================*/

int main(int argc, char* argv[]) {
    (void)argc;
    (void)argv;

    const char* groups = getenv("TL_TEST_GROUPS");
    g_test_filter = getenv("TL_TEST_FILTER");

    if (test_groups_validate(groups) != 0) {
        return 1;
    }

    printf("Timelog Test Suite\n");
    printf("========================================\n\n");

    test_init();

    /*-----------------------------------------------------------------------
     * Internal Tests
     *-----------------------------------------------------------------------*/

    if (test_group_enabled(groups, "internal_sync")) {
        printf("[Internal] Sync Primitives\n");
        printf("----------------------------------------\n");
        run_internal_sync_tests();
    }

    if (test_group_enabled(groups, "internal_data")) {
        printf("\n[Internal] Data Structures\n");
        printf("----------------------------------------\n");
        run_internal_data_structures_tests();
    }

    if (test_group_enabled(groups, "storage")) {
        printf("\n[Internal] Storage Layer\n");
        printf("----------------------------------------\n");
        run_storage_internal_tests();
        run_search_branchless_tests();
    }

    if (test_group_enabled(groups, "delta")) {
        printf("\n[Internal] Delta Layer\n");
        printf("----------------------------------------\n");
        run_delta_internal_tests();
    }

    if (test_group_enabled(groups, "compaction")) {
        printf("\n[Internal] Compaction\n");
        printf("----------------------------------------\n");
        run_compaction_internal_tests();
    }

    if (test_group_enabled(groups, "pagespan")) {
        printf("\n[Internal] PageSpan Iterator\n");
        printf("----------------------------------------\n");
        run_pagespan_iter_tests();
    }

    if (test_group_enabled(groups, "adaptive")) {
        printf("\n[Internal] Adaptive Segmentation\n");
        printf("----------------------------------------\n");
        run_adaptive_internal_tests();
    }

    /*-----------------------------------------------------------------------
     * Functional Tests (Public API behavior)
     *-----------------------------------------------------------------------*/

    if (test_group_enabled(groups, "functional")) {
        printf("\n[Functional] Core Operations\n");
        printf("----------------------------------------\n");
        run_functional_tests();
    }

    if (test_group_enabled(groups, "api_semantics")) {
        printf("\n[Functional] API Semantics\n");
        printf("----------------------------------------\n");
        run_api_semantics_tests();
    }

    if (test_group_enabled(groups, "snapshot_lifetime")) {
        printf("\n[Functional] Snapshot Lifetime\n");
        printf("----------------------------------------\n");
        run_snapshot_lifetime_tests();
    }

    if (test_group_enabled(groups, "invariants")) {
        printf("\n[Functional] Invariants\n");
        printf("----------------------------------------\n");
        run_invariants_tests();
    }

    /*-----------------------------------------------------------------------
     * Concurrency and Stress Tests
     *-----------------------------------------------------------------------*/

    if (test_group_enabled(groups, "concurrency")) {
        printf("\n[Concurrency] Thread Safety\n");
        printf("----------------------------------------\n");
        run_concurrency_tests();
    }

    if (test_group_enabled(groups, "stress")) {
        printf("\n[Stress] Load Testing\n");
        printf("----------------------------------------\n");
        run_stress_tests();
    }

    return test_report();
}
