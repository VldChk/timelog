#include "test_harness.h"
#include "timelog/timelog.h"
#include <inttypes.h>
#include <stdbool.h>

/*===========================================================================
 * Global Test Context
 *===========================================================================*/

test_context_t g_test_ctx;
static const char* g_test_filter;
static bool test_name_in_list(const char* list, const char* name);

/*===========================================================================
 * Test Framework Implementation
 *===========================================================================*/

void test_init(void) {
    memset(&g_test_ctx, 0, sizeof(g_test_ctx));
}

void test_run(const char* name, test_fn fn) {
    if (!test_name_in_list(g_test_filter, name)) {
        return;
    }

    g_test_ctx.current_test = name;
    printf("  Running: %s ... ", name);
    fflush(stdout);

    int prev_failed = g_test_ctx.failed;

    /* Run the test */
    fn();

    /* If no failure was recorded, the test passed */
    if (g_test_ctx.failed == prev_failed) {
        g_test_ctx.passed++;
        printf("PASSED\n");
    }
}

void test_fail(const char* file, int line, const char* msg) {
    /* Record failures only (passes just increment the counter). The recap
     * array is clamped at TEST_MAX_TESTS; extra failures still count and
     * fail the run, and test_report() notes the truncation. */
    if (g_test_ctx.count < TEST_MAX_TESTS) {
        test_result_t* r = &g_test_ctx.results[g_test_ctx.count++];
        r->name = g_test_ctx.current_test;
        snprintf(r->message, sizeof(r->message), "%s", msg);
    }
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
            printf("  - %s: %s\n",
                   g_test_ctx.results[i].name,
                   g_test_ctx.results[i].message);
        }
        if (g_test_ctx.failed > g_test_ctx.count) {
            printf("  (recap capped at %d records; %d additional "
                   "failure(s) not listed above)\n",
                   TEST_MAX_TESTS, g_test_ctx.failed - g_test_ctx.count);
        }
    }

    return g_test_ctx.failed > 0 ? 1 : 0;
}

/*===========================================================================
 * Optional Group/Name Filter (Targeted Runs)
 *
 * One matcher serves both TL_TEST_GROUPS (group names in main) and
 * TL_TEST_FILTER (test names in test_run): comma-separated exact match,
 * NULL/empty list matches everything.
 *===========================================================================*/

static bool test_name_in_list(const char* list, const char* name) {
    if (list == NULL || *list == '\0') {
        return true;
    }

    size_t name_len = strlen(name);
    const char* p = list;

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
 *===========================================================================*/

extern void run_internal_sync_tests(void);
extern void run_internal_data_structures_tests(void);
extern void run_storage_internal_tests(void);
extern void run_search_branchless_tests(void);
extern void run_delta_internal_tests(void);
extern void run_compaction_internal_tests(void);
extern void run_pagespan_iter_tests(void);
extern void run_adaptive_internal_tests(void);
extern void run_functional_tests(void);
extern void run_api_semantics_tests(void);
extern void run_snapshot_lifetime_tests(void);
extern void run_invariants_tests(void);
extern void run_concurrency_tests(void);
extern void run_stress_tests(void);

/*===========================================================================
 * Suite Table
 *
 * SINGLE SOURCE OF TRUTH for group names: the TL_TEST_GROUPS validation
 * guard below and the core_group_<name> CTest entries in the root
 * CMakeLists.txt both derive from this table. Rows may repeat a group
 * name to run several runners under one group ("storage"); a NULL banner
 * marks such a continuation row.
 *===========================================================================*/

typedef struct {
    const char* group;
    const char* banner;
    void (*runner)(void);
} test_suite_t;

static const test_suite_t k_test_suites[] = {
    { "internal_sync",     "[Internal] Sync Primitives",       run_internal_sync_tests },
    { "internal_data",     "[Internal] Data Structures",       run_internal_data_structures_tests },
    { "storage",           "[Internal] Storage Layer",         run_storage_internal_tests },
    { "storage",           NULL,                               run_search_branchless_tests },
    { "delta",             "[Internal] Delta Layer",           run_delta_internal_tests },
    { "compaction",        "[Internal] Compaction",            run_compaction_internal_tests },
    { "pagespan",          "[Internal] PageSpan Iterator",     run_pagespan_iter_tests },
    { "adaptive",          "[Internal] Adaptive Segmentation", run_adaptive_internal_tests },
    { "functional",        "[Functional] Core Operations",     run_functional_tests },
    { "api_semantics",     "[Functional] API Semantics",       run_api_semantics_tests },
    { "snapshot_lifetime", "[Functional] Snapshot Lifetime",   run_snapshot_lifetime_tests },
    { "invariants",        "[Functional] Invariants",          run_invariants_tests },
    { "concurrency",       "[Concurrency] Thread Safety",      run_concurrency_tests },
    { "stress",            "[Stress] Load Testing",            run_stress_tests },
};

#define TEST_SUITE_COUNT (sizeof(k_test_suites) / sizeof(k_test_suites[0]))

/* Validate TL_TEST_GROUPS: every requested name must match a registered
 * group in k_test_suites (prevents silent test skips in CI). Tokenization
 * and comparison are identical to test_name_in_list(). Returns 0 if groups
 * is NULL/empty or all names match; otherwise prints the unmatched name(s)
 * and returns nonzero. */
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
        for (size_t i = 0; i < TEST_SUITE_COUNT; i++) {
            if (len == strlen(k_test_suites[i].group) &&
                strncmp(p, k_test_suites[i].group, len) == 0) {
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

/* TL_TEST_EXPECT_GROUPS: bidirectional CI drift guard. When set (by the
 * core_group_sync CTest entry) it must list EXACTLY the unique group names
 * in k_test_suites. A group in the list but not the table fails via
 * test_groups_validate's logic; a group in the table but not the list —
 * i.e. a new suite CI would silently skip — fails here. Runs no tests. */
static int test_groups_expect(const char* expected) {
    int st = test_groups_validate(expected);

    for (size_t i = 0; i < TEST_SUITE_COUNT; i++) {
        /* Skip continuation rows (same group as a previous row). */
        if (i > 0 && strcmp(k_test_suites[i].group,
                            k_test_suites[i - 1].group) == 0) {
            continue;
        }
        if (!test_name_in_list(expected, k_test_suites[i].group)) {
            fprintf(stderr,
                    "ERROR: group '%s' is registered in test_main.c but "
                    "missing from TL_TEST_EXPECT_GROUPS (update "
                    "TIMELOG_TEST_GROUPS in CMakeLists.txt or CI will "
                    "silently skip it)\n",
                    k_test_suites[i].group);
            st = 1;
        }
    }

    if (st == 0) {
        printf("core_group_sync: %d group names in sync\n",
               (int)TEST_SUITE_COUNT);
    }
    return st;
}

/*===========================================================================
 * Main Entry Point
 *===========================================================================*/

int main(int argc, char* argv[]) {
    (void)argc;
    (void)argv;

    const char* groups = getenv("TL_TEST_GROUPS");
    g_test_filter = getenv("TL_TEST_FILTER");

    const char* expect = getenv("TL_TEST_EXPECT_GROUPS");
    if (expect != NULL) {
        return test_groups_expect(expect);
    }

    if (test_groups_validate(groups) != 0) {
        return 1;
    }

    printf("Timelog Test Suite\n");
    printf("========================================\n");

    test_init();

    for (size_t i = 0; i < TEST_SUITE_COUNT; i++) {
        const test_suite_t* s = &k_test_suites[i];
        if (!test_name_in_list(groups, s->group)) {
            continue;
        }
        if (s->banner != NULL) {
            printf("\n%s\n", s->banner);
            printf("----------------------------------------\n");
        }
        s->runner();
    }

    return test_report();
}
