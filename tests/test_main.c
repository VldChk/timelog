#include <stdio.h>
#include <stdlib.h>

/* Simple test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))

/* Test declarations */
extern int test_status(void);
extern int test_alloc(void);
extern int test_recvec(void);
extern int test_intervals(void);
/* Phase 2: Storage tests */
extern int test_page(void);
extern int test_segment(void);
extern int test_manifest(void);
/* Phase 3: Write path tests */
extern int test_memtable(void);
extern int test_flush(void);
/* Phase 4: Read path tests */
extern int test_snapshot(void);
extern int test_iter(void);
extern int test_merge(void);
extern int test_read_path(void);
/* Phase 5: Diagnostics tests */
extern int test_diagnostics(void);
/* Phase 6: Maintenance tests */
extern int test_maintenance(void);

int main(void) {
    int failed = 0;

    printf("Running timelog tests...\n\n"); fflush(stdout);

    printf("Starting test_status...\n"); fflush(stdout);
    if (test_status()) { failed++; printf("test_status FAILED\n"); }
    else printf("test_status PASSED\n");

    printf("Starting test_alloc...\n"); fflush(stdout);
    if (test_alloc()) { failed++; printf("test_alloc FAILED\n"); }
    else printf("test_alloc PASSED\n");

    printf("Starting test_recvec...\n"); fflush(stdout);
    if (test_recvec()) { failed++; printf("test_recvec FAILED\n"); }
    else printf("test_recvec PASSED\n");

    printf("Starting test_intervals...\n"); fflush(stdout);
    if (test_intervals()) { failed++; printf("test_intervals FAILED\n"); }
    else printf("test_intervals PASSED\n");

    /* Phase 2: Storage tests */
    printf("Starting test_page...\n"); fflush(stdout);
    if (test_page()) { failed++; printf("test_page FAILED\n"); }
    else printf("test_page PASSED\n");

    printf("Starting test_segment...\n"); fflush(stdout);
    if (test_segment()) { failed++; printf("test_segment FAILED\n"); }
    else printf("test_segment PASSED\n");

    printf("Starting test_manifest...\n"); fflush(stdout);
    if (test_manifest()) { failed++; printf("test_manifest FAILED\n"); }
    else printf("test_manifest PASSED\n");

    /* Phase 3: Write path tests */
    printf("Starting test_memtable...\n"); fflush(stdout);
    if (test_memtable()) { failed++; printf("test_memtable FAILED\n"); }
    else printf("test_memtable PASSED\n");

    printf("Starting test_flush...\n"); fflush(stdout);
    if (test_flush()) { failed++; printf("test_flush FAILED\n"); }
    else printf("test_flush PASSED\n");

    /* Phase 4: Read path tests */
    printf("Starting test_snapshot...\n"); fflush(stdout);
    if (test_snapshot()) { failed++; printf("test_snapshot FAILED\n"); }
    else printf("test_snapshot PASSED\n");

    printf("Starting test_iter...\n"); fflush(stdout);
    if (test_iter()) { failed++; printf("test_iter FAILED\n"); }
    else printf("test_iter PASSED\n");

    printf("Starting test_merge...\n"); fflush(stdout);
    if (test_merge()) { failed++; printf("test_merge FAILED\n"); }
    else printf("test_merge PASSED\n");

    printf("Starting test_read_path...\n"); fflush(stdout);
    if (test_read_path()) { failed++; printf("test_read_path FAILED\n"); }
    else printf("test_read_path PASSED\n");

    /* Phase 5: Diagnostics tests */
    printf("Starting test_diagnostics...\n"); fflush(stdout);
    if (test_diagnostics()) { failed++; printf("test_diagnostics FAILED\n"); }
    else printf("test_diagnostics PASSED\n");

    /* Phase 6: Maintenance tests */
    printf("Starting test_maintenance...\n"); fflush(stdout);
    if (test_maintenance()) { failed++; printf("test_maintenance FAILED\n"); }
    else printf("test_maintenance PASSED\n");

    printf("\n%d test(s) failed.\n", failed);
    return failed ? EXIT_FAILURE : EXIT_SUCCESS;
}
