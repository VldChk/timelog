#ifndef TEST_HARNESS_H
#define TEST_HARNESS_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "timelog/timelog.h"

/*===========================================================================
 * Test Framework Configuration
 *===========================================================================*/

#define TEST_MAX_NAME_LEN 256
#define TEST_MAX_TESTS    1000

/*===========================================================================
 * Test Result Tracking
 *===========================================================================*/

typedef struct test_result {
    const char* name;
    const char* file;
    int         line;
    int         passed;
    char        message[512];
} test_result_t;

typedef struct test_context {
    test_result_t results[TEST_MAX_TESTS];
    int           count;
    int           passed;
    int           failed;
    const char*   current_test;
} test_context_t;

/* Global test context */
extern test_context_t g_test_ctx;

/*===========================================================================
 * Test Registration and Execution
 *===========================================================================*/

typedef void (*test_fn)(void);

typedef struct test_entry {
    const char* name;
    test_fn     fn;
} test_entry_t;

#define TEST_DECLARE(name) void test_##name(void)
#define TEST_ENTRY(name) { #name, test_##name }

/*===========================================================================
 * Assertion Macros
 *===========================================================================*/

#define TEST_ASSERT(cond) \
    do { \
        if (!(cond)) { \
            test_fail(__FILE__, __LINE__, "Assertion failed: " #cond); \
            return; \
        } \
    } while(0)

#define TEST_ASSERT_MSG(cond, msg) \
    do { \
        if (!(cond)) { \
            test_fail(__FILE__, __LINE__, msg); \
            return; \
        } \
    } while(0)

#define TEST_ASSERT_EQ(expected, actual) \
    do { \
        if ((expected) != (actual)) { \
            test_fail_eq(__FILE__, __LINE__, #expected, #actual, \
                         (long long)(expected), (long long)(actual)); \
            return; \
        } \
    } while(0)

/**
 * Type-safe equality assertions to avoid truncation and format mismatches.
 * Use these instead of TEST_ASSERT_EQ for specific types.
 */
#define TEST_ASSERT_EQ_U64(expected, actual) \
    do { \
        uint64_t _exp = (expected); \
        uint64_t _act = (actual); \
        if (_exp != _act) { \
            test_fail_eq_u64(__FILE__, __LINE__, #expected, #actual, _exp, _act); \
            return; \
        } \
    } while(0)

#define TEST_ASSERT_EQ_SIZE(expected, actual) \
    do { \
        size_t _exp = (expected); \
        size_t _act = (actual); \
        if (_exp != _act) { \
            test_fail_eq_size(__FILE__, __LINE__, #expected, #actual, _exp, _act); \
            return; \
        } \
    } while(0)

#define TEST_ASSERT_PTR_EQ(expected, actual) \
    do { \
        const void* _exp = (expected); \
        const void* _act = (actual); \
        if (_exp != _act) { \
            test_fail_eq_ptr(__FILE__, __LINE__, #expected, #actual, _exp, _act); \
            return; \
        } \
    } while(0)

#define TEST_ASSERT_NE(a, b) \
    do { \
        if ((a) == (b)) { \
            test_fail(__FILE__, __LINE__, "Expected " #a " != " #b); \
            return; \
        } \
    } while(0)

#define TEST_ASSERT_NULL(ptr) \
    do { \
        if ((ptr) != NULL) { \
            test_fail(__FILE__, __LINE__, "Expected " #ptr " to be NULL"); \
            return; \
        } \
    } while(0)

#define TEST_ASSERT_NOT_NULL(ptr) \
    do { \
        if ((ptr) == NULL) { \
            test_fail(__FILE__, __LINE__, "Expected " #ptr " to be non-NULL"); \
            return; \
        } \
    } while(0)

#define TEST_ASSERT_STATUS(expected, actual) \
    do { \
        tl_status_t _exp = (expected); \
        tl_status_t _act = (actual); \
        if (_exp != _act) { \
            test_fail_status(__FILE__, __LINE__, _exp, _act); \
            return; \
        } \
    } while(0)

/*===========================================================================
 * Test Execution Functions
 *===========================================================================*/

void test_init(void);
void test_run(const char* name, test_fn fn);
int  test_report(void);

void test_fail(const char* file, int line, const char* msg);
void test_fail_eq(const char* file, int line,
                  const char* expected_expr, const char* actual_expr,
                  long long expected, long long actual);
void test_fail_eq_u64(const char* file, int line,
                      const char* expected_expr, const char* actual_expr,
                      uint64_t expected, uint64_t actual);
void test_fail_eq_size(const char* file, int line,
                       const char* expected_expr, const char* actual_expr,
                       size_t expected, size_t actual);
void test_fail_eq_ptr(const char* file, int line,
                      const char* expected_expr, const char* actual_expr,
                      const void* expected, const void* actual);
void test_fail_status(const char* file, int line,
                      tl_status_t expected, tl_status_t actual);

/*===========================================================================
 * Test Runner Macro
 *===========================================================================*/

#define RUN_TEST(name) test_run(#name, test_##name)

#endif /* TEST_HARNESS_H */
