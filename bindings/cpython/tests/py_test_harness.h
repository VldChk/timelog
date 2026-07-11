/**
 * @file py_test_harness.h
 * @brief Shared mini-harness for the embedded-Python C binding tests.
 *
 * Each test executable compiles exactly one test .c file, so the static
 * helpers and counters below are per-binary by construction. Include this
 * header first (it defines PY_SSIZE_T_CLEAN before <Python.h>).
 *
 * Contract:
 * - main() calls tlpy_init_python() (or a file-local wrapper around it),
 *   runs the run_* wrappers emitted by TEST(), then ends with
 *   `return tlpy_test_report();`.
 * - TEST() fails a test that returns with a Python exception set, so tests
 *   must clear or consume expected exceptions (e.g. via ASSERT_EXCEPTION).
 */
#ifndef TL_PY_TEST_HARNESS_H
#define TL_PY_TEST_HARNESS_H

#ifndef PY_SSIZE_T_CLEAN
#define PY_SSIZE_T_CLEAN
#endif
#include <Python.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int tests_run = 0;
static int tests_failed = 0;

/*===========================================================================
 * Python Initialization Helpers
 *===========================================================================*/

/* Embedded-Python test executables may run under launcher shims (e.g.
 * pyenv) where the executable dirname is not a valid CPython home. Derive
 * PYTHONHOME from the configure-time interpreter unless already set. */
static void tlpy_set_pythonhome(void)
{
#ifdef TIMELOG_PYTHON_EXECUTABLE
    const char* existing = getenv("PYTHONHOME");
    if (existing != NULL && existing[0] != '\0') {
        return;
    }

    const char* exe = TIMELOG_PYTHON_EXECUTABLE;
    size_t len = strlen(exe);
    char* buf = (char*)malloc(len + 1);
    if (buf == NULL) {
        return;
    }
    memcpy(buf, exe, len + 1);

    char* last_slash = strrchr(buf, '\\');
    char* last_fwd = strrchr(buf, '/');
    char* last = last_slash;
    if (last_fwd != NULL && (last == NULL || last_fwd > last)) {
        last = last_fwd;
    }
    if (last != NULL) {
        *last = '\0';
#ifdef _WIN32
        _putenv_s("PYTHONHOME", buf);
#else
        setenv("PYTHONHOME", buf, 0);
#endif
    }
    free(buf);
#endif
}

static void tlpy_init_python(void)
{
    tlpy_set_pythonhome();
    Py_Initialize();
}

static int tlpy_finalize_python(void)
{
    return Py_FinalizeEx();
}

/* Print the summary, finalize Python, and map results to an exit code.
 * Call as the last statement of main(): `return tlpy_test_report();`.
 * Any per-file module teardown (Py_CLEAR of cached types) must happen
 * before this call, while the interpreter is still alive. */
static int tlpy_test_report(void)
{
    printf("\nSummary: %d run, %d failed\n", tests_run, tests_failed);
    if (tlpy_finalize_python() < 0) {
        fprintf(stderr, "Py_FinalizeEx failed\n");
        return 1;
    }
    return tests_failed > 0 ? 1 : 0;
}

/*===========================================================================
 * Test Macros
 *===========================================================================*/

/* Defines test_<name>() and a run_<name>() wrapper that counts the test,
 * runs it, and fails it if it returns with a Python exception set. */
#define TEST(name) \
    static void test_##name(void); \
    static void run_##name(void) { \
        printf("  %s... ", #name); \
        fflush(stdout); \
        tests_run++; \
        PyErr_Clear(); \
        test_##name(); \
        if (PyErr_Occurred()) { \
            printf("FAIL (exception set)\n"); \
            PyErr_Print(); \
            tests_failed++; \
            return; \
        } \
        printf("PASS\n"); \
    } \
    static void test_##name(void)

#define ASSERT(cond) \
    do { \
        if (!(cond)) { \
            printf("FAIL\n    Assertion failed: %s\n    at %s:%d\n", \
                   #cond, __FILE__, __LINE__); \
            tests_failed++; \
            return; \
        } \
    } while(0)

#define ASSERT_EQ(a, b) \
    do { \
        if ((a) != (b)) { \
            printf("FAIL\n    Expected %s == %s\n    Got %lld != %lld\n    at %s:%d\n", \
                   #a, #b, (long long)(a), (long long)(b), __FILE__, __LINE__); \
            tests_failed++; \
            return; \
        } \
    } while(0)

#define ASSERT_NOT_NULL(ptr) \
    do { \
        if ((ptr) == NULL) { \
            printf("FAIL\n    Expected %s != NULL\n    at %s:%d\n", \
                   #ptr, __FILE__, __LINE__); \
            if (PyErr_Occurred()) PyErr_Print(); \
            tests_failed++; \
            return; \
        } \
    } while(0)

#define ASSERT_NULL(ptr) \
    do { \
        if ((ptr) != NULL) { \
            printf("FAIL\n    Expected %s == NULL\n    at %s:%d\n", \
                   #ptr, __FILE__, __LINE__); \
            tests_failed++; \
            return; \
        } \
    } while(0)

#define ASSERT_EXCEPTION(exc_type) \
    do { \
        if (!PyErr_Occurred()) { \
            printf("FAIL\n    Expected exception %s, none occurred\n    at %s:%d\n", \
                   #exc_type, __FILE__, __LINE__); \
            tests_failed++; \
            return; \
        } \
        if (!PyErr_ExceptionMatches(exc_type)) { \
            printf("FAIL\n    Expected exception %s, got different\n    at %s:%d\n", \
                   #exc_type, __FILE__, __LINE__); \
            PyErr_Print(); \
            tests_failed++; \
            return; \
        } \
        PyErr_Clear(); \
    } while(0)

#endif /* TL_PY_TEST_HARNESS_H */
