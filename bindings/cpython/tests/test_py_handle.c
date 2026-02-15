/**
 * @file test_py_handle.c
 * @brief Unit tests for Python handle context
 *
 * Tests the lock-free queue, pin tracking, and drain logic
 * without requiring a running Timelog instance.
 *
 * Note: These tests require Python to be initialized for Py_DECREF calls.
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_handle.h"
#include "timelog/timelog.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*===========================================================================
 * Test Framework (minimal)
 *===========================================================================*/

static int tests_run = 0;
static int tests_failed = 0;

/*===========================================================================
 * Python Initialization Helper
 *===========================================================================*/

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

#define TEST(name) \
    static void test_##name(void); \
    static void run_##name(void) { \
        printf("  %s... ", #name); \
        fflush(stdout); \
        tests_run++; \
        test_##name(); \
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
            printf("FAIL\n    Expected %s == %s\n    at %s:%d\n", \
                   #a, #b, __FILE__, __LINE__); \
            tests_failed++; \
            return; \
        } \
    } while(0)

/*===========================================================================
 * Tests
 *===========================================================================*/

typedef struct {
    PyObject_HEAD
    tl_py_handle_ctx_t* ctx;
} ReentrantObj;

static void Reentrant_dealloc(ReentrantObj* self)
{
    if (self->ctx != NULL) {
        /* Re-enter drain while already draining */
        (void)tl_py_drain_retired(self->ctx, 0);
    }
    Py_TYPE(self)->tp_free((PyObject*)self);
}

static PyTypeObject Reentrant_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._test.ReentrantObj",
    .tp_basicsize = sizeof(ReentrantObj),
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_dealloc = (destructor)Reentrant_dealloc,
    .tp_new = PyType_GenericNew,
};

TEST(ctx_init_destroy)
{
    tl_py_handle_ctx_t ctx;

    tl_status_t st = tl_py_handle_ctx_init(&ctx, 0);
    ASSERT_EQ(st, TL_OK);
    ASSERT_EQ(tl_py_pins_count(&ctx), 0);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);
    ASSERT_EQ(tl_py_alloc_failures(&ctx), 0);

    tl_py_handle_ctx_destroy(&ctx);
}

TEST(ctx_init_null_fails)
{
    tl_status_t st = tl_py_handle_ctx_init(NULL, 0);
    ASSERT_EQ(st, TL_EINVAL);
}

TEST(pins_enter_exit)
{
    tl_py_handle_ctx_t ctx;
    tl_py_handle_ctx_init(&ctx, 0);

    ASSERT_EQ(tl_py_pins_count(&ctx), 0);

    tl_py_pins_enter(&ctx);
    ASSERT_EQ(tl_py_pins_count(&ctx), 1);

    tl_py_pins_enter(&ctx);
    ASSERT_EQ(tl_py_pins_count(&ctx), 2);

    tl_py_pins_exit_and_maybe_drain(&ctx);
    ASSERT_EQ(tl_py_pins_count(&ctx), 1);

    tl_py_pins_exit_and_maybe_drain(&ctx);
    ASSERT_EQ(tl_py_pins_count(&ctx), 0);

    tl_py_handle_ctx_destroy(&ctx);
}

TEST(handle_encode_decode_roundtrip)
{
    /* Use Py_None as test object (always available) */
    PyObject* obj = Py_None;

    tl_handle_t h = tl_py_handle_encode(obj);
    PyObject* decoded = tl_py_handle_decode(h);

    ASSERT(decoded == obj);
}

TEST(on_drop_enqueues)
{
    tl_py_handle_ctx_t ctx;
    tl_py_handle_ctx_init(&ctx, 0);

    /*
     * Create a test object.
     * IMPORTANT: Use PyDict_New() instead of PyLong_FromLong() because
     * Python 3.12+ makes small integers "immortal" - their refcount never
     * changes, making Py_INCREF/Py_DECREF no-ops. Dicts are always new.
     */
    PyObject* obj = PyDict_New();
    ASSERT(obj != NULL);

    /* Increment refcount (simulating append) */
    Py_INCREF(obj);
    Py_ssize_t initial_refcnt = Py_REFCNT(obj);

    /* Simulate on_drop callback */
    tl_handle_t h = tl_py_handle_encode(obj);
    tl_py_on_drop_handle(&ctx, 1000, h);

    /* Object should be queued but not DECREF'd yet */
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 1);
    ASSERT_EQ(Py_REFCNT(obj), initial_refcnt);

    /* Drain the queue */
    size_t drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, 1);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    /* Refcount should be decremented */
    ASSERT_EQ(Py_REFCNT(obj), initial_refcnt - 1);

    /* Clean up */
    Py_DECREF(obj);
    tl_py_handle_ctx_destroy(&ctx);
}

TEST(drain_reentrancy_guard)
{
    tl_py_handle_ctx_t ctx;
    tl_py_handle_ctx_init(&ctx, 0);

    if (PyType_Ready(&Reentrant_Type) < 0) {
        PyErr_Print();
        tests_failed++;
        return;
    }

    ReentrantObj* obj = (ReentrantObj*)Reentrant_Type.tp_alloc(&Reentrant_Type, 0);
    ASSERT(obj != NULL);
    obj->ctx = &ctx;

    /* Use the sole reference as the engine-owned ref */
    tl_handle_t h = tl_py_handle_encode((PyObject*)obj);
    tl_py_on_drop_handle(&ctx, 1000, h);

    size_t drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, 1);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    tl_py_handle_ctx_destroy(&ctx);
}

TEST(drain_blocked_by_pins)
{
    tl_py_handle_ctx_t ctx;
    tl_py_handle_ctx_init(&ctx, 0);

    /* Use dict (non-immortal) - see on_drop_enqueues comment */
    PyObject* obj = PyDict_New();
    ASSERT(obj != NULL);
    Py_INCREF(obj);  /* Simulating append */

    /* Enter pinned region (simulating active iterator) */
    tl_py_pins_enter(&ctx);

    /* Enqueue via on_drop */
    tl_handle_t h = tl_py_handle_encode(obj);
    tl_py_on_drop_handle(&ctx, 2000, h);

    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 1);

    /* Try to drain - should be blocked by pins */
    size_t drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, 0);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 1);

    /* Exit pin - should trigger drain */
    tl_py_pins_exit_and_maybe_drain(&ctx);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    /* Clean up */
    Py_DECREF(obj);
    tl_py_handle_ctx_destroy(&ctx);
}

TEST(force_drain_ignores_pins)
{
    tl_py_handle_ctx_t ctx;
    tl_py_handle_ctx_init(&ctx, 0);

    /* Use dict (non-immortal) - see on_drop_enqueues comment */
    PyObject* obj = PyDict_New();
    ASSERT(obj != NULL);
    Py_INCREF(obj);

    /* Enter pinned region */
    tl_py_pins_enter(&ctx);

    /* Enqueue */
    tl_handle_t h = tl_py_handle_encode(obj);
    tl_py_on_drop_handle(&ctx, 3000, h);

    /* Force drain should work despite pins */
    size_t drained = tl_py_drain_retired(&ctx, 1);  /* force=1 */
    ASSERT_EQ(drained, 1);

    /* Exit pin */
    tl_py_pins_exit_and_maybe_drain(&ctx);

    Py_DECREF(obj);
    tl_py_handle_ctx_destroy(&ctx);
}

TEST(batch_limit)
{
    tl_py_handle_ctx_t ctx;
    tl_py_handle_ctx_init(&ctx, 2);  /* batch limit = 2 */

    /* Create and enqueue 5 objects (dicts, non-immortal) */
    PyObject* objs[5];
    for (int i = 0; i < 5; i++) {
        objs[i] = PyDict_New();
        ASSERT(objs[i] != NULL);
        Py_INCREF(objs[i]);

        tl_handle_t h = tl_py_handle_encode(objs[i]);
        tl_py_on_drop_handle(&ctx, (tl_ts_t)(i * 1000), h);
    }

    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 5);

    /* First drain: should drain 2 */
    size_t drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, 2);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 3);

    /* Second drain: should drain 2 */
    drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, 2);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 1);

    /* Third drain: should drain 1 */
    drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, 1);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    /* Clean up */
    for (int i = 0; i < 5; i++) {
        Py_DECREF(objs[i]);
    }
    tl_py_handle_ctx_destroy(&ctx);
}

TEST(multiple_on_drop_concurrent_simulation)
{
    /*
     * Simulate what happens when multiple on_drop calls occur.
     * In real usage, these would be from the maintenance thread.
     * Here we just verify the queue handles multiple pushes correctly.
     */
    tl_py_handle_ctx_t ctx;
    tl_py_handle_ctx_init(&ctx, 0);

    const int count = 100;
    PyObject* objs[100];

    /* Use dicts (non-immortal) - see on_drop_enqueues comment */
    for (int i = 0; i < count; i++) {
        objs[i] = PyDict_New();
        ASSERT(objs[i] != NULL);
        Py_INCREF(objs[i]);

        tl_handle_t h = tl_py_handle_encode(objs[i]);
        tl_py_on_drop_handle(&ctx, (tl_ts_t)i, h);
    }

    ASSERT_EQ(tl_py_retired_queue_len(&ctx), (uint64_t)count);

    /* Drain all */
    size_t drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, (size_t)count);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    for (int i = 0; i < count; i++) {
        Py_DECREF(objs[i]);
    }
    tl_py_handle_ctx_destroy(&ctx);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

/**
 * Run all py_handle tests. Returns number of failures.
 * Python must already be initialized before calling this.
 */
int run_py_handle_tests(void)
{
    /* Reset counters for this suite */
    tests_run = 0;
    tests_failed = 0;

    run_ctx_init_destroy();
    run_ctx_init_null_fails();
    run_pins_enter_exit();
    run_handle_encode_decode_roundtrip();
    run_on_drop_enqueues();
    run_drain_reentrancy_guard();
    run_drain_blocked_by_pins();
    run_force_drain_ignores_pins();
    run_batch_limit();
    run_multiple_on_drop_concurrent_simulation();

    printf("%d tests run, %d failed\n", tests_run, tests_failed);
    return tests_failed;
}

#ifndef TEST_PY_MAIN
/* Standalone executable entry point */
int main(int argc, char* argv[])
{
    (void)argc;
    (void)argv;

    /* Initialize Python */
    tlpy_init_python();

    printf("Running py_handle tests...\n");
    int failures = run_py_handle_tests();

    /* Finalize Python */
    tlpy_finalize_python();

    return failures > 0 ? 1 : 0;
}
#endif /* TEST_PY_MAIN */
