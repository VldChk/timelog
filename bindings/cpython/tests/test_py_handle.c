/**
 * @file test_py_handle.c
 * @brief Unit tests for Python handle context (LLD-B1)
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

    /* Create a test object */
    PyObject* obj = PyLong_FromLong(42);
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

TEST(drain_blocked_by_pins)
{
    tl_py_handle_ctx_t ctx;
    tl_py_handle_ctx_init(&ctx, 0);

    /* Create a test object */
    PyObject* obj = PyLong_FromLong(123);
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

    PyObject* obj = PyLong_FromLong(456);
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

    /* Create and enqueue 5 objects */
    PyObject* objs[5];
    for (int i = 0; i < 5; i++) {
        objs[i] = PyLong_FromLong(i);
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

    for (int i = 0; i < count; i++) {
        objs[i] = PyLong_FromLong(i);
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

int main(int argc, char* argv[])
{
    (void)argc;
    (void)argv;

    /* Initialize Python */
    Py_Initialize();

    printf("Running py_handle tests...\n");

    run_ctx_init_destroy();
    run_ctx_init_null_fails();
    run_pins_enter_exit();
    run_handle_encode_decode_roundtrip();
    run_on_drop_enqueues();
    run_drain_blocked_by_pins();
    run_force_drain_ignores_pins();
    run_batch_limit();
    run_multiple_on_drop_concurrent_simulation();

    printf("\n%d tests run, %d failed\n", tests_run, tests_failed);

    /* Finalize Python */
    Py_Finalize();

    return tests_failed > 0 ? 1 : 0;
}
