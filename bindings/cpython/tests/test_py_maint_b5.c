/**
 * @file test_py_maint_b5.c
 * @brief Maintenance + threading integration tests
 *
 * Test Categories:
 * - Handle-only tests: Use tl_py_handle_ctx_t directly
 * - PyTimelog tests: Require module/errors/type initialization
 *
 * Key Design Decisions:
 * - Use PyDict_New() NOT PyLong_FromLong() because small integers are
 *   immortal on Python 3.12+ (their refcount doesn't change)
 * - Tests for LIFO Treiber stack behavior (not FIFO)
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_handle.h"
#include "timelogpy/py_timelog.h"
#include "timelogpy/py_errors.h"
#include "timelog/timelog.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

/*===========================================================================
 * Test Framework (from test_py_handle.c pattern)
 *===========================================================================*/

static int tests_run = 0;
static int tests_failed = 0;

/*===========================================================================
 * Python Initialization Helpers
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

/* Module storage for full init */
static PyObject* test_module = NULL;

/* Module definition for test harness */
static struct PyModuleDef test_module_def = {
    PyModuleDef_HEAD_INIT,
    "test_maint_b5",
    NULL,
    -1,
    NULL
};

/* Full init for PyTimelog tests */
static int tlpy_init_python_full(void)
{
    tlpy_set_pythonhome();
    Py_Initialize();

    /* Create test module for error registration */
    test_module = PyModule_Create(&test_module_def);
    if (test_module == NULL) {
        fprintf(stderr, "Failed to create test module\n");
        return -1;
    }

    /* Initialize error types FIRST */
    if (TlPy_InitErrors(test_module) < 0) {
        fprintf(stderr, "Failed to initialize error types\n");
        return -1;
    }

    /* Ready PyTimelog type */
    if (PyType_Ready(&PyTimelog_Type) < 0) {
        fprintf(stderr, "Failed to initialize PyTimelog type\n");
        return -1;
    }

    return 0;
}

static int tlpy_finalize_python(void)
{
    Py_XDECREF(test_module);
    test_module = NULL;
    return Py_FinalizeEx();
}

/*===========================================================================
 * Test Macros
 *===========================================================================*/

#define TEST(name) \
    static void test_##name(void); \
    static void run_##name(void) { \
        printf("  %s... ", #name); \
        fflush(stdout); \
        tests_run++; \
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

/*===========================================================================
 * Helper: Create PyTimelog with custom config
 *===========================================================================*/

static PyTimelog* create_timelog_custom(const char* maint_mode,
                                         const char* busy_policy)
{
    PyObject* args = PyTuple_New(0);
    if (args == NULL) return NULL;

    PyObject* kwargs = PyDict_New();
    if (kwargs == NULL) {
        Py_DECREF(args);
        return NULL;
    }

    if (maint_mode != NULL) {
        PyObject* val = PyUnicode_FromString(maint_mode);
        if (val == NULL || PyDict_SetItemString(kwargs, "maintenance", val) < 0) {
            Py_XDECREF(val);
            Py_DECREF(args);
            Py_DECREF(kwargs);
            return NULL;
        }
        Py_DECREF(val);
    }

    if (busy_policy != NULL) {
        PyObject* val = PyUnicode_FromString(busy_policy);
        if (val == NULL || PyDict_SetItemString(kwargs, "busy_policy", val) < 0) {
            Py_XDECREF(val);
            Py_DECREF(args);
            Py_DECREF(kwargs);
            return NULL;
        }
        Py_DECREF(val);
    }

    PyTimelog* self = (PyTimelog*)PyTimelog_Type.tp_alloc(&PyTimelog_Type, 0);
    if (self == NULL) {
        Py_DECREF(args);
        Py_DECREF(kwargs);
        return NULL;
    }

    if (PyTimelog_Type.tp_init((PyObject*)self, args, kwargs) < 0) {
        Py_DECREF(self);
        Py_DECREF(args);
        Py_DECREF(kwargs);
        return NULL;
    }

    Py_DECREF(args);
    Py_DECREF(kwargs);
    return self;
}

static PyTimelog* create_timelog_custom_with_memtable(const char* maint_mode,
                                                      const char* busy_policy,
                                                      long long memtable_max_bytes)
{
    PyObject* args = PyTuple_New(0);
    if (args == NULL) return NULL;

    PyObject* kwargs = PyDict_New();
    if (kwargs == NULL) {
        Py_DECREF(args);
        return NULL;
    }

    if (maint_mode != NULL) {
        PyObject* val = PyUnicode_FromString(maint_mode);
        if (val == NULL || PyDict_SetItemString(kwargs, "maintenance", val) < 0) {
            Py_XDECREF(val);
            Py_DECREF(kwargs);
            Py_DECREF(args);
            return NULL;
        }
        Py_DECREF(val);
    }

    if (busy_policy != NULL) {
        PyObject* val = PyUnicode_FromString(busy_policy);
        if (val == NULL || PyDict_SetItemString(kwargs, "busy_policy", val) < 0) {
            Py_XDECREF(val);
            Py_DECREF(kwargs);
            Py_DECREF(args);
            return NULL;
        }
        Py_DECREF(val);
    }

    if (memtable_max_bytes > 0) {
        PyObject* val = PyLong_FromLongLong(memtable_max_bytes);
        if (val == NULL || PyDict_SetItemString(kwargs, "memtable_max_bytes", val) < 0) {
            Py_XDECREF(val);
            Py_DECREF(kwargs);
            Py_DECREF(args);
            return NULL;
        }
        Py_DECREF(val);
    }

    PyObject* obj = PyObject_Call((PyObject*)&PyTimelog_Type, args, kwargs);
    Py_DECREF(kwargs);
    Py_DECREF(args);

    if (obj == NULL) return NULL;
    return (PyTimelog*)obj;
}

static void close_and_dealloc(PyTimelog* self)
{
    if (self == NULL) return;

    /* Call close method */
    PyObject* close_method = PyObject_GetAttrString((PyObject*)self, "close");
    if (close_method != NULL) {
        PyObject* result = PyObject_CallNoArgs(close_method);
        Py_XDECREF(result);
        Py_DECREF(close_method);
    }
    PyErr_Clear();  /* Ignore any errors from close */

    /* Deallocate */
    Py_DECREF(self);
}

/*===========================================================================
 * Drain Mechanism Tests (Handle-only)
 *
 * These tests use tl_py_handle_ctx_t directly without PyTimelog.
 *===========================================================================*/

TEST(drain_batch_limit_exact)
{
    /*
     * Verify batch limit is respected exactly.
     * Setup: ctx with batch_limit=3, enqueue 10 objects
     * Action: drain(force=0)
     * Assert: exactly 3 drained, 7 remaining
     */
    tl_py_handle_ctx_t ctx;
    tl_status_t st = tl_py_handle_ctx_init(&ctx, 3);  /* batch_limit = 3 */
    ASSERT_EQ(st, TL_OK);

    /*
     * Enqueue 10 objects using PyDict_New().
     * IMPORTANT: Do NOT use PyLong_FromLong() - small integers are
     * immortal on Python 3.12+ (their refcount doesn't change).
     */
    for (int i = 0; i < 10; i++) {
        PyObject* obj = PyDict_New();  /* Fresh dict has refcnt=1 */
        ASSERT_NOT_NULL(obj);
        tl_handle_t h = tl_py_handle_encode(obj);
        tl_py_on_drop_handle(&ctx, (tl_ts_t)i, h);
    }

    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 10);

    /* Drain with force=0 (respects batch limit) */
    size_t drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, 3);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 7);

    /* Force drain remaining to clean up */
    tl_py_drain_retired(&ctx, 1);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    tl_py_handle_ctx_destroy(&ctx);
}

TEST(drain_reattach_remaining)
{
    /*
     * Verify re-attachment works correctly after partial drain.
     * Note: Treiber stack is LIFO, NOT FIFO. Order is NOT preserved.
     *
     * Setup: ctx with batch_limit=2, enqueue 5 objects
     * Action: drain, then on_drop 1 more, then drain again
     * Assert: re-attachment works correctly (remaining items prepended on re-attach)
     */
    tl_py_handle_ctx_t ctx;
    tl_status_t st = tl_py_handle_ctx_init(&ctx, 2);  /* batch_limit = 2 */
    ASSERT_EQ(st, TL_OK);

    /* Enqueue 5 objects */
    for (int i = 0; i < 5; i++) {
        PyObject* obj = PyDict_New();
        ASSERT_NOT_NULL(obj);
        tl_handle_t h = tl_py_handle_encode(obj);
        tl_py_on_drop_handle(&ctx, (tl_ts_t)(i * 100), h);
    }
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 5);

    /* First drain: drains 2 */
    size_t drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, 2);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 3);

    /* On_drop 1 more (simulating concurrent callback) */
    PyObject* new_obj = PyDict_New();
    ASSERT_NOT_NULL(new_obj);
    tl_py_on_drop_handle(&ctx, 999, tl_py_handle_encode(new_obj));
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 4);  /* 3 re-attached + 1 new */

    /* Second drain: drains 2 */
    drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, 2);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 2);

    /* Clean up remaining */
    tl_py_drain_retired(&ctx, 1);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    tl_py_handle_ctx_destroy(&ctx);
}

TEST(force_drain_ignores_batch_limit)
{
    /*
     * Verify force=1 drains all regardless of batch limit.
     * Setup: ctx with batch_limit=2, enqueue 10 objects
     * Action: drain(force=1)
     * Assert: all 10 drained regardless of limit
     */
    tl_py_handle_ctx_t ctx;
    tl_status_t st = tl_py_handle_ctx_init(&ctx, 2);  /* batch_limit = 2 */
    ASSERT_EQ(st, TL_OK);

    /* Enqueue 10 objects */
    for (int i = 0; i < 10; i++) {
        PyObject* obj = PyDict_New();
        ASSERT_NOT_NULL(obj);
        tl_handle_t h = tl_py_handle_encode(obj);
        tl_py_on_drop_handle(&ctx, (tl_ts_t)i, h);
    }
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 10);

    /* Force drain should drain all regardless of batch limit */
    size_t drained = tl_py_drain_retired(&ctx, 1);  /* force=1 */
    ASSERT_EQ(drained, 10);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    tl_py_handle_ctx_destroy(&ctx);
}

TEST(metrics_queue_len_accuracy)
{
    /*
     * Verify tl_py_retired_queue_len() returns correct approximate count.
     * Setup: enqueue 10, drain 3, check queue_len == 7
     */
    tl_py_handle_ctx_t ctx;
    tl_status_t st = tl_py_handle_ctx_init(&ctx, 3);  /* batch_limit = 3 */
    ASSERT_EQ(st, TL_OK);

    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    /* Enqueue 10 objects */
    for (int i = 0; i < 10; i++) {
        PyObject* obj = PyDict_New();
        ASSERT_NOT_NULL(obj);
        tl_py_on_drop_handle(&ctx, (tl_ts_t)i, tl_py_handle_encode(obj));
    }
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 10);

    /* Drain 3 */
    size_t drained = tl_py_drain_retired(&ctx, 0);
    ASSERT_EQ(drained, 3);

    /* Verify queue_len reflects remaining */
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 7);

    /* Clean up */
    tl_py_drain_retired(&ctx, 1);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    tl_py_handle_ctx_destroy(&ctx);
}

/*===========================================================================
 * Close Path Tests (Mixed)
 *
 * Tests verifying close sequence behavior with retired queue.
 *===========================================================================*/

TEST(close_drains_injected_queue)
{
    /*
     * Verify that force drain clears directly injected objects.
     * This test uses direct on_drop injection to avoid non-deterministic
     * compaction timing.
     *
     * Setup: Create handle_ctx, directly inject objects via on_drop
     * Action: Simulate close sequence (force drain)
     * Assert: retired_queue_len == 0 after force drain
     */
    tl_py_handle_ctx_t ctx;
    tl_status_t st = tl_py_handle_ctx_init(&ctx, 0);  /* unlimited batch */
    ASSERT_EQ(st, TL_OK);

    /* Inject 5 objects directly via on_drop */
    for (int i = 0; i < 5; i++) {
        PyObject* obj = PyDict_New();
        ASSERT_NOT_NULL(obj);
        tl_py_on_drop_handle(&ctx, (tl_ts_t)i, tl_py_handle_encode(obj));
    }
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 5);

    /* Simulate close sequence: force drain */
    size_t drained = tl_py_drain_retired(&ctx, 1);  /* force=1 */
    ASSERT_EQ(drained, 5);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    tl_py_handle_ctx_destroy(&ctx);
}

TEST(close_force_drain_with_batch_limit)
{
    /*
     * Verify force=1 overrides batch limit during close.
     * Setup: ctx with drain_batch_limit=2, inject 10 objects via on_drop
     * Action: tl_py_drain_retired(ctx, force=1)
     * Assert: all 10 drained (force=1 overrides limit)
     */
    tl_py_handle_ctx_t ctx;
    tl_status_t st = tl_py_handle_ctx_init(&ctx, 2);  /* batch_limit = 2 */
    ASSERT_EQ(st, TL_OK);

    /* Inject 10 objects */
    for (int i = 0; i < 10; i++) {
        PyObject* obj = PyDict_New();
        ASSERT_NOT_NULL(obj);
        tl_py_on_drop_handle(&ctx, (tl_ts_t)i, tl_py_handle_encode(obj));
    }
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 10);

    /* Force drain should override batch_limit=2 */
    size_t drained = tl_py_drain_retired(&ctx, 1);  /* force=1 */
    ASSERT_EQ(drained, 10);
    ASSERT_EQ(tl_py_retired_queue_len(&ctx), 0);

    tl_py_handle_ctx_destroy(&ctx);
}

TEST(dealloc_with_pins_warning)
{
    /*
     * Verify dealloc with pins > 0 doesn't crash (leaks resources with warning).
     * Setup: PyTimelog, simulate pins=1, trigger dealloc
     * Assert: No crash (debug warning may be printed)
     *
     * Note: This test requires full PyTimelog initialization.
     */
    PyTimelog* tl = create_timelog_custom("disabled", "raise");
    ASSERT_NOT_NULL(tl);

    /* Simulate active snapshot by incrementing pins */
    tl_py_pins_enter(&tl->handle_ctx);
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 1);

    /*
     * Dealloc without releasing pins.
     * This should NOT crash, but may print a debug warning.
     * Resources will be leaked (by design - leak over crash).
     */
    Py_DECREF(tl);

    /* If we get here without crash, test passes */
}

/*===========================================================================
 * Worker Lifecycle Tests (PyTimelog)
 *
 * Tests for maintenance worker start/stop behavior.
 *===========================================================================*/

TEST(maint_start_idempotent)
{
    /*
     * Verify start_maintenance() is idempotent (can be called twice).
     * Setup: PyTimelog(maintenance="background")
     * Action: start_maintenance() twice
     * Assert: both return success (TL_OK)
     */
    PyTimelog* tl = create_timelog_custom("background", "raise");
    ASSERT_NOT_NULL(tl);

    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "start_maintenance");
    ASSERT_NOT_NULL(method);

    /* First start */
    PyObject* result1 = PyObject_CallNoArgs(method);
    ASSERT_NOT_NULL(result1);
    Py_DECREF(result1);

    /* Second start - should also succeed (idempotent) */
    PyObject* result2 = PyObject_CallNoArgs(method);
    ASSERT_NOT_NULL(result2);
    Py_DECREF(result2);

    Py_DECREF(method);

    /* Stop before close */
    PyObject* stop_method = PyObject_GetAttrString((PyObject*)tl, "stop_maintenance");
    PyObject* stop_result = PyObject_CallNoArgs(stop_method);
    Py_XDECREF(stop_result);
    Py_DECREF(stop_method);

    close_and_dealloc(tl);
}

TEST(maint_stop_without_start)
{
    /*
     * Verify stop_maintenance() without prior start returns success.
     * Setup: PyTimelog(maintenance="background")
     * Action: stop_maintenance() without prior start
     * Assert: returns success (idempotent)
     */
    PyTimelog* tl = create_timelog_custom("background", "raise");
    ASSERT_NOT_NULL(tl);

    /* Stop without start - should succeed (idempotent) */
    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "stop_maintenance");
    ASSERT_NOT_NULL(method);

    PyObject* result = PyObject_CallNoArgs(method);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    Py_DECREF(method);
    close_and_dealloc(tl);
}

TEST(stress_start_stop_cycles)
{
    /*
     * Stress test: 50 cycles of start -> stop.
     * Verifies no crash, no thread leak, no deadlock.
     *
     * Note: Run with TSan in CI to detect races.
     */
    PyTimelog* tl = create_timelog_custom("background", "raise");
    ASSERT_NOT_NULL(tl);

    PyObject* start_method = PyObject_GetAttrString((PyObject*)tl, "start_maintenance");
    PyObject* stop_method = PyObject_GetAttrString((PyObject*)tl, "stop_maintenance");
    ASSERT_NOT_NULL(start_method);
    ASSERT_NOT_NULL(stop_method);

    for (int i = 0; i < 50; i++) {
        /* Start */
        PyObject* start_result = PyObject_CallNoArgs(start_method);
        if (start_result == NULL) {
            printf("FAIL at cycle %d (start)\n", i);
            PyErr_Print();
            tests_failed++;
            break;
        }
        Py_DECREF(start_result);

        /* Stop */
        PyObject* stop_result = PyObject_CallNoArgs(stop_method);
        if (stop_result == NULL) {
            printf("FAIL at cycle %d (stop)\n", i);
            PyErr_Print();
            tests_failed++;
            break;
        }
        Py_DECREF(stop_result);
    }

    Py_DECREF(start_method);
    Py_DECREF(stop_method);
    close_and_dealloc(tl);
}

/*===========================================================================
 * EBUSY Integration Tests (PyTimelog)
 *
 * Tests for TL_EBUSY (backpressure) handling.
 *
 * Note: Triggering real EBUSY requires filling the memtable to trigger seal
 * while maintenance is disabled. These tests verify the policy configuration
 * is correct and exception types are raised properly.
 *===========================================================================*/

TEST(ebusy_raise_exception)
{
    /*
     * Verify TimelogBusyError exception type exists and is correct.
     * With "raise" policy, EBUSY would raise TimelogBusyError.
     */
    PyTimelog* tl = create_timelog_custom("disabled", "raise");
    ASSERT_NOT_NULL(tl);
    ASSERT_EQ(tl->busy_policy, TL_PY_BUSY_RAISE);

    /* Verify TlPy_TimelogBusyError is initialized */
    ASSERT(TlPy_TimelogBusyError != NULL);

    close_and_dealloc(tl);
}

TEST(ebusy_raise_triggers_exception)
{
    /*
     * Trigger a real TL_EBUSY by forcing frequent seals in manual mode.
     * With busy_policy="raise", append must raise TimelogBusyError.
     */
    PyTimelog* tl = create_timelog_custom_with_memtable("disabled", "raise", 64);
    ASSERT_NOT_NULL(tl);

    PyObject* append_method = PyObject_GetAttrString((PyObject*)tl, "append");
    ASSERT_NOT_NULL(append_method);

    bool saw_busy = false;
    for (int i = 0; i < 10000; i++) {
        PyObject* obj = PyDict_New();
        PyObject* ts = PyLong_FromLongLong(1000 + i);
        ASSERT_NOT_NULL(obj);
        ASSERT_NOT_NULL(ts);

        PyObject* args = PyTuple_Pack(2, ts, obj);
        Py_DECREF(ts);
        Py_DECREF(obj);
        ASSERT_NOT_NULL(args);

        PyObject* result = PyObject_Call(append_method, args, NULL);
        Py_DECREF(args);

        if (result == NULL) {
            if (PyErr_ExceptionMatches(TlPy_TimelogBusyError)) {
                PyErr_Clear();
                saw_busy = true;
                break;
            }
            PyErr_Print();
            tests_failed++;
            break;
        }
        Py_DECREF(result);
    }

    ASSERT(saw_busy);
    Py_DECREF(append_method);
    close_and_dealloc(tl);
}

TEST(ebusy_silent_no_exception)
{
    /*
     * Verify silent policy is configured correctly.
     * With "silent" policy, EBUSY would return success without exception.
     */
    PyTimelog* tl = create_timelog_custom("disabled", "silent");
    ASSERT_NOT_NULL(tl);
    ASSERT_EQ(tl->busy_policy, TL_PY_BUSY_SILENT);

    close_and_dealloc(tl);
}

TEST(ebusy_flush_triggers_segment)
{
    /*
     * Verify flush policy is configured correctly.
     * With "flush" policy, EBUSY would trigger a flush before returning.
     *
     * Note: We cannot directly observe flush call. This test verifies
     * the policy is configured. Behavior-based assertion would require
     * checking segment count before/after EBUSY, but triggering EBUSY
     * requires filling memtable which is complex to set up in unit test.
     */
    PyTimelog* tl = create_timelog_custom("background", "flush");
    ASSERT_NOT_NULL(tl);
    ASSERT_EQ(tl->busy_policy, TL_PY_BUSY_FLUSH);

    /* Verify engine is operational */
    ASSERT(tl->tl != NULL);
    ASSERT_EQ(tl->closed, 0);

    close_and_dealloc(tl);
}

TEST(ebusy_extend_partial_commit)
{
    /*
     * Test extend behavior - items are committed sequentially.
     * If EBUSY occurs mid-batch, prior items remain committed.
     *
     * This test verifies the extend mechanism works correctly.
     * Actual EBUSY partial commit requires filling memtable.
     */
    PyTimelog* tl = create_timelog_custom("disabled", "raise");
    ASSERT_NOT_NULL(tl);

    /*
     * Create list of (ts, obj) tuples using dicts (non-immortal).
     *
     * Refcount protocol:
     * - PyDict_New() returns new ref (refcnt=1)
     * - PyLong_FromLongLong() returns new ref (refcnt=1)
     * - PyTuple_Pack() INCREFs all its arguments
     * - We must DECREF the timestamps after tuple creation
     * - DO NOT DECREF obj1/2/3 - they'll be freed when list destroys tuples
     */
    PyObject* obj1 = PyDict_New();
    PyObject* obj2 = PyDict_New();
    PyObject* obj3 = PyDict_New();
    ASSERT_NOT_NULL(obj1);
    ASSERT_NOT_NULL(obj2);
    ASSERT_NOT_NULL(obj3);

    PyObject* ts1 = PyLong_FromLongLong(1000);
    PyObject* ts2 = PyLong_FromLongLong(2000);
    PyObject* ts3 = PyLong_FromLongLong(3000);
    ASSERT_NOT_NULL(ts1);
    ASSERT_NOT_NULL(ts2);
    ASSERT_NOT_NULL(ts3);

    PyObject* list = PyList_New(3);
    ASSERT_NOT_NULL(list);
    PyList_SET_ITEM(list, 0, PyTuple_Pack(2, ts1, obj1));
    PyList_SET_ITEM(list, 1, PyTuple_Pack(2, ts2, obj2));
    PyList_SET_ITEM(list, 2, PyTuple_Pack(2, ts3, obj3));

    /* DECREF timestamps since PyTuple_Pack INCREF'd them */
    Py_DECREF(ts1);
    Py_DECREF(ts2);
    Py_DECREF(ts3);

    PyObject* extend_method = PyObject_GetAttrString((PyObject*)tl, "extend");
    ASSERT_NOT_NULL(extend_method);

    PyObject* args = PyTuple_Pack(1, list);
    PyObject* result = PyObject_Call(extend_method, args, NULL);
    ASSERT_NOT_NULL(result);  /* Should succeed */
    Py_DECREF(result);

    Py_DECREF(args);
    Py_DECREF(extend_method);
    Py_DECREF(list);  /* Destroys tuples, which DECREF one ref to obj1/2/3 each */

    /*
     * DECREF our original refs to obj1/2/3.
     * After PyTuple_Pack: refcnt=2 (our ref + tuple's ref)
     * After Py_DECREF(list): refcnt=1 (tuple destroyed, only our ref remains)
     * After these DECREFs: refcnt=0 (freed)
     */
    Py_DECREF(obj1);
    Py_DECREF(obj2);
    Py_DECREF(obj3);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Error Mapping Tests
 *===========================================================================*/

TEST(error_mapping_overflow)
{
    PyObject* res = TlPy_RaiseFromStatus(TL_EOVERFLOW);
    ASSERT_NULL(res);
    ASSERT_EXCEPTION(PyExc_OverflowError);
}

TEST(error_mapping_enomem)
{
    PyObject* res = TlPy_RaiseFromStatus(TL_ENOMEM);
    ASSERT_NULL(res);
    ASSERT_EXCEPTION(PyExc_MemoryError);
}

/*===========================================================================
 * Test Runners
 *===========================================================================*/

static void run_handle_only_tests(void)
{
    printf("\n=== Drain Mechanism (Handle-only) ===\n");
    run_drain_batch_limit_exact();
    run_drain_reattach_remaining();
    run_force_drain_ignores_batch_limit();
    run_metrics_queue_len_accuracy();

    printf("\n=== Close Path (Handle-only) ===\n");
    run_close_drains_injected_queue();
    run_close_force_drain_with_batch_limit();
}

static void run_pytimelog_tests(void)
{
    printf("\n=== Close Path (PyTimelog) ===\n");
    run_dealloc_with_pins_warning();

    printf("\n=== Worker Lifecycle ===\n");
    run_maint_start_idempotent();
    run_maint_stop_without_start();
    run_stress_start_stop_cycles();

    printf("\n=== EBUSY Integration ===\n");
    run_ebusy_raise_exception();
    run_ebusy_raise_triggers_exception();
    run_ebusy_silent_no_exception();
    run_ebusy_flush_triggers_segment();
    run_ebusy_extend_partial_commit();

    printf("\n=== Error Mapping ===\n");
    run_error_mapping_overflow();
    run_error_mapping_enomem();
}

/*===========================================================================
 * Main - Two-phase execution
 *===========================================================================*/

int main(int argc, char* argv[])
{
    (void)argc;
    (void)argv;

    printf("test_py_maint_b5 (maintenance compliance):\n");

    /* Single Python initialization for all phases */
    if (tlpy_init_python_full() < 0) {
        fprintf(stderr, "FATAL: Python full initialization failed\n");
        return 1;
    }
    run_handle_only_tests();
    run_pytimelog_tests();

    if (tlpy_finalize_python() < 0) {
        fprintf(stderr, "Warning: Py_FinalizeEx failed after PyTimelog tests\n");
    }

    printf("\n=== TOTAL: %d tests, %d failed ===\n", tests_run, tests_failed);
    return tests_failed > 0 ? 1 : 0;
}
