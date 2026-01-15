/**
 * @file test_py_timelog.c
 * @brief Unit tests for PyTimelog CPython extension (LLD-B2)
 *
 * TDD-driven tests for the PyTimelog wrapper type.
 * Tests run with Python initialized and GIL held.
 *
 * See: docs/engineering_plan_B2_pytimelog.md Section 2.2
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_timelog.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_errors.h"
#include "timelog/timelog.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*===========================================================================
 * Test Framework (same as test_py_handle.c)
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
 * Helper: Create a PyTimelog instance with default config
 *===========================================================================*/

static PyTimelog* create_timelog_default(void)
{
    PyObject* args = PyTuple_New(0);
    if (args == NULL) return NULL;

    PyObject* kwargs = PyDict_New();
    if (kwargs == NULL) {
        Py_DECREF(args);
        return NULL;
    }

    /* Allocate object */
    PyTimelog* self = (PyTimelog*)PyTimelog_Type.tp_alloc(&PyTimelog_Type, 0);
    if (self == NULL) {
        Py_DECREF(args);
        Py_DECREF(kwargs);
        return NULL;
    }

    /* Initialize */
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

/*===========================================================================
 * Helper: Create a PyTimelog instance with custom config
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
        PyDict_SetItemString(kwargs, "maintenance", val);
        Py_DECREF(val);
    }

    if (busy_policy != NULL) {
        PyObject* val = PyUnicode_FromString(busy_policy);
        PyDict_SetItemString(kwargs, "busy_policy", val);
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

/*===========================================================================
 * Helper: Close and deallocate PyTimelog
 *===========================================================================*/

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
 * Test Suite: Lifecycle
 *===========================================================================*/

TEST(init_defaults)
{
    /* Default config creates valid instance */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);
    ASSERT(tl->tl != NULL);
    ASSERT_EQ(tl->closed, 0);

    close_and_dealloc(tl);
}

TEST(init_custom_config)
{
    /* Create with background maintenance mode */
    PyTimelog* tl = create_timelog_custom("background", "raise");
    ASSERT_NOT_NULL(tl);
    ASSERT(tl->tl != NULL);
    ASSERT_EQ(tl->closed, 0);
    ASSERT_EQ(tl->maint_mode, TL_MAINT_BACKGROUND);
    ASSERT_EQ(tl->busy_policy, TL_PY_BUSY_RAISE);

    close_and_dealloc(tl);
}

TEST(reinit_fails)
{
    /* Re-init on open instance fails with TypeError */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* args = PyTuple_New(0);
    PyObject* kwargs = PyDict_New();

    int result = PyTimelog_Type.tp_init((PyObject*)tl, args, kwargs);
    ASSERT_EQ(result, -1);
    ASSERT_EXCEPTION(PyExc_TypeError);

    Py_DECREF(args);
    Py_DECREF(kwargs);
    close_and_dealloc(tl);
}

TEST(close_idempotent)
{
    /* Close is idempotent - can be called multiple times */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* close_method = PyObject_GetAttrString((PyObject*)tl, "close");
    ASSERT_NOT_NULL(close_method);

    /* First close */
    PyObject* result = PyObject_CallNoArgs(close_method);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    ASSERT_EQ(tl->closed, 1);
    ASSERT_NULL(tl->tl);

    /* Second close - should not crash */
    result = PyObject_CallNoArgs(close_method);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    Py_DECREF(close_method);
    Py_DECREF(tl);
}

TEST(close_sets_state)
{
    /* Close sets tl=NULL and closed=1 */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);
    ASSERT(tl->tl != NULL);
    ASSERT_EQ(tl->closed, 0);

    PyObject* close_method = PyObject_GetAttrString((PyObject*)tl, "close");
    PyObject* result = PyObject_CallNoArgs(close_method);
    Py_XDECREF(result);
    Py_DECREF(close_method);

    ASSERT_NULL(tl->tl);
    ASSERT_EQ(tl->closed, 1);

    Py_DECREF(tl);
}

TEST(close_refuses_with_pins)
{
    /* Close raises TimelogError if pins > 0 */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Simulate active snapshot by incrementing pins */
    tl_py_pins_enter(&tl->handle_ctx);
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 1);

    PyObject* close_method = PyObject_GetAttrString((PyObject*)tl, "close");
    PyObject* result = PyObject_CallNoArgs(close_method);

    /* Should fail */
    ASSERT_NULL(result);
    ASSERT_EXCEPTION(TlPy_TimelogError);

    /* Engine should still be open */
    ASSERT(tl->tl != NULL);
    ASSERT_EQ(tl->closed, 0);

    /* Release pin and close properly */
    tl_py_pins_exit_and_maybe_drain(&tl->handle_ctx);
    result = PyObject_CallNoArgs(close_method);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    Py_DECREF(close_method);
    Py_DECREF(tl);
}

TEST(dealloc_handles_unclosed)
{
    /* Dealloc on unclosed instance doesn't crash */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Don't close, just dealloc */
    Py_DECREF(tl);

    /* If we get here without crash, test passes */
}

/*===========================================================================
 * Test Suite: Append
 *===========================================================================*/

TEST(append_incref)
{
    /*
     * Append increments refcount.
     *
     * IMPORTANT: Use a dict, not a small int. Small integers (-5 to 256)
     * are immortal in Python 3.12+ and their refcount doesn't change.
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Use dict - guaranteed non-immortal, fresh object */
    PyObject* obj = PyDict_New();
    ASSERT_NOT_NULL(obj);
    Py_ssize_t initial_refcnt = Py_REFCNT(obj);
    ASSERT_EQ(initial_refcnt, 1);  /* Freshly created dict has refcnt=1 */

    /* Call append(1000, obj) */
    PyObject* append_method = PyObject_GetAttrString((PyObject*)tl, "append");
    ASSERT_NOT_NULL(append_method);

    PyObject* ts = PyLong_FromLongLong(1000);
    PyObject* args = PyTuple_Pack(2, ts, obj);
    PyObject* result = PyObject_Call(append_method, args, NULL);

    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    /* Release args tuple BEFORE checking refcount.
     * PyTuple_Pack INCREFs obj, so we must DECREF args first to get
     * the "net" refcount change from append.
     */
    Py_DECREF(args);
    Py_DECREF(ts);
    Py_DECREF(append_method);

    /* Refcount should be incremented by 1 (engine owns one ref) */
    ASSERT_EQ(Py_REFCNT(obj), initial_refcnt + 1);

    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(append_invalid_ts_type)
{
    /* Append with invalid ts type raises TypeError */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* append_method = PyObject_GetAttrString((PyObject*)tl, "append");
    PyObject* ts = PyUnicode_FromString("not_an_int");
    PyObject* obj = PyLong_FromLong(42);
    PyObject* args = PyTuple_Pack(2, ts, obj);

    PyObject* result = PyObject_Call(append_method, args, NULL);
    ASSERT_NULL(result);
    ASSERT_EXCEPTION(PyExc_TypeError);

    Py_DECREF(args);
    Py_DECREF(obj);
    Py_DECREF(ts);
    Py_DECREF(append_method);
    close_and_dealloc(tl);
}

TEST(append_after_close)
{
    /* Append after close raises TimelogError */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Close the timelog */
    PyObject* close_method = PyObject_GetAttrString((PyObject*)tl, "close");
    PyObject* close_result = PyObject_CallNoArgs(close_method);
    Py_XDECREF(close_result);
    Py_DECREF(close_method);

    /* Try to append */
    PyObject* append_method = PyObject_GetAttrString((PyObject*)tl, "append");
    PyObject* ts = PyLong_FromLongLong(1000);
    PyObject* obj = PyLong_FromLong(42);
    PyObject* args = PyTuple_Pack(2, ts, obj);

    PyObject* result = PyObject_Call(append_method, args, NULL);
    ASSERT_NULL(result);
    ASSERT_EXCEPTION(TlPy_TimelogError);

    Py_DECREF(args);
    Py_DECREF(obj);
    Py_DECREF(ts);
    Py_DECREF(append_method);
    Py_DECREF(tl);
}

/*===========================================================================
 * Test Suite: Extend
 *===========================================================================*/

TEST(extend_empty)
{
    /* Extend with empty iterable is no-op */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* extend_method = PyObject_GetAttrString((PyObject*)tl, "extend");
    PyObject* empty_list = PyList_New(0);
    PyObject* args = PyTuple_Pack(1, empty_list);

    PyObject* result = PyObject_Call(extend_method, args, NULL);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    Py_DECREF(args);
    Py_DECREF(empty_list);
    Py_DECREF(extend_method);
    close_and_dealloc(tl);
}

TEST(extend_appends_all)
{
    /* Extend appends all items */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /*
     * Use dicts, not small ints. Small integers are immortal in Python 3.12+.
     * Fresh dicts have refcnt=1.
     */
    PyObject* obj1 = PyDict_New();
    PyObject* obj2 = PyDict_New();
    PyObject* obj3 = PyDict_New();
    ASSERT_NOT_NULL(obj1);
    ASSERT_NOT_NULL(obj2);
    ASSERT_NOT_NULL(obj3);

    /* Fresh dicts start at refcnt=1 */
    ASSERT_EQ(Py_REFCNT(obj1), 1);
    ASSERT_EQ(Py_REFCNT(obj2), 1);
    ASSERT_EQ(Py_REFCNT(obj3), 1);

    /*
     * Create list of (ts, obj) tuples.
     * PyTuple_Pack increfs its arguments, so after this:
     * obj1,2,3 refcnt = 2 (our ref + tuple's ref)
     */
    PyObject* list = PyList_New(3);
    PyList_SET_ITEM(list, 0, PyTuple_Pack(2, PyLong_FromLongLong(1000), obj1));
    PyList_SET_ITEM(list, 1, PyTuple_Pack(2, PyLong_FromLongLong(2000), obj2));
    PyList_SET_ITEM(list, 2, PyTuple_Pack(2, PyLong_FromLongLong(3000), obj3));

    /* After PyTuple_Pack: our ref (1) + tuple ref (1) = 2 */
    ASSERT_EQ(Py_REFCNT(obj1), 2);
    ASSERT_EQ(Py_REFCNT(obj2), 2);
    ASSERT_EQ(Py_REFCNT(obj3), 2);

    PyObject* extend_method = PyObject_GetAttrString((PyObject*)tl, "extend");
    PyObject* args = PyTuple_Pack(1, list);

    PyObject* result = PyObject_Call(extend_method, args, NULL);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    /*
     * After extend: our ref (1) + tuple ref (1) + engine ref (1) = 3
     */
    ASSERT_EQ(Py_REFCNT(obj1), 3);
    ASSERT_EQ(Py_REFCNT(obj2), 3);
    ASSERT_EQ(Py_REFCNT(obj3), 3);

    Py_DECREF(args);
    Py_DECREF(list);  /* This decrefs tuples, which decref obj1,2,3 */
    Py_DECREF(extend_method);

    /* After list cleanup: our ref (1) + engine ref (1) = 2 */
    ASSERT_EQ(Py_REFCNT(obj1), 2);
    ASSERT_EQ(Py_REFCNT(obj2), 2);
    ASSERT_EQ(Py_REFCNT(obj3), 2);

    Py_DECREF(obj1);
    Py_DECREF(obj2);
    Py_DECREF(obj3);
    close_and_dealloc(tl);
}

/*===========================================================================
 * Test Suite: Delete
 *===========================================================================*/

TEST(delete_range_valid)
{
    /* delete_range with valid range succeeds */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "delete_range");
    PyObject* t1 = PyLong_FromLongLong(100);
    PyObject* t2 = PyLong_FromLongLong(200);
    PyObject* args = PyTuple_Pack(2, t1, t2);

    PyObject* result = PyObject_Call(method, args, NULL);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    Py_DECREF(args);
    Py_DECREF(t2);
    Py_DECREF(t1);
    Py_DECREF(method);
    close_and_dealloc(tl);
}

TEST(delete_range_t1_equal_t2)
{
    /* delete_range with t1 == t2 is allowed (empty range, no-op) */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "delete_range");
    PyObject* t1 = PyLong_FromLongLong(100);
    PyObject* t2 = PyLong_FromLongLong(100);  /* Same as t1 */
    PyObject* args = PyTuple_Pack(2, t1, t2);

    PyObject* result = PyObject_Call(method, args, NULL);
    ASSERT_NOT_NULL(result);  /* Should succeed */
    Py_DECREF(result);

    Py_DECREF(args);
    Py_DECREF(t2);
    Py_DECREF(t1);
    Py_DECREF(method);
    close_and_dealloc(tl);
}

TEST(delete_range_t1_gt_t2)
{
    /* delete_range with t1 > t2 raises ValueError */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "delete_range");
    PyObject* t1 = PyLong_FromLongLong(200);  /* Greater than t2 */
    PyObject* t2 = PyLong_FromLongLong(100);
    PyObject* args = PyTuple_Pack(2, t1, t2);

    PyObject* result = PyObject_Call(method, args, NULL);
    ASSERT_NULL(result);
    ASSERT_EXCEPTION(PyExc_ValueError);

    Py_DECREF(args);
    Py_DECREF(t2);
    Py_DECREF(t1);
    Py_DECREF(method);
    close_and_dealloc(tl);
}

TEST(delete_before_valid)
{
    /* delete_before with valid cutoff succeeds */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "delete_before");
    PyObject* cutoff = PyLong_FromLongLong(1000);
    PyObject* args = PyTuple_Pack(1, cutoff);

    PyObject* result = PyObject_Call(method, args, NULL);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    Py_DECREF(args);
    Py_DECREF(cutoff);
    Py_DECREF(method);
    close_and_dealloc(tl);
}

TEST(delete_after_close)
{
    /* delete after close raises TimelogError */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Close */
    PyObject* close_method = PyObject_GetAttrString((PyObject*)tl, "close");
    PyObject* close_result = PyObject_CallNoArgs(close_method);
    Py_XDECREF(close_result);
    Py_DECREF(close_method);

    /* Try delete_range */
    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "delete_range");
    PyObject* t1 = PyLong_FromLongLong(100);
    PyObject* t2 = PyLong_FromLongLong(200);
    PyObject* args = PyTuple_Pack(2, t1, t2);

    PyObject* result = PyObject_Call(method, args, NULL);
    ASSERT_NULL(result);
    ASSERT_EXCEPTION(TlPy_TimelogError);

    Py_DECREF(args);
    Py_DECREF(t2);
    Py_DECREF(t1);
    Py_DECREF(method);
    Py_DECREF(tl);
}

/*===========================================================================
 * Test Suite: Flush/Compact
 *===========================================================================*/

TEST(flush_succeeds)
{
    /* flush succeeds */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Append something first */
    PyObject* append_method = PyObject_GetAttrString((PyObject*)tl, "append");
    PyObject* ts = PyLong_FromLongLong(1000);
    PyObject* obj = PyLong_FromLong(42);
    PyObject* append_args = PyTuple_Pack(2, ts, obj);
    PyObject* append_result = PyObject_Call(append_method, append_args, NULL);
    Py_XDECREF(append_result);
    Py_DECREF(append_args);
    Py_DECREF(obj);
    Py_DECREF(ts);
    Py_DECREF(append_method);

    /* Flush */
    PyObject* flush_method = PyObject_GetAttrString((PyObject*)tl, "flush");
    PyObject* result = PyObject_CallNoArgs(flush_method);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);
    Py_DECREF(flush_method);

    close_and_dealloc(tl);
}

TEST(compact_succeeds)
{
    /* compact succeeds */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* compact_method = PyObject_GetAttrString((PyObject*)tl, "compact");
    PyObject* result = PyObject_CallNoArgs(compact_method);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);
    Py_DECREF(compact_method);

    close_and_dealloc(tl);
}

TEST(flush_after_close)
{
    /* flush after close raises TimelogError */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Close */
    PyObject* close_method = PyObject_GetAttrString((PyObject*)tl, "close");
    PyObject* close_result = PyObject_CallNoArgs(close_method);
    Py_XDECREF(close_result);
    Py_DECREF(close_method);

    /* Try flush */
    PyObject* flush_method = PyObject_GetAttrString((PyObject*)tl, "flush");
    PyObject* result = PyObject_CallNoArgs(flush_method);
    ASSERT_NULL(result);
    ASSERT_EXCEPTION(TlPy_TimelogError);

    Py_DECREF(flush_method);
    Py_DECREF(tl);
}

/*===========================================================================
 * Test Suite: Maintenance
 *===========================================================================*/

TEST(start_maintenance_background)
{
    /* start_maintenance in background mode succeeds */
    PyTimelog* tl = create_timelog_custom("background", "raise");
    ASSERT_NOT_NULL(tl);

    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "start_maintenance");
    PyObject* result = PyObject_CallNoArgs(method);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    /* Stop maintenance before close */
    PyObject* stop_method = PyObject_GetAttrString((PyObject*)tl, "stop_maintenance");
    PyObject* stop_result = PyObject_CallNoArgs(stop_method);
    Py_XDECREF(stop_result);
    Py_DECREF(stop_method);
    Py_DECREF(method);

    close_and_dealloc(tl);
}

TEST(start_maintenance_disabled_fails)
{
    /* start_maintenance in disabled mode raises TimelogError */
    PyTimelog* tl = create_timelog_custom("disabled", "raise");
    ASSERT_NOT_NULL(tl);

    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "start_maintenance");
    PyObject* result = PyObject_CallNoArgs(method);
    ASSERT_NULL(result);
    ASSERT_EXCEPTION(TlPy_TimelogError);

    Py_DECREF(method);
    close_and_dealloc(tl);
}

TEST(stop_maintenance_idempotent)
{
    /* stop_maintenance is idempotent */
    PyTimelog* tl = create_timelog_custom("background", "raise");
    ASSERT_NOT_NULL(tl);

    /* Start maintenance */
    PyObject* start_method = PyObject_GetAttrString((PyObject*)tl, "start_maintenance");
    PyObject* start_result = PyObject_CallNoArgs(start_method);
    Py_XDECREF(start_result);
    Py_DECREF(start_method);

    /* Stop twice */
    PyObject* stop_method = PyObject_GetAttrString((PyObject*)tl, "stop_maintenance");

    PyObject* result1 = PyObject_CallNoArgs(stop_method);
    ASSERT_NOT_NULL(result1);
    Py_DECREF(result1);

    PyObject* result2 = PyObject_CallNoArgs(stop_method);
    ASSERT_NOT_NULL(result2);
    Py_DECREF(result2);

    Py_DECREF(stop_method);
    close_and_dealloc(tl);
}

/*===========================================================================
 * Test Suite: Backpressure / Busy Policy
 *===========================================================================*/

TEST(busy_policy_silent)
{
    /* With SILENT policy, success is returned even on EBUSY */
    PyTimelog* tl = create_timelog_custom("disabled", "silent");
    ASSERT_NOT_NULL(tl);
    ASSERT_EQ(tl->busy_policy, TL_PY_BUSY_SILENT);

    close_and_dealloc(tl);
}

TEST(busy_policy_flush)
{
    /* With FLUSH policy, flush is called on EBUSY */
    PyTimelog* tl = create_timelog_custom("disabled", "flush");
    ASSERT_NOT_NULL(tl);
    ASSERT_EQ(tl->busy_policy, TL_PY_BUSY_FLUSH);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Test Suite: Context Manager
 *===========================================================================*/

TEST(context_manager_enter)
{
    /* __enter__ returns self */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* enter_method = PyObject_GetAttrString((PyObject*)tl, "__enter__");
    PyObject* result = PyObject_CallNoArgs(enter_method);
    ASSERT_NOT_NULL(result);
    ASSERT(result == (PyObject*)tl);

    Py_DECREF(result);
    Py_DECREF(enter_method);
    close_and_dealloc(tl);
}

TEST(context_manager_exit)
{
    /* __exit__ calls close */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);
    ASSERT_EQ(tl->closed, 0);

    /* Call __exit__(None, None, None) */
    PyObject* exit_method = PyObject_GetAttrString((PyObject*)tl, "__exit__");
    PyObject* args = PyTuple_Pack(3, Py_None, Py_None, Py_None);
    PyObject* result = PyObject_Call(exit_method, args, NULL);
    ASSERT_NOT_NULL(result);
    ASSERT(result == Py_False);  /* Should return False */

    ASSERT_EQ(tl->closed, 1);

    Py_DECREF(result);
    Py_DECREF(args);
    Py_DECREF(exit_method);
    Py_DECREF(tl);
}

TEST(context_manager_exit_with_exception)
{
    /* __exit__ with exception still closes */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Simulate exception context */
    PyObject* exit_method = PyObject_GetAttrString((PyObject*)tl, "__exit__");
    PyObject* exc_type = PyExc_RuntimeError;
    PyObject* exc_val = PyUnicode_FromString("test error");
    PyObject* args = PyTuple_Pack(3, exc_type, exc_val, Py_None);

    PyObject* result = PyObject_Call(exit_method, args, NULL);
    ASSERT_NOT_NULL(result);
    ASSERT(result == Py_False);  /* Don't suppress exception */

    ASSERT_EQ(tl->closed, 1);

    Py_DECREF(result);
    Py_DECREF(exc_val);
    Py_DECREF(args);
    Py_DECREF(exit_method);
    Py_DECREF(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

/* Module definition for test harness */
static struct PyModuleDef test_module_def = {
    PyModuleDef_HEAD_INIT,
    "_timelog_test",
    NULL,
    -1,
    NULL
};

int main(int argc, char* argv[])
{
    (void)argc;
    (void)argv;

    /* Initialize Python */
    tlpy_init_python();

    /* Initialize error types first */
    PyObject* module = PyModule_Create(&test_module_def);

    if (TlPy_InitErrors(module) < 0) {
        fprintf(stderr, "Failed to initialize error types\n");
        return 1;
    }

    /* Initialize PyTimelog type */
    if (PyType_Ready(&PyTimelog_Type) < 0) {
        fprintf(stderr, "Failed to initialize PyTimelog type\n");
        return 1;
    }

    printf("Running py_timelog tests...\n");

    /* Lifecycle tests */
    printf("\n[Lifecycle]\n");
    run_init_defaults();
    run_init_custom_config();
    run_reinit_fails();
    run_close_idempotent();
    run_close_sets_state();
    run_close_refuses_with_pins();
    run_dealloc_handles_unclosed();

    /* Append tests */
    printf("\n[Append]\n");
    run_append_incref();
    run_append_invalid_ts_type();
    run_append_after_close();

    /* Extend tests */
    printf("\n[Extend]\n");
    run_extend_empty();
    run_extend_appends_all();

    /* Delete tests */
    printf("\n[Delete]\n");
    run_delete_range_valid();
    run_delete_range_t1_equal_t2();
    run_delete_range_t1_gt_t2();
    run_delete_before_valid();
    run_delete_after_close();

    /* Flush/Compact tests */
    printf("\n[Flush/Compact]\n");
    run_flush_succeeds();
    run_compact_succeeds();
    run_flush_after_close();

    /* Maintenance tests */
    printf("\n[Maintenance]\n");
    run_start_maintenance_background();
    run_start_maintenance_disabled_fails();
    run_stop_maintenance_idempotent();

    /* Backpressure tests */
    printf("\n[Backpressure]\n");
    run_busy_policy_silent();
    run_busy_policy_flush();

    /* Context manager tests */
    printf("\n[Context Manager]\n");
    run_context_manager_enter();
    run_context_manager_exit();
    run_context_manager_exit_with_exception();

    printf("\n%d tests run, %d failed\n", tests_run, tests_failed);

    Py_DECREF(module);

    /* Finalize Python */
    if (tlpy_finalize_python() < 0) {
        return 2;
    }

    return tests_failed > 0 ? 1 : 0;
}
