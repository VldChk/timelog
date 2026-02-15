/**
 * @file test_py_iter.c
 * @brief Unit tests for PyTimelogIter CPython extension
 *
 * TDD-driven tests for the PyTimelogIter iterator type.
 * Tests run with Python initialized and GIL held.
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_timelog.h"
#include "timelogpy/py_iter.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_errors.h"
#include "timelog/timelog.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef TL_PY_ITER_TEST_HOOKS
/* Test-only failpoints from py_iter.c */
extern void tl_py_iter_test_reset_failpoints(void);
extern void tl_py_iter_test_fail_iternext_once(void);
extern void tl_py_iter_test_fail_next_batch_once(void);
#endif

/*===========================================================================
 * Test Framework (same as test_py_timelog.c)
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
 * Helper: Close and dealloc a PyTimelog
 *===========================================================================*/

static void close_and_dealloc(PyTimelog* tl)
{
    if (tl == NULL) return;

    /* Close if not already closed */
    if (!tl->closed && tl->tl != NULL) {
        PyObject* close_method = PyObject_GetAttrString((PyObject*)tl, "close");
        if (close_method) {
            PyObject* result = PyObject_CallNoArgs(close_method);
            Py_XDECREF(result);
            Py_DECREF(close_method);
        } else {
            PyErr_Clear();
        }
    }

    Py_DECREF(tl);
}

/*===========================================================================
 * Helper: Append a record to a timelog
 *===========================================================================*/

static int append_record(PyTimelog* tl, long long ts, PyObject* obj)
{
    PyObject* append_method = PyObject_GetAttrString((PyObject*)tl, "append");
    if (!append_method) return -1;

    PyObject* ts_py = PyLong_FromLongLong(ts);
    if (!ts_py) {
        Py_DECREF(append_method);
        return -1;
    }

    PyObject* args = PyTuple_Pack(2, ts_py, obj);
    Py_DECREF(ts_py);
    if (!args) {
        Py_DECREF(append_method);
        return -1;
    }

    PyObject* result = PyObject_Call(append_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(append_method);

    if (!result) return -1;
    Py_DECREF(result);
    return 0;
}

/*===========================================================================
 * Helper: Create range args tuple without leaking PyLong objects
 *
 * PyTuple_Pack does NOT steal references, so inline PyLong_FromLong() leaks.
 * This helper properly creates and releases the temporary PyLong objects.
 *===========================================================================*/

static PyObject* make_range_args(long t1, long t2)
{
    PyObject* arg1 = PyLong_FromLong(t1);
    if (!arg1) return NULL;

    PyObject* arg2 = PyLong_FromLong(t2);
    if (!arg2) {
        Py_DECREF(arg1);
        return NULL;
    }

    PyObject* args = PyTuple_Pack(2, arg1, arg2);
    Py_DECREF(arg1);
    Py_DECREF(arg2);
    return args;
}

/*===========================================================================
 * Test Suite: Direct Instantiation Blocked
 *===========================================================================*/

TEST(direct_instantiation_blocked)
{
    /*
     * Attempting to create TimelogIter directly via TimelogIter()
     * must raise TypeError. Iterators are only created via factory methods.
     */

    /* Get the type object from our initialized type */
    PyObject* args = PyTuple_New(0);
    ASSERT_NOT_NULL(args);

    /* Try to call TimelogIter() */
    PyObject* result = PyObject_Call((PyObject*)&PyTimelogIter_Type, args, NULL);

    /* Should fail with TypeError */
    ASSERT_NULL(result);
    ASSERT_EXCEPTION(PyExc_TypeError);

    Py_DECREF(args);
}

/*===========================================================================
 * Test Suite: Basic Iteration
 *===========================================================================*/

TEST(range_basic)
{
    /*
     * Insert 10 records at ts=0,1,2,...,9
     * Query range(3, 7) should yield ts 3,4,5,6 (4 records)
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Create 10 dict objects with unique values for tracking */
    PyObject* objs[10];
    for (int i = 0; i < 10; i++) {
        objs[i] = PyDict_New();
        ASSERT_NOT_NULL(objs[i]);
        /* Tag each dict with its index for verification */
        PyObject* idx = PyLong_FromLong(i);
        PyDict_SetItemString(objs[i], "idx", idx);
        Py_DECREF(idx);

        int rc = append_record(tl, (long long)i, objs[i]);
        ASSERT_EQ(rc, 0);
    }

    /* Get the range method */
    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    ASSERT_NOT_NULL(range_method);

    /* Call range(3, 7) */
    PyObject* t1 = PyLong_FromLong(3);
    PyObject* t2 = PyLong_FromLong(7);
    PyObject* args = PyTuple_Pack(2, t1, t2);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(t2);
    Py_DECREF(t1);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);
    ASSERT(PyTimelogIter_Check(iter));

    /* Iterate and count */
    int count = 0;
    PyObject* item;
    while ((item = PyIter_Next(iter)) != NULL) {
        /* Should be a (ts, obj) tuple */
        ASSERT(PyTuple_Check(item));
        ASSERT_EQ(PyTuple_Size(item), 2);

        PyObject* ts = PyTuple_GET_ITEM(item, 0);
        PyObject* obj = PyTuple_GET_ITEM(item, 1);

        long long ts_val = PyLong_AsLongLong(ts);
        ASSERT(ts_val >= 3 && ts_val < 7);

        /* Verify object has correct index */
        PyObject* idx_obj = PyDict_GetItemString(obj, "idx");
        ASSERT_NOT_NULL(idx_obj);
        long idx_val = PyLong_AsLong(idx_obj);
        ASSERT_EQ(idx_val, ts_val);

        Py_DECREF(item);
        count++;
    }

    /* Check for iteration error */
    if (PyErr_Occurred()) {
        PyErr_Print();
        ASSERT(0);  /* Fail */
    }

    ASSERT_EQ(count, 4);  /* ts 3,4,5,6 */

    Py_DECREF(iter);

    /* Cleanup objects */
    for (int i = 0; i < 10; i++) {
        Py_DECREF(objs[i]);
    }

    close_and_dealloc(tl);
}

TEST(empty_range)
{
    /*
     * range(100, 200) on empty timelog should yield nothing
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    ASSERT_NOT_NULL(range_method);

    PyObject* t1 = PyLong_FromLong(100);
    PyObject* t2 = PyLong_FromLong(200);
    PyObject* args = PyTuple_Pack(2, t1, t2);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(t2);
    Py_DECREF(t1);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    /* Iterate - should get nothing */
    PyObject* item = PyIter_Next(iter);
    ASSERT_NULL(item);
    ASSERT(!PyErr_Occurred());  /* StopIteration, not error */

    Py_DECREF(iter);
    close_and_dealloc(tl);
}

TEST(reversed_range_empty)
{
    /*
     * range(10, 5) should raise ValueError (t1 > t2)
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Insert some records */
    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);
    append_record(tl, 5, obj);
    append_record(tl, 10, obj);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    ASSERT_NOT_NULL(range_method);

    /* Call range(10, 5) - reversed */
    PyObject* t1 = PyLong_FromLong(10);
    PyObject* t2 = PyLong_FromLong(5);
    PyObject* args = PyTuple_Pack(2, t1, t2);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(t2);
    Py_DECREF(t1);
    Py_DECREF(range_method);

    ASSERT_NULL(iter);
    ASSERT_EXCEPTION(PyExc_ValueError);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(yield_tuple_format)
{
    /*
     * Verify each yield is (int, object) tuple
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyUnicode_FromString("test_value");
    append_record(tl, 42, obj);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* t1 = PyLong_FromLong(0);
    PyObject* t2 = PyLong_FromLong(100);
    PyObject* args = PyTuple_Pack(2, t1, t2);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(t2);
    Py_DECREF(t1);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    PyObject* item = PyIter_Next(iter);
    ASSERT_NOT_NULL(item);

    /* Check tuple format */
    ASSERT(PyTuple_Check(item));
    ASSERT_EQ(PyTuple_Size(item), 2);

    PyObject* ts = PyTuple_GET_ITEM(item, 0);
    PyObject* val = PyTuple_GET_ITEM(item, 1);

    ASSERT(PyLong_Check(ts));
    ASSERT_EQ(PyLong_AsLongLong(ts), 42);
    ASSERT(PyUnicode_Check(val));

    Py_DECREF(item);
    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(iter_on_closed_timelog)
{
    /*
     * Calling range() on closed timelog raises TimelogError
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Close the timelog */
    PyObject* close_method = PyObject_GetAttrString((PyObject*)tl, "close");
    PyObject* close_result = PyObject_CallNoArgs(close_method);
    Py_XDECREF(close_result);
    Py_DECREF(close_method);

    /* Try to get range iterator */
    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    ASSERT_NOT_NULL(range_method);

    PyObject* t1 = PyLong_FromLong(0);
    PyObject* t2 = PyLong_FromLong(100);
    PyObject* args = PyTuple_Pack(2, t1, t2);
    PyObject* iter = PyObject_Call(range_method, args, NULL);

    ASSERT_NULL(iter);
    ASSERT_EXCEPTION(TlPy_TimelogError);

    Py_DECREF(args);
    Py_DECREF(t2);
    Py_DECREF(t1);
    Py_DECREF(range_method);
    Py_DECREF(tl);
}

/*===========================================================================
 * Test Suite: Factory Methods
 *===========================================================================*/

TEST(since_basic)
{
    /*
     * since(5) yields all records with ts >= 5
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Insert records at ts 0..9 */
    PyObject* obj = PyDict_New();
    for (int i = 0; i < 10; i++) {
        append_record(tl, i, obj);
    }

    /* since(5) should yield ts 5,6,7,8,9 */
    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "since");
    ASSERT_NOT_NULL(method);

    PyObject* t = PyLong_FromLong(5);
    PyObject* args = PyTuple_Pack(1, t);
    PyObject* iter = PyObject_Call(method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(t);
    Py_DECREF(method);

    ASSERT_NOT_NULL(iter);

    int count = 0;
    PyObject* item;
    while ((item = PyIter_Next(iter)) != NULL) {
        PyObject* ts = PyTuple_GET_ITEM(item, 0);
        long long ts_val = PyLong_AsLongLong(ts);
        ASSERT(ts_val >= 5);
        Py_DECREF(item);
        count++;
    }
    ASSERT(!PyErr_Occurred());
    ASSERT_EQ(count, 5);  /* 5,6,7,8,9 */

    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(until_basic)
{
    /*
     * until(5) yields all records with ts < 5
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Insert records at ts 0..9 */
    PyObject* obj = PyDict_New();
    for (int i = 0; i < 10; i++) {
        append_record(tl, i, obj);
    }

    /* until(5) should yield ts 0,1,2,3,4 */
    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "until");
    ASSERT_NOT_NULL(method);

    PyObject* t = PyLong_FromLong(5);
    PyObject* args = PyTuple_Pack(1, t);
    PyObject* iter = PyObject_Call(method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(t);
    Py_DECREF(method);

    ASSERT_NOT_NULL(iter);

    int count = 0;
    PyObject* item;
    while ((item = PyIter_Next(iter)) != NULL) {
        PyObject* ts = PyTuple_GET_ITEM(item, 0);
        long long ts_val = PyLong_AsLongLong(ts);
        ASSERT(ts_val < 5);
        Py_DECREF(item);
        count++;
    }
    ASSERT(!PyErr_Occurred());
    ASSERT_EQ(count, 5);  /* 0,1,2,3,4 */

    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(all_basic)
{
    /*
     * all() yields all records
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Insert records at ts 0..9 */
    PyObject* obj = PyDict_New();
    for (int i = 0; i < 10; i++) {
        append_record(tl, i, obj);
    }

    /* all() should yield all 10 records */
    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "all");
    ASSERT_NOT_NULL(method);

    PyObject* iter = PyObject_CallNoArgs(method);
    Py_DECREF(method);

    ASSERT_NOT_NULL(iter);

    int count = 0;
    PyObject* item;
    while ((item = PyIter_Next(iter)) != NULL) {
        Py_DECREF(item);
        count++;
    }
    ASSERT(!PyErr_Occurred());
    ASSERT_EQ(count, 10);

    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(equal_basic)
{
    /*
     * equal(5) yields all records with ts == 5
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Insert multiple records at ts 5 */
    PyObject* obj1 = PyDict_New();
    PyObject* obj2 = PyDict_New();
    PyObject* obj3 = PyDict_New();
    append_record(tl, 1, obj1);
    append_record(tl, 5, obj1);
    append_record(tl, 5, obj2);
    append_record(tl, 5, obj3);
    append_record(tl, 10, obj1);

    /* equal(5) should yield 3 records */
    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "equal");
    ASSERT_NOT_NULL(method);

    PyObject* t = PyLong_FromLong(5);
    PyObject* args = PyTuple_Pack(1, t);
    PyObject* iter = PyObject_Call(method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(t);
    Py_DECREF(method);

    ASSERT_NOT_NULL(iter);

    int count = 0;
    PyObject* item;
    while ((item = PyIter_Next(iter)) != NULL) {
        PyObject* ts = PyTuple_GET_ITEM(item, 0);
        long long ts_val = PyLong_AsLongLong(ts);
        ASSERT_EQ(ts_val, 5);
        Py_DECREF(item);
        count++;
    }
    ASSERT(!PyErr_Occurred());
    ASSERT_EQ(count, 3);

    Py_DECREF(iter);
    Py_DECREF(obj1);
    Py_DECREF(obj2);
    Py_DECREF(obj3);
    close_and_dealloc(tl);
}

TEST(point_basic)
{
    /*
     * point(5) is same as equal(5) - yields records at exact timestamp
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);
    append_record(tl, 5, obj);
    append_record(tl, 10, obj);

    PyObject* method = PyObject_GetAttrString((PyObject*)tl, "point");
    ASSERT_NOT_NULL(method);

    PyObject* t = PyLong_FromLong(5);
    PyObject* args = PyTuple_Pack(1, t);
    PyObject* iter = PyObject_Call(method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(t);
    Py_DECREF(method);

    ASSERT_NOT_NULL(iter);

    int count = 0;
    PyObject* item;
    while ((item = PyIter_Next(iter)) != NULL) {
        PyObject* ts = PyTuple_GET_ITEM(item, 0);
        long long ts_val = PyLong_AsLongLong(ts);
        ASSERT_EQ(ts_val, 5);
        Py_DECREF(item);
        count++;
    }
    ASSERT(!PyErr_Occurred());
    ASSERT_EQ(count, 1);

    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

/*===========================================================================
 * Test Suite: Iterator Close & Cleanup
 *===========================================================================*/

TEST(close_drops_pin)
{
    /*
     * Creating iterator increments pins, close() decrements pins
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Initial pins should be 0 */
    uint64_t initial_pins = tl_py_pins_count(&tl->handle_ctx);
    ASSERT_EQ(initial_pins, 0);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);

    /* Create iterator - pins should be 1 */
    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);
    uint64_t pins_with_iter = tl_py_pins_count(&tl->handle_ctx);
    ASSERT_EQ(pins_with_iter, 1);

    /* Close iterator - pins should be 0 */
    PyObject* close_method = PyObject_GetAttrString(iter, "close");
    PyObject* close_result = PyObject_CallNoArgs(close_method);
    Py_XDECREF(close_result);
    Py_DECREF(close_method);

    uint64_t pins_after_close = tl_py_pins_count(&tl->handle_ctx);
    ASSERT_EQ(pins_after_close, 0);

    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(close_is_idempotent)
{
    /*
     * Calling close() twice should not crash or corrupt state
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    /* Close twice */
    PyObject* close_method = PyObject_GetAttrString(iter, "close");
    PyObject* result1 = PyObject_CallNoArgs(close_method);
    ASSERT_NOT_NULL(result1);
    Py_DECREF(result1);

    PyObject* result2 = PyObject_CallNoArgs(close_method);
    ASSERT_NOT_NULL(result2);
    Py_DECREF(result2);

    Py_DECREF(close_method);
    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(next_after_close)
{
    /*
     * __next__ after close() should return NULL (StopIteration)
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    /* Close the iterator */
    PyObject* close_method = PyObject_GetAttrString(iter, "close");
    PyObject* close_result = PyObject_CallNoArgs(close_method);
    Py_XDECREF(close_result);
    Py_DECREF(close_method);

    /* __next__ should return NULL (StopIteration, not error) */
    PyObject* item = PyIter_Next(iter);
    ASSERT_NULL(item);
    ASSERT(!PyErr_Occurred());  /* StopIteration, not RuntimeError */

    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(closed_property)
{
    /*
     * .closed property reflects iterator state
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    /* Initially not closed */
    PyObject* closed = PyObject_GetAttrString(iter, "closed");
    ASSERT(closed == Py_False);
    Py_DECREF(closed);

    /* Close it */
    PyObject* close_method = PyObject_GetAttrString(iter, "close");
    PyObject* close_result = PyObject_CallNoArgs(close_method);
    Py_XDECREF(close_result);
    Py_DECREF(close_method);

    /* Now closed */
    closed = PyObject_GetAttrString(iter, "closed");
    ASSERT(closed == Py_True);
    Py_DECREF(closed);

    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(exhaust_clears_resources)
{
    /*
     * After full iteration, pins should be 0
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    for (int i = 0; i < 5; i++) {
        append_record(tl, i, obj);
    }

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 1);

    /* Exhaust the iterator */
    PyObject* item;
    while ((item = PyIter_Next(iter)) != NULL) {
        Py_DECREF(item);
    }

    /* After exhaustion, pins should be 0 */
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 0);

    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

/*===========================================================================
 * Test Suite: Multiple Concurrent Iterators
 *===========================================================================*/

TEST(two_iterators_two_pins)
{
    /*
     * Two active iterators on same timelog should have pins == 2
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);
    append_record(tl, 2, obj);

    /* Initial pins: 0 */
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 0);

    /* Create first iterator */
    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args1 = make_range_args(0, 100);
    PyObject* iter1 = PyObject_Call(range_method, args1, NULL);
    Py_DECREF(args1);
    ASSERT_NOT_NULL(iter1);
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 1);

    /* Create second iterator */
    PyObject* args2 = make_range_args(0, 100);
    PyObject* iter2 = PyObject_Call(range_method, args2, NULL);
    Py_DECREF(args2);
    Py_DECREF(range_method);
    ASSERT_NOT_NULL(iter2);
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 2);

    /* Both iterators work */
    PyObject* item1 = PyIter_Next(iter1);
    ASSERT_NOT_NULL(item1);
    Py_DECREF(item1);

    PyObject* item2 = PyIter_Next(iter2);
    ASSERT_NOT_NULL(item2);
    Py_DECREF(item2);

    /* Cleanup */
    Py_DECREF(iter1);
    Py_DECREF(iter2);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(close_one_keeps_other)
{
    /*
     * Closing one iterator should leave other iterator functional
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);
    append_record(tl, 2, obj);

    /* Create two iterators */
    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args1 = make_range_args(0, 100);
    PyObject* iter1 = PyObject_Call(range_method, args1, NULL);
    Py_DECREF(args1);
    ASSERT_NOT_NULL(iter1);

    PyObject* args2 = make_range_args(0, 100);
    PyObject* iter2 = PyObject_Call(range_method, args2, NULL);
    Py_DECREF(args2);
    Py_DECREF(range_method);
    ASSERT_NOT_NULL(iter2);

    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 2);

    /* Close iter1 */
    PyObject* close_method = PyObject_GetAttrString(iter1, "close");
    PyObject* close_result = PyObject_CallNoArgs(close_method);
    Py_XDECREF(close_result);
    Py_DECREF(close_method);

    /* Pins drops to 1 */
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 1);

    /* iter2 still works */
    int count = 0;
    PyObject* item;
    while ((item = PyIter_Next(iter2)) != NULL) {
        Py_DECREF(item);
        count++;
    }
    ASSERT_EQ(count, 2);

    /* Now pins is 0 (iter2 exhausted) */
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 0);

    Py_DECREF(iter1);
    Py_DECREF(iter2);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(snapshot_boundary)
{
    /*
     * Snapshot isolation: iter A created, append new record, iter B created
     * A doesn't see new record, B does see it
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);  /* Initial record */

    /* Create iter A (sees 1 record) */
    PyObject* all_method = PyObject_GetAttrString((PyObject*)tl, "all");
    PyObject* iter_a = PyObject_CallNoArgs(all_method);
    ASSERT_NOT_NULL(iter_a);

    /* Append new record AFTER iter A was created */
    append_record(tl, 2, obj);

    /* Create iter B (should see 2 records) */
    PyObject* iter_b = PyObject_CallNoArgs(all_method);
    Py_DECREF(all_method);
    ASSERT_NOT_NULL(iter_b);

    /* Drain iter A - should see only 1 record */
    int count_a = 0;
    PyObject* item;
    while ((item = PyIter_Next(iter_a)) != NULL) {
        Py_DECREF(item);
        count_a++;
    }
    ASSERT_EQ(count_a, 1);  /* A doesn't see new record */

    /* Drain iter B - should see 2 records */
    int count_b = 0;
    while ((item = PyIter_Next(iter_b)) != NULL) {
        Py_DECREF(item);
        count_b++;
    }
    ASSERT_EQ(count_b, 2);  /* B sees new record */

    Py_DECREF(iter_a);
    Py_DECREF(iter_b);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(close_timelog_with_live_iterator)
{
    /*
     * Integration test: Timelog.close() must raise TimelogError
     * when there's an active iterator (real iterator, not simulated pins).
     *
     * This tests the full integration path, not just pin manipulation.
     * Note: TL_ESTATE (state error) maps to TimelogError.
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);
    append_record(tl, 2, obj);

    /* Create iterator - this pins the handle context */
    PyObject* all_method = PyObject_GetAttrString((PyObject*)tl, "all");
    PyObject* iter = PyObject_CallNoArgs(all_method);
    Py_DECREF(all_method);
    ASSERT_NOT_NULL(iter);

    /* Verify pins are active */
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 1);

    /* Attempt to close Timelog - should fail with TimelogError */
    PyObject* close_method = PyObject_GetAttrString((PyObject*)tl, "close");
    PyObject* close_result = PyObject_CallNoArgs(close_method);
    ASSERT_NULL(close_result);
    ASSERT_EXCEPTION(TlPy_TimelogError);

    /* Timelog should still be open */
    ASSERT(!tl->closed);
    ASSERT(tl->tl != NULL);

    /* Close iterator - this releases the pin */
    PyObject* iter_close = PyObject_GetAttrString(iter, "close");
    PyObject* iter_close_result = PyObject_CallNoArgs(iter_close);
    Py_XDECREF(iter_close_result);
    Py_DECREF(iter_close);

    /* Now Timelog.close() should succeed */
    close_result = PyObject_CallNoArgs(close_method);
    ASSERT_NOT_NULL(close_result);
    Py_DECREF(close_result);

    Py_DECREF(close_method);
    Py_DECREF(iter);
    Py_DECREF(obj);
    Py_DECREF(tl);
}

/*===========================================================================
 * Test Suite: Context Manager
 *===========================================================================*/

TEST(context_manager_normal)
{
    /*
     * Iterator works as context manager
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);
    append_record(tl, 2, obj);
    append_record(tl, 3, obj);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    /* __enter__ returns self */
    PyObject* enter_method = PyObject_GetAttrString(iter, "__enter__");
    PyObject* enter_result = PyObject_CallNoArgs(enter_method);
    ASSERT(enter_result == iter);
    Py_DECREF(enter_result);
    Py_DECREF(enter_method);

    /* Iterate */
    int count = 0;
    PyObject* item;
    while ((item = PyIter_Next(iter)) != NULL) {
        Py_DECREF(item);
        count++;
    }
    ASSERT_EQ(count, 3);

    /* __exit__ closes iterator */
    PyObject* exit_method = PyObject_GetAttrString(iter, "__exit__");
    PyObject* exit_args = PyTuple_Pack(3, Py_None, Py_None, Py_None);
    PyObject* exit_result = PyObject_Call(exit_method, exit_args, NULL);
    ASSERT(exit_result == Py_False);  /* Don't suppress exceptions */
    Py_DECREF(exit_result);
    Py_DECREF(exit_args);
    Py_DECREF(exit_method);

    /* Iterator should now be closed */
    PyObject* closed = PyObject_GetAttrString(iter, "closed");
    ASSERT(closed == Py_True);
    Py_DECREF(closed);

    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

/*===========================================================================
 * Test Suite: next_batch
 *===========================================================================*/

TEST(next_batch_full)
{
    /*
     * next_batch(5) returns 5 items when available
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    for (int i = 0; i < 10; i++) {
        append_record(tl, i, obj);
    }

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    /* next_batch(5) */
    PyObject* batch_method = PyObject_GetAttrString(iter, "next_batch");
    PyObject* n = PyLong_FromLong(5);
    PyObject* batch = PyObject_CallOneArg(batch_method, n);
    Py_DECREF(n);
    Py_DECREF(batch_method);

    ASSERT_NOT_NULL(batch);
    ASSERT(PyList_Check(batch));
    ASSERT_EQ(PyList_Size(batch), 5);

    /* Each item is (ts, obj) tuple */
    for (Py_ssize_t i = 0; i < 5; i++) {
        PyObject* item = PyList_GET_ITEM(batch, i);
        ASSERT(PyTuple_Check(item));
        ASSERT_EQ(PyTuple_Size(item), 2);
    }

    Py_DECREF(batch);
    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(next_batch_partial)
{
    /*
     * next_batch(100) on 3 items returns 3
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);
    append_record(tl, 2, obj);
    append_record(tl, 3, obj);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    /* next_batch(100) */
    PyObject* batch_method = PyObject_GetAttrString(iter, "next_batch");
    PyObject* n = PyLong_FromLong(100);
    PyObject* batch = PyObject_CallOneArg(batch_method, n);
    Py_DECREF(n);
    Py_DECREF(batch_method);

    ASSERT_NOT_NULL(batch);
    ASSERT_EQ(PyList_Size(batch), 3);  /* Only 3 available */

    Py_DECREF(batch);
    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(next_batch_zero)
{
    /*
     * next_batch(0) returns empty list
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    /* next_batch(0) */
    PyObject* batch_method = PyObject_GetAttrString(iter, "next_batch");
    PyObject* n = PyLong_FromLong(0);
    PyObject* batch = PyObject_CallOneArg(batch_method, n);
    Py_DECREF(n);
    Py_DECREF(batch_method);

    ASSERT_NOT_NULL(batch);
    ASSERT_EQ(PyList_Size(batch), 0);

    Py_DECREF(batch);
    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(next_batch_negative)
{
    /*
     * next_batch(-1) raises ValueError
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    /* next_batch(-1) should raise ValueError */
    PyObject* batch_method = PyObject_GetAttrString(iter, "next_batch");
    PyObject* n = PyLong_FromLong(-1);
    PyObject* batch = PyObject_CallOneArg(batch_method, n);
    Py_DECREF(n);
    Py_DECREF(batch_method);

    ASSERT_NULL(batch);
    ASSERT_EXCEPTION(PyExc_ValueError);

    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(next_batch_closed)
{
    /*
     * next_batch on closed iterator returns empty list
     */
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    append_record(tl, 1, obj);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);

    ASSERT_NOT_NULL(iter);

    /* Close iterator */
    PyObject* close_method = PyObject_GetAttrString(iter, "close");
    PyObject* close_result = PyObject_CallNoArgs(close_method);
    Py_XDECREF(close_result);
    Py_DECREF(close_method);

    /* next_batch on closed iter */
    PyObject* batch_method = PyObject_GetAttrString(iter, "next_batch");
    PyObject* n = PyLong_FromLong(10);
    PyObject* batch = PyObject_CallOneArg(batch_method, n);
    Py_DECREF(n);
    Py_DECREF(batch_method);

    ASSERT_NOT_NULL(batch);
    ASSERT_EQ(PyList_Size(batch), 0);  /* Empty, not error */

    Py_DECREF(batch);
    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
}

TEST(iternext_alloc_failure_is_fail_closed)
{
#ifdef TL_PY_ITER_TEST_HOOKS
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    ASSERT_NOT_NULL(obj);
    ASSERT_EQ(append_record(tl, 1, obj), 0);
    ASSERT_EQ(append_record(tl, 2, obj), 0);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);
    ASSERT_NOT_NULL(iter);

    ASSERT_EQ(PyObject_Length(iter), 2);

    tl_py_iter_test_reset_failpoints();
    tl_py_iter_test_fail_iternext_once();

    PyObject* item = PyIter_Next(iter);
    ASSERT_NULL(item);
    ASSERT_EXCEPTION(PyExc_MemoryError);

    PyObject* closed = PyObject_GetAttrString(iter, "closed");
    ASSERT_NOT_NULL(closed);
    ASSERT(closed == Py_True);
    Py_DECREF(closed);

    ASSERT_EQ(PyObject_Length(iter), 0);

    /* Closed iterator: stop iteration, no error. */
    item = PyIter_Next(iter);
    ASSERT_NULL(item);
    ASSERT(!PyErr_Occurred());

    tl_py_iter_test_reset_failpoints();
    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
#else
    ASSERT(0);
#endif
}

TEST(next_batch_alloc_failure_is_fail_closed)
{
#ifdef TL_PY_ITER_TEST_HOOKS
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyDict_New();
    ASSERT_NOT_NULL(obj);
    ASSERT_EQ(append_record(tl, 1, obj), 0);
    ASSERT_EQ(append_record(tl, 2, obj), 0);
    ASSERT_EQ(append_record(tl, 3, obj), 0);

    PyObject* range_method = PyObject_GetAttrString((PyObject*)tl, "range");
    PyObject* args = make_range_args(0, 100);
    PyObject* iter = PyObject_Call(range_method, args, NULL);
    Py_DECREF(args);
    Py_DECREF(range_method);
    ASSERT_NOT_NULL(iter);

    ASSERT_EQ(PyObject_Length(iter), 3);

    tl_py_iter_test_reset_failpoints();
    tl_py_iter_test_fail_next_batch_once();

    PyObject* batch_method = PyObject_GetAttrString(iter, "next_batch");
    ASSERT_NOT_NULL(batch_method);
    PyObject* n = PyLong_FromLong(2);
    ASSERT_NOT_NULL(n);
    PyObject* batch = PyObject_CallOneArg(batch_method, n);
    Py_DECREF(n);
    ASSERT_NULL(batch);
    ASSERT_EXCEPTION(PyExc_MemoryError);

    PyObject* closed = PyObject_GetAttrString(iter, "closed");
    ASSERT_NOT_NULL(closed);
    ASSERT(closed == Py_True);
    Py_DECREF(closed);

    ASSERT_EQ(PyObject_Length(iter), 0);

    /* Closed iterator returns empty batch. */
    n = PyLong_FromLong(5);
    ASSERT_NOT_NULL(n);
    batch = PyObject_CallOneArg(batch_method, n);
    Py_DECREF(n);
    ASSERT_NOT_NULL(batch);
    ASSERT(PyList_Check(batch));
    ASSERT_EQ(PyList_Size(batch), 0);

    tl_py_iter_test_reset_failpoints();
    Py_DECREF(batch);
    Py_DECREF(batch_method);
    Py_DECREF(iter);
    Py_DECREF(obj);
    close_and_dealloc(tl);
#else
    ASSERT(0);
#endif
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

/* Module definition for test harness */
static struct PyModuleDef test_module_def = {
    PyModuleDef_HEAD_INIT,
    "_timelog_iter_test",
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

    /* Initialize PyTimelogIter type */
    if (PyType_Ready(&PyTimelogIter_Type) < 0) {
        fprintf(stderr, "Failed to initialize PyTimelogIter type\n");
        return 1;
    }

    printf("Running py_iter tests...\n");

    /* Direct Instantiation Blocked */
    printf("\n[Direct Instantiation Blocked]\n");
    run_direct_instantiation_blocked();

    /* Basic Iteration */
    printf("\n[Basic Iteration]\n");
    run_range_basic();
    run_empty_range();
    run_reversed_range_empty();
    run_yield_tuple_format();
    run_iter_on_closed_timelog();

    /* Factory Methods */
    printf("\n[Factory Methods]\n");
    run_since_basic();
    run_until_basic();
    run_all_basic();
    run_equal_basic();
    run_point_basic();

    /* Close & Cleanup */
    printf("\n[Close & Cleanup]\n");
    run_close_drops_pin();
    run_close_is_idempotent();
    run_next_after_close();
    run_closed_property();
    run_exhaust_clears_resources();

    /* Multiple Concurrent Iterators */
    printf("\n[Multiple Concurrent Iterators]\n");
    run_two_iterators_two_pins();
    run_close_one_keeps_other();
    run_snapshot_boundary();
    run_close_timelog_with_live_iterator();

    /* Context Manager */
    printf("\n[Context Manager]\n");
    run_context_manager_normal();

    /* next_batch */
    printf("\n[next_batch]\n");
    run_next_batch_full();
    run_next_batch_partial();
    run_next_batch_zero();
    run_next_batch_negative();
    run_next_batch_closed();
    run_iternext_alloc_failure_is_fail_closed();
    run_next_batch_alloc_failure_is_fail_closed();

    printf("\n%d tests run, %d failed\n", tests_run, tests_failed);

    Py_DECREF(module);

    /* Finalize Python */
    if (tlpy_finalize_python() < 0) {
        return 2;
    }

    return tests_failed > 0 ? 1 : 0;
}
