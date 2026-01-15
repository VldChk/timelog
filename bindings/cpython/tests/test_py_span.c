/**
 * @file test_py_span.c
 * @brief Unit tests for PyPageSpan and related types (LLD-B4)
 *
 * TDD-driven tests for the PageSpan, PageSpanIter, and PageSpanObjectsView types.
 * Tests run with Python initialized and GIL held.
 *
 * See: docs/timelog_v1_lld_B4_pagespan_zero_copy.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_timelog.h"
#include "timelogpy/py_iter.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_span_iter.h"
#include "timelogpy/py_span_objects.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_errors.h"
#include "timelog/timelog.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*===========================================================================
 * Test Framework
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

    /* First flush to ensure records are in segments */
    if (!tl->closed && tl->tl) {
        tl_flush(tl->tl);
    }

    /* Drain any retired objects before close */
    if (!tl->closed) {
        tl_py_drain_retired(&tl->handle_ctx, 1);
    }

    /* Now close */
    if (!tl->closed && tl->tl) {
        tl_close(tl->tl);
        tl->tl = NULL;
        tl->closed = 1;
    }

    /* Final drain */
    tl_py_drain_retired(&tl->handle_ctx, 1);
    tl_py_handle_ctx_destroy(&tl->handle_ctx);

    Py_DECREF((PyObject*)tl);
}

/*===========================================================================
 * Helper: Append records and flush to create segments
 *===========================================================================*/

static int append_and_flush(PyTimelog* tl, tl_ts_t* timestamps, PyObject** objects, size_t count)
{
    for (size_t i = 0; i < count; i++) {
        Py_INCREF(objects[i]);
        tl_handle_t h = tl_py_handle_encode(objects[i]);
        tl_status_t st = tl_append(tl->tl, timestamps[i], h);
        if (st != TL_OK && st != TL_EBUSY) {
            Py_DECREF(objects[i]);
            return -1;
        }
    }

    /* Flush to create segments */
    tl_status_t st = tl_flush(tl->tl);
    if (st != TL_OK) {
        return -1;
    }

    return 0;
}

/*===========================================================================
 * Phase 1: Infrastructure Tests
 *===========================================================================*/

/**
 * Test: All three types are ready and registered.
 */
TEST(types_ready)
{
    /* Check types are ready */
    ASSERT(PyType_Ready(&PyPageSpan_Type) == 0 || PyPageSpan_Type.tp_dict != NULL);
    ASSERT(PyType_Ready(&PyPageSpanIter_Type) == 0 || PyPageSpanIter_Type.tp_dict != NULL);
    ASSERT(PyType_Ready(&PyPageSpanObjectsView_Type) == 0 || PyPageSpanObjectsView_Type.tp_dict != NULL);

    /* Check type names */
    ASSERT(strcmp(PyPageSpan_Type.tp_name, "timelog._timelog.PageSpan") == 0);
    ASSERT(strcmp(PyPageSpanIter_Type.tp_name, "timelog._timelog.PageSpanIter") == 0);
    ASSERT(strcmp(PyPageSpanObjectsView_Type.tp_name, "timelog._timelog.PageSpanObjectsView") == 0);
}

/**
 * Test: Direct instantiation is blocked.
 */
TEST(direct_instantiation_blocked)
{
    PyObject* args = PyTuple_New(0);
    ASSERT_NOT_NULL(args);

    /* PageSpan */
    PyObject* span = PyPageSpan_Type.tp_new(&PyPageSpan_Type, args, NULL);
    ASSERT_NULL(span);
    ASSERT_EXCEPTION(PyExc_TypeError);

    /* PageSpanIter */
    PyObject* iter = PyPageSpanIter_Type.tp_new(&PyPageSpanIter_Type, args, NULL);
    ASSERT_NULL(iter);
    ASSERT_EXCEPTION(PyExc_TypeError);

    /* PageSpanObjectsView */
    PyObject* view = PyPageSpanObjectsView_Type.tp_new(&PyPageSpanObjectsView_Type, args, NULL);
    ASSERT_NULL(view);
    ASSERT_EXCEPTION(PyExc_TypeError);

    Py_DECREF(args);
}

/*===========================================================================
 * Phase 3: Span Collection Tests
 *===========================================================================*/

/**
 * Test: page_spans on empty timelog returns empty iterator.
 */
TEST(page_spans_empty_timelog)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Call page_spans - should work but return empty iterator */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    /* Try to iterate - should get NULL immediately (StopIteration) */
    PyObject* span = PyIter_Next(iter);
    ASSERT_NULL(span);
    ASSERT(!PyErr_Occurred());  /* StopIteration, not error */

    Py_DECREF(iter);
    close_and_dealloc(tl);
}

/**
 * Test: page_spans with invalid kind raises ValueError.
 */
TEST(page_spans_kind_invalid)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "invalid");
    ASSERT_NULL(iter);
    ASSERT_EXCEPTION(PyExc_ValueError);

    close_and_dealloc(tl);
}

/**
 * Test: page_spans with data returns spans.
 */
TEST(page_spans_with_data)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Create test objects */
    PyObject* obj1 = PyDict_New();
    PyObject* obj2 = PyDict_New();
    PyObject* obj3 = PyDict_New();
    ASSERT_NOT_NULL(obj1);
    ASSERT_NOT_NULL(obj2);
    ASSERT_NOT_NULL(obj3);

    /* Insert records */
    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj1, obj2, obj3};

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    /* Query page_spans */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    /* Should get at least one span */
    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);
    ASSERT(PyPageSpan_Check(span));

    /* Check span properties */
    PyPageSpan* ps = (PyPageSpan*)span;
    ASSERT(!ps->closed);
    ASSERT(ps->row_end > ps->row_start);

    Py_DECREF(span);
    Py_DECREF(iter);

    Py_DECREF(obj1);
    Py_DECREF(obj2);
    Py_DECREF(obj3);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Phase 4: Buffer Protocol Tests
 *===========================================================================*/

/**
 * Test: span.timestamps returns a memoryview.
 */
TEST(timestamps_memoryview)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Create test object */
    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj, obj, obj};
    /* Need to incref for each use */
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    /* Get span */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Get timestamps property */
    PyObject* mv = PyObject_GetAttrString(span, "timestamps");
    ASSERT_NOT_NULL(mv);
    ASSERT(PyMemoryView_Check(mv));

    /* Check it's 1D */
    Py_buffer* buf = PyMemoryView_GET_BUFFER(mv);
    ASSERT_EQ(buf->ndim, 1);
    ASSERT_EQ(buf->itemsize, (Py_ssize_t)sizeof(tl_ts_t));
    ASSERT(buf->readonly);

    Py_DECREF(mv);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: buffer ndim is always 1, even under PyBUF_SIMPLE.
 */
TEST(buffer_ndim_always_one)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100};
    PyObject* objects[] = {obj};

    int rc = append_and_flush(tl, timestamps, objects, 1);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Request buffer with PyBUF_SIMPLE (no format, no shape) */
    Py_buffer view;
    int res = PyObject_GetBuffer(span, &view, PyBUF_SIMPLE);
    ASSERT_EQ(res, 0);

    /* ndim must still be 1 per CPython docs */
    ASSERT_EQ(view.ndim, 1);

    PyBuffer_Release(&view);

    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: buffer write is rejected.
 */
TEST(buffer_write_rejected)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100};
    PyObject* objects[] = {obj};

    int rc = append_and_flush(tl, timestamps, objects, 1);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Request writable buffer - should fail */
    Py_buffer view;
    int res = PyObject_GetBuffer(span, &view, PyBUF_WRITABLE);
    ASSERT(res < 0);
    ASSERT_EXCEPTION(PyExc_BufferError);

    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Phase 5: Close Semantics Tests
 *===========================================================================*/

/**
 * Test: close is idempotent.
 */
TEST(close_idempotent)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100};
    PyObject* objects[] = {obj};

    int rc = append_and_flush(tl, timestamps, objects, 1);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Close multiple times */
    PyObject* result1 = PyObject_CallMethod(span, "close", NULL);
    ASSERT_NOT_NULL(result1);
    Py_DECREF(result1);

    PyObject* result2 = PyObject_CallMethod(span, "close", NULL);
    ASSERT_NOT_NULL(result2);
    Py_DECREF(result2);

    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: close with exported buffer raises BufferError.
 */
TEST(close_with_exported_buffer_raises)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100};
    PyObject* objects[] = {obj};

    int rc = append_and_flush(tl, timestamps, objects, 1);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Get memoryview (exports buffer) */
    PyObject* mv = PyObject_GetAttrString(span, "timestamps");
    ASSERT_NOT_NULL(mv);

    /* Try to close - should fail */
    PyObject* result = PyObject_CallMethod(span, "close", NULL);
    ASSERT_NULL(result);
    ASSERT_EXCEPTION(PyExc_BufferError);

    /* Release memoryview */
    Py_DECREF(mv);

    /* Now close should work */
    result = PyObject_CallMethod(span, "close", NULL);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Phase 6: Iterator Tests
 *===========================================================================*/

/**
 * Test: Iterator exhaustion triggers cleanup.
 */
TEST(iter_exhaustion)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200};
    PyObject* objects[] = {obj, obj};
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 2);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    /* Exhaust the iterator */
    PyObject* span;
    int count = 0;
    while ((span = PyIter_Next(iter)) != NULL) {
        count++;
        Py_DECREF(span);
    }
    ASSERT(!PyErr_Occurred());  /* StopIteration, not error */
    ASSERT(count >= 1);

    /* Iterator should be marked closed after exhaustion */
    PyPageSpanIter* it = (PyPageSpanIter*)iter;
    ASSERT(it->closed);

    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: iter.close() works and is idempotent.
 */
TEST(iter_close)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100};
    PyObject* objects[] = {obj};

    int rc = append_and_flush(tl, timestamps, objects, 1);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    /* Close explicitly */
    PyObject* result = PyObject_CallMethod(iter, "close", NULL);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    /* Second close should also succeed (idempotent) */
    result = PyObject_CallMethod(iter, "close", NULL);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    /* Further iteration should return NULL */
    PyObject* span = PyIter_Next(iter);
    ASSERT_NULL(span);
    ASSERT(!PyErr_Occurred());

    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: Iterator context manager protocol.
 */
TEST(iter_context_manager)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100};
    PyObject* objects[] = {obj};

    int rc = append_and_flush(tl, timestamps, objects, 1);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    /* __enter__ returns self */
    PyObject* entered = PyObject_CallMethod(iter, "__enter__", NULL);
    ASSERT_NOT_NULL(entered);
    ASSERT(entered == iter);
    Py_DECREF(entered);

    /* __exit__ closes */
    PyObject* exit_result = PyObject_CallMethod(iter, "__exit__", "OOO", Py_None, Py_None, Py_None);
    ASSERT_NOT_NULL(exit_result);
    Py_DECREF(exit_result);

    /* Should be closed */
    PyPageSpanIter* it = (PyPageSpanIter*)iter;
    ASSERT(it->closed);

    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Phase 7: Objects View Tests
 *===========================================================================*/

/**
 * Test: objects() returns a view with correct length.
 */
TEST(objects_len)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj, obj, obj};
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Get objects view */
    PyObject* view = PyObject_CallMethod(span, "objects", NULL);
    ASSERT_NOT_NULL(view);

    /* Check length */
    Py_ssize_t len = PyObject_Length(view);
    ASSERT(len >= 1);

    Py_DECREF(view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: objects view iteration works.
 */
TEST(objects_iteration)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    /* Create distinct objects to verify we get the right ones */
    PyObject* obj1 = PyLong_FromLong(111);
    PyObject* obj2 = PyLong_FromLong(222);
    PyObject* obj3 = PyLong_FromLong(333);
    ASSERT_NOT_NULL(obj1);
    ASSERT_NOT_NULL(obj2);
    ASSERT_NOT_NULL(obj3);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj1, obj2, obj3};

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Get objects view */
    PyObject* view = PyObject_CallMethod(span, "objects", NULL);
    ASSERT_NOT_NULL(view);

    /* Iterate using Python iterator protocol */
    PyObject* view_iter = PyObject_GetIter(view);
    ASSERT_NOT_NULL(view_iter);

    int count = 0;
    PyObject* item;
    while ((item = PyIter_Next(view_iter)) != NULL) {
        ASSERT(PyLong_Check(item));
        count++;
        Py_DECREF(item);
    }
    ASSERT(!PyErr_Occurred());
    ASSERT_EQ(count, 3);

    Py_DECREF(view_iter);
    Py_DECREF(view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj1);
    Py_DECREF(obj2);
    Py_DECREF(obj3);

    close_and_dealloc(tl);
}

/**
 * Test: objects view indexing (positive, negative, out of bounds).
 */
TEST(objects_indexing)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj1 = PyLong_FromLong(111);
    PyObject* obj2 = PyLong_FromLong(222);
    PyObject* obj3 = PyLong_FromLong(333);
    ASSERT_NOT_NULL(obj1);
    ASSERT_NOT_NULL(obj2);
    ASSERT_NOT_NULL(obj3);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj1, obj2, obj3};

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    PyObject* view = PyObject_CallMethod(span, "objects", NULL);
    ASSERT_NOT_NULL(view);

    /* Positive index */
    PyObject* item0 = PySequence_GetItem(view, 0);
    ASSERT_NOT_NULL(item0);
    ASSERT_EQ(PyLong_AsLong(item0), 111);
    Py_DECREF(item0);

    PyObject* item2 = PySequence_GetItem(view, 2);
    ASSERT_NOT_NULL(item2);
    ASSERT_EQ(PyLong_AsLong(item2), 333);
    Py_DECREF(item2);

    /* Negative index */
    PyObject* item_neg1 = PySequence_GetItem(view, -1);
    ASSERT_NOT_NULL(item_neg1);
    ASSERT_EQ(PyLong_AsLong(item_neg1), 333);
    Py_DECREF(item_neg1);

    PyObject* item_neg3 = PySequence_GetItem(view, -3);
    ASSERT_NOT_NULL(item_neg3);
    ASSERT_EQ(PyLong_AsLong(item_neg3), 111);
    Py_DECREF(item_neg3);

    /* Out of bounds */
    PyObject* item_oob = PySequence_GetItem(view, 100);
    ASSERT_NULL(item_oob);
    ASSERT_EXCEPTION(PyExc_IndexError);

    PyObject* item_oob_neg = PySequence_GetItem(view, -100);
    ASSERT_NULL(item_oob_neg);
    ASSERT_EXCEPTION(PyExc_IndexError);

    Py_DECREF(view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj1);
    Py_DECREF(obj2);
    Py_DECREF(obj3);

    close_and_dealloc(tl);
}

/**
 * Test: objects view .copy() returns a list.
 */
TEST(objects_copy)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj1 = PyLong_FromLong(111);
    PyObject* obj2 = PyLong_FromLong(222);
    ASSERT_NOT_NULL(obj1);
    ASSERT_NOT_NULL(obj2);

    tl_ts_t timestamps[] = {100, 200};
    PyObject* objects[] = {obj1, obj2};

    int rc = append_and_flush(tl, timestamps, objects, 2);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    PyObject* view = PyObject_CallMethod(span, "objects", NULL);
    ASSERT_NOT_NULL(view);

    /* Call copy() */
    PyObject* copy = PyObject_CallMethod(view, "copy", NULL);
    ASSERT_NOT_NULL(copy);
    ASSERT(PyList_Check(copy));
    ASSERT_EQ(PyList_Size(copy), 2);

    /* Verify contents */
    ASSERT_EQ(PyLong_AsLong(PyList_GetItem(copy, 0)), 111);
    ASSERT_EQ(PyLong_AsLong(PyList_GetItem(copy, 1)), 222);

    Py_DECREF(copy);
    Py_DECREF(view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj1);
    Py_DECREF(obj2);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Phase 8: Lifetime Integration Tests (CRITICAL - Pin Protocol)
 *===========================================================================*/

/**
 * CRITICAL TEST: Span holds pins via pin protocol.
 *
 * While any span exists, pins should be > 0, which blocks safe close.
 * This is the core safety mechanism protecting handle references.
 */
TEST(span_holds_pins)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj, obj, obj};
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    /* Initially pins should be 0 */
    uint64_t initial_pins = tl_py_pins_count(&tl->handle_ctx);
    ASSERT_EQ(initial_pins, 0);

    /* Create span iterator and get a span */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* While span exists, pins should be > 0 */
    uint64_t pins_with_span = tl_py_pins_count(&tl->handle_ctx);
    ASSERT(pins_with_span > 0);

    /* Clean up span and iterator */
    Py_DECREF(span);
    Py_DECREF(iter);

    /* Drain to let owner destroy complete */
    tl_py_drain_retired(&tl->handle_ctx, 1);

    /* After cleanup, pins should be back to 0 */
    uint64_t final_pins = tl_py_pins_count(&tl->handle_ctx);
    ASSERT_EQ(final_pins, 0);

    Py_DECREF(obj);
    close_and_dealloc(tl);
}

/**
 * CRITICAL TEST: Closed spans release pins.
 *
 * After all spans are explicitly closed, pins should return to 0.
 */
TEST(closed_spans_release_pins)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100};
    PyObject* objects[] = {obj};

    int rc = append_and_flush(tl, timestamps, objects, 1);
    ASSERT_EQ(rc, 0);

    /* Initially pins should be 0 */
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 0);

    /* Create span */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Pins should be > 0 with active span */
    ASSERT(tl_py_pins_count(&tl->handle_ctx) > 0);

    /* Close span explicitly */
    PyObject* close_result = PyObject_CallMethod(span, "close", NULL);
    ASSERT_NOT_NULL(close_result);
    Py_DECREF(close_result);

    /* Close iterator */
    close_result = PyObject_CallMethod(iter, "close", NULL);
    ASSERT_NOT_NULL(close_result);
    Py_DECREF(close_result);

    Py_DECREF(span);
    Py_DECREF(iter);

    /* Drain retired objects */
    tl_py_drain_retired(&tl->handle_ctx, 1);

    /* After explicit close and drain, pins should be 0 */
    ASSERT_EQ(tl_py_pins_count(&tl->handle_ctx), 0);

    Py_DECREF(obj);
    close_and_dealloc(tl);
}

/**
 * CRITICAL TEST: Multiple spans share owner correctly.
 *
 * Multiple spans from same iterator share the snapshot owner.
 */
TEST(multiple_spans_share_owner)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    /* Create enough records that they might span multiple pages */
    tl_ts_t timestamps[100];
    PyObject* objects[100];
    for (int i = 0; i < 100; i++) {
        timestamps[i] = (tl_ts_t)(i * 10);
        objects[i] = obj;
        Py_INCREF(obj);
    }

    int rc = append_and_flush(tl, timestamps, objects, 100);
    ASSERT_EQ(rc, 0);

    /* Get multiple spans */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 10000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* spans[10];
    int span_count = 0;
    PyObject* span;
    while ((span = PyIter_Next(iter)) != NULL && span_count < 10) {
        spans[span_count++] = span;
    }
    ASSERT(span_count >= 1);

    /* Verify all spans have same owner (internal check) */
    if (span_count > 1) {
        PyPageSpan* ps0 = (PyPageSpan*)spans[0];
        for (int i = 1; i < span_count; i++) {
            PyPageSpan* ps = (PyPageSpan*)spans[i];
            ASSERT(ps->owner == ps0->owner);
        }
    }

    /* Clean up spans */
    for (int i = 0; i < span_count; i++) {
        Py_DECREF(spans[i]);
    }
    Py_DECREF(iter);

    /* For remaining refs from iteration */
    for (int i = 0; i < 100; i++) {
        Py_DECREF(obj);
    }

    close_and_dealloc(tl);
}

/*===========================================================================
 * Phase 9: Timestamp Correctness Tests
 *===========================================================================*/

/**
 * CRITICAL TEST: Timestamps in memoryview match appended data.
 */
TEST(timestamps_match_appended_data)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    /* Known timestamps */
    tl_ts_t expected[] = {100, 200, 300, 400, 500};
    PyObject* objects[] = {obj, obj, obj, obj, obj};
    for (int i = 0; i < 4; i++) Py_INCREF(obj);

    int rc = append_and_flush(tl, expected, objects, 5);
    ASSERT_EQ(rc, 0);

    /* Get span */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Get buffer directly */
    Py_buffer view;
    rc = PyObject_GetBuffer(span, &view, PyBUF_SIMPLE);
    ASSERT_EQ(rc, 0);

    /* Verify timestamps match */
    tl_ts_t* actual = (tl_ts_t*)view.buf;
    size_t count = view.len / sizeof(tl_ts_t);
    ASSERT_EQ(count, 5);

    for (size_t i = 0; i < count; i++) {
        ASSERT_EQ(actual[i], expected[i]);
    }

    PyBuffer_Release(&view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: Timestamps are non-decreasing within span.
 */
TEST(timestamps_sorted_within_span)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    /* Timestamps should be sorted after flush */
    tl_ts_t timestamps[] = {100, 150, 200, 250, 300};
    PyObject* objects[] = {obj, obj, obj, obj, obj};
    for (int i = 0; i < 4; i++) Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 5);
    ASSERT_EQ(rc, 0);

    /* Get span */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Verify sortedness */
    Py_buffer view;
    rc = PyObject_GetBuffer(span, &view, PyBUF_SIMPLE);
    ASSERT_EQ(rc, 0);

    tl_ts_t* ts = (tl_ts_t*)view.buf;
    size_t count = view.len / sizeof(tl_ts_t);

    for (size_t i = 1; i < count; i++) {
        ASSERT(ts[i - 1] <= ts[i]);  /* Non-decreasing */
    }

    PyBuffer_Release(&view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: Buffer length equals len(span) * sizeof(tl_ts_t).
 */
TEST(buffer_length_correct)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj, obj, obj};
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Get span length */
    Py_ssize_t span_len = PyObject_Length(span);
    ASSERT_EQ(span_len, 3);

    /* Get buffer */
    Py_buffer view;
    rc = PyObject_GetBuffer(span, &view, PyBUF_SIMPLE);
    ASSERT_EQ(rc, 0);

    /* Verify buffer length */
    ASSERT_EQ(view.len, span_len * (Py_ssize_t)sizeof(tl_ts_t));

    PyBuffer_Release(&view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: span.start_ts and span.end_ts match first/last timestamps.
 */
TEST(span_start_end_ts)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj, obj, obj};
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Get start_ts */
    PyObject* start_ts = PyObject_GetAttrString(span, "start_ts");
    ASSERT_NOT_NULL(start_ts);
    ASSERT_EQ(PyLong_AsLongLong(start_ts), 100);
    Py_DECREF(start_ts);

    /* Get end_ts */
    PyObject* end_ts = PyObject_GetAttrString(span, "end_ts");
    ASSERT_NOT_NULL(end_ts);
    ASSERT_EQ(PyLong_AsLongLong(end_ts), 300);
    Py_DECREF(end_ts);

    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: len(span) matches row_end - row_start.
 */
TEST(span_len)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300, 400};
    PyObject* objects[] = {obj, obj, obj, obj};
    Py_INCREF(obj);
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 4);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Verify __len__ */
    Py_ssize_t len = PyObject_Length(span);
    ASSERT_EQ(len, 4);

    /* Verify internal consistency */
    PyPageSpan* ps = (PyPageSpan*)span;
    ASSERT_EQ((Py_ssize_t)(ps->row_end - ps->row_start), len);

    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Phase 4b: Additional Buffer Protocol Tests
 *===========================================================================*/

/**
 * Test: Buffer format is "q" when PyBUF_FORMAT requested.
 */
TEST(buffer_format_is_q)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100};
    PyObject* objects[] = {obj};

    int rc = append_and_flush(tl, timestamps, objects, 1);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Request buffer with format */
    Py_buffer view;
    rc = PyObject_GetBuffer(span, &view, PyBUF_FORMAT);
    ASSERT_EQ(rc, 0);

    /* Format should be "q" (signed 64-bit) */
    ASSERT_NOT_NULL(view.format);
    ASSERT(strcmp(view.format, "q") == 0);

    PyBuffer_Release(&view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: Buffer itemsize is sizeof(tl_ts_t) = 8.
 */
TEST(buffer_itemsize)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100};
    PyObject* objects[] = {obj};

    int rc = append_and_flush(tl, timestamps, objects, 1);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    Py_buffer view;
    rc = PyObject_GetBuffer(span, &view, PyBUF_SIMPLE);
    ASSERT_EQ(rc, 0);

    /* itemsize should be 8 */
    ASSERT_EQ(view.itemsize, (Py_ssize_t)sizeof(tl_ts_t));
    ASSERT_EQ(view.itemsize, 8);

    PyBuffer_Release(&view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: Buffer strides are correct when PyBUF_STRIDES requested.
 */
TEST(buffer_strides)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj, obj, obj};
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Request with strides */
    Py_buffer view;
    rc = PyObject_GetBuffer(span, &view, PyBUF_STRIDES);
    ASSERT_EQ(rc, 0);

    /* strides should be set */
    ASSERT_NOT_NULL(view.strides);
    ASSERT_EQ(view.strides[0], (Py_ssize_t)sizeof(tl_ts_t));

    /* shape should also be set (STRIDES implies ND) */
    ASSERT_NOT_NULL(view.shape);
    ASSERT_EQ(view.shape[0], 3);

    PyBuffer_Release(&view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Phase 5b: Additional Close Semantics Tests
 *===========================================================================*/

/**
 * Test: Operations on closed span raise ValueError.
 */
TEST(operations_on_closed_span_raise)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100};
    PyObject* objects[] = {obj};

    int rc = append_and_flush(tl, timestamps, objects, 1);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Close the span */
    PyObject* result = PyObject_CallMethod(span, "close", NULL);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    /* Try to get timestamps - should fail */
    PyObject* mv = PyObject_GetAttrString(span, "timestamps");
    ASSERT_NULL(mv);
    ASSERT_EXCEPTION(PyExc_ValueError);

    /* Try to get objects - should fail */
    PyObject* view = PyObject_CallMethod(span, "objects", NULL);
    ASSERT_NULL(view);
    ASSERT_EXCEPTION(PyExc_ValueError);

    /* Try to get start_ts - should fail */
    PyObject* start = PyObject_GetAttrString(span, "start_ts");
    ASSERT_NULL(start);
    ASSERT_EXCEPTION(PyExc_ValueError);

    /* Try to get end_ts - should fail */
    PyObject* end = PyObject_GetAttrString(span, "end_ts");
    ASSERT_NULL(end);
    ASSERT_EXCEPTION(PyExc_ValueError);

    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: copy_timestamps() returns correct list.
 */
TEST(copy_timestamps)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj, obj, obj};
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Call copy_timestamps */
    PyObject* copy = PyObject_CallMethod(span, "copy_timestamps", NULL);
    ASSERT_NOT_NULL(copy);
    ASSERT(PyList_Check(copy));
    ASSERT_EQ(PyList_Size(copy), 3);

    /* Verify contents */
    ASSERT_EQ(PyLong_AsLongLong(PyList_GetItem(copy, 0)), 100);
    ASSERT_EQ(PyLong_AsLongLong(PyList_GetItem(copy, 1)), 200);
    ASSERT_EQ(PyLong_AsLongLong(PyList_GetItem(copy, 2)), 300);

    Py_DECREF(copy);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Phase 3b: Additional Span Collection Tests
 *===========================================================================*/

/**
 * Test: page_spans with t1 >= t2 returns empty iterator.
 */
TEST(page_spans_empty_range)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj, obj, obj};
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    /* Query with t1 >= t2 - should return empty */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 500, 100, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NULL(span);
    ASSERT(!PyErr_Occurred());

    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: page_spans with no overlap returns empty iterator.
 */
TEST(page_spans_no_overlap)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj, obj, obj};
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    /* Query range that doesn't overlap data */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 1000, 2000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NULL(span);
    ASSERT(!PyErr_Occurred());

    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/**
 * Test: Partial range overlap returns correct slice.
 */
TEST(page_spans_partial_range)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200, 300, 400, 500};
    PyObject* objects[] = {obj, obj, obj, obj, obj};
    for (int i = 0; i < 4; i++) Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 5);
    ASSERT_EQ(rc, 0);

    /* Query partial range [200, 400) */
    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 200, 400, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Get buffer and verify we got the right slice */
    Py_buffer view;
    rc = PyObject_GetBuffer(span, &view, PyBUF_SIMPLE);
    ASSERT_EQ(rc, 0);

    tl_ts_t* ts = (tl_ts_t*)view.buf;
    size_t count = view.len / sizeof(tl_ts_t);

    /* Should get timestamps 200, 300 (400 is exclusive) */
    ASSERT_EQ(count, 2);
    ASSERT_EQ(ts[0], 200);
    ASSERT_EQ(ts[1], 300);

    PyBuffer_Release(&view);
    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Phase 10: Stress Tests
 *===========================================================================*/

/**
 * Test: Many spans don't cause pin overflow or leaks.
 */
TEST(many_spans_no_leak)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    /* Create some data */
    tl_ts_t timestamps[] = {100, 200, 300};
    PyObject* objects[] = {obj, obj, obj};
    Py_INCREF(obj);
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 3);
    ASSERT_EQ(rc, 0);

    /* Create many iterators and spans */
    for (int i = 0; i < 100; i++) {
        PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
        ASSERT_NOT_NULL(iter);

        PyObject* span;
        while ((span = PyIter_Next(iter)) != NULL) {
            /* Access timestamps to ensure buffer protocol works */
            PyObject* mv = PyObject_GetAttrString(span, "timestamps");
            ASSERT_NOT_NULL(mv);
            Py_DECREF(mv);
            Py_DECREF(span);
        }

        Py_DECREF(iter);
    }

    Py_DECREF(obj);
    close_and_dealloc(tl);
}

/**
 * Test: Buffer export/release cycling doesn't cause issues.
 */
TEST(buffer_cycle_stress)
{
    PyTimelog* tl = create_timelog_default();
    ASSERT_NOT_NULL(tl);

    PyObject* obj = PyLong_FromLong(42);
    ASSERT_NOT_NULL(obj);

    tl_ts_t timestamps[] = {100, 200};
    PyObject* objects[] = {obj, obj};
    Py_INCREF(obj);

    int rc = append_and_flush(tl, timestamps, objects, 2);
    ASSERT_EQ(rc, 0);

    PyObject* iter = PyPageSpanIter_Create((PyObject*)tl, 0, 1000, "segment");
    ASSERT_NOT_NULL(iter);

    PyObject* span = PyIter_Next(iter);
    ASSERT_NOT_NULL(span);

    /* Export and release buffer many times */
    for (int i = 0; i < 100; i++) {
        Py_buffer view;
        rc = PyObject_GetBuffer(span, &view, PyBUF_SIMPLE);
        ASSERT_EQ(rc, 0);

        /* Verify data */
        tl_ts_t* ts = (tl_ts_t*)view.buf;
        ASSERT_EQ(ts[0], 100);

        PyBuffer_Release(&view);
    }

    /* Span should be closeable after all buffers released */
    PyObject* result = PyObject_CallMethod(span, "close", NULL);
    ASSERT_NOT_NULL(result);
    Py_DECREF(result);

    Py_DECREF(span);
    Py_DECREF(iter);
    Py_DECREF(obj);

    close_and_dealloc(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

int main(void)
{
    printf("Initializing Python...\n");
    tlpy_init_python();

    /* Ready types */
    if (PyType_Ready(&PyTimelog_Type) < 0) {
        fprintf(stderr, "Failed to ready PyTimelog_Type\n");
        return 1;
    }
    if (PyType_Ready(&PyTimelogIter_Type) < 0) {
        fprintf(stderr, "Failed to ready PyTimelogIter_Type\n");
        return 1;
    }
    if (PyType_Ready(&PyPageSpan_Type) < 0) {
        fprintf(stderr, "Failed to ready PyPageSpan_Type\n");
        return 1;
    }
    if (PyType_Ready(&PyPageSpanIter_Type) < 0) {
        fprintf(stderr, "Failed to ready PyPageSpanIter_Type\n");
        return 1;
    }
    if (PyType_Ready(&PyPageSpanObjectsView_Type) < 0) {
        fprintf(stderr, "Failed to ready PyPageSpanObjectsView_Type\n");
        return 1;
    }
    if (PyType_Ready(&PyPageSpanObjectsViewIter_Type) < 0) {
        fprintf(stderr, "Failed to ready PyPageSpanObjectsViewIter_Type\n");
        return 1;
    }

    /* Initialize errors module */
    PyObject* mod = PyModule_New("_timelog");
    if (!mod || TlPy_InitErrors(mod) < 0) {
        fprintf(stderr, "Failed to initialize error types\n");
        return 1;
    }
    Py_DECREF(mod);

    printf("\nRunning LLD-B4 PageSpan tests:\n\n");

    /* Phase 1: Infrastructure */
    printf("Phase 1: Infrastructure\n");
    run_types_ready();
    run_direct_instantiation_blocked();

    /* Phase 3: Span Collection */
    printf("\nPhase 3: Span Collection\n");
    run_page_spans_empty_timelog();
    run_page_spans_kind_invalid();
    run_page_spans_with_data();
    run_page_spans_empty_range();
    run_page_spans_no_overlap();
    run_page_spans_partial_range();

    /* Phase 4: Buffer Protocol */
    printf("\nPhase 4: Buffer Protocol\n");
    run_timestamps_memoryview();
    run_buffer_ndim_always_one();
    run_buffer_write_rejected();
    run_buffer_format_is_q();
    run_buffer_itemsize();
    run_buffer_strides();
    run_buffer_length_correct();

    /* Phase 5: Close Semantics */
    printf("\nPhase 5: Close Semantics\n");
    run_close_idempotent();
    run_close_with_exported_buffer_raises();
    run_operations_on_closed_span_raise();
    run_copy_timestamps();

    /* Phase 6: Iterator Tests */
    printf("\nPhase 6: Iterator Tests\n");
    run_iter_exhaustion();
    run_iter_close();
    run_iter_context_manager();

    /* Phase 7: Objects View */
    printf("\nPhase 7: Objects View\n");
    run_objects_len();
    run_objects_iteration();
    run_objects_indexing();
    run_objects_copy();

    /* Phase 8: Lifetime Integration (CRITICAL) */
    printf("\nPhase 8: Lifetime Integration (CRITICAL)\n");
    run_span_holds_pins();
    run_closed_spans_release_pins();
    run_multiple_spans_share_owner();

    /* Phase 9: Timestamp Correctness */
    printf("\nPhase 9: Timestamp Correctness\n");
    run_timestamps_match_appended_data();
    run_timestamps_sorted_within_span();
    run_span_start_end_ts();
    run_span_len();

    /* Phase 10: Stress Tests */
    printf("\nPhase 10: Stress Tests\n");
    run_many_spans_no_leak();
    run_buffer_cycle_stress();

    /* Summary */
    printf("\n=================================\n");
    printf("Tests run:    %d\n", tests_run);
    printf("Tests passed: %d\n", tests_run - tests_failed);
    printf("Tests failed: %d\n", tests_failed);
    printf("=================================\n");

    tlpy_finalize_python();

    return tests_failed > 0 ? 1 : 0;
}
