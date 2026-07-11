/**
 * @file py_iter.c
 * @brief PyTimelogIter CPython extension type implementation
 *
 * Implements snapshot-based iteration over timelog records.
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_compat.h"
#include "timelogpy/py_iter.h"
#include "timelogpy/py_errors.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_span_iter.h"
#include "timelogpy/py_timelog.h"
#include "timelog/timelog.h"

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static void pytimelogiter_cleanup(PyTimelogIter* self);

/*===========================================================================
 * Test-Only Failpoints
 *
 * These hooks are compiled only for the py_iter C test target. They allow
 * deterministic simulation of allocation failure AFTER tl_iter_next consumes
 * a row, so we can validate fail-closed iterator behavior.
 *===========================================================================*/

#ifdef TL_PY_ITER_TEST_HOOKS
volatile int tl_py_iter_fail_after_fetch_iternext = 0;
volatile int tl_py_iter_fail_after_fetch_next_batch = 0;

void tl_py_iter_test_reset_failpoints(void)
{
    tl_py_iter_fail_after_fetch_iternext = 0;
    tl_py_iter_fail_after_fetch_next_batch = 0;
}

void tl_py_iter_test_fail_iternext_once(void)
{
    tl_py_iter_fail_after_fetch_iternext = 1;
}

void tl_py_iter_test_fail_next_batch_once(void)
{
    tl_py_iter_fail_after_fetch_next_batch = 1;
}

static int tl_py_iter_test_should_fail_iternext(void)
{
    if (tl_py_iter_fail_after_fetch_iternext > 0) {
        tl_py_iter_fail_after_fetch_iternext--;
        PyErr_NoMemory();
        return 1;
    }
    return 0;
}

static int tl_py_iter_test_should_fail_next_batch(void)
{
    if (tl_py_iter_fail_after_fetch_next_batch > 0) {
        tl_py_iter_fail_after_fetch_next_batch--;
        PyErr_NoMemory();
        return 1;
    }
    return 0;
}
#else
/* Production builds pass no hook at all: pytimelogiter_step guards
 * `test_fail_hook != NULL`, so the branch folds away at compile time. */
#define tl_py_iter_test_should_fail_iternext NULL
#define tl_py_iter_test_should_fail_next_batch NULL
#endif

/*===========================================================================
 * Cleanup Routine (Single Source of Truth)
 *
 * All resource release goes through this routine:
 * - close() calls it
 * - exhaustion calls it
 * - tp_clear calls it
 * - tp_dealloc calls it
 *
 * It is idempotent (safe to call multiple times).
 *===========================================================================*/

/*
 * Detach iterator resources under the iter's critical section. If the iter
 * is already closed, returns 0 (nothing to release). Otherwise, snapshots
 * all owned resources into the out-params, NULLs the fields, sets closed=1,
 * and returns 1. Caller MUST call pytimelogiter_release_resources outside
 * the critical section with the returned values.
 *
 * Splitting cleanup this way lets iternext / next_batch hold the CS through
 * the engine call (which prevents a concurrent close from freeing self->iter
 * mid-call) while keeping the hard rule "no Py_DECREF, hook or __del__ work
 * under any internal lock" — that work runs only after the release helper
 * has been invoked outside the CS.
 */
static int pytimelogiter_detach_locked(
    PyTimelogIter* self,
    tl_iter_t** out_it,
    tl_snapshot_t** out_snap,
    tl_py_handle_ctx_t** out_handle_ctx,
    tl_py_engine_ctx_t** out_engine_ctx,
    PyObject** out_owner)
{
    if (self->closed) {
        *out_it = NULL;
        *out_snap = NULL;
        *out_handle_ctx = NULL;
        *out_engine_ctx = NULL;
        *out_owner = NULL;
        return 0;
    }
    self->closed = 1;

    *out_it = self->iter;
    self->iter = NULL;

    *out_snap = self->pinned_snapshot;
    self->pinned_snapshot = NULL;

    self->remaining_count = 0;

    *out_handle_ctx = self->handle_ctx;
    self->handle_ctx = NULL;

    *out_engine_ctx = self->engine_ctx;
    self->engine_ctx = NULL;

    *out_owner = self->owner;
    self->owner = NULL;

    return 1;
}

static void pytimelogiter_release_resources(
    tl_iter_t* it,
    tl_snapshot_t* snap,
    tl_py_handle_ctx_t* handle_ctx,
    tl_py_engine_ctx_t* engine_ctx,
    PyObject* owner)
{
    /*
     * Release order: iter/snapshot first (C only), then pins_exit/DECREF
     * (may run Python code). Preserve exception state across the latter.
     */
    if (it) {
        tl_iter_destroy(it);
    }
    if (snap) {
        tl_snapshot_release(snap);
    }

    TL_PY_PRESERVE_EXC_BEGIN;

    if (handle_ctx) {
        tl_py_pins_exit_and_maybe_drain(handle_ctx);
    }
    if (engine_ctx) {
        tl_py_engine_ctx_decref(engine_ctx);
    }
    if (handle_ctx) {
        tl_py_handle_ctx_decref(handle_ctx);
    }

    Py_XDECREF(owner);

    TL_PY_PRESERVE_EXC_END;
}

static void pytimelogiter_cleanup(PyTimelogIter* self)
{
    tl_iter_t* it = NULL;
    tl_snapshot_t* snap = NULL;
    tl_py_handle_ctx_t* handle_ctx = NULL;
    tl_py_engine_ctx_t* engine_ctx = NULL;
    PyObject* owner = NULL;
    int detached;

    TL_PY_OBJ_LOCK(self);
    detached = pytimelogiter_detach_locked(
        self, &it, &snap, &handle_ctx, &engine_ctx, &owner);
    TL_PY_OBJ_UNLOCK();

    if (detached) {
        pytimelogiter_release_resources(it, snap, handle_ctx, engine_ctx, owner);
    }
}

/*===========================================================================
 * GC Support
 *===========================================================================*/

static int PyTimelogIter_traverse(PyTimelogIter* self, visitproc visit, void* arg)
{
    Py_VISIT(Py_TYPE(self));
    Py_VISIT(self->owner);
    return 0;
}

static int PyTimelogIter_clear(PyTimelogIter* self)
{
    pytimelogiter_cleanup(self);
    return 0;
}

static void PyTimelogIter_dealloc(PyTimelogIter* self)
{
    /* pytimelogiter_cleanup is idempotent. */
    TL_PY_GC_DEALLOC(self, pytimelogiter_cleanup(self));
}

/*===========================================================================
 * Iterator Protocol
 *===========================================================================*/

/*
 * Perform one iteration step. Under the iterator's critical section, advance
 * the engine (tl_iter_next) and pin the decoded payload with a strong ref so a
 * concurrent close()+drain cannot free it before materialization; on EOF/error
 * detach the iterator's resources under the same CS. Outside the CS,
 * materialize the (timestamp, obj) 2-tuple. Holding the CS across the pure-C
 * engine call is the irreducible close-vs-next UAF guard (see py_compat.h); no
 * Python runs under it.
 *
 * Returns a new 2-tuple on success. Returns NULL with *out_stop=1 on
 * closed/EOF (StopIteration; no exception set). Returns NULL with *out_stop=0
 * on error (Python exception set) or a fired failpoint. test_fail_hook, when
 * non-NULL, is consulted once per produced record and MUST be checked here,
 * not at the call site, so it only fires on a materializing step.
 */
static PyObject* pytimelogiter_step(PyTimelogIter* self,
                                    int (*test_fail_hook)(void),
                                    int* out_stop)
{
    *out_stop = 0;

    tl_record_t rec;
    tl_status_t st = TL_EOF;
    int was_closed = 0;
    int do_release = 0;
    tl_iter_t* it = NULL;
    tl_snapshot_t* snap = NULL;
    tl_py_handle_ctx_t* handle_ctx = NULL;
    tl_py_engine_ctx_t* engine_ctx = NULL;
    PyObject* owner = NULL;
    PyObject* obj = NULL;

    TL_PY_OBJ_LOCK(self);
    if (self->closed) {
        was_closed = 1;
    } else {
        st = tl_iter_next(self->iter, &rec);
        if (st == TL_OK) {
            /* Pin the payload before releasing the CS. The CS keeps the
             * iterator's pin/snapshot alive, so the decoded object is still
             * live here; the incref makes it survive a subsequent concurrent
             * close()+drain. (Lone INCREF of a distinct object under a
             * single-object CS — permitted, see py_compat.h.) */
            obj = Py_NewRef(tl_py_handle_decode(rec.handle));
            if (self->remaining_count > 0) {
                self->remaining_count--;
            }
        } else {
            /* EOF or error — detach under CS so concurrent observers see the
             * closed transition coherently. */
            do_release = pytimelogiter_detach_locked(
                self, &it, &snap, &handle_ctx, &engine_ctx, &owner);
        }
    }
    TL_PY_OBJ_UNLOCK();

    if (was_closed) {
        *out_stop = 1;
        return NULL;  /* StopIteration */
    }

    if (st != TL_OK) {
        if (do_release) {
            pytimelogiter_release_resources(it, snap, handle_ctx, engine_ctx, owner);
        }
        if (st == TL_EOF) {
            *out_stop = 1;
            return NULL;  /* StopIteration */
        }
        return TlPy_RaiseFromObject((PyObject*)self, st);
    }

    /* obj is now an owned strong ref. Materialization (the timestamp Long +
     * the result tuple) runs OUTSIDE the CS. */
    if (test_fail_hook != NULL && test_fail_hook()) {
        Py_DECREF(obj);
        pytimelogiter_cleanup(self);
        return NULL;
    }

    PyObject* ts = PyLong_FromLongLong((long long)rec.ts);
    if (!ts) {
        Py_DECREF(obj);
        pytimelogiter_cleanup(self);
        return NULL;
    }

    PyObject* tup = PyTuple_New(2);
    if (!tup) {
        Py_DECREF(ts);
        Py_DECREF(obj);
        pytimelogiter_cleanup(self);
        return NULL;
    }

    PyTuple_SET_ITEM(tup, 0, ts);  /* steals ref */
    PyTuple_SET_ITEM(tup, 1, obj);
    return tup;
}

static PyObject* PyTimelogIter_iternext(PyTimelogIter* self)
{
    /* One step; NULL is StopIteration (stop) or a raised error / failpoint. */
    int stop = 0;
    return pytimelogiter_step(
        self, tl_py_iter_test_should_fail_iternext, &stop);
}

/*===========================================================================
 * Methods
 *===========================================================================*/

static PyObject* PyTimelogIter_close(PyTimelogIter* self, PyObject* noargs)
{
    (void)noargs;
    pytimelogiter_cleanup(self);
    Py_RETURN_NONE;
}

static PyObject* PyTimelogIter_exit(PyTimelogIter* self, PyObject* args)
{
    (void)args;
    pytimelogiter_cleanup(self);
    Py_RETURN_FALSE;  /* Don't suppress exceptions */
}

static PyObject* PyTimelogIter_next_batch(PyTimelogIter* self, PyObject* arg_n)
{
    Py_ssize_t n = PyLong_AsSsize_t(arg_n);
    if (n == -1 && PyErr_Occurred()) {
        return NULL;  /* Conversion error */
    }

    /* Negative is an error; zero returns empty list. */
    if (n < 0) {
        PyErr_SetString(PyExc_ValueError, "next_batch size must be >= 0");
        return NULL;
    }

    if (n == 0) {
        return PyList_New(0);
    }

    /* Fast-path closed check under CS so it's race-safe. */
    {
        int closed_now;
        TL_PY_OBJ_LOCK(self);
        closed_now = self->closed;
        TL_PY_OBJ_UNLOCK();
        if (closed_now) {
            return PyList_New(0);
        }
    }

    PyObject* list = PyList_New(n);
    if (!list) {
        return NULL;
    }

    Py_ssize_t i = 0;
    for (; i < n; i++) {
        int stop = 0;
        PyObject* tup = pytimelogiter_step(
            self, tl_py_iter_test_should_fail_next_batch, &stop);
        if (tup == NULL) {
            if (stop) {
                break;    /* closed/EOF: trim the list below */
            }
            goto fail;    /* error (exception set) or a fired failpoint */
        }
        PyList_SET_ITEM(list, i, tup);  /* steals ref */
    }

    /* Trim list if exhausted before n. */
    if (i < n) {
        if (PyList_SetSlice(list, i, n, NULL) < 0) {
            goto fail;
        }
    }

    return list;

fail:
    Py_DECREF(list);
    return NULL;
}

/*===========================================================================
 * Getters/Setters
 *===========================================================================*/

static Py_ssize_t PyTimelogIter_len(PyTimelogIter* self)
{
    uint64_t count;
    TL_PY_OBJ_LOCK(self);
    count = self->remaining_count;
    TL_PY_OBJ_UNLOCK();

    if (count > (uint64_t)PY_SSIZE_T_MAX) {
        PyErr_SetString(PyExc_OverflowError,
            "iterator length does not fit in Py_ssize_t");
        return -1;
    }

    return (Py_ssize_t)count;
}

TL_PY_DEFINE_CLOSED_GETTER(PyTimelogIter_get_closed, PyTimelogIter)

/*===========================================================================
 * Method/GetSet Tables
 *===========================================================================*/

static PyObject* PyTimelogIter_view(PyTimelogIter* self, PyObject* Py_UNUSED(noargs))
{
    int closed;
    PyObject* owner;
    tl_ts_t t1, t2;
    TL_PY_OBJ_LOCK(self);
    closed = self->closed;
    /* Strong ref so close cannot drop owner between snapshot and use. */
    owner = self->owner ? Py_NewRef(self->owner) : NULL;
    t1 = self->range_t1;
    t2 = self->range_t2;
    TL_PY_OBJ_UNLOCK();

    if (closed) {
        Py_XDECREF(owner);
        PyErr_SetString(PyExc_ValueError, "iterator is closed");
        return NULL;
    }
    if (!owner) {
        PyErr_SetString(PyExc_RuntimeError, "iterator owner is no longer available");
        return NULL;
    }
    PyObject* result = PyPageSpanIter_Create(owner, t1, t2, "segment");
    Py_DECREF(owner);
    return result;
}

static PyMethodDef PyTimelogIter_methods[] = {
    {"close", (PyCFunction)PyTimelogIter_close, METH_NOARGS,
     "close() -> None\n\nRelease iterator resources. Idempotent."},
    {"next_batch", (PyCFunction)PyTimelogIter_next_batch, METH_O,
     "next_batch(n) -> list[tuple[int, object]]\n\n"
     "Return up to n records. Empty list on exhaustion."},
    {"view", (PyCFunction)PyTimelogIter_view, METH_NOARGS,
     "view() -> PageSpanIter\n\nReturn a PageSpanIter for the same time range."},
    {"__enter__", (PyCFunction)tl_py_enter_self, METH_NOARGS,
     "Context manager entry."},
    {"__exit__", (PyCFunction)PyTimelogIter_exit, METH_VARARGS,
     "Context manager exit (closes iterator)."},
    {NULL, NULL, 0, NULL}
};

static PyGetSetDef PyTimelogIter_getset[] = {
    {"closed", (getter)PyTimelogIter_get_closed, NULL,
     "True if iterator is closed or exhausted.", NULL},
    {NULL, NULL, NULL, NULL, NULL}
};

/*===========================================================================
 * Type Specification
 *===========================================================================*/

static PyObject* PyTimelogIter_repr(PyTimelogIter* self)
{
    /* Notebook-grade summary (v1.3 usability lab): the range and the
     * precomputed remaining count are already on hand. */
    int closed;
    uint64_t remaining;
    tl_ts_t t1, t2;

    TL_PY_OBJ_LOCK(self);
    closed = self->closed;
    remaining = self->remaining_count;
    t1 = self->range_t1;
    t2 = self->range_t2;
    TL_PY_OBJ_UNLOCK();

    if (closed) {
        return PyUnicode_FromString("<TimelogIter closed>");
    }
    if (t2 == TL_TS_MAX) {           /* normalized unbounded upper bound */
        return PyUnicode_FromFormat(
            "<TimelogIter [%lld..) remaining=%llu>",
            (long long)t1, (unsigned long long)remaining);
    }
    return PyUnicode_FromFormat(
        "<TimelogIter [%lld..%lld) remaining=%llu>",
        (long long)t1, (long long)t2, (unsigned long long)remaining);
}

static PyType_Slot PyTimelogIter_slots[] = {
    {Py_tp_doc, PyDoc_STR(
        "Snapshot-based iterator over timelog records.\n\n"
        "Yields (timestamp, object) tuples. Cannot be instantiated directly;\n"
        "use Timelog.range(), .since(), .until(), .all() factory methods.\n\n"
        "len(iter) reports remaining visible rows in the iterator snapshot,\n"
        "not a live global timelog count."
    )},
    {Py_tp_dealloc, (void*)PyTimelogIter_dealloc},
    {Py_tp_traverse, (void*)PyTimelogIter_traverse},
    {Py_tp_clear, (void*)PyTimelogIter_clear},
    {Py_tp_repr, (void*)PyTimelogIter_repr},
    {Py_tp_iter, PyObject_SelfIter},
    {Py_tp_iternext, (void*)PyTimelogIter_iternext},
    {Py_tp_methods, PyTimelogIter_methods},
    {Py_tp_getset, PyTimelogIter_getset},
    {Py_sq_length, (void*)PyTimelogIter_len},
    {0, NULL}
};

static PyType_Spec PyTimelogIter_spec = {
    .name = "timelog._timelog.TimelogIter",
    .basicsize = sizeof(PyTimelogIter),
    .itemsize = 0,
    .flags = Py_TPFLAGS_DEFAULT |
             Py_TPFLAGS_HAVE_GC |
             Py_TPFLAGS_IMMUTABLETYPE |
             Py_TPFLAGS_DISALLOW_INSTANTIATION,
    .slots = PyTimelogIter_slots,
};

PyObject* TlPy_CreateTimelogIterType(PyObject* module)
{
    return PyType_FromModuleAndSpec(module, &PyTimelogIter_spec, NULL);
}

TL_PY_DEFINE_CHECK(TlPyTimelogIter_Check, type_timelog_iter)
