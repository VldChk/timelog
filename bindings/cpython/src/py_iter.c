/**
 * @file py_iter.c
 * @brief PyTimelogIter CPython extension type implementation
 *
 * Implements snapshot-based iteration over timelog records.
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <stdio.h>

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
static int tl_py_iter_test_should_fail_iternext(void)
{
    return 0;
}

static int tl_py_iter_test_should_fail_next_batch(void)
{
    return 0;
}
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

static void pytimelogiter_cleanup(PyTimelogIter* self)
{
    fprintf(stderr, "pytimelogiter_cleanup: self=%p closed=%d engine_ctx=%p\n",
            (void*)self, (int)self->closed, (void*)self->engine_ctx);
    if (self->closed) {
        return;  /* Already cleaned up */
    }
    self->closed = 1;

    /* Clear pointers before Py_DECREF to prevent reentrancy via __del__. */
    tl_iter_t* it = self->iter;
    self->iter = NULL;

    tl_snapshot_t* snap = self->pinned_snapshot;
    self->pinned_snapshot = NULL;

    self->remaining_count = 0;

    tl_py_handle_ctx_t* ctx = self->handle_ctx;
    /* handle_ctx is borrowed; keep for pin exit below */

    tl_py_engine_ctx_t* engine_ctx = self->engine_ctx;
    self->engine_ctx = NULL;

    PyObject* owner = self->owner;
    self->owner = NULL;

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

    /* Preserve exception state across Py_DECREF / drain. */
    PyObject *exc_type, *exc_value, *exc_tb;
    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);

    if (ctx) {
        tl_py_pins_exit_and_maybe_drain(ctx);
    }

    if (engine_ctx) {
        tl_py_engine_ctx_decref(engine_ctx);
    }

    if (ctx) {
        tl_py_handle_ctx_decref(ctx);
    }

    Py_XDECREF(owner);

    PyErr_Restore(exc_type, exc_value, exc_tb);
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
    fprintf(stderr, "PyTimelogIter_clear: self=%p\n", (void*)self);
    pytimelogiter_cleanup(self);
    return 0;
}

static void PyTimelogIter_dealloc(PyTimelogIter* self)
{
    fprintf(stderr, "PyTimelogIter_dealloc: self=%p\n", (void*)self);
    PyTypeObject* tp = Py_TYPE(self);
    PyObject_GC_UnTrack(self);
    pytimelogiter_cleanup(self);  /* Idempotent */
    tp->tp_free((PyObject*)self);
    Py_DECREF(tp);
}

/*===========================================================================
 * Iterator Protocol
 *===========================================================================*/

static PyObject* PyTimelogIter_iternext(PyTimelogIter* self)
{
    /* NULL without exception signals StopIteration (CPython convention). */
    if (self->closed) {
        return NULL;
    }

    tl_record_t rec;
    tl_status_t st = tl_iter_next(self->iter, &rec);

    if (st == TL_OK) {
        /* Fail closed on materialization error to avoid silent row loss. */
        if (tl_py_iter_test_should_fail_iternext()) {
            pytimelogiter_cleanup(self);
            return NULL;
        }

        PyObject* obj = Py_NewRef(tl_py_handle_decode(rec.handle));

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

        if (self->remaining_valid && self->remaining_count > 0) {
            self->remaining_count--;
        }

        return tup;
    }

    if (st == TL_EOF) {
        pytimelogiter_cleanup(self);
        return NULL;  /* StopIteration */
    }

    /* Error path - cleanup and raise */
    pytimelogiter_cleanup(self);
    return TlPy_RaiseFromObject((PyObject*)self, st);
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

static PyObject* PyTimelogIter_enter(PyTimelogIter* self, PyObject* noargs)
{
    (void)noargs;
    return Py_NewRef((PyObject*)self);
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

    if (n == 0 || self->closed) {
        return PyList_New(0);
    }

    PyObject* list = PyList_New(n);
    if (!list) {
        return NULL;
    }

    Py_ssize_t i = 0;
    for (; i < n; i++) {
        tl_record_t rec;
        tl_status_t st = tl_iter_next(self->iter, &rec);

        if (st == TL_OK) {
            /* Fail closed on materialization error to avoid silent row loss. */
            if (tl_py_iter_test_should_fail_next_batch()) {
                pytimelogiter_cleanup(self);
                goto fail;
            }

            PyObject* obj = Py_NewRef(tl_py_handle_decode(rec.handle));

            PyObject* ts = PyLong_FromLongLong((long long)rec.ts);
            if (!ts) {
                Py_DECREF(obj);
                pytimelogiter_cleanup(self);
                goto fail;
            }

            PyObject* tup = PyTuple_New(2);
            if (!tup) {
                Py_DECREF(ts);
                Py_DECREF(obj);
                pytimelogiter_cleanup(self);
                goto fail;
            }

            PyTuple_SET_ITEM(tup, 0, ts);
            PyTuple_SET_ITEM(tup, 1, obj);
            PyList_SET_ITEM(list, i, tup);

            if (self->remaining_valid && self->remaining_count > 0) {
                self->remaining_count--;
            }
            continue;
        }

        if (st == TL_EOF) {
            pytimelogiter_cleanup(self);
            break;
        }

        /* Error path */
        pytimelogiter_cleanup(self);
        TlPy_RaiseFromObject((PyObject*)self, st);
        goto fail;
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
    if (!self->remaining_valid) {
        PyErr_SetString(PyExc_RuntimeError,
            "iterator remaining length is unavailable");
        return -1;
    }

    if (self->remaining_count > (uint64_t)PY_SSIZE_T_MAX) {
        PyErr_SetString(PyExc_OverflowError,
            "iterator length does not fit in Py_ssize_t");
        return -1;
    }

    return (Py_ssize_t)self->remaining_count;
}

static PyObject* PyTimelogIter_get_closed(PyTimelogIter* self, void* closure)
{
    (void)closure;
    return PyBool_FromLong(self->closed);
}

/*===========================================================================
 * Method/GetSet Tables
 *===========================================================================*/

static PyObject* PyTimelogIter_view(PyTimelogIter* self, PyObject* Py_UNUSED(noargs))
{
    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "iterator is closed");
        return NULL;
    }
    if (!self->owner) {
        PyErr_SetString(PyExc_RuntimeError, "iterator owner is no longer available");
        return NULL;
    }
    return PyPageSpanIter_Create(self->owner, self->range_t1, self->range_t2, "segment");
}

static PyMethodDef PyTimelogIter_methods[] = {
    {"close", (PyCFunction)PyTimelogIter_close, METH_NOARGS,
     "close() -> None\n\nRelease iterator resources. Idempotent."},
    {"next_batch", (PyCFunction)PyTimelogIter_next_batch, METH_O,
     "next_batch(n) -> list[tuple[int, object]]\n\n"
     "Return up to n records. Empty list on exhaustion."},
    {"view", (PyCFunction)PyTimelogIter_view, METH_NOARGS,
     "view() -> PageSpanIter\n\nReturn a PageSpanIter for the same time range."},
    {"__enter__", (PyCFunction)PyTimelogIter_enter, METH_NOARGS,
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

int TlPyTimelogIter_Check(PyObject* op, const tl_py_module_state_t* st)
{
    return op != NULL && st != NULL && st->type_timelog_iter != NULL &&
           PyObject_TypeCheck(op, (PyTypeObject*)st->type_timelog_iter);
}
