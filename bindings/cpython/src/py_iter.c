/**
 * @file py_iter.c
 * @brief PyTimelogIter CPython extension type implementation (LLD-B3)
 *
 * Implements snapshot-based iteration over timelog records.
 *
 * See: docs/timelog_v1_lld_B3_pytimelogiter_snapshot_iterator.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_iter.h"
#include "timelogpy/py_errors.h"
#include "timelogpy/py_handle.h"
#include "timelog/timelog.h"

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static void pytimelogiter_cleanup(PyTimelogIter* self);

/*===========================================================================
 * Block Direct Construction
 *
 * Iterators are only created via factory methods (range, since, etc.).
 *===========================================================================*/

static PyObject* PyTimelogIter_new_error(PyTypeObject* type,
                                          PyObject* args,
                                          PyObject* kwds)
{
    (void)type;
    (void)args;
    (void)kwds;

    PyErr_SetString(PyExc_TypeError,
        "TimelogIter cannot be instantiated directly; "
        "use Timelog.range(), .since(), .until(), .all(), etc.");
    return NULL;
}

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
    if (self->closed) {
        return;  /* Already cleaned up */
    }
    self->closed = 1;

    /*
     * Clear pointers BEFORE operations that may run Python code.
     * This prevents reentrancy issues if Py_DECREF triggers __del__.
     */
    tl_iter_t* it = self->iter;
    self->iter = NULL;

    tl_snapshot_t* snap = self->snapshot;
    self->snapshot = NULL;

    tl_py_handle_ctx_t* ctx = self->handle_ctx;
    /* Don't NULL handle_ctx - it's borrowed, and we need it for pin exit */

    PyObject* owner = self->owner;
    self->owner = NULL;

    /*
     * Release resources in order:
     * 1. Destroy iterator (no Python code)
     * 2. Release snapshot (no Python code)
     * 3. Exit pins - may drain retired objects (runs Python code via Py_DECREF)
     * 4. DECREF owner (runs Python code)
     */
    if (it) {
        tl_iter_destroy(it);
    }

    if (snap) {
        tl_snapshot_release(snap);
    }

    /*
     * Preserve exception state across operations that may run arbitrary Python
     * code (drain, owner DECREF). This ensures:
     * - TL_EOF path stays a clean StopIteration (no exception)
     * - __exit__ path doesn't corrupt the propagating exception
     * - Bad finalizers in __del__ don't clobber our exception state
     */
    PyObject *exc_type, *exc_value, *exc_tb;
    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);

    if (ctx) {
        tl_py_pins_exit_and_maybe_drain(ctx);
    }

    Py_XDECREF(owner);

    PyErr_Restore(exc_type, exc_value, exc_tb);
}

/*===========================================================================
 * GC Support
 *===========================================================================*/

static int PyTimelogIter_traverse(PyTimelogIter* self, visitproc visit, void* arg)
{
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
    PyObject_GC_UnTrack(self);
    pytimelogiter_cleanup(self);  /* Idempotent */
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * Iterator Protocol
 *===========================================================================*/

static PyObject* PyTimelogIter_iternext(PyTimelogIter* self)
{
    /*
     * Closed iterator returns NULL with no exception set.
     * Per CPython convention, this signals StopIteration.
     */
    if (self->closed) {
        return NULL;
    }

    tl_record_t rec;
    tl_status_t st = tl_iter_next(self->iter, &rec);

    if (st == TL_OK) {
        /* Decode handle to PyObject* and take new reference */
        PyObject* obj = Py_NewRef(tl_py_handle_decode(rec.handle));

        PyObject* ts = PyLong_FromLongLong((long long)rec.ts);
        if (!ts) {
            Py_DECREF(obj);
            return NULL;
        }

        PyObject* tup = PyTuple_New(2);
        if (!tup) {
            Py_DECREF(ts);
            Py_DECREF(obj);
            return NULL;
        }

        /* PyTuple_SET_ITEM steals references */
        PyTuple_SET_ITEM(tup, 0, ts);
        PyTuple_SET_ITEM(tup, 1, obj);
        return tup;
    }

    if (st == TL_EOF) {
        /* Exhaustion - cleanup and signal StopIteration */
        pytimelogiter_cleanup(self);
        return NULL;  /* No exception = StopIteration */
    }

    /* Error path - cleanup and raise */
    pytimelogiter_cleanup(self);
    return TlPy_RaiseFromStatus(st);
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

    /* Negative n is an error (unlike zero which returns empty list) */
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
            PyObject* obj = Py_NewRef(tl_py_handle_decode(rec.handle));

            PyObject* ts = PyLong_FromLongLong((long long)rec.ts);
            if (!ts) {
                Py_DECREF(obj);
                goto fail;
            }

            PyObject* tup = PyTuple_New(2);
            if (!tup) {
                Py_DECREF(ts);
                Py_DECREF(obj);
                goto fail;
            }

            PyTuple_SET_ITEM(tup, 0, ts);
            PyTuple_SET_ITEM(tup, 1, obj);
            PyList_SET_ITEM(list, i, tup);
            continue;
        }

        if (st == TL_EOF) {
            pytimelogiter_cleanup(self);
            break;
        }

        /* Error path */
        pytimelogiter_cleanup(self);
        TlPy_RaiseFromStatus(st);
        goto fail;
    }

    /* Shrink list if early EOF */
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

static PyObject* PyTimelogIter_get_closed(PyTimelogIter* self, void* closure)
{
    (void)closure;
    return PyBool_FromLong(self->closed);
}

/*===========================================================================
 * Method/GetSet Tables
 *===========================================================================*/

static PyMethodDef PyTimelogIter_methods[] = {
    {"close", (PyCFunction)PyTimelogIter_close, METH_NOARGS,
     "close() -> None\n\nRelease iterator resources. Idempotent."},
    {"next_batch", (PyCFunction)PyTimelogIter_next_batch, METH_O,
     "next_batch(n) -> list[tuple[int, object]]\n\n"
     "Return up to n records. Empty list on exhaustion."},
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
 * Type Object
 *===========================================================================*/

PyTypeObject PyTimelogIter_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.TimelogIter",
    .tp_doc = PyDoc_STR(
        "Snapshot-based iterator over timelog records.\n\n"
        "Yields (timestamp, object) tuples. Cannot be instantiated directly;\n"
        "use Timelog.range(), .since(), .until(), .all() factory methods."
    ),
    .tp_basicsize = sizeof(PyTimelogIter),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_GC,
    .tp_new = PyTimelogIter_new_error,  /* Block direct construction */
    .tp_dealloc = (destructor)PyTimelogIter_dealloc,
    .tp_traverse = (traverseproc)PyTimelogIter_traverse,
    .tp_clear = (inquiry)PyTimelogIter_clear,
    .tp_free = PyObject_GC_Del,         /* Explicit for GC-allocated types */
    .tp_iter = PyObject_SelfIter,
    .tp_iternext = (iternextfunc)PyTimelogIter_iternext,
    .tp_methods = PyTimelogIter_methods,
    .tp_getset = PyTimelogIter_getset,
};
