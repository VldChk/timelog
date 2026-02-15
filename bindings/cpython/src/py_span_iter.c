/**
 * @file py_span_iter.c
 * @brief PyPageSpanIter CPython extension type implementation (Core API Integration)
 *
 * Implements streaming iteration over page spans using core tl_pagespan_iter_*.
 * Delegates span enumeration and ownership management to core.
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <string.h>  /* For strcmp, memset */

#include "timelogpy/py_span_iter.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_timelog.h"
#include "timelogpy/py_errors.h"

/*
 * Core API for pagespan iteration.
 * This is the ONLY core dependency needed - no storage internals.
 */
#include "query/tl_pagespan_iter.h"

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static void pagespaniter_cleanup(PyPageSpanIter* self);

/*===========================================================================
 * Release Hook Context
 *
 * The core owner calls our hook when refcount reaches 0.
 * The hook handles:
 *   1. pins_exit_and_maybe_drain() - allow handle cleanup
 *   2. Py_DECREF(timelog) - release our strong reference
 *   3. PyMem_Free(ctx) - free this context struct
 *
 * The "armed" flag prevents double cleanup if core calls the hook during
 * iter_open failure paths before we've completed setup.
 *===========================================================================*/

typedef struct tl_py_pagespan_hook_ctx {
    PyObject* timelog;          /**< Strong ref, decref on release */
    tl_py_handle_ctx_t* ctx;    /**< Borrowed handle context */
    int armed;                  /**< 0 until iter_open succeeds */
} tl_py_pagespan_hook_ctx_t;

/**
 * Release hook: called by core when owner refcount reaches 0.
 * GIL must be held. Preserves exception state (may run during GC).
 */
static void tl_py_pagespan_on_release(void* user)
{
    tl_py_pagespan_hook_ctx_t* hook_ctx = (tl_py_pagespan_hook_ctx_t*)user;
    if (hook_ctx == NULL) {
        return;
    }

    /* Not armed: iter_open failed before setup completed. */
    if (!hook_ctx->armed) {
        return;
    }

    /* Preserve exception state across Py_DECREF (may run __del__). */
    PyObject *exc_type, *exc_value, *exc_tb;
    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);

    /* Exit pins (may drain retired objects via Py_DECREF). */
    if (hook_ctx->ctx != NULL) {
        tl_py_pins_exit_and_maybe_drain(hook_ctx->ctx);
    }

    Py_XDECREF(hook_ctx->timelog);
    PyMem_Free(hook_ctx);
    PyErr_Restore(exc_type, exc_value, exc_tb);
}

/*===========================================================================
 * Block Direct Construction
 *
 * PageSpanIter is only created via page_spans() factory.
 *===========================================================================*/

static PyObject* PyPageSpanIter_new_error(PyTypeObject* type,
                                           PyObject* args,
                                           PyObject* kwds)
{
    (void)type;
    (void)args;
    (void)kwds;

    PyErr_SetString(PyExc_TypeError,
        "PageSpanIter cannot be instantiated directly; "
        "use Timelog.page_spans()");
    return NULL;
}

/*===========================================================================
 * Factory Function
 *
 * Creates a streaming iterator using core tl_pagespan_iter_open().
 * Sets up release hook to handle pins and timelog ref on cleanup.
 *===========================================================================*/

PyObject* PyPageSpanIter_Create(PyObject* timelog,
                                tl_ts_t t1,
                                tl_ts_t t2,
                                const char* kind)
{
    /* Only "segment" kind is supported. */
    if (kind == NULL || strcmp(kind, "segment") != 0) {
        PyErr_Format(PyExc_ValueError,
            "page_spans: kind must be 'segment', got '%s'", kind ? kind : "(null)");
        return NULL;
    }

    /* Defensive type check for internal C callers. */
    if (!PyTimelog_Check(timelog)) {
        PyErr_SetString(PyExc_TypeError,
            "page_spans: expected Timelog instance");
        return NULL;
    }

    PyTimelog* tl_obj = (PyTimelog*)timelog;

    /* Check closed state. */
    if (tl_obj->closed || tl_obj->tl == NULL) {
        TlPy_RaiseFromStatusFmt(TL_ESTATE, "Timelog is closed");
        return NULL;
    }

    /* Enter pins BEFORE iter_open (snapshot acquisition). */
    tl_py_pins_enter(&tl_obj->handle_ctx);

    /* Hook context: armed=0 prevents double cleanup on iter_open failure. */
    tl_py_pagespan_hook_ctx_t* hook_ctx = PyMem_Malloc(sizeof(*hook_ctx));
    if (hook_ctx == NULL) {
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        PyErr_NoMemory();
        return NULL;
    }
    hook_ctx->timelog = Py_NewRef((PyObject*)tl_obj);
    hook_ctx->ctx = &tl_obj->handle_ctx;
    hook_ctx->armed = 0;

    /* Set up release hook for core owner. */
    tl_pagespan_owner_hooks_t hooks = {
        .user = hook_ctx,
        .on_release = tl_py_pagespan_on_release
    };

    /* Open core iterator (acquires snapshot, creates owner). */
    uint32_t flags = TL_PAGESPAN_DEFAULT;
    tl_pagespan_iter_t* core_iter = NULL;

    if (tl_py_lock_checked(tl_obj) < 0) {
        Py_DECREF(hook_ctx->timelog);
        PyMem_Free(hook_ctx);
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        return NULL;
    }
    tl_status_t st = tl_pagespan_iter_open(tl_obj->tl, t1, t2, flags, &hooks, &core_iter);
    TL_PY_UNLOCK(tl_obj);

    if (st != TL_OK) {
        /* iter_open failed: hook not armed, manual cleanup required. */
        Py_DECREF(hook_ctx->timelog);
        PyMem_Free(hook_ctx);
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        TlPy_RaiseFromStatus(st);
        return NULL;
    }

    /* Arm hook: core now owns it and will call on owner release. */
    hook_ctx->armed = 1;

    /* Allocate Python iterator. */
    PyPageSpanIter* self = PyObject_GC_New(PyPageSpanIter, &PyPageSpanIter_Type);
    if (self == NULL) {
        /* Close core iter triggers armed hook for cleanup. */
        tl_pagespan_iter_close(core_iter);
        return NULL;
    }

    /* Initialize fields. */
    self->iter = core_iter;
    self->timelog = Py_NewRef((PyObject*)tl_obj);
    self->closed = 0;

    /* GC track after full initialization. */
    PyObject_GC_Track((PyObject*)self);
    return (PyObject*)self;
}

/*===========================================================================
 * Cleanup (Single Source of Truth)
 *
 * Closes core iterator and clears Python references.
 * The core iter_close releases the iterator's owner ref, which may trigger
 * the release hook if that was the last ref.
 *===========================================================================*/

static void pagespaniter_cleanup(PyPageSpanIter* self)
{
    if (self->closed) {
        return;
    }
    self->closed = 1;

    /* Releases iterator's owner ref; hook fires if that was the last. */
    tl_pagespan_iter_t* iter = self->iter;
    self->iter = NULL;

    if (iter != NULL) {
        tl_pagespan_iter_close(iter);
    }

    /* Preserve exception state across Py_CLEAR (may run __del__). */
    {
        PyObject *exc_type, *exc_value, *exc_tb;
        PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
        Py_CLEAR(self->timelog);
        PyErr_Restore(exc_type, exc_value, exc_tb);
    }
}

/*===========================================================================
 * GC Support
 *===========================================================================*/

static int PyPageSpanIter_traverse(PyPageSpanIter* self, visitproc visit, void* arg)
{
    Py_VISIT(self->timelog);
    return 0;
}

static int PyPageSpanIter_clear(PyPageSpanIter* self)
{
    pagespaniter_cleanup(self);
    return 0;
}

static void PyPageSpanIter_dealloc(PyPageSpanIter* self)
{
    PyObject_GC_UnTrack(self);
    pagespaniter_cleanup(self);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * Iterator Protocol
 *
 * Each __next__ call invokes core iter_next to get the next span on-demand.
 * This is streaming - no pre-collection of spans.
 *===========================================================================*/

static PyObject* PyPageSpanIter_iternext(PyPageSpanIter* self)
{
    if (self->closed || self->iter == NULL) {
        return NULL;  /* StopIteration */
    }
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));

    tl_status_t st = tl_pagespan_iter_next(self->iter, &view);

    if (st == TL_OK) {
        /* PyPageSpan_FromView consumes view.owner on success. */
        PyObject* span = PyPageSpan_FromView(&view, self->timelog);
        if (span == NULL) {
            /* Creation failed; release the view's owner ref. */
            tl_pagespan_view_release(&view);
            return NULL;
        }
        return span;
    }

    if (st == TL_EOF) {
        /* Exhausted. */
        pagespaniter_cleanup(self);
        return NULL;  /* StopIteration */
    }

    /* Error. */
    pagespaniter_cleanup(self);
    TlPy_RaiseFromStatus(st);
    return NULL;
}

/*===========================================================================
 * Methods
 *===========================================================================*/

static PyObject* PyPageSpanIter_close(PyPageSpanIter* self, PyObject* noargs)
{
    (void)noargs;
    pagespaniter_cleanup(self);
    Py_RETURN_NONE;
}

static PyObject* PyPageSpanIter_enter(PyPageSpanIter* self, PyObject* noargs)
{
    (void)noargs;
    return Py_NewRef((PyObject*)self);
}

static PyObject* PyPageSpanIter_exit(PyPageSpanIter* self, PyObject* args)
{
    (void)args;
    pagespaniter_cleanup(self);
    Py_RETURN_FALSE;
}

/*===========================================================================
 * Properties
 *===========================================================================*/

static PyObject* PyPageSpanIter_get_closed(PyPageSpanIter* self, void* closure)
{
    (void)closure;
    return PyBool_FromLong(self->closed);
}

/*===========================================================================
 * Method/GetSet Tables
 *===========================================================================*/

static PyMethodDef PyPageSpanIter_methods[] = {
    {"close", (PyCFunction)PyPageSpanIter_close, METH_NOARGS,
     "close() -> None\n\nRelease iterator resources. Idempotent."},
    {"__enter__", (PyCFunction)PyPageSpanIter_enter, METH_NOARGS,
     "Context manager entry."},
    {"__exit__", (PyCFunction)PyPageSpanIter_exit, METH_VARARGS,
     "Context manager exit (closes iterator)."},
    {NULL, NULL, 0, NULL}
};

static PyGetSetDef PyPageSpanIter_getset[] = {
    {"closed", (getter)PyPageSpanIter_get_closed, NULL,
     "True if iterator is closed or exhausted.", NULL},
    {NULL, NULL, NULL, NULL, NULL}
};

/*===========================================================================
 * Type Object
 *===========================================================================*/

PyTypeObject PyPageSpanIter_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.PageSpanIter",
    .tp_doc = PyDoc_STR(
        "Streaming iterator yielding PageSpan objects for a time range.\n\n"
        "Cannot be instantiated directly; use Timelog.page_spans()."
    ),
    .tp_basicsize = sizeof(PyPageSpanIter),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_GC,
    .tp_new = PyPageSpanIter_new_error,
    .tp_dealloc = (destructor)PyPageSpanIter_dealloc,
    .tp_traverse = (traverseproc)PyPageSpanIter_traverse,
    .tp_clear = (inquiry)PyPageSpanIter_clear,
    .tp_free = PyObject_GC_Del,
    .tp_iter = PyObject_SelfIter,
    .tp_iternext = (iternextfunc)PyPageSpanIter_iternext,
    .tp_methods = PyPageSpanIter_methods,
    .tp_getset = PyPageSpanIter_getset,
};
