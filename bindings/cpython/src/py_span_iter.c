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

#include "timelogpy/py_compat.h"
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
 *   2. release handle/engine lifetime refs
 *   3. PyMem_Free(ctx) - free this context struct
 *
 * The "armed" flag prevents double cleanup if core calls the hook during
 * iter_open failure paths before we've completed setup.
 *===========================================================================*/

typedef struct tl_py_pagespan_hook_ctx {
    tl_py_handle_ctx_t* ctx;    /**< Strong lifetime ref */
    tl_py_engine_ctx_t* engine_ctx; /**< Strong engine lifetime ref */
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
    if (hook_ctx->engine_ctx != NULL) {
        tl_py_engine_ctx_decref(hook_ctx->engine_ctx);
    }
    if (hook_ctx->ctx != NULL) {
        tl_py_handle_ctx_decref(hook_ctx->ctx);
    }

    PyMem_Free(hook_ctx);
    PyErr_Restore(exc_type, exc_value, exc_tb);
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

    tl_py_module_state_t* mod_st = TlPy_StateFromObject(timelog);
    if (mod_st == NULL) {
        return NULL;
    }

    /* Defensive type check for internal C callers. */
    if (!TlPyTimelog_Check(timelog, mod_st)) {
        PyErr_SetString(PyExc_TypeError,
            "page_spans: expected Timelog instance");
        return NULL;
    }

    PyTimelog* tl_obj = (PyTimelog*)timelog;

    /* Allocate the hook context before taking the lock (no lifecycle state
     * touched yet). armed=0 prevents double cleanup on iter_open failure. */
    tl_py_pagespan_hook_ctx_t* hook_ctx = PyMem_Malloc(sizeof(*hook_ctx));
    if (hook_ctx == NULL) {
        PyErr_NoMemory();
        return NULL;
    }
    hook_ctx->armed = 0;
    hook_ctx->ctx = NULL;
    hook_ctx->engine_ctx = NULL;

    /*
     * Acquire all lifetime guards under core_lock so a concurrent close()
     * cannot free handle_ctx/engine_ctx in the window between the open-state
     * check and the pin/incref (the pin-before-own TOCTOU). Under the lock:
     * recheck open (tl_py_lock_checked), own a handle_ctx + engine_ctx ref,
     * enter the pin, then open the core iterator. The owned refs + pin are
     * transferred to the hook context (released by tl_py_pagespan_on_release
     * when the owner refcount reaches zero).
     */
    if (tl_py_lock_checked(tl_obj) < 0) {
        PyMem_Free(hook_ctx);
        return NULL;
    }

    tl_py_handle_ctx_t* hctx = tl_obj->handle_ctx;
    tl_py_engine_ctx_t* ectx = tl_obj->engine_ctx;
    if (hctx == NULL || ectx == NULL) {
        TL_PY_UNLOCK(tl_obj);
        PyMem_Free(hook_ctx);
        PyErr_SetString(PyExc_RuntimeError,
                        "timelog context is unavailable");
        return NULL;
    }
    tl_py_handle_ctx_incref(hctx);
    tl_py_engine_ctx_incref(ectx);
    tl_py_pins_enter(hctx);
    hook_ctx->ctx = hctx;
    hook_ctx->engine_ctx = ectx;

    tl_pagespan_owner_hooks_t hooks = {
        .user = hook_ctx,
        .on_release = tl_py_pagespan_on_release
    };

    uint32_t flags = TL_PAGESPAN_DEFAULT;
    tl_pagespan_iter_t* core_iter = NULL;
    tl_status_t st = tl_pagespan_iter_open(tl_obj->tl, t1, t2, flags, &hooks, &core_iter);
    TL_PY_UNLOCK(tl_obj);

    if (st != TL_OK) {
        /* iter_open failed: hook not armed, manual cleanup required.
         * Release outside the lock (pins_exit may drain Python objects). */
        tl_py_pins_exit_and_maybe_drain(hctx);
        tl_py_engine_ctx_decref(ectx);
        tl_py_handle_ctx_decref(hctx);
        PyMem_Free(hook_ctx);
        TlPy_RaiseFromObject((PyObject*)tl_obj, st);
        return NULL;
    }

    /* Arm hook: core now owns it and will call on owner release. */
    hook_ctx->armed = 1;

    /* Allocate Python iterator. */
    PyTypeObject* span_iter_type = (PyTypeObject*)mod_st->type_pagespan_iter;
    PyPageSpanIter* self = (PyPageSpanIter*)span_iter_type->tp_alloc(span_iter_type, 0);
    if (self == NULL) {
        /* Close core iter triggers armed hook for cleanup. */
        tl_pagespan_iter_close(core_iter);
        return NULL;
    }

    /* Initialize fields. */
    self->iter = core_iter;
    self->timelog = Py_NewRef((PyObject*)tl_obj);
    self->closed = 0;
    return (PyObject*)self;
}

/*===========================================================================
 * Cleanup (Single Source of Truth)
 *
 * Closes core iterator and clears Python references.
 * The core iter_close releases the iterator's owner ref, which may trigger
 * the release hook if that was the last ref.
 *===========================================================================*/

/* Detach iterator resources under CS. Caller must release outside. */
static int pagespaniter_detach_locked(PyPageSpanIter* self,
                                       tl_pagespan_iter_t** out_iter,
                                       PyObject** out_timelog)
{
    if (self->closed) {
        *out_iter = NULL;
        *out_timelog = NULL;
        return 0;
    }
    self->closed = 1;
    *out_iter = self->iter;
    self->iter = NULL;
    *out_timelog = self->timelog;
    self->timelog = NULL;
    return 1;
}

static void pagespaniter_release_resources(tl_pagespan_iter_t* iter,
                                            PyObject* timelog)
{
    if (iter != NULL) {
        /* Releases iterator's owner ref; release hook fires if last ref. */
        tl_pagespan_iter_close(iter);
    }
    if (timelog != NULL) {
        /* Preserve exception state across Py_DECREF (may run __del__). */
        PyObject *exc_type, *exc_value, *exc_tb;
        PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
        Py_DECREF(timelog);
        PyErr_Restore(exc_type, exc_value, exc_tb);
    }
}

static void pagespaniter_cleanup(PyPageSpanIter* self)
{
    tl_pagespan_iter_t* iter = NULL;
    PyObject* timelog = NULL;
    int detached;

    TL_PY_OBJ_LOCK(self);
    detached = pagespaniter_detach_locked(self, &iter, &timelog);
    TL_PY_OBJ_UNLOCK();

    if (detached) {
        pagespaniter_release_resources(iter, timelog);
    }
}

/*===========================================================================
 * GC Support
 *===========================================================================*/

static int PyPageSpanIter_traverse(PyPageSpanIter* self, visitproc visit, void* arg)
{
    Py_VISIT(Py_TYPE(self));
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
    PyTypeObject* tp = Py_TYPE(self);
    PyObject_GC_UnTrack(self);
    pagespaniter_cleanup(self);
    tp->tp_free((PyObject*)self);
    Py_DECREF(tp);
}

/*===========================================================================
 * Iterator Protocol
 *
 * Each __next__ call invokes core iter_next to get the next span on-demand.
 * This is streaming - no pre-collection of spans.
 *===========================================================================*/

static PyObject* PyPageSpanIter_iternext(PyPageSpanIter* self)
{
    /* Hold CS through the engine call so a concurrent close cannot free
     * self->iter mid-call. tl_pagespan_iter_next is pure C, honoring the
     * "no Python work under internal locks" invariant. */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));
    tl_status_t st = TL_EOF;
    int was_closed = 0;
    int do_release = 0;
    tl_pagespan_iter_t* iter_local = NULL;
    PyObject* timelog_local = NULL;
    /* Capture timelog under CS for PyPageSpan_FromView below. */
    PyObject* timelog_ref = NULL;

    TL_PY_OBJ_LOCK(self);
    if (self->closed || self->iter == NULL) {
        was_closed = 1;
    } else {
        st = tl_pagespan_iter_next(self->iter, &view);
        if (st == TL_OK) {
            /* PyPageSpan_FromView needs a Python ref to the timelog. Take
             * a strong ref under CS so close cannot null it from us. */
            timelog_ref = self->timelog ? Py_NewRef(self->timelog) : NULL;
        } else {
            do_release = pagespaniter_detach_locked(
                self, &iter_local, &timelog_local);
        }
    }
    TL_PY_OBJ_UNLOCK();

    if (was_closed) {
        return NULL;  /* StopIteration */
    }
    if (st != TL_OK) {
        if (do_release) {
            pagespaniter_release_resources(iter_local, timelog_local);
        }
        if (st == TL_EOF) {
            return NULL;
        }
        return TlPy_RaiseFromObject((PyObject*)self, st);
    }

    /* PyPageSpan_FromView consumes view.owner on success. */
    PyObject* span = PyPageSpan_FromView(&view, timelog_ref);
    Py_XDECREF(timelog_ref);
    if (span == NULL) {
        /* Creation failed; release the view's owner ref. */
        tl_pagespan_view_release(&view);
        return NULL;
    }
    return span;
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
    int closed;
    TL_PY_OBJ_LOCK(self);
    closed = self->closed;
    TL_PY_OBJ_UNLOCK();
    return PyBool_FromLong(closed);
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
 * Type Specification
 *===========================================================================*/

static PyType_Slot PyPageSpanIter_slots[] = {
    {Py_tp_doc, PyDoc_STR(
        "Streaming iterator yielding PageSpan objects for a time range.\n\n"
        "Cannot be instantiated directly; use Timelog.page_spans()."
    )},
    {Py_tp_dealloc, (void*)PyPageSpanIter_dealloc},
    {Py_tp_traverse, (void*)PyPageSpanIter_traverse},
    {Py_tp_clear, (void*)PyPageSpanIter_clear},
    {Py_tp_iter, PyObject_SelfIter},
    {Py_tp_iternext, (void*)PyPageSpanIter_iternext},
    {Py_tp_methods, PyPageSpanIter_methods},
    {Py_tp_getset, PyPageSpanIter_getset},
    {0, NULL}
};

static PyType_Spec PyPageSpanIter_spec = {
    .name = "timelog._timelog.PageSpanIter",
    .basicsize = sizeof(PyPageSpanIter),
    .itemsize = 0,
    .flags = Py_TPFLAGS_DEFAULT |
             Py_TPFLAGS_HAVE_GC |
             Py_TPFLAGS_IMMUTABLETYPE |
             Py_TPFLAGS_DISALLOW_INSTANTIATION,
    .slots = PyPageSpanIter_slots,
};

PyObject* TlPy_CreatePageSpanIterType(PyObject* module)
{
    return PyType_FromModuleAndSpec(module, &PyPageSpanIter_spec, NULL);
}

int TlPyPageSpanIter_Check(PyObject* op, const tl_py_module_state_t* st)
{
    return op != NULL && st != NULL && st->type_pagespan_iter != NULL &&
           PyObject_TypeCheck(op, (PyTypeObject*)st->type_pagespan_iter);
}
