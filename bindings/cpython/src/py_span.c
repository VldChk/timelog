/**
 * @file py_span.c
 * @brief PyPageSpan CPython extension type implementation
 *
 * Implements zero-copy timestamp exposure via the CPython buffer protocol.
 * Delegates ownership management to core tl_pagespan_owner_t.
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <assert.h>  /* For internal-contract asserts */
#include <stdint.h>  /* For SIZE_MAX */
#include <string.h>  /* For memset */

#include "timelogpy/py_compat.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_span_objects.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_timelog.h"

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static void pagespan_cleanup(PyPageSpan* self);

/*===========================================================================
 * PageSpan Creation from Core View
 *
 * Consume a core view's owner reference to create a PageSpan.
 *===========================================================================*/

PyObject* PyPageSpan_FromView(tl_pagespan_view_t* view, PyObject* timelog)
{
    /* On failure, caller must call tl_pagespan_view_release().
     *
     * Internal contract (single caller: PyPageSpanIter_iternext): the view
     * was freshly filled by tl_pagespan_iter_next (owner set by core
     * contract) and timelog was captured under the iterator's CS while
     * open — asserts, not runtime checks. */
    assert(view != NULL && view->owner != NULL && timelog != NULL);
    tl_py_module_state_t* mod_st = TlPy_StateFromObject(timelog);
    if (mod_st == NULL) {
        return NULL;
    }
    assert(TlPyTimelog_Check(timelog, mod_st));

    /* Allocate GC-tracked Python object. */
    PyTypeObject* span_type = (PyTypeObject*)mod_st->type_pagespan;
    PyPageSpan* self = (PyPageSpan*)span_type->tp_alloc(span_type, 0);
    if (self == NULL) {
        /* Allocation failed - caller must release view */
        return NULL;
    }

    /* Transfer owner reference from view to span (no incref needed). */
    self->owner = view->owner;
    view->owner = NULL;

    /* Strong ref for GC visibility (core owner is opaque to GC). */
    self->timelog = Py_NewRef(timelog);

    /* Borrowed from owner's snapshot; valid while owner is alive. */
    self->ts = view->ts;
    self->h = view->h;
    self->len = view->len;
    self->first_ts = view->first_ts;
    self->last_ts = view->last_ts;

    /* Buffer protocol metadata is immutable after creation. Existing
     * memoryviews may read these arrays without taking our critical section, so
     * getbuffer() must not rewrite them under free-threaded CPython. */
    self->shape[0] = (Py_ssize_t)view->len;
    self->strides[0] = (Py_ssize_t)sizeof(tl_ts_t);
    self->exports = 0;
    self->closed = 0;

    return (PyObject*)self;
}

/*===========================================================================
 * Cleanup (Single Source of Truth)
 *
 * Releases owner reference and clears borrowed pointers.
 * The core owner's release hook (set during iterator creation) handles
 * pins_exit and Py_DECREF of the iteration-level timelog reference.
 *===========================================================================*/

/*
 * Detach the span's owned resources in ONE critical section, making the
 * "check exports + mark closed + detach owner" sequence atomic with respect
 * to a concurrent getbuffer (which checks closed + increments exports under
 * the same CS). Without this, getbuffer could export a buffer in the gap
 * between an exports==0 read and the mark-closed store.
 *
 * Returns:
 *   1  detached — caller MUST release (*out_owner, *out_timelog) outside CS
 *   0  already closed — nothing to do
 *  -1  busy — a buffer is exported and force==0; no state change
 *
 * force==1 (dealloc) detaches regardless of exports.
 */
static int pagespan_detach_locked(PyPageSpan* self, int force,
                                  tl_pagespan_owner_t** out_owner,
                                  PyObject** out_timelog)
{
    int result;
    *out_owner = NULL;
    *out_timelog = NULL;

    TL_PY_OBJ_LOCK(self);
    if (self->closed) {
        result = 0;
    } else if (!force && self->exports > 0) {
        result = -1;
    } else {
        self->closed = 1;
        /* Clear borrowed pointers before releasing owner; the underlying
         * snapshot pages may be freed when the hook runs. */
        self->ts = NULL;
        self->h = NULL;
        self->len = 0;
        *out_owner = self->owner;
        *out_timelog = self->timelog;
        self->owner = NULL;
        self->timelog = NULL;
        result = 1;
    }
    TL_PY_OBJ_UNLOCK();
    return result;
}

/* Release detached resources OUTSIDE any critical section: the owner
 * release hook may drain retired objects and Py_DECREF may run __del__,
 * neither of which is permitted while an internal lock is held. */
static void pagespan_release_detached(tl_pagespan_owner_t* owner,
                                      PyObject* timelog)
{
    if (owner != NULL) {
        tl_pagespan_owner_decref(owner);
    }
    if (timelog != NULL) {
        TL_PY_PRESERVE_EXC_BEGIN;
        Py_DECREF(timelog);
        TL_PY_PRESERVE_EXC_END;
    }
}

/* Force cleanup (dealloc/clear-without-exports). Ignores exports. */
static void pagespan_cleanup(PyPageSpan* self)
{
    tl_pagespan_owner_t* owner = NULL;
    PyObject* timelog = NULL;
    if (pagespan_detach_locked(self, 1, &owner, &timelog) == 1) {
        pagespan_release_detached(owner, timelog);
    }
}

/*===========================================================================
 * GC Support
 *===========================================================================*/

static int PyPageSpan_traverse(PyPageSpan* self, visitproc visit, void* arg)
{
    Py_VISIT(Py_TYPE(self));
    Py_VISIT(self->timelog);
    return 0;
}

static int PyPageSpan_clear(PyPageSpan* self)
{
    /* Defer cleanup while buffers are exported (the exporter holds a strong
     * ref to self, so dealloc cannot run; cleanup happens on the last
     * releasebuffer/close). force=0 makes the exports check atomic with the
     * detach. */
    tl_pagespan_owner_t* owner = NULL;
    PyObject* timelog = NULL;
    if (pagespan_detach_locked(self, 0, &owner, &timelog) == 1) {
        pagespan_release_detached(owner, timelog);
    }
    return 0;
}

static void PyPageSpan_dealloc(PyPageSpan* self)
{
    /* exports > 0 here means a bug; cleanup anyway to avoid leaks. */
    TL_PY_GC_DEALLOC(self, pagespan_cleanup(self));
}

/*===========================================================================
 * Buffer Protocol
 *
 * Exposes timestamps as a read-only 1D array of int64.
 * Uses span->ts and span->len instead of page pointer + row indices.
 *===========================================================================*/

/* Static format string - must outlive buffer view */
static const char* PAGESPAN_TS_FORMAT = "q";

/*
 * Atomic state check + exports increment under self's critical section.
 * The check-then-set must be atomic w.r.t. concurrent close (which checks
 * exports and sets closed under the same critical section).
 *
 * Py_NewRef on the exporter happens OUTSIDE the CS — Python ref ops can
 * touch internal CPython mutexes and should not run under our own.
 */
static int pagespan_getbuffer(PyObject* exporter, Py_buffer* view, int flags)
{
    PyPageSpan* self = (PyPageSpan*)exporter;

    /* CPython contract: view->obj = NULL on error. */
    view->obj = NULL;

    /* err codes: 0 ok, 1 closed, 2 overflow, 3 writable-rejected.
     * The closed check runs BEFORE the writable check so a closed span
     * always raises ValueError, even when the caller asked for a writable
     * buffer (which would otherwise mask the closed state with
     * BufferError). */
    int err = 0;
    void* ts_local = NULL;
    size_t byte_len_local = 0;

    TL_PY_OBJ_LOCK(self);
    if (self->closed || self->ts == NULL) {
        err = 1;
    } else if (flags & PyBUF_WRITABLE) {
        err = 3;
#if SIZE_MAX <= UINT32_MAX
    } else if ((size_t)self->len > (size_t)PY_SSIZE_T_MAX / sizeof(tl_ts_t)) {
        err = 2;
#endif
    } else {
        byte_len_local = (size_t)self->len * sizeof(tl_ts_t);
        ts_local = (void*)self->ts;

        /* SECURITY: export ONLY the int64 timestamp array (self->ts). The
         * handle array self->h holds encoded PyObject* values; exposing it as
         * a numeric zero-copy buffer would disclose/forge raw pointers (UAF).
         * Decoded payloads are reachable only via PageSpanObjectsView, which
         * returns real PyObjects, never the raw handle. PageSpan is the sole
         * buffer exporter in the binding (guarded by test_hardening.py). */
        /* Fill view (request-independent fields). */
        view->buf = ts_local;
        view->len = (Py_ssize_t)byte_len_local;
        view->readonly = 1;
        view->itemsize = (Py_ssize_t)sizeof(tl_ts_t);
        view->ndim = 1;
        view->format = (flags & PyBUF_FORMAT) ? (char*)PAGESPAN_TS_FORMAT : NULL;
        if (flags & PyBUF_ND) {
            view->shape = self->shape;
        } else {
            view->shape = NULL;
        }
        if (flags & PyBUF_STRIDES) {
            view->strides = self->strides;
        } else {
            view->strides = NULL;
        }
        view->suboffsets = NULL;
        view->internal = NULL;

        self->exports++;
    }
    TL_PY_OBJ_UNLOCK();

    if (err == 1) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return -1;
    }
    if (err == 3) {
        PyErr_SetString(PyExc_BufferError, "PageSpan buffer is read-only");
        return -1;
    }
    if (err == 2) {
        PyErr_SetString(PyExc_OverflowError, "PageSpan too large for buffer");
        return -1;
    }

    /* Pin the exporter outside CS. Caller balances with releasebuffer. */
    view->obj = Py_NewRef(exporter);
    return 0;
}

static void pagespan_releasebuffer(PyObject* exporter, Py_buffer* view)
{
    PyPageSpan* self = (PyPageSpan*)exporter;
    (void)view;

    TL_PY_OBJ_LOCK(self);
    if (self->exports > 0) {
        self->exports--;
    }
    TL_PY_OBJ_UNLOCK();
}

/*===========================================================================
 * Methods
 *===========================================================================*/

static PyObject* PyPageSpan_close(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;

    /* Atomic: the exports check and the closed/detach transition happen in
     * one critical section, so a concurrent getbuffer cannot export a
     * buffer in a window between "exports==0" and "mark closed". */
    tl_pagespan_owner_t* owner = NULL;
    PyObject* timelog = NULL;
    int r = pagespan_detach_locked(self, 0, &owner, &timelog);
    if (r == -1) {
        PyErr_SetString(PyExc_BufferError,
            "cannot close PageSpan: buffer is exported");
        return NULL;
    }
    if (r == 1) {
        pagespan_release_detached(owner, timelog);
    }
    /* r == 0 (already closed) is idempotent success. */
    Py_RETURN_NONE;
}

static PyObject* PyPageSpan_exit(PyPageSpan* self, PyObject* args)
{
    (void)args;

    /* Atomic exports check + detach. force=0: if a buffer is exported,
     * skip cleanup silently (use close() for strict error checking). */
    tl_pagespan_owner_t* owner = NULL;
    PyObject* timelog = NULL;
    if (pagespan_detach_locked(self, 0, &owner, &timelog) == 1) {
        pagespan_release_detached(owner, timelog);
    }
    Py_RETURN_FALSE;  /* Don't suppress exceptions */
}

static PyObject* PyPageSpan_objects(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;

    /* Fail early on a closed span. (h is never NULL while open: the core
     * always fills it and detach clears it only together with closed=1
     * under this same CS.) */
    int closed;
    TL_PY_OBJ_LOCK(self);
    closed = self->closed;
    TL_PY_OBJ_UNLOCK();

    if (closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    return PyPageSpanObjectsView_Create((PyObject*)self);
}

static PyObject* PyPageSpan_copy_timestamps(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;

    /* Pin the owner across the copy so the underlying ts array cannot
     * be freed by a concurrent close. Under the critical section we
     * validate state, snapshot length + ts pointer + owner, and incref
     * the owner ONLY once all preconditions hold — so no exit path can
     * leave the owner incref'd without a matching decref. Then iterate
     * outside the CS using the pinned values.
     *
     * err codes: 0 ok, 1 closed, 2 no-buffer. */
    int err = 0;
    Py_ssize_t n = 0;
    const tl_ts_t* ts_local = NULL;
    tl_pagespan_owner_t* owner = NULL;

    TL_PY_OBJ_LOCK(self);
    if (self->closed) {
        err = 1;
    } else if (self->owner == NULL || self->ts == NULL) {
        err = 2;
    } else {
        n = (Py_ssize_t)self->len;
        ts_local = self->ts;
        owner = self->owner;
        tl_pagespan_owner_incref(owner);
    }
    TL_PY_OBJ_UNLOCK();

    if (err == 1) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }
    if (err == 2) {
        PyErr_SetString(PyExc_RuntimeError,
            "PageSpan has no underlying buffer");
        return NULL;
    }

    PyObject* list = PyList_New(n);
    if (list == NULL) {
        tl_pagespan_owner_decref(owner);
        return NULL;
    }

    for (Py_ssize_t i = 0; i < n; i++) {
        PyObject* val = PyLong_FromLongLong((long long)ts_local[i]);
        if (val == NULL) {
            Py_DECREF(list);
            tl_pagespan_owner_decref(owner);
            return NULL;
        }
        PyList_SET_ITEM(list, i, val);
    }

    tl_pagespan_owner_decref(owner);
    return list;
}

/*===========================================================================
 * Sequence Protocol (__len__)
 *===========================================================================*/

static Py_ssize_t PyPageSpan_length(PyPageSpan* self)
{
    Py_ssize_t n;
    TL_PY_OBJ_LOCK(self);
    n = self->closed ? 0 : (Py_ssize_t)self->len;
    TL_PY_OBJ_UNLOCK();
    return n;
}

/*===========================================================================
 * Properties
 *===========================================================================*/

static PyObject* PyPageSpan_get_timestamps(PyPageSpan* self, void* closure)
{
    (void)closure;

    /* PyMemoryView_FromObject calls bf_getbuffer, which takes the CS and
     * checks closed atomically with exports++, raising the byte-identical
     * ValueError("PageSpan is closed") — no pre-check needed. */
    return PyMemoryView_FromObject((PyObject*)self);
}

/* first_ts/last_ts are immutable after construction; only closed needs CS. */
TL_PY_DEFINE_SPAN_TS_GETTER(PyPageSpan_get_start_ts, PyPageSpan, first_ts)
TL_PY_DEFINE_SPAN_TS_GETTER(PyPageSpan_get_end_ts, PyPageSpan, last_ts)

static PyObject* PyPageSpan_get_last_ts(PyPageSpan* self, void* closure)
{
    return PyPageSpan_get_end_ts(self, closure);
}

TL_PY_DEFINE_CLOSED_GETTER(PyPageSpan_get_closed, PyPageSpan)

/*===========================================================================
 * Method/GetSet Tables
 *===========================================================================*/

static PyMethodDef PyPageSpan_methods[] = {
    {"close", (PyCFunction)PyPageSpan_close, METH_NOARGS,
     "close() -> None\n\n"
     "Release span resources. Raises BufferError if buffers are exported."},
    {"objects", (PyCFunction)PyPageSpan_objects, METH_NOARGS,
     "objects() -> PageSpanObjectsView\n\n"
     "Return a lazy sequence view over decoded Python objects."},
    {"copy_timestamps", (PyCFunction)PyPageSpan_copy_timestamps, METH_NOARGS,
     "copy_timestamps() -> list[int]\n\n"
     "Return a copy of timestamps as a Python list."},
    {"__enter__", (PyCFunction)tl_py_enter_self, METH_NOARGS,
     "Context manager entry."},
    {"__exit__", (PyCFunction)PyPageSpan_exit, METH_VARARGS,
     "Context manager exit (closes span if no buffers exported)."},
    {NULL, NULL, 0, NULL}
};

static PyGetSetDef PyPageSpan_getset[] = {
    {"timestamps", (getter)PyPageSpan_get_timestamps, NULL,
     "Read-only memoryview of timestamps (int64).", NULL},
    {"start_ts", (getter)PyPageSpan_get_start_ts, NULL,
     "First timestamp in this span.", NULL},
    {"end_ts", (getter)PyPageSpan_get_end_ts, NULL,
     "Last (inclusive) timestamp in this span.", NULL},
    {"last_ts", (getter)PyPageSpan_get_last_ts, NULL,
     "Alias for end_ts (inclusive last timestamp).", NULL},
    {"closed", (getter)PyPageSpan_get_closed, NULL,
     "True if span is closed.", NULL},
    {NULL, NULL, NULL, NULL, NULL}
};

/*===========================================================================
 * Type Specification
 *===========================================================================*/

static PyType_Slot PyPageSpan_slots[] = {
    {Py_tp_doc, PyDoc_STR(
        "Zero-copy view of timestamps from a single page slice.\n\n"
        "The .timestamps property returns a memoryview directly backed by\n"
        "page memory. Cannot be instantiated directly; use Timelog.views()\n"
        "(alias: page_spans()).\n\n"
        "Implements the PEP 688 buffer protocol over read-only int64 (format\n"
        "'q') timestamps, so it is a collections.abc.Buffer and works with\n"
        "memoryview(). The encoded handle array is never exposed numerically;\n"
        "decoded payloads are reached via .objects() as real Python objects."
    )},
    {Py_tp_dealloc, (void*)PyPageSpan_dealloc},
    {Py_tp_traverse, (void*)PyPageSpan_traverse},
    {Py_tp_clear, (void*)PyPageSpan_clear},
    {Py_tp_methods, PyPageSpan_methods},
    {Py_tp_getset, PyPageSpan_getset},
    {Py_bf_getbuffer, (void*)pagespan_getbuffer},
    {Py_bf_releasebuffer, (void*)pagespan_releasebuffer},
    {Py_sq_length, (void*)PyPageSpan_length},
    /* No Py_tp_call / vectorcall slot (see PyTimelog_slots): PageSpan exposes
     * only the read-only int64 timestamp buffer above, never a call protocol. */
    {0, NULL}
};

static PyType_Spec PyPageSpan_spec = {
    .name = "timelog._timelog.PageSpan",
    .basicsize = sizeof(PyPageSpan),
    .itemsize = 0,
    .flags = Py_TPFLAGS_DEFAULT |
             Py_TPFLAGS_HAVE_GC |
             Py_TPFLAGS_IMMUTABLETYPE |
             Py_TPFLAGS_DISALLOW_INSTANTIATION,
    .slots = PyPageSpan_slots,
};

PyObject* TlPy_CreatePageSpanType(PyObject* module)
{
    return PyType_FromModuleAndSpec(module, &PyPageSpan_spec, NULL);
}

TL_PY_DEFINE_CHECK(TlPyPageSpan_Check, type_pagespan)
