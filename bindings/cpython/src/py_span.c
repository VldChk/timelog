/**
 * @file py_span.c
 * @brief PyPageSpan CPython extension type implementation (Core API Integration)
 *
 * Implements zero-copy timestamp exposure via the CPython buffer protocol.
 * Delegates ownership management to core tl_pagespan_owner_t.
 *
 * See: docs/V2/timelog_v2_lld_storage_pages.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <string.h>  /* For memset */

#include "timelogpy/py_span.h"
#include "timelogpy/py_span_objects.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_timelog.h"

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static void pagespan_cleanup(PyPageSpan* self);

/*===========================================================================
 * Block Direct Construction
 *
 * PageSpans are only created via factory (page_spans iterator).
 *===========================================================================*/

static PyObject* PyPageSpan_new_error(PyTypeObject* type,
                                       PyObject* args,
                                       PyObject* kwds)
{
    (void)type;
    (void)args;
    (void)kwds;

    PyErr_SetString(PyExc_TypeError,
        "PageSpan cannot be instantiated directly; "
        "use Timelog.page_spans()");
    return NULL;
}

/*===========================================================================
 * PageSpan Creation from Core View
 *
 * This replaces PyPageSpan_Create which took page pointer + row indices.
 * Now we take a core view and CONSUME its owner reference.
 *===========================================================================*/

PyObject* PyPageSpan_FromView(tl_pagespan_view_t* view, PyObject* timelog)
{
    /*
     * Validate inputs.
     * On any failure, the caller must call tl_pagespan_view_release().
     */
    if (view == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "view is NULL");
        return NULL;
    }
    if (view->owner == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "view->owner is NULL");
        return NULL;
    }
    if (timelog == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "timelog is NULL");
        return NULL;
    }
    if (!PyTimelog_Check(timelog)) {
        PyErr_SetString(PyExc_TypeError, "expected PyTimelog");
        return NULL;
    }

    /*
     * Allocate the Python object with GC support.
     */
    PyPageSpan* self = PyObject_GC_New(PyPageSpan, &PyPageSpan_Type);
    if (self == NULL) {
        /* Allocation failed - caller must release view */
        return NULL;
    }

    /*
     * Transfer ownership from view to span.
     * The view's owner reference is CONSUMED - no incref needed.
     * We set view->owner = NULL to prevent accidental double-decref.
     */
    self->owner = view->owner;
    view->owner = NULL;

    /*
     * Store strong reference to timelog for GC visibility.
     * The core owner is opaque, so GC cannot traverse it.
     */
    self->timelog = Py_NewRef(timelog);

    /*
     * Copy view pointers. These are borrowed from the owner's snapshot
     * and remain valid as long as the owner is alive.
     */
    self->ts = view->ts;
    self->h = view->h;
    self->len = view->len;
    self->first_ts = view->first_ts;
    self->last_ts = view->last_ts;

    /*
     * Initialize buffer protocol state.
     */
    self->shape[0] = 0;
    self->strides[0] = 0;
    self->exports = 0;
    self->closed = 0;

    /*
     * Track with GC after all fields are initialized.
     */
    PyObject_GC_Track((PyObject*)self);
    return (PyObject*)self;
}

/*===========================================================================
 * Cleanup (Single Source of Truth)
 *
 * Releases owner reference and clears borrowed pointers.
 * The core owner's release hook (set during iterator creation) handles
 * pins_exit and Py_DECREF of the iteration-level timelog reference.
 *===========================================================================*/

static void pagespan_cleanup(PyPageSpan* self)
{
    if (self->closed) {
        return;
    }
    self->closed = 1;

    /*
     * Clear borrowed pointers first (before releasing owner).
     * After owner is released, snapshot may be freed and pointers invalid.
     */
    self->ts = NULL;
    self->h = NULL;

    /*
     * Release owner reference via core API.
     * When refcount reaches 0, core calls the release hook which handles
     * pins_exit and Py_DECREF of the hook context's timelog reference.
     */
    tl_pagespan_owner_t* owner = self->owner;
    self->owner = NULL;

    if (owner != NULL) {
        tl_pagespan_owner_decref(owner);
    }

    /*
     * Clear our direct timelog reference (for GC visibility).
     * This is separate from the hook context's reference.
     *
     * Exception preservation: Py_CLEAR may trigger __del__ which can
     * clobber active exceptions (e.g., when __exit__ calls cleanup).
     * Per LLD-B6, preserve exception state across cleanup.
     */
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

static int PyPageSpan_traverse(PyPageSpan* self, visitproc visit, void* arg)
{
    /*
     * Visit timelog for GC cycle detection.
     * The core owner is opaque and cannot be traversed directly.
     */
    Py_VISIT(self->timelog);
    return 0;
}

static int PyPageSpan_clear(PyPageSpan* self)
{
    /*
     * GC clear - called to break reference cycles.
     * Cannot cleanup if buffers are exported.
     */
    if (self->exports > 0) {
        return 0;
    }
    pagespan_cleanup(self);
    return 0;
}

static void PyPageSpan_dealloc(PyPageSpan* self)
{
    PyObject_GC_UnTrack(self);
    /*
     * Note: if exports > 0 at dealloc, something went very wrong.
     * We cleanup anyway to avoid leaks.
     */
    pagespan_cleanup(self);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * Buffer Protocol
 *
 * Exposes timestamps as a read-only 1D array of int64.
 * Uses span->ts and span->len instead of page pointer + row indices.
 *===========================================================================*/

/* Static format string - must outlive buffer view */
static const char* PAGESPAN_TS_FORMAT = "q";

static int pagespan_getbuffer(PyObject* exporter, Py_buffer* view, int flags)
{
    PyPageSpan* self = (PyPageSpan*)exporter;

    /*
     * CPython contract: on error, view->obj must be NULL.
     */
    view->obj = NULL;

    if (self->closed || self->ts == NULL) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return -1;
    }
    if (flags & PyBUF_WRITABLE) {
        PyErr_SetString(PyExc_BufferError, "PageSpan buffer is read-only");
        return -1;
    }

    const Py_ssize_t n = (Py_ssize_t)self->len;
    void* ptr = (void*)self->ts;

    /*
     * Overflow guard: ensure n * sizeof(tl_ts_t) doesn't overflow Py_ssize_t.
     * This is defensive - page sizes should never approach this limit.
     */
    if (n > PY_SSIZE_T_MAX / (Py_ssize_t)sizeof(tl_ts_t)) {
        PyErr_SetString(PyExc_OverflowError, "PageSpan too large for buffer");
        return -1;
    }

    /*
     * Request-independent fields (ALWAYS set per CPython docs).
     */
    view->obj = Py_NewRef(exporter);
    view->buf = ptr;
    view->len = n * (Py_ssize_t)sizeof(tl_ts_t);
    view->readonly = 1;
    view->itemsize = (Py_ssize_t)sizeof(tl_ts_t);
    view->ndim = 1;  /* ALWAYS 1 - request-independent */

    /*
     * Request-dependent fields.
     */
    view->format = (flags & PyBUF_FORMAT) ? (char*)PAGESPAN_TS_FORMAT : NULL;

    if (flags & PyBUF_ND) {
        self->shape[0] = n;
        view->shape = self->shape;
    } else {
        view->shape = NULL;
    }

    if (flags & PyBUF_STRIDES) {
        self->strides[0] = (Py_ssize_t)sizeof(tl_ts_t);
        view->strides = self->strides;
    } else {
        view->strides = NULL;
    }

    view->suboffsets = NULL;
    view->internal = NULL;

    self->exports++;
    return 0;
}

static void pagespan_releasebuffer(PyObject* exporter, Py_buffer* view)
{
    PyPageSpan* self = (PyPageSpan*)exporter;
    (void)view;

    if (self->exports > 0) {
        self->exports--;
    }
}

static PyBufferProcs pagespan_as_buffer = {
    .bf_getbuffer = pagespan_getbuffer,
    .bf_releasebuffer = pagespan_releasebuffer,
};

/*===========================================================================
 * Methods
 *===========================================================================*/

static PyObject* PyPageSpan_close(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;

    if (self->exports > 0) {
        PyErr_SetString(PyExc_BufferError,
            "cannot close PageSpan: buffer is exported");
        return NULL;
    }

    pagespan_cleanup(self);
    Py_RETURN_NONE;
}

static PyObject* PyPageSpan_enter(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;
    return Py_NewRef((PyObject*)self);
}

static PyObject* PyPageSpan_exit(PyPageSpan* self, PyObject* args)
{
    (void)args;

    if (self->exports > 0) {
        /*
         * Per Python convention, __exit__ should NOT raise for cleanup
         * issues that aren't actual exceptions being propagated.
         * Users who need strict error checking should call close() explicitly,
         * which DOES raise BufferError when exports > 0.
         *
         * Returning False signals "do not suppress any exception".
         */
        Py_RETURN_FALSE;
    }

    pagespan_cleanup(self);
    Py_RETURN_FALSE;  /* Don't suppress exceptions */
}

static PyObject* PyPageSpan_objects(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /*
     * Fail early if handles are not available.
     * This gives a clear error at .objects() rather than deferring
     * to the first access (which would raise RuntimeError).
     */
    if (self->h == NULL) {
        PyErr_SetString(PyExc_RuntimeError,
            "handles not available in this span");
        return NULL;
    }

    return PyPageSpanObjectsView_Create((PyObject*)self);
}

static PyObject* PyPageSpan_copy_timestamps(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    const Py_ssize_t n = (Py_ssize_t)self->len;
    PyObject* list = PyList_New(n);
    if (list == NULL) {
        return NULL;
    }

    for (Py_ssize_t i = 0; i < n; i++) {
        PyObject* val = PyLong_FromLongLong((long long)self->ts[i]);
        if (val == NULL) {
            Py_DECREF(list);
            return NULL;
        }
        PyList_SET_ITEM(list, i, val);
    }

    return list;
}

static PyObject* PyPageSpan_copy(PyPageSpan* self, PyObject* noargs)
{
    /* Current behavior: copy() returns the same as copy_timestamps(). */
    return PyPageSpan_copy_timestamps(self, noargs);
}

/*===========================================================================
 * Sequence Protocol (__len__)
 *===========================================================================*/

static Py_ssize_t PyPageSpan_length(PyPageSpan* self)
{
    if (self->closed) {
        return 0;
    }
    return (Py_ssize_t)self->len;
}

static PySequenceMethods pagespan_as_sequence = {
    .sq_length = (lenfunc)PyPageSpan_length,
};

/*===========================================================================
 * Properties
 *
 * Use cached first_ts/last_ts instead of page pointer dereference.
 *===========================================================================*/

static PyObject* PyPageSpan_get_timestamps(PyPageSpan* self, void* closure)
{
    (void)closure;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    return PyMemoryView_FromObject((PyObject*)self);
}

static PyObject* PyPageSpan_get_start_ts(PyPageSpan* self, void* closure)
{
    (void)closure;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /*
     * Use cached first_ts from view - no pointer dereference needed.
     * For valid spans, len > 0 is guaranteed by core iter_next.
     */
    return PyLong_FromLongLong((long long)self->first_ts);
}

static PyObject* PyPageSpan_get_end_ts(PyPageSpan* self, void* closure)
{
    (void)closure;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /*
     * Use cached last_ts from view - no pointer dereference needed.
     * For valid spans, len > 0 is guaranteed by core iter_next.
     */
    return PyLong_FromLongLong((long long)self->last_ts);
}

static PyObject* PyPageSpan_get_last_ts(PyPageSpan* self, void* closure)
{
    return PyPageSpan_get_end_ts(self, closure);
}

static PyObject* PyPageSpan_get_closed(PyPageSpan* self, void* closure)
{
    (void)closure;
    return PyBool_FromLong(self->closed);
}

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
    {"copy", (PyCFunction)PyPageSpan_copy, METH_NOARGS,
     "copy() -> list[int]\n\n"
     "Return a copy of timestamps as a Python list."},
    {"__enter__", (PyCFunction)PyPageSpan_enter, METH_NOARGS,
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
 * Type Object
 *===========================================================================*/

PyTypeObject PyPageSpan_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.PageSpan",
    .tp_doc = PyDoc_STR(
        "Zero-copy view of timestamps from a single page slice.\n\n"
        "The .timestamps property returns a memoryview directly backed by\n"
        "page memory. Cannot be instantiated directly; use Timelog.page_spans()."
    ),
    .tp_basicsize = sizeof(PyPageSpan),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_GC,
    .tp_new = PyPageSpan_new_error,
    .tp_dealloc = (destructor)PyPageSpan_dealloc,
    .tp_traverse = (traverseproc)PyPageSpan_traverse,
    .tp_clear = (inquiry)PyPageSpan_clear,
    .tp_free = PyObject_GC_Del,
    .tp_as_buffer = &pagespan_as_buffer,
    .tp_as_sequence = &pagespan_as_sequence,
    .tp_methods = PyPageSpan_methods,
    .tp_getset = PyPageSpan_getset,
};
