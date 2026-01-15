/**
 * @file py_span.c
 * @brief PyPageSpan CPython extension type implementation (LLD-B4)
 *
 * Implements zero-copy timestamp exposure via the CPython buffer protocol.
 *
 * See: docs/timelog_v1_lld_B4_pagespan_zero_copy.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_span.h"
#include "timelogpy/py_span_objects.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_timelog.h"

/* Internal headers for page access */
#include "storage/tl_page.h"

/* For tl_snapshot_alloc */
#include "query/tl_snapshot.h"

/* For tl__malloc/tl__free */
#include "internal/tl_alloc.h"

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
 * Shared Snapshot Owner Implementation
 *===========================================================================*/

tl_py_span_owner_t* tl_py_span_owner_create(PyObject* timelog,
                                             tl_snapshot_t* snapshot,
                                             tl_alloc_ctx_t* alloc)
{
    /* Caller must have already called:
     *   1. tl_py_pins_enter(handle_ctx) -- BEFORE snapshot acquire
     *   2. tl_snapshot_acquire() to get snapshot
     * This function assumes pins are already held.
     */
    if (!timelog || !PyTimelog_Check(timelog)) {
        PyErr_SetString(PyExc_TypeError, "expected PyTimelog");
        return NULL;
    }

    if (!snapshot) {
        PyErr_SetString(PyExc_RuntimeError, "snapshot is NULL");
        return NULL;
    }

    if (!alloc) {
        PyErr_SetString(PyExc_RuntimeError, "allocator is NULL");
        return NULL;
    }

    PyTimelog* tl_obj = (PyTimelog*)timelog;

    tl_py_span_owner_t* owner = tl__malloc(alloc, sizeof(tl_py_span_owner_t));
    if (!owner) {
        PyErr_NoMemory();
        return NULL;
    }

    owner->refcnt = 1;
    owner->timelog = Py_NewRef(timelog);
    owner->snapshot = snapshot;
    owner->handle_ctx = &tl_obj->handle_ctx;
    owner->alloc = alloc;

    /* NOTE: pins_enter was called by the caller BEFORE snapshot_acquire.
     * This function does NOT call pins_enter -- it assumes pins are held.
     */

    return owner;
}

void tl_py_span_owner_incref(tl_py_span_owner_t* owner)
{
    if (owner) {
        owner->refcnt++;
    }
}

static void span_owner_destroy(tl_py_span_owner_t* owner)
{
    if (!owner) return;

    /* Move pointers to locals BEFORE Python code (reentrancy safety) */
    tl_snapshot_t* snap = owner->snapshot;
    owner->snapshot = NULL;

    tl_py_handle_ctx_t* ctx = owner->handle_ctx;
    owner->handle_ctx = NULL;

    PyObject* timelog = owner->timelog;
    owner->timelog = NULL;

    tl_alloc_ctx_t* alloc = owner->alloc;
    owner->alloc = NULL;

    /* Release order (critical):
     * 1. Release snapshot (no Python code)
     * 2. Exit pins and maybe drain (may run Py_DECREF)
     * 3. DECREF timelog owner (may run Python code)
     */
    if (snap) {
        tl_snapshot_release(snap);
    }

    /* Free owner BEFORE decref'ing timelog.
     * The allocator is borrowed from the timelog, so we must use it
     * before the timelog is potentially destroyed by DECREF.
     */
    tl__free(alloc, owner);

    /* Preserve exception state across drain/DECREF */
    PyObject *exc_type, *exc_value, *exc_tb;
    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);

    if (ctx) {
        tl_py_pins_exit_and_maybe_drain(ctx);
    }

    Py_XDECREF(timelog);

    PyErr_Restore(exc_type, exc_value, exc_tb);
}

void tl_py_span_owner_decref(tl_py_span_owner_t* owner)
{
    if (owner && --owner->refcnt == 0) {
        span_owner_destroy(owner);
    }
}

/*===========================================================================
 * PageSpan Creation
 *===========================================================================*/

PyObject* PyPageSpan_Create(tl_py_span_owner_t* owner,
                            const tl_page_t* page,
                            size_t row_start,
                            size_t row_end)
{
    PyPageSpan* self = PyObject_GC_New(PyPageSpan, &PyPageSpan_Type);
    if (!self) {
        return NULL;
    }

    tl_py_span_owner_incref(owner);
    self->owner = owner;
    self->page = page;
    self->row_start = row_start;
    self->row_end = row_end;
    self->shape[0] = 0;
    self->strides[0] = 0;
    self->exports = 0;
    self->closed = 0;

    PyObject_GC_Track((PyObject*)self);
    return (PyObject*)self;
}

/*===========================================================================
 * Cleanup (Single Source of Truth)
 *===========================================================================*/

static void pagespan_cleanup(PyPageSpan* self)
{
    if (self->closed) {
        return;
    }
    self->closed = 1;

    /* Clear borrowed pointers */
    self->page = NULL;

    /* Release owner reference */
    tl_py_span_owner_t* owner = self->owner;
    self->owner = NULL;

    if (owner) {
        tl_py_span_owner_decref(owner);
    }
}

/*===========================================================================
 * GC Support
 *===========================================================================*/

static int PyPageSpan_traverse(PyPageSpan* self, visitproc visit, void* arg)
{
    /* Visit the timelog held by our owner.
     * This allows the GC to detect cycles involving PageSpan -> owner -> timelog.
     * Per CPython docs, tp_traverse must visit every PyObject* the object contains.
     */
    if (self->owner && self->owner->timelog) {
        Py_VISIT(self->owner->timelog);
    }
    return 0;
}

static int PyPageSpan_clear(PyPageSpan* self)
{
    /* Can't cleanup if buffers exported */
    if (self->exports > 0) {
        return 0;
    }
    pagespan_cleanup(self);
    return 0;
}

static void PyPageSpan_dealloc(PyPageSpan* self)
{
    PyObject_GC_UnTrack(self);
    /* Note: if exports > 0 at dealloc, something went very wrong.
     * We cleanup anyway to avoid leaks. */
    pagespan_cleanup(self);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * Buffer Protocol
 *===========================================================================*/

/* Static format string - must outlive buffer view */
static const char* PAGESPAN_TS_FORMAT = "q";

static int pagespan_getbuffer(PyObject* exporter, Py_buffer* view, int flags)
{
    PyPageSpan* self = (PyPageSpan*)exporter;

    /* CPython contract: on error, view->obj must be NULL */
    view->obj = NULL;

    if (self->closed || self->page == NULL) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return -1;
    }
    if (flags & PyBUF_WRITABLE) {
        PyErr_SetString(PyExc_BufferError, "PageSpan buffer is read-only");
        return -1;
    }

    const Py_ssize_t n = (Py_ssize_t)(self->row_end - self->row_start);
    void* ptr = (void*)(self->page->ts + self->row_start);

    /* Request-independent fields (ALWAYS set per CPython docs) */
    view->obj = Py_NewRef(exporter);
    view->buf = ptr;
    view->len = n * (Py_ssize_t)sizeof(tl_ts_t);
    view->readonly = 1;
    view->itemsize = (Py_ssize_t)sizeof(tl_ts_t);
    view->ndim = 1;  /* ALWAYS 1 - request-independent */

    /* Request-dependent fields */
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
        /* Per Python convention, __exit__ should NOT raise for cleanup
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

    return PyPageSpanObjectsView_Create((PyObject*)self);
}

static PyObject* PyPageSpan_copy_timestamps(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    Py_ssize_t n = (Py_ssize_t)(self->row_end - self->row_start);
    PyObject* list = PyList_New(n);
    if (!list) {
        return NULL;
    }

    const tl_ts_t* ts = self->page->ts + self->row_start;
    for (Py_ssize_t i = 0; i < n; i++) {
        PyObject* val = PyLong_FromLongLong((long long)ts[i]);
        if (!val) {
            Py_DECREF(list);
            return NULL;
        }
        PyList_SET_ITEM(list, i, val);
    }

    return list;
}

static PyObject* PyPageSpan_copy(PyPageSpan* self, PyObject* noargs)
{
    /* For V1, copy() returns same as copy_timestamps() */
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
    return (Py_ssize_t)(self->row_end - self->row_start);
}

static PySequenceMethods pagespan_as_sequence = {
    .sq_length = (lenfunc)PyPageSpan_length,
};

/*===========================================================================
 * Properties
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

    if (self->row_start >= self->row_end) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is empty");
        return NULL;
    }

    return PyLong_FromLongLong((long long)self->page->ts[self->row_start]);
}

static PyObject* PyPageSpan_get_end_ts(PyPageSpan* self, void* closure)
{
    (void)closure;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    if (self->row_start >= self->row_end) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is empty");
        return NULL;
    }

    /* end_ts is the LAST timestamp (inclusive), not row_end */
    return PyLong_FromLongLong((long long)self->page->ts[self->row_end - 1]);
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
     "Last timestamp in this span.", NULL},
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
