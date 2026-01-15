/**
 * @file py_span_objects.c
 * @brief PyPageSpanObjectsView CPython extension type implementation (Core API Integration)
 *
 * Implements lazy access to decoded Python objects from a PageSpan.
 * Uses span->h[] pointer directly (borrowed from core owner's snapshot).
 *
 * See: docs/timelog_v2_lld_pagespan_cpython_bindings_update.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_span_objects.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_handle.h"

/*
 * NO storage headers needed - span->h and span->len provide direct access.
 */

/*===========================================================================
 * Py_NewRef Compatibility
 *===========================================================================*/

#if PY_VERSION_HEX < 0x030A0000
#ifndef TL_Py_NewRef_DEFINED
#define TL_Py_NewRef_DEFINED
static inline PyObject* TL_Py_NewRef_OV(PyObject* obj) {
    Py_INCREF(obj);
    return obj;
}
#define Py_NewRef TL_Py_NewRef_OV
#endif
#endif

/*===========================================================================
 * Block Direct Construction
 *===========================================================================*/

static PyObject* PyPageSpanObjectsView_new_error(PyTypeObject* type,
                                                  PyObject* args,
                                                  PyObject* kwds)
{
    (void)type;
    (void)args;
    (void)kwds;

    PyErr_SetString(PyExc_TypeError,
        "PageSpanObjectsView cannot be instantiated directly; "
        "use PageSpan.objects()");
    return NULL;
}

/*===========================================================================
 * Factory Function
 *===========================================================================*/

PyObject* PyPageSpanObjectsView_Create(PyObject* span)
{
    if (!PyPageSpan_Check(span)) {
        PyErr_SetString(PyExc_TypeError, "expected PageSpan");
        return NULL;
    }

    PyPageSpan* span_obj = (PyPageSpan*)span;
    if (span_obj->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    PyPageSpanObjectsView* self = PyObject_New(PyPageSpanObjectsView,
                                                &PyPageSpanObjectsView_Type);
    if (!self) {
        return NULL;
    }

    self->span = Py_NewRef(span);
    return (PyObject*)self;
}

/*===========================================================================
 * Dealloc
 *===========================================================================*/

static void PyPageSpanObjectsView_dealloc(PyPageSpanObjectsView* self)
{
    Py_XDECREF(self->span);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * Sequence Protocol
 *===========================================================================*/

static Py_ssize_t PyPageSpanObjectsView_length(PyPageSpanObjectsView* self)
{
    PyPageSpan* span = (PyPageSpan*)self->span;
    if (span->closed) {
        return 0;
    }
    return (Py_ssize_t)span->len;
}

static PyObject* PyPageSpanObjectsView_getitem(PyPageSpanObjectsView* self,
                                                Py_ssize_t index)
{
    PyPageSpan* span = (PyPageSpan*)self->span;

    if (span->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /*
     * Check handle pointer availability.
     * span->h may be NULL if handles are unavailable (future-proofing).
     */
    if (span->h == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }

    const Py_ssize_t len = (Py_ssize_t)span->len;

    /* Handle negative indices */
    if (index < 0) {
        index += len;
    }

    if (index < 0 || index >= len) {
        PyErr_SetString(PyExc_IndexError, "index out of range");
        return NULL;
    }

    /*
     * Access handle directly via span->h[index].
     * This is borrowed from the owner's snapshot and valid while span is open.
     */
    tl_handle_t h = span->h[index];
    PyObject* obj = tl_py_handle_decode(h);

    /* Defensive NULL check (handle could be corrupted) */
    if (!obj) {
        PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
        return NULL;
    }

    return Py_NewRef(obj);
}

static PySequenceMethods objectsview_as_sequence = {
    .sq_length = (lenfunc)PyPageSpanObjectsView_length,
    .sq_item = (ssizeargfunc)PyPageSpanObjectsView_getitem,
};

/*===========================================================================
 * Iterator Protocol
 *===========================================================================*/

typedef struct {
    PyObject_HEAD
    PyObject* view;     /* Strong ref to objects view */
    Py_ssize_t index;   /* Current position */
} PyPageSpanObjectsViewIter;

/* Forward declaration (non-static, exported via header) */
extern PyTypeObject PyPageSpanObjectsViewIter_Type;

static void objectsviewiter_dealloc(PyPageSpanObjectsViewIter* self)
{
    Py_XDECREF(self->view);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

static PyObject* objectsviewiter_next(PyPageSpanObjectsViewIter* self)
{
    PyPageSpanObjectsView* view = (PyPageSpanObjectsView*)self->view;
    PyPageSpan* span = (PyPageSpan*)view->span;

    if (span->closed) {
        return NULL;  /* StopIteration */
    }

    /*
     * Check handle pointer availability.
     * span->h may be NULL if handles are unavailable (future-proofing).
     */
    if (span->h == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }

    const Py_ssize_t len = (Py_ssize_t)span->len;

    if (self->index >= len) {
        return NULL;  /* StopIteration */
    }

    /*
     * Access handle directly via span->h[index].
     * This is borrowed from the owner's snapshot and valid while span is open.
     */
    tl_handle_t h = span->h[self->index];
    PyObject* obj = tl_py_handle_decode(h);

    /* Defensive NULL check (handle could be corrupted) */
    if (!obj) {
        PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
        return NULL;
    }

    self->index++;
    return Py_NewRef(obj);
}

/* Exported (non-static) so module.c can call PyType_Ready */
PyTypeObject PyPageSpanObjectsViewIter_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.PageSpanObjectsViewIter",
    .tp_basicsize = sizeof(PyPageSpanObjectsViewIter),
    .tp_dealloc = (destructor)objectsviewiter_dealloc,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_iter = PyObject_SelfIter,
    .tp_iternext = (iternextfunc)objectsviewiter_next,
};

static PyObject* PyPageSpanObjectsView_iter(PyPageSpanObjectsView* self)
{
    /* Type is readied by module init (module.c) - no lazy init needed.
     * This avoids a potential race condition in free-threaded Python builds.
     */

    PyPageSpanObjectsViewIter* iter = PyObject_New(PyPageSpanObjectsViewIter,
                                                    &PyPageSpanObjectsViewIter_Type);
    if (!iter) {
        return NULL;
    }

    iter->view = Py_NewRef((PyObject*)self);
    iter->index = 0;

    return (PyObject*)iter;
}

/*===========================================================================
 * Methods
 *===========================================================================*/

static PyObject* PyPageSpanObjectsView_copy(PyPageSpanObjectsView* self,
                                             PyObject* noargs)
{
    (void)noargs;

    PyPageSpan* span = (PyPageSpan*)self->span;

    if (span->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /*
     * Check handle pointer availability.
     * span->h may be NULL if handles are unavailable (future-proofing).
     */
    if (span->h == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }

    const Py_ssize_t len = (Py_ssize_t)span->len;

    PyObject* list = PyList_New(len);
    if (!list) {
        return NULL;
    }

    for (Py_ssize_t i = 0; i < len; i++) {
        /*
         * Access handle directly via span->h[i].
         * This is borrowed from the owner's snapshot and valid while span is open.
         */
        tl_handle_t h = span->h[i];
        PyObject* obj = tl_py_handle_decode(h);

        /* Defensive NULL check */
        if (!obj) {
            Py_DECREF(list);
            PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
            return NULL;
        }

        PyList_SET_ITEM(list, i, Py_NewRef(obj));
    }

    return list;
}

static PyMethodDef PyPageSpanObjectsView_methods[] = {
    {"copy", (PyCFunction)PyPageSpanObjectsView_copy, METH_NOARGS,
     "copy() -> list[object]\n\n"
     "Return a copy of all objects as a Python list."},
    {NULL, NULL, 0, NULL}
};

/*===========================================================================
 * Type Object
 *===========================================================================*/

PyTypeObject PyPageSpanObjectsView_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.PageSpanObjectsView",
    .tp_doc = PyDoc_STR(
        "Lazy sequence view over decoded Python objects from a PageSpan.\n\n"
        "Supports len(), indexing, and iteration.\n"
        "Cannot be instantiated directly; use PageSpan.objects()."
    ),
    .tp_basicsize = sizeof(PyPageSpanObjectsView),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_new = PyPageSpanObjectsView_new_error,
    .tp_dealloc = (destructor)PyPageSpanObjectsView_dealloc,
    .tp_as_sequence = &objectsview_as_sequence,
    .tp_iter = (getiterfunc)PyPageSpanObjectsView_iter,
    .tp_methods = PyPageSpanObjectsView_methods,
};
