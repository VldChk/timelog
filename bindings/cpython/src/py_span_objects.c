/**
 * @file py_span_objects.c
 * @brief PyPageSpanObjectsView CPython extension type implementation
 *
 * Implements lazy access to decoded Python objects from a PageSpan.
 * Uses span->h[] pointer directly (borrowed from core owner's snapshot).
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_compat.h"
#include "timelogpy/py_span_objects.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_handle.h"
#include "query/tl_pagespan_iter.h"  /* for tl_pagespan_owner_incref/decref */


/*===========================================================================
 * Factory Function
 *===========================================================================*/

PyObject* PyPageSpanObjectsView_Create(PyObject* span)
{
    tl_py_module_state_t* mod_st = TlPy_StateFromObject(span);
    if (mod_st == NULL) {
        return NULL;
    }
    if (!TlPyPageSpan_Check(span, mod_st)) {
        PyErr_SetString(PyExc_TypeError, "expected PageSpan");
        return NULL;
    }

    PyPageSpan* span_obj = (PyPageSpan*)span;
    int closed;
    TL_PY_OBJ_LOCK(span_obj);
    closed = span_obj->closed;
    TL_PY_OBJ_UNLOCK();
    if (closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    PyTypeObject* view_type = (PyTypeObject*)mod_st->type_pagespan_objects_view;
    PyPageSpanObjectsView* self =
        (PyPageSpanObjectsView*)view_type->tp_alloc(view_type, 0);
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
    TL_PY_GC_DEALLOC(self, Py_XDECREF(self->span));
}

static int PyPageSpanObjectsView_traverse(PyPageSpanObjectsView* self,
                                          visitproc visit,
                                          void* arg)
{
    Py_VISIT(Py_TYPE(self));
    Py_VISIT(self->span);
    return 0;
}

static int PyPageSpanObjectsView_clear(PyPageSpanObjectsView* self)
{
    Py_CLEAR(self->span);
    return 0;
}

/*===========================================================================
 * Sequence Protocol
 *===========================================================================*/

static Py_ssize_t PyPageSpanObjectsView_length(PyPageSpanObjectsView* self)
{
    if (self->span == NULL) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return -1;
    }

    PyPageSpan* span = (PyPageSpan*)self->span;
    Py_ssize_t n;
    int closed;

    TL_PY_OBJ_LOCK(span);
    closed = span->closed;
    n = closed ? -1 : (Py_ssize_t)span->len;
    TL_PY_OBJ_UNLOCK();

    if (closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return -1;
    }
    return n;
}

static PyObject* PyPageSpanObjectsView_getitem(PyPageSpanObjectsView* self,
                                                Py_ssize_t index)
{
    if (self->span == NULL) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    PyPageSpan* span = (PyPageSpan*)self->span;

    /* Decode AND Py_NewRef the payload UNDER the span's CS. Holding the
     * span's CS prevents this span's close() from detaching the owner, so
     * its snapshot (and the pin that blocks retired-object drain) stay
     * live — the decoded object cannot be freed before we incref it. The
     * incref is a lone INCREF of a distinct object (permitted, py_compat.h);
     * Py_DECREF on error is moot since we only succeed here. */
    int err = 0; /* 0=ok 1=closed 2=no-h 3=out-of-range 4=bad-handle */
    PyObject* obj = NULL;

    TL_PY_OBJ_LOCK(span);
    if (span->closed) {
        err = 1;
    } else if (span->h == NULL) {
        err = 2;
    } else {
        Py_ssize_t len = (Py_ssize_t)span->len;
        Py_ssize_t adj = index < 0 ? index + len : index;
        if (adj < 0 || adj >= len) {
            err = 3;
        } else {
            PyObject* decoded = tl_py_handle_decode(span->h[adj]);
            if (decoded == NULL) {
                err = 4;
            } else {
                obj = Py_NewRef(decoded);
            }
        }
    }
    TL_PY_OBJ_UNLOCK();

    if (err == 1) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }
    if (err == 2) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }
    if (err == 3) {
        PyErr_SetString(PyExc_IndexError, "index out of range");
        return NULL;
    }
    if (err == 4) {
        PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
        return NULL;
    }
    return obj;
}

/*===========================================================================
 * Iterator Protocol
 *===========================================================================*/

typedef struct {
    PyObject_HEAD
    PyObject* view;     /* Strong ref to objects view */
    Py_ssize_t index;   /* Current position */
} PyPageSpanObjectsViewIter;

static void objectsviewiter_dealloc(PyPageSpanObjectsViewIter* self)
{
    TL_PY_GC_DEALLOC(self, Py_XDECREF(self->view));
}

static int objectsviewiter_traverse(PyPageSpanObjectsViewIter* self,
                                    visitproc visit,
                                    void* arg)
{
    Py_VISIT(Py_TYPE(self));
    Py_VISIT(self->view);
    return 0;
}

static int objectsviewiter_clear(PyPageSpanObjectsViewIter* self)
{
    Py_CLEAR(self->view);
    return 0;
}

static PyObject* objectsviewiter_next(PyPageSpanObjectsViewIter* self)
{
    PyPageSpanObjectsView* view = (PyPageSpanObjectsView*)self->view;
    if (view == NULL) {
        return NULL;  /* StopIteration — cleared by GC */
    }
    PyPageSpan* span = (PyPageSpan*)view->span;
    if (span == NULL) {
        return NULL;
    }

    /*
     * Two objects need protection here:
     *  - self->index (read+advance on this iter)
     *  - span->closed/h/len (read on the span)
     * Use the two-object critical section to acquire both atomically and
     * avoid lock-order issues. The payload is decoded AND Py_NewRef'd
     * UNDER the span's CS (held via LOCK2): the span's CS prevents its
     * close()/owner-detach, so the snapshot + drain-blocking pin stay live
     * and the decoded object cannot be freed before we incref it. Only the
     * final result return happens after the CS.
     */
    int err = 0;  /* 0=ok 1=eof 2=no-h 3=bad-handle 4=closed */
    PyObject* obj = NULL;

    TL_PY_OBJ_LOCK2(self, span);
    if (self->view == NULL) {
        err = 1;
    } else if (span->closed) {
        err = 4;
    } else if (span->h == NULL) {
        err = 2;
    } else {
        Py_ssize_t len = (Py_ssize_t)span->len;
        if (self->index >= len) {
            err = 1;
        } else {
            PyObject* decoded = tl_py_handle_decode(span->h[self->index]);
            if (decoded == NULL) {
                err = 3;
            } else {
                obj = Py_NewRef(decoded);
                self->index++;
            }
        }
    }
    TL_PY_OBJ_UNLOCK2();

    if (err == 1) {
        return NULL;  /* StopIteration */
    }
    if (err == 2) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }
    if (err == 3) {
        PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
        return NULL;
    }
    if (err == 4) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }
    return obj;
}

static PyObject* PyPageSpanObjectsView_iter(PyPageSpanObjectsView* self)
{
    tl_py_module_state_t* mod_st = TlPy_StateFromObject((PyObject*)self);
    if (mod_st == NULL) {
        return NULL;
    }

    PyTypeObject* iter_type = (PyTypeObject*)mod_st->type_pagespan_objects_view_iter;
    PyPageSpanObjectsViewIter* iter =
        (PyPageSpanObjectsViewIter*)iter_type->tp_alloc(iter_type, 0);
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

    if (self->span == NULL) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    PyPageSpan* span = (PyPageSpan*)self->span;

    /* Pin the owner across the copy so the underlying h[] array cannot be
     * freed by a concurrent close. Read len + h + owner under the span's
     * CS, incref the owner, release CS, then iterate using the pinned
     * pointers. */
    int err = 0;  /* 0=ok 1=closed 2=no-h */
    Py_ssize_t len = 0;
    const tl_handle_t* h_local = NULL;
    tl_pagespan_owner_t* owner = NULL;

    TL_PY_OBJ_LOCK(span);
    if (span->closed) {
        err = 1;
    } else if (span->h == NULL) {
        err = 2;
    } else {
        len = (Py_ssize_t)span->len;
        h_local = span->h;
        owner = span->owner;
        if (owner != NULL) {
            tl_pagespan_owner_incref(owner);
        }
    }
    TL_PY_OBJ_UNLOCK();

    if (err == 1) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }
    if (err == 2) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }
    if (owner == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "PageSpan has no underlying buffer");
        return NULL;
    }

    PyObject* list = PyList_New(len);
    if (!list) {
        tl_pagespan_owner_decref(owner);
        return NULL;
    }

    for (Py_ssize_t i = 0; i < len; i++) {
        PyObject* obj = tl_py_handle_decode(h_local[i]);
        if (!obj) {
            Py_DECREF(list);
            tl_pagespan_owner_decref(owner);
            PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
            return NULL;
        }
        PyList_SET_ITEM(list, i, Py_NewRef(obj));
    }

    tl_pagespan_owner_decref(owner);
    return list;
}

static PyMethodDef PyPageSpanObjectsView_methods[] = {
    {"copy", (PyCFunction)PyPageSpanObjectsView_copy, METH_NOARGS,
     "copy() -> list[object]\n\n"
     "Return a copy of all objects as a Python list."},
    {NULL, NULL, 0, NULL}
};

/*===========================================================================
 * Type Specifications
 *===========================================================================*/

static PyType_Slot PyPageSpanObjectsView_slots[] = {
    {Py_tp_doc, PyDoc_STR(
        "Lazy sequence view over decoded Python objects from a PageSpan.\n\n"
        "Supports len(), indexing, and iteration.\n"
        "Cannot be instantiated directly; use PageSpan.objects()."
    )},
    {Py_tp_dealloc, (void*)PyPageSpanObjectsView_dealloc},
    {Py_tp_traverse, (void*)PyPageSpanObjectsView_traverse},
    {Py_tp_clear, (void*)PyPageSpanObjectsView_clear},
    {Py_tp_iter, (void*)PyPageSpanObjectsView_iter},
    {Py_tp_methods, PyPageSpanObjectsView_methods},
    {Py_sq_length, (void*)PyPageSpanObjectsView_length},
    {Py_sq_item, (void*)PyPageSpanObjectsView_getitem},
    {0, NULL}
};

static PyType_Spec PyPageSpanObjectsView_spec = {
    .name = "timelog._timelog.PageSpanObjectsView",
    .basicsize = sizeof(PyPageSpanObjectsView),
    .itemsize = 0,
    .flags = Py_TPFLAGS_DEFAULT |
             Py_TPFLAGS_HAVE_GC |
             Py_TPFLAGS_IMMUTABLETYPE |
             Py_TPFLAGS_DISALLOW_INSTANTIATION,
    .slots = PyPageSpanObjectsView_slots,
};

static PyType_Slot PyPageSpanObjectsViewIter_slots[] = {
    {Py_tp_dealloc, (void*)objectsviewiter_dealloc},
    {Py_tp_traverse, (void*)objectsviewiter_traverse},
    {Py_tp_clear, (void*)objectsviewiter_clear},
    {Py_tp_iter, PyObject_SelfIter},
    {Py_tp_iternext, (void*)objectsviewiter_next},
    {0, NULL}
};

static PyType_Spec PyPageSpanObjectsViewIter_spec = {
    .name = "timelog._timelog.PageSpanObjectsViewIter",
    .basicsize = sizeof(PyPageSpanObjectsViewIter),
    .itemsize = 0,
    .flags = Py_TPFLAGS_DEFAULT |
             Py_TPFLAGS_HAVE_GC |
             Py_TPFLAGS_IMMUTABLETYPE |
             Py_TPFLAGS_DISALLOW_INSTANTIATION,
    .slots = PyPageSpanObjectsViewIter_slots,
};

PyObject* TlPy_CreatePageSpanObjectsViewType(PyObject* module)
{
    return PyType_FromModuleAndSpec(module, &PyPageSpanObjectsView_spec, NULL);
}

PyObject* TlPy_CreatePageSpanObjectsViewIterType(PyObject* module)
{
    return PyType_FromModuleAndSpec(module, &PyPageSpanObjectsViewIter_spec, NULL);
}

TL_PY_DEFINE_CHECK(TlPyPageSpanObjectsView_Check, type_pagespan_objects_view)
