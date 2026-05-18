/**
 * @file py_span_objects.c
 * @brief PyPageSpanObjectsView CPython extension type implementation (Core API Integration)
 *
 * Implements lazy access to decoded Python objects from a PageSpan.
 * Uses span->h[] pointer directly (borrowed from core owner's snapshot).
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_span_objects.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_handle.h"


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
    if (span_obj->closed) {
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
    PyTypeObject* tp = Py_TYPE(self);
    PyObject_GC_UnTrack(self);
    Py_XDECREF(self->span);
    tp->tp_free((PyObject*)self);
    Py_DECREF(tp);
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

    if (span->h == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }

    const Py_ssize_t len = (Py_ssize_t)span->len;

    if (index < 0) {
        index += len;
    }

    if (index < 0 || index >= len) {
        PyErr_SetString(PyExc_IndexError, "index out of range");
        return NULL;
    }

    tl_handle_t h = span->h[index];
    PyObject* obj = tl_py_handle_decode(h);
    if (!obj) {
        PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
        return NULL;
    }

    return Py_NewRef(obj);
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
    PyTypeObject* tp = Py_TYPE(self);
    PyObject_GC_UnTrack(self);
    Py_XDECREF(self->view);
    tp->tp_free((PyObject*)self);
    Py_DECREF(tp);
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
    PyPageSpan* span = (PyPageSpan*)view->span;

    if (span->closed) {
        return NULL;  /* StopIteration */
    }

    if (span->h == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }

    const Py_ssize_t len = (Py_ssize_t)span->len;

    if (self->index >= len) {
        return NULL;  /* StopIteration */
    }

    tl_handle_t h = span->h[self->index];
    PyObject* obj = tl_py_handle_decode(h);
    if (!obj) {
        PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
        return NULL;
    }

    self->index++;
    return Py_NewRef(obj);
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

    PyPageSpan* span = (PyPageSpan*)self->span;

    if (span->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

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
        tl_handle_t h = span->h[i];
        PyObject* obj = tl_py_handle_decode(h);
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

int TlPyPageSpanObjectsView_Check(PyObject* op, const tl_py_module_state_t* st)
{
    return op != NULL && st != NULL && st->type_pagespan_objects_view != NULL &&
           PyObject_TypeCheck(op, (PyTypeObject*)st->type_pagespan_objects_view);
}
