/**
 * @file py_span_objects.h
 * @brief PyPageSpanObjectsView CPython extension type declaration (Core API Integration)
 *
 * This module provides the PyPageSpanObjectsView type which provides
 * lazy access to decoded Python objects from a PageSpan.
 *
 * No-Copy Access:
 *   The objects view does NOT allocate a list of objects.
 *   It decodes handles lazily on indexing/iteration via span->h[].
 *   Use .copy() to materialize a list when needed.
 *
 * Thread Safety:
 *   A PageSpanObjectsView instance is NOT thread-safe. Do not access the same
 *   instance from multiple threads without external synchronization.
 *
 * Lifetime:
 *   The view holds a strong reference to its parent PageSpan.
 *   The PageSpan must remain open for the view to function.
 *
 * See: docs/internals/components/storage-and-manifest.md
 */

#ifndef TL_PY_SPAN_OBJECTS_H
#define TL_PY_SPAN_OBJECTS_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * PyPageSpanObjectsView Type
 *
 * Lazy sequence view over handles decoded to PyObject*.
 * Supports len(), indexing, and iteration.
 *
 * Cannot be instantiated directly; use PageSpan.objects() factory.
 *===========================================================================*/

typedef struct {
    PyObject_HEAD

    /**
     * Strong reference to parent PageSpan.
     * The span's h[] pointer is used for handle decoding.
     */
    PyObject* span;

} PyPageSpanObjectsView;

/*===========================================================================
 * Type Object
 *===========================================================================*/

/**
 * PyPageSpanObjectsView type object.
 * Defined in py_span_objects.c.
 */
extern PyTypeObject PyPageSpanObjectsView_Type;

/**
 * PyPageSpanObjectsViewIter type object.
 * Internal iterator type for PageSpanObjectsView.
 * Must be readied by module init.
 */
extern PyTypeObject PyPageSpanObjectsViewIter_Type;

/**
 * Type check macro.
 */
#define PyPageSpanObjectsView_Check(op) PyObject_TypeCheck(op, &PyPageSpanObjectsView_Type)

/*===========================================================================
 * Factory Function (Internal)
 *
 * Creates a PageSpanObjectsView from a PageSpan.
 * Called by PageSpan.objects() method.
 *===========================================================================*/

/**
 * Create a PageSpanObjectsView for the given span.
 *
 * @param span PyPageSpan instance (takes strong ref)
 * @return New PageSpanObjectsView object, or NULL on error
 */
PyObject* PyPageSpanObjectsView_Create(PyObject* span);

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_SPAN_OBJECTS_H */
