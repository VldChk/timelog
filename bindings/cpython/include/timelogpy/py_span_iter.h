/**
 * @file py_span_iter.h
 * @brief PyPageSpanIter CPython extension type declaration (Core API Integration)
 *
 * This module provides the PyPageSpanIter type which wraps the core
 * tl_pagespan_iter_t for streaming iteration over page spans.
 *
 * Architecture (Post-Migration):
 *   The iterator delegates to the core tl_pagespan_iter_* API instead of
 *   pre-collecting span descriptors. This eliminates algorithm duplication
 *   and reduces memory usage for large result sets.
 *
 * Streaming Behavior:
 *   Each call to __next__ invokes tl_pagespan_iter_next() which returns
 *   the next span on-demand. No spans are pre-collected or cached.
 *
 * Thread Safety:
 *   A PageSpanIter instance is NOT thread-safe. Do not access the same
 *   instance from multiple threads without external synchronization.
 *
 * Lifetime:
 *   The iterator holds the core tl_pagespan_iter_t which holds one owner
 *   reference. When closed or exhausted, the iterator releases this ref.
 *   Individual PageSpan instances each hold their own owner ref, remaining
 *   valid after the iterator is closed.
 *
 * See: docs/V2/timelog_v2_lld_storage_pages.md
 */

#ifndef TL_PY_SPAN_ITER_H
#define TL_PY_SPAN_ITER_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_span.h"

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * PyPageSpanIter Type
 *
 * Streaming iterator over page spans using core API.
 * Yields PyPageSpan instances.
 *
 * Cannot be instantiated directly; use Timelog.page_spans() factory.
 *===========================================================================*/

typedef struct {
    PyObject_HEAD

    /**
     * Core iterator (owned).
     * Wraps snapshot acquisition and span enumeration logic.
     * The core iterator holds one owner reference which is released on close.
     * NULL if closed.
     */
    tl_pagespan_iter_t* iter;

    /**
     * Strong reference to PyTimelog for GC visibility.
     * Required because core iterator is opaque and GC cannot traverse it.
     * Also used to pass timelog reference to created PageSpan instances.
     * NULL if closed.
     */
    PyObject* timelog;

    /**
     * State flag.
     * 0 = open (resources valid)
     * 1 = closed (resources released)
     */
    uint8_t closed;

} PyPageSpanIter;

/*===========================================================================
 * Type Object
 *===========================================================================*/

/**
 * PyPageSpanIter type object.
 * Defined in py_span_iter.c.
 */
extern PyTypeObject PyPageSpanIter_Type;

/**
 * Type check macro.
 */
#define PyPageSpanIter_Check(op) PyObject_TypeCheck(op, &PyPageSpanIter_Type)

/*===========================================================================
 * Factory Function (Internal)
 *
 * Creates a PageSpanIter from a PyTimelog and time range.
 * Called by PyTimelog.page_spans() method.
 *===========================================================================*/

/**
 * Create a PageSpanIter for the given time range.
 *
 * Delegates to tl_pagespan_iter_open() which acquires a snapshot and
 * sets up streaming iteration. Spans are returned on-demand via __next__.
 *
 * Lifetime Protocol:
 *   1. Calls pins_enter() before core iter_open
 *   2. Sets up release hook to call pins_exit on owner destruction
 *   3. On failure: cleans up hook context and calls pins_exit
 *
 * @param timelog PyTimelog instance
 * @param t1      Range start (inclusive)
 * @param t2      Range end (exclusive)
 * @param kind    "segment" (currently supported value)
 * @return New PageSpanIter object, or NULL on error with exception set
 */
PyObject* PyPageSpanIter_Create(PyObject* timelog,
                                tl_ts_t t1,
                                tl_ts_t t2,
                                const char* kind);

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_SPAN_ITER_H */
