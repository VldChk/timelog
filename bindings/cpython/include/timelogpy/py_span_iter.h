/**
 * @file py_span_iter.h
 * @brief PyPageSpanIter CPython extension type declaration (LLD-B4)
 *
 * This module provides the PyPageSpanIter type which iterates over
 * precomputed span descriptors, yielding PyPageSpan instances.
 *
 * Span Collection:
 *   On creation, the iterator collects all matching page slices from
 *   the snapshot (L1 segments first, then L0). Each yielded PageSpan
 *   shares the same snapshot owner for efficient lifetime management.
 *
 * Thread Safety:
 *   A PageSpanIter instance is NOT thread-safe. Do not access the same
 *   instance from multiple threads without external synchronization.
 *
 * Lifetime:
 *   The iterator holds a reference to the shared snapshot owner.
 *   When the iterator is closed or exhausted, it releases its owner ref.
 *   Individual PageSpan instances each hold their own owner ref.
 *
 * See: docs/timelog_v1_lld_B4_pagespan_zero_copy.md
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
 * Span Descriptor
 *
 * Describes a single page slice to be exposed as a PageSpan.
 * Collected during iterator creation, consumed during iteration.
 *===========================================================================*/

typedef struct span_desc {
    const tl_page_t* page;          /**< Borrowed pointer into snapshot */
    size_t row_start;               /**< Inclusive */
    size_t row_end;                 /**< Exclusive */
} span_desc_t;

/*===========================================================================
 * PyPageSpanIter Type
 *
 * Iterator over precomputed span descriptors.
 * Yields PyPageSpan instances.
 *
 * Cannot be instantiated directly; use Timelog.page_spans() factory.
 *===========================================================================*/

typedef struct {
    PyObject_HEAD

    /**
     * Shared snapshot owner (refcounted).
     * NULL if closed.
     */
    tl_py_span_owner_t* owner;

    /**
     * Array of span descriptors.
     * Allocated on creation, freed on close/dealloc.
     */
    span_desc_t* spans;

    /**
     * Total number of spans.
     */
    size_t count;

    /**
     * Current iteration index.
     */
    size_t index;

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
 * Collects all matching page slices from L1 and L0 segments.
 * Only emits spans from TL_PAGE_FULLY_LIVE pages.
 *
 * @param timelog PyTimelog instance
 * @param t1      Range start (inclusive)
 * @param t2      Range end (exclusive)
 * @param kind    "segment" (only supported value in V1)
 * @return New PageSpanIter object, or NULL on error
 */
PyObject* PyPageSpanIter_Create(PyObject* timelog,
                                tl_ts_t t1,
                                tl_ts_t t2,
                                const char* kind);

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_SPAN_ITER_H */
