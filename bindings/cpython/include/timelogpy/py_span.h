/**
 * @file py_span.h
 * @brief PyPageSpan CPython extension type declaration (Core API Integration)
 *
 * This module provides the PyPageSpan type which exposes a contiguous
 * slice of page memory (timestamps) via the CPython buffer protocol.
 *
 * Architecture (Post-Migration):
 *   PageSpan now wraps the core tl_pagespan_view_t, storing ts/h/len
 *   pointers directly instead of page pointer + row indices. The core
 *   tl_pagespan_owner_t manages snapshot lifetime via hooks.
 *
 * Zero-Copy Promise:
 *   The .timestamps property returns a memoryview directly backed by
 *   span->ts memory. No copying occurs unless explicitly requested
 *   via copy_timestamps() or copy().
 *
 * Thread Safety:
 *   A PageSpan instance is NOT thread-safe. Do not access the same
 *   instance from multiple threads without external synchronization.
 *   All owner refcount operations must be serialized by the GIL.
 *
 * Lifetime:
 *   PageSpan holds a reference to the core tl_pagespan_owner_t which
 *   in turn pins the snapshot. The owner's release hook (set during
 *   iterator creation) handles pins_exit and Py_DECREF of the timelog.
 *   Page memory remains valid as long as any span holds an owner ref.
 *
 * See: docs/V2/timelog_v2_lld_storage_pages.md
 */

#ifndef TL_PY_SPAN_H
#define TL_PY_SPAN_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelog/timelog.h"
#include "query/tl_pagespan_iter.h"
#include "timelogpy/py_handle.h"

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * Py_NewRef Compatibility
 *
 * Py_NewRef was added in Python 3.10. For older versions, provide
 * an inline equivalent.
 *===========================================================================*/

#if PY_VERSION_HEX < 0x030A0000
#ifndef TL_Py_NewRef_DEFINED
#define TL_Py_NewRef_DEFINED
static inline PyObject* TL_Py_NewRef(PyObject* obj) {
    Py_INCREF(obj);
    return obj;
}
#define Py_NewRef TL_Py_NewRef
#endif
#endif

/*===========================================================================
 * PyPageSpan Type
 *
 * Zero-copy view of timestamps from a single span slice.
 * Implements the buffer protocol for memoryview exposure.
 *
 * Data Layout (Core API Integration):
 *   The span stores pointers from tl_pagespan_view_t directly:
 *   - ts: pointer to timestamp array (borrowed from owner's snapshot)
 *   - h:  pointer to handle array (borrowed from owner's snapshot)
 *   - len: row count
 *   - first_ts, last_ts: cached boundary timestamps
 *
 * Cannot be instantiated directly; use Timelog.page_spans() factory.
 *===========================================================================*/

typedef struct {
    PyObject_HEAD

    /**
     * Core snapshot owner (refcounted via core API).
     * Each span holds one reference; decref on close/dealloc.
     * NULL if closed.
     */
    tl_pagespan_owner_t* owner;

    /**
     * Strong reference to PyTimelog for GC visibility.
     * Required because core owner is opaque and GC cannot traverse it.
     * NULL if closed.
     */
    PyObject* timelog;

    /**
     * Pointer to timestamp array (borrowed from owner's snapshot).
     * Points directly to page memory; valid while owner is alive.
     * NULL if closed.
     */
    const tl_ts_t* ts;

    /**
     * Pointer to handle array (borrowed from owner's snapshot).
     * Points directly to page memory; valid while owner is alive.
     * May be NULL if handles are unavailable (future-proofing).
     */
    const tl_handle_t* h;

    /**
     * Row count (number of elements in ts/h arrays).
     * Always > 0 for valid spans returned by iter_next.
     */
    uint32_t len;

    /**
     * Cached first timestamp (== ts[0]).
     * Provides O(1) access for start_ts property.
     */
    tl_ts_t first_ts;

    /**
     * Cached last timestamp (== ts[len-1]).
     * Provides O(1) access for end_ts property.
     */
    tl_ts_t last_ts;

    /**
     * Buffer protocol shape/strides.
     * Stored in struct for stable pointer across getbuffer calls.
     */
    Py_ssize_t shape[1];
    Py_ssize_t strides[1];

    /**
     * Buffer protocol export tracking.
     * close() is blocked while exports > 0.
     */
    uint32_t exports;

    /**
     * State flag.
     * 0 = open (resources valid)
     * 1 = closed (resources released)
     */
    uint8_t closed;

} PyPageSpan;

/*===========================================================================
 * Type Object
 *===========================================================================*/

/**
 * PyPageSpan type object.
 * Defined in py_span.c.
 */
extern PyTypeObject PyPageSpan_Type;

/**
 * Type check macro.
 */
#define PyPageSpan_Check(op) PyObject_TypeCheck(op, &PyPageSpan_Type)

/*===========================================================================
 * Span Creation API (Internal)
 *
 * Used by py_span_iter.c to create spans from core views.
 *===========================================================================*/

/**
 * Create a PageSpan from a core view, CONSUMING the view's owner reference.
 *
 * Ownership Transfer Protocol:
 *   - On success: span owns the reference; view->owner is set to NULL
 *   - On failure: caller must call tl_pagespan_view_release(&view)
 *
 * This function does NOT incref the owner - it transfers ownership from
 * the view to the span. The caller (iter_next) receives an already-incref'd
 * owner from tl_pagespan_iter_next() and passes it here.
 *
 * @param view      Core view with owner ref (consumed on success)
 * @param timelog   PyTimelog instance (takes strong ref for GC)
 * @return New PageSpan object, or NULL on error (view NOT consumed)
 */
PyObject* PyPageSpan_FromView(tl_pagespan_view_t* view, PyObject* timelog);

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_SPAN_H */
