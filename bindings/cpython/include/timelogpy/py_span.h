/**
 * @file py_span.h
 * @brief PyPageSpan CPython extension type declaration (LLD-B4)
 *
 * This module provides the PyPageSpan type which exposes a contiguous
 * slice of page memory (timestamps) via the CPython buffer protocol.
 *
 * Zero-Copy Promise:
 *   The .timestamps property returns a memoryview directly backed by
 *   page->ts[] memory. No copying occurs unless explicitly requested
 *   via copy_timestamps() or copy().
 *
 * Thread Safety:
 *   A PageSpan instance is NOT thread-safe. Do not access the same
 *   instance from multiple threads without external synchronization.
 *
 * Lifetime:
 *   PageSpan holds a reference to a shared snapshot owner (tl_py_span_owner_t)
 *   which in turn holds a snapshot pin and strong ref to PyTimelog.
 *   Page memory remains valid as long as any span or exported buffer exists.
 *
 * See: docs/timelog_v1_lld_B4_pagespan_zero_copy.md
 */

#ifndef TL_PY_SPAN_H
#define TL_PY_SPAN_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelog/timelog.h"
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
 * Forward Declarations
 *===========================================================================*/

/* Internal page type from core storage */
struct tl_page;
typedef struct tl_page tl_page_t;

/*===========================================================================
 * Shared Snapshot Owner (Internal, C-only)
 *
 * Provides shared snapshot ownership across multiple PageSpan instances.
 * Uses manual refcounting under GIL (no atomics needed).
 *
 * Lifetime chain:
 *   span_owner -> holds ref to PyTimelog (keeps handle_ctx alive)
 *   span_owner -> owns tl_snapshot_t (keeps page memory valid)
 *===========================================================================*/

/* Forward declaration for allocator context */
struct tl_alloc_ctx;
typedef struct tl_alloc_ctx tl_alloc_ctx_t;

typedef struct tl_py_span_owner {
    uint32_t refcnt;                /**< GIL-protected refcount */
    PyObject* timelog;              /**< Strong ref to PyTimelog */
    tl_snapshot_t* snapshot;        /**< Owned snapshot */
    tl_py_handle_ctx_t* handle_ctx; /**< Borrowed from timelog */
    tl_alloc_ctx_t* alloc;          /**< Allocator (borrowed from snapshot) */
} tl_py_span_owner_t;

/*===========================================================================
 * PyPageSpan Type
 *
 * Zero-copy view of timestamps from a single page slice.
 * Implements the buffer protocol for memoryview exposure.
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
     * Page pointer (borrowed from snapshot).
     * NULL if closed.
     */
    const tl_page_t* page;

    /**
     * Slice boundaries within page arrays.
     */
    size_t row_start;               /**< Inclusive */
    size_t row_end;                 /**< Exclusive */

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
 * Shared Owner API (Internal)
 *
 * Used by py_span_iter.c to create and manage shared owners.
 *===========================================================================*/

/**
 * Create a shared snapshot owner.
 *
 * PRECONDITIONS (caller must ensure):
 *   1. tl_py_pins_enter() already called on handle_ctx
 *   2. tl_snapshot_acquire() already called to get snapshot
 *
 * This function does NOT call pins_enter - caller must do it first.
 * This ensures the correct protocol: pins_enter BEFORE snapshot_acquire.
 *
 * @param timelog    PyTimelog instance (borrows handle_ctx, takes strong ref)
 * @param snapshot   Snapshot to own (takes ownership)
 * @param alloc      Allocator from snapshot (for owner allocation)
 * @return New owner with refcnt=1, or NULL on error
 */
tl_py_span_owner_t* tl_py_span_owner_create(PyObject* timelog,
                                             tl_snapshot_t* snapshot,
                                             tl_alloc_ctx_t* alloc);

/**
 * Increment owner refcount.
 *
 * @param owner Owner to incref
 */
void tl_py_span_owner_incref(tl_py_span_owner_t* owner);

/**
 * Decrement owner refcount, destroying if zero.
 *
 * @param owner Owner to decref
 */
void tl_py_span_owner_decref(tl_py_span_owner_t* owner);

/*===========================================================================
 * Span Creation API (Internal)
 *
 * Used by py_span_iter.c to create spans.
 *===========================================================================*/

/**
 * Create a PageSpan from a shared owner and page slice.
 *
 * @param owner     Shared owner (will be incref'd)
 * @param page      Page pointer (borrowed from snapshot)
 * @param row_start Inclusive start index
 * @param row_end   Exclusive end index
 * @return New PageSpan object, or NULL on error
 */
PyObject* PyPageSpan_Create(tl_py_span_owner_t* owner,
                            const tl_page_t* page,
                            size_t row_start,
                            size_t row_end);

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_SPAN_H */
