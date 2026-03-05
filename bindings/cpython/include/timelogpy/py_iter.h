/**
 * @file py_iter.h
 * @brief PyTimelogIter CPython extension type declaration
 *
 * This module provides the PyTimelogIter type which wraps a core
 * tl_iter_t* plus snapshot for snapshot-isolated iteration.
 *
 * Thread Safety:
 *   A TimelogIter instance is NOT thread-safe. Do not access the same
 *   instance from multiple threads without external synchronization.
 *
 * Lifetime:
 *   The iterator holds a strong reference to its owner PyTimelog,
 *   ensuring the embedded handle_ctx remains valid. A pin is acquired
 *   on creation and released on close/exhaustion/dealloc.
 *
 * See: docs/internals/components/read-path.md
 *      docs/internals/components/python-binding-architecture.md
 */

#ifndef TL_PY_ITER_H
#define TL_PY_ITER_H

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
 * PyTimelogIter Type
 *
 * Snapshot-based iterator over timelog records.
 * Yields (timestamp, object) tuples.
 *
 * Cannot be instantiated directly; use Timelog.range(), .since(),
 * .until(), .all(), .equal(), .point() factory methods.
 *===========================================================================*/

typedef struct {
    PyObject_HEAD

    /**
     * Strong reference to owner PyTimelog.
     * Prevents UAF if user drops PyTimelog ref while iterator exists.
     * Pin tracking replaces HLD's open-iterator counter.
     */
    PyObject* owner;

    /**
     * Pinned core snapshot (valid only when !closed).
     * Acquired via tl_snapshot_acquire, released on cleanup.
     */
    tl_snapshot_t* pinned_snapshot;

    /**
     * Core iterator derived from snapshot (valid only when !closed).
     * Created via tl_iter_range/since/until/equal/point.
     */
    tl_iter_t* iter;

    /**
     * Handle lifetime context (borrowed pointer to owner->handle_ctx).
     * Stored explicitly to avoid dereferencing owner during cleanup.
     * Safe because owner strong ref guarantees handle_ctx lifetime.
     */
    tl_py_handle_ctx_t* handle_ctx;

    /**
     * Query range bounds for view() support.
     * Normalized at creation time so view() can create a PageSpanIter
     * covering the same range regardless of original factory method.
     */
    tl_ts_t range_t1;
    tl_ts_t range_t2;

    /**
     * Exact count of remaining rows visible in this iterator snapshot.
     *
     * Initialized once at iterator creation for the iterator's normalized
     * query bounds, then decremented after each successful next().
     */
    uint64_t remaining_count;

    /**
     * Whether remaining_count is valid.
     *
     * Set to 1 on successful iterator construction after count precompute.
     * Kept explicit so __len__ can fail deterministically if initialization
     * logic changes in the future.
     */
    uint8_t remaining_valid;

    /**
     * State flag.
     * 0 = open (resources valid)
     * 1 = closed/exhausted (resources released)
     */
    uint8_t closed;

} PyTimelogIter;

/*===========================================================================
 * Type Object
 *===========================================================================*/

/**
 * PyTimelogIter type object.
 * Defined in py_iter.c.
 */
extern PyTypeObject PyTimelogIter_Type;

/**
 * Type check macro.
 */
#define PyTimelogIter_Check(op) PyObject_TypeCheck(op, &PyTimelogIter_Type)

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_ITER_H */
