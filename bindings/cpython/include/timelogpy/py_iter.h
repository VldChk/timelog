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
#include "timelogpy/py_errors.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_module_state.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct tl_py_engine_ctx tl_py_engine_ctx_t;

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
     * Refcounted handle lifetime context held independently of owner.
     */
    tl_py_handle_ctx_t* handle_ctx;

    /**
     * Refcounted engine lifetime context.
     * Held until iter/snapshot cleanup completes.
     */
    tl_py_engine_ctx_t* engine_ctx;

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
     * query bounds (any user-visible iterator has a valid count — the
     * count-failure construction path never returns the object), then
     * decremented after each successful next().
     */
    uint64_t remaining_count;

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

PyObject* TlPy_CreateTimelogIterType(PyObject* module);
int TlPyTimelogIter_Check(PyObject* op, const tl_py_module_state_t* st);

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_ITER_H */
