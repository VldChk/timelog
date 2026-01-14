/**
 * @file py_timelog.h
 * @brief PyTimelog CPython extension type declaration (LLD-B2)
 *
 * This module provides the PyTimelog type which wraps tl_timelog_t*
 * and exposes a stable, low-overhead Python API for writes, deletes,
 * and maintenance.
 *
 * Thread Safety:
 *   A Timelog instance is NOT thread-safe. Do not access the same instance
 *   from multiple threads without external synchronization. This is consistent
 *   with Python's sqlite3.Connection and file objects.
 *
 *   The GIL is released during flush(), compact(), stop_maintenance(), and
 *   close() to allow other Python threads to run. The user must ensure no
 *   other thread accesses this Timelog instance during these operations.
 *
 * Known Limitations:
 *   - Unflushed records leak on close(): The core engine's tl_close() does
 *     not invoke the on_drop callback for memtable records. To avoid leaking
 *     Python objects, ALWAYS call flush() before close(). Records that reach
 *     compaction will have their references properly released.
 *
 *   - Close-time reclamation: Even with flush(), compaction must run to
 *     physically drop records and trigger DECREF. If maintenance is disabled,
 *     call compact() and run_maintenance() before close().
 *
 * See: docs/timelog_v1_lld_B2_pytimelog_engine_wrapper.md
 *      docs/engineering_plan_B2_pytimelog.md
 */

#ifndef TL_PY_TIMELOG_H
#define TL_PY_TIMELOG_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelog/timelog.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_errors.h"

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * Busy Policy Enum
 *
 * Controls behavior when TL_EBUSY is returned from write operations.
 *
 * CRITICAL: TL_EBUSY from tl_append/tl_delete_* means the record/tombstone
 * WAS successfully inserted, but backpressure occurred (sealed queue full).
 * This is NOT a failure - the data is in the engine.
 *
 * Policy options:
 * - RAISE:  Raise TimelogBusyError (record IS inserted)
 * - SILENT: Return success silently (record IS inserted)
 * - FLUSH:  Flush to relieve backpressure, return success (record IS inserted)
 *===========================================================================*/

typedef enum {
    TL_PY_BUSY_RAISE  = 0,  /**< Raise TimelogBusyError (record IS inserted) */
    TL_PY_BUSY_SILENT = 1,  /**< Return success silently */
    TL_PY_BUSY_FLUSH  = 2   /**< Flush to relieve backpressure, return success */
} tl_py_busy_policy_t;

/*===========================================================================
 * PyTimelog Type
 *
 * Python wrapper for tl_timelog_t* with lifetime management.
 *===========================================================================*/

typedef struct {
    PyObject_HEAD

    /**
     * Engine instance.
     * Set to NULL after close() to prevent use-after-free.
     */
    tl_timelog_t* tl;

    /**
     * Lifecycle state.
     * 0 = open, 1 = closed.
     * Set early in close() to prevent reentrancy.
     */
    int closed;

    /**
     * Handle/lifetime context (embedded, not pointer).
     * Embedding simplifies shutdown sequence - no separate allocation.
     * Contains: retired queue, pin counter, metrics.
     */
    tl_py_handle_ctx_t handle_ctx;

    /**
     * Config introspection (stored for Python access).
     * Set during init, immutable after.
     */
    tl_time_unit_t time_unit;
    tl_maint_mode_t maint_mode;

    /**
     * Backpressure policy.
     * Controls behavior when TL_EBUSY is returned.
     */
    tl_py_busy_policy_t busy_policy;

} PyTimelog;

/*===========================================================================
 * Type Object
 *===========================================================================*/

/**
 * PyTimelog type object.
 * Defined in py_timelog.c.
 */
extern PyTypeObject PyTimelog_Type;

/**
 * Type check macro.
 */
#define PyTimelog_Check(op) PyObject_TypeCheck(op, &PyTimelog_Type)

/*===========================================================================
 * Macros for Method Implementation
 *===========================================================================*/

/**
 * Check if timelog is closed and raise TimelogError if so.
 * Returns NULL on closed (for use in PyObject* returning methods).
 */
#define CHECK_CLOSED(self) \
    do { \
        if ((self)->closed || (self)->tl == NULL) { \
            return TlPy_RaiseFromStatusFmt(TL_ESTATE, "Timelog is closed"); \
        } \
    } while (0)

/**
 * Check if timelog is closed and return -1 if so.
 * For use in methods returning int (like tp_init).
 */
#define CHECK_CLOSED_INT(self) \
    do { \
        if ((self)->closed || (self)->tl == NULL) { \
            TlPy_RaiseFromStatusFmt(TL_ESTATE, "Timelog is closed"); \
            return -1; \
        } \
    } while (0)

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_TIMELOG_H */
