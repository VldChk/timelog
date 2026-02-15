/**
 * @file py_timelog.h
 * @brief PyTimelog CPython extension type declaration
 *
 * This module provides the PyTimelog type which wraps tl_timelog_t*
 * and exposes a stable, low-overhead Python API for writes, deletes,
 * and maintenance.
 *
 * Thread Safety:
 *   Single-writer model: the same instance must not be used concurrently
 *   for writes or lifecycle operations without external synchronization.
 *   The binding serializes core calls to prevent concurrent use while the
 *   GIL is released, but this is not a guarantee of full thread safety.
 *   Snapshot-based iterators are safe for concurrent reads.
 *
 *   The GIL is released during flush(), compact(), stop_maintenance(), and
 *   close(). The user must ensure no other thread touches this Timelog
 *   instance while these operations are in progress.
 *
 *   This binding requires the CPython GIL and is NOT supported on
 *   free-threaded/no-GIL Python builds.
 *
 * Known Limitations:
 *   - Unflushed records are dropped on close(). The binding tracks all
 *     inserted handles and releases Python objects during close(), but
 *     data is not persisted. Call flush() before close() if you need to
 *     preserve all records.
 *
 * See: docs/V2/timelog_v2_engineering_plan.md
 *      docs/V2/timelog_v2_c_software_design_spec.md
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
 * WAS successfully inserted, but backpressure occurred. This is NOT a
 * failure - the data is in the engine.
 *
 * Note: TL_EBUSY can also be returned by flush/maintenance publish retries
 * (safe to retry). Busy policy only applies to write operations.
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
     * Per-instance lock to serialize all core calls.
     * Protects against concurrent use while GIL is released.
     */
    PyThread_type_lock core_lock;

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

    /**
     * Weak reference list head for Python weakref support.
     */
    PyObject* weakreflist;

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

/**
 * Internal helper: acquire core lock and re-check closed state.
 * Returns 0 on success, -1 with exception set on closed.
 */
int tl_py_lock_checked(PyTimelog* self);

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

/**
 * Serialize core calls. No-op if lock is NULL.
 */
#define TL_PY_LOCK(self) \
    do { \
        if ((self)->core_lock) { \
            PyThread_acquire_lock((self)->core_lock, 1); \
        } \
    } while (0)

#define TL_PY_UNLOCK(self) \
    do { \
        if ((self)->core_lock) { \
            PyThread_release_lock((self)->core_lock); \
        } \
    } while (0)

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_TIMELOG_H */
