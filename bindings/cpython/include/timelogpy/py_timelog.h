/**
 * @file py_timelog.h
 * @brief PyTimelog CPython extension type declaration
 *
 * This module provides the PyTimelog type which wraps tl_timelog_t*
 * and exposes a stable, low-overhead Python API for writes, deletes,
 * and maintenance.
 *
 * Thread Safety:
 *   Single-writer API contract: the same instance must not be used
 *   concurrently for *writes* or lifecycle operations without external
 *   serialization. Snapshot-based iterators are safe for concurrent reads
 *   from independent threads.
 *
 *   The binding's internal synchronization (LLD §5.4) is:
 *     - per-instance core_lock (PyThread_type_lock)
 *     - atomic mirrors for the hot-path closed/tl fields
 *     - per-object Py_BEGIN_CRITICAL_SECTION on mutable extension fields
 *     - live_lock on the handle context's live-handle table
 *     - atomic refcount on the core tl_pagespan_owner
 *     - lock-free retired-stack between maintenance thread and drain
 *
 *   Thread states required, not the GIL: Python C-API access requires an
 *   attached thread state on the owning interpreter. The binding releases
 *   the active interpreter's GIL during flush(), compact(),
 *   stop_maintenance(), and close().
 *
 *   Supported builds:
 *     - Regular CPython 3.12-3.14 (single interpreter).
 *     - Isolated subinterpreters with per-interpreter GIL (3.12+).
 *     - Free-threaded CPython 3.14t (Py_GIL_DISABLED=1): the module's
 *       PyModuleDef declares Py_mod_gil = Py_MOD_GIL_NOT_USED.
 *
 * Known Limitations:
 *   - Unflushed records are dropped on close(). The binding tracks all
 *     inserted handles and releases Python objects during close(), but
 *     data is not persisted. Call flush() before close() if you need to
 *     preserve all records.
 *
 * See: docs/python-api.md
 *      docs/internals/components/python-binding-architecture.md
 */

#ifndef TL_PY_TIMELOG_H
#define TL_PY_TIMELOG_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <stdatomic.h>
#include <stdint.h>

#include "timelog/timelog.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_errors.h"
#include "timelogpy/py_module_state.h"

#include <stdatomic.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct tl_py_engine_ctx {
    _Atomic(uint64_t) refcnt;
    tl_timelog_t* tl;
} tl_py_engine_ctx_t;

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
     *
     * Atomic so fast-path checks (CHECK_CLOSED) and the strict/best_effort
     * core-call paths can read without taking core_lock. Writes happen
     * under core_lock with memory_order_release.
     */
    _Atomic(tl_timelog_t*) tl;

    /**
     * Lifecycle state.
     * 0 = open, 1 = closed.
     * Set early in close() to prevent reentrancy.
     *
     * Atomic mirror of the lifecycle state (LLD §5.4 invariant L1): any
     * fast-path unlocked closed check must be atomically synchronized,
     * not racy. Writers hold core_lock and use memory_order_release;
     * readers may use memory_order_acquire without the lock.
     */
    _Atomic(uint8_t) closed;

    /**
     * Refcounted handle/lifetime context.
     * Iterators and PageSpan owner hooks hold independent references so GC
     * clearing a Timelog cannot invalidate active snapshot pins.
     */
    tl_py_handle_ctx_t* handle_ctx;

    /**
     * Refcounted engine lifetime context.
     * Iterator snapshots and PageSpan owners hold independent references so
     * GC clearing a Timelog cannot free tl_timelog_t before their core
     * snapshots have been released.
     */
    tl_py_engine_ctx_t* engine_ctx;

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

} PyTimelog;

/*===========================================================================
 * Type Object
 *===========================================================================*/

PyObject* TlPy_CreateTimelogType(PyObject* module);
int TlPyTimelog_Check(PyObject* op, const tl_py_module_state_t* st);

tl_py_engine_ctx_t* tl_py_engine_ctx_new(tl_timelog_t* tl);
void tl_py_engine_ctx_incref(tl_py_engine_ctx_t* ctx);
void tl_py_engine_ctx_decref(tl_py_engine_ctx_t* ctx);
void tl_py_engine_ctx_close(tl_py_engine_ctx_t* ctx, int allow_threads);

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
        if (atomic_load_explicit(&(self)->closed, memory_order_acquire) || \
            atomic_load_explicit(&(self)->tl, memory_order_acquire) == NULL) { \
            return TlPy_RaiseFromObjectFmt((PyObject*)(self), TL_ESTATE, \
                                           "Timelog is closed"); \
        } \
    } while (0)

/**
 * Check if timelog is closed and return -1 if so.
 * For use in methods returning int (like tp_init).
 */
#define CHECK_CLOSED_INT(self) \
    do { \
        if (atomic_load_explicit(&(self)->closed, memory_order_acquire) || \
            atomic_load_explicit(&(self)->tl, memory_order_acquire) == NULL) { \
            TlPy_RaiseFromObjectFmt((PyObject*)(self), TL_ESTATE, \
                                    "Timelog is closed"); \
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
