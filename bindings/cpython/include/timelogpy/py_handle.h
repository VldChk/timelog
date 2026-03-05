/**
 * @file py_handle.h
 * @brief Python handle and lifetime management subsystem
 *
 * This module provides the handle encoding/decoding and lifetime management
 * for storing CPython objects as tl_handle_t values in Timelog.
 *
 * Key responsibilities:
 * - Encode PyObject* to tl_handle_t and decode back
 * - Track active snapshot pins to prevent premature release
 * - Queue retired objects for deferred DECREF via lock-free stack
 * - Drain retired objects when safe (pins == 0 and GIL held)
 * - Track live handles (multiset) to release all objects on close()
 *
 * Thread safety:
 * - on_drop callback: called from flush/maintenance publisher thread, NO GIL,
 *   NO Python C-API
 * - drain: called from Python thread with GIL held
 * - pins: atomic counter, safe from any thread
 *
 * See: docs/internals/components/python-binding-architecture.md
 *      docs/errors-and-retry-semantics.md
 */

#ifndef TL_PY_HANDLE_H
#define TL_PY_HANDLE_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelog/timelog.h"

#include <stdatomic.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct tl_py_live_entry tl_py_live_entry_t;

/*===========================================================================
 * Compile-Time Safety
 *===========================================================================*/

/**
 * Verify that pointers fit in tl_handle_t.
 * Required for safe PyObject* <-> tl_handle_t round-trip.
 */
_Static_assert(sizeof(void*) <= sizeof(tl_handle_t),
               "Pointer size exceeds tl_handle_t width");

/*===========================================================================
 * Handle Encoding/Decoding (Invariant I1)
 *
 * Guarantee: decode(encode(obj)) == obj for all valid PyObject* pointers.
 *===========================================================================*/

/**
 * Encode a PyObject pointer as a tl_handle_t.
 *
 * @param obj  Valid PyObject pointer (must not be NULL)
 * @return     Handle encoding the pointer
 */
static inline tl_handle_t tl_py_handle_encode(PyObject* obj) {
    return (tl_handle_t)(uintptr_t)obj;
}

/**
 * Decode a tl_handle_t back to a PyObject pointer.
 *
 * @param h  Handle previously created by tl_py_handle_encode
 * @return   Original PyObject pointer
 */
static inline PyObject* tl_py_handle_decode(tl_handle_t h) {
    return (PyObject*)(uintptr_t)h;
}

/*===========================================================================
 * Drop Node (Lock-Free Stack Element)
 *
 * Used to queue retired PyObjects for deferred DECREF.
 * Allocated in on_drop callback, freed in drain.
 *===========================================================================*/

typedef struct tl_py_drop_node {
    struct tl_py_drop_node* next;   /**< Intrusive list link */
    PyObject*               obj;    /**< Object to DECREF */
    tl_ts_t                 ts;     /**< Timestamp for debugging/metrics */
} tl_py_drop_node_t;

/*===========================================================================
 * Handle Context (Per-Timelog State)
 *
 * Manages the lifetime of PyObjects stored in a Timelog instance.
 * Created during PyTimelog initialization, destroyed on close.
 *===========================================================================*/

typedef struct tl_py_handle_ctx {
    /**
     * Lock-free MPSC stack of retired objects awaiting DECREF.
     * Producers: flush or maintenance thread (on_drop callback)
     * Consumer: Python thread (drain function)
     */
    _Atomic(tl_py_drop_node_t*) retired_head;

    /**
     * Count of active snapshot pins.
     * Drain is blocked while pins > 0 (unless force=1).
     */
    _Atomic(uint64_t) pins;

    /**
     * Configuration: max objects to drain per call (0 = unlimited).
     * Set during init, immutable after.
     */
    uint32_t drain_batch_limit;

    /**
     * Metrics: total objects retired (enqueued by on_drop).
     * Written by flush or maintenance thread, read by Python thread.
     */
    _Atomic(uint64_t) retired_count;

    /**
     * Metrics: total objects drained (DECREF'd).
     * Written and read by Python thread only.
     */
    _Atomic(uint64_t) drained_count;

    /**
     * Metrics: allocation failures in on_drop callback.
     * Each failure represents a leaked object (unavoidable to prevent UAF).
     */
    _Atomic(uint64_t) alloc_failures;

    /**
     * Reentrancy guard for drain path.
     * Prevents nested tl_py_drain_retired() calls via __del__ reentry.
     */
    atomic_flag drain_guard;

    /**
     * Live handle tracking (multiset by pointer identity).
     * Used to DECREF all remaining objects on close().
     *
     * NOTE: Accessed only with GIL held (append/extend/drain/close).
     */
    struct tl_py_live_entry* live_entries;
    size_t                  live_cap;
    size_t                  live_len;
    size_t                  live_tombstones;
    uint8_t                 live_tracking_failed;

} tl_py_handle_ctx_t;

/*===========================================================================
 * Lifecycle API
 *===========================================================================*/

/**
 * Initialize a handle context.
 *
 * @param ctx               Context to initialize (must be valid pointer)
 * @param drain_batch_limit Max objects per drain (0 = unlimited)
 * @return TL_OK on success
 */
tl_status_t tl_py_handle_ctx_init(tl_py_handle_ctx_t* ctx,
                                   uint32_t drain_batch_limit);

/**
 * Destroy a handle context.
 *
 * PRECONDITION: pins must be 0 and retired queue should be empty.
 * Call tl_py_drain_retired(ctx, 1) before destruction to clean up.
 *
 * @param ctx Context to destroy
 */
void tl_py_handle_ctx_destroy(tl_py_handle_ctx_t* ctx);

/*===========================================================================
 * Pin Tracking API (Invariant I3)
 *
 * Used to track active snapshots/iterators. While pins > 0, retired
 * objects cannot be safely DECREF'd because a snapshot might still
 * yield them.
 *===========================================================================*/

/**
 * Enter a pinned region (before snapshot acquire).
 *
 * Thread safety: Safe from any thread.
 *
 * @param ctx Handle context
 */
void tl_py_pins_enter(tl_py_handle_ctx_t* ctx);

/**
 * Exit a pinned region (after snapshot release).
 * If pins drops to 0, triggers opportunistic drain.
 *
 * PRECONDITION: Caller must hold the GIL (drain may run).
 *
 * @param ctx Handle context
 */
void tl_py_pins_exit_and_maybe_drain(tl_py_handle_ctx_t* ctx);

/**
 * Get current pin count (for diagnostics/assertions).
 *
 * @param ctx Handle context
 * @return Current pin count
 */
uint64_t tl_py_pins_count(const tl_py_handle_ctx_t* ctx);

/*===========================================================================
 * On-Drop Callback (Invariant I4)
 *
 * Called from flush/maintenance thread when records are physically reclaimed.
 * Does NOT acquire GIL or call Python C-API. Enqueues to lock-free stack.
 *===========================================================================*/

/**
 * Callback invoked when a record is physically dropped.
 *
 * @param on_drop_ctx  The tl_py_handle_ctx_t* (from tl_config_t.on_drop_ctx)
 * @param ts           Timestamp of dropped record
 * @param handle       Handle of dropped record (encodes PyObject*)
 */
void tl_py_on_drop_handle(void* on_drop_ctx, tl_ts_t ts, tl_handle_t handle);

/*===========================================================================
 * Drain API
 *
 * Performs deferred DECREF on retired objects.
 * Must be called with GIL held.
 *===========================================================================*/

/**
 * Drain retired objects, performing DECREF for each.
 *
 * PRECONDITION: Caller must hold the GIL.
 *
 * Behavior:
 * - If pins > 0 and force=0: returns immediately without draining
 * - If pins == 0 or force=1: drains up to drain_batch_limit objects
 *   (0 = drain all)
 *
 * @param ctx   Handle context
 * @param force If true, drain even if pins > 0 (use only on close)
 * @return Number of objects drained
 */
size_t tl_py_drain_retired(tl_py_handle_ctx_t* ctx, int force);

/*===========================================================================
 * Live Handle Tracking (Multiset)
 *
 * Best-effort tracking of inserted handles so close() can DECREF all
 * remaining objects even if they were never tombstoned/compacted.
 *===========================================================================*/

/**
 * Record that a handle was inserted (increments count).
 * Must be called with GIL held.
 *
 * @return TL_OK on success, TL_ENOMEM on allocation failure.
 *         On failure, tracking is best-effort; caller should continue.
 */
tl_status_t tl_py_live_note_insert(tl_py_handle_ctx_t* ctx, PyObject* obj);

/**
 * Record that a handle was physically dropped (decrements count).
 * Must be called with GIL held.
 */
void tl_py_live_note_drop(tl_py_handle_ctx_t* ctx, PyObject* obj);

/**
 * Release all remaining tracked objects (DECREF counts).
 * Must be called with GIL held. Clears tracking table.
 */
void tl_py_live_release_all(tl_py_handle_ctx_t* ctx);

/**
 * GC traversal helper: visit all Python objects currently referenced by ctx.
 * Must be called with GIL held.
 */
int tl_py_handle_ctx_traverse(tl_py_handle_ctx_t* ctx, visitproc visit, void* arg);

/**
 * GC clear helper: release Python references held by ctx (force-drain + live table).
 * Must be called with GIL held.
 */
void tl_py_handle_ctx_clear(tl_py_handle_ctx_t* ctx);

/*===========================================================================
 * Metrics API
 *===========================================================================*/

/**
 * Get count of objects currently in retired queue.
 *
 * Note: This is approximate (retired_count - drained_count).
 *
 * @param ctx Handle context
 * @return Approximate queue length
 */
uint64_t tl_py_retired_queue_len(const tl_py_handle_ctx_t* ctx);

/**
 * Get count of allocation failures in on_drop.
 * Each failure represents a leaked object.
 *
 * @param ctx Handle context
 * @return Allocation failure count
 */
uint64_t tl_py_alloc_failures(const tl_py_handle_ctx_t* ctx);

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_HANDLE_H */
