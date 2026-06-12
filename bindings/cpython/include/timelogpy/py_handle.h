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
 * - Drain retired objects when safe (pins == 0 on the owning interpreter)
 * - Track live handles (multiset) to release all objects on close()
 *
 * Thread safety:
 * - on_drop callback: called from flush/maintenance publisher thread, NO GIL,
 *   NO Python C-API
 * - drain: called on the owning interpreter with an attached Python thread state
 * - pins: atomic counter plus pin_lock for zero-transition/drain handoff
 *
 * See: docs/internals/components/python-binding-architecture.md
 *      docs/errors-and-retry-semantics.md
 */

#ifndef TL_PY_HANDLE_H
#define TL_PY_HANDLE_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelog/timelog.h"
#include "timelogpy/py_compat.h"

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
 * Handle Encoding/Decoding
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
     * Lifetime reference count for heap-allocated contexts.
     * PyTimelog, iterators, and PageSpan release hooks each hold refs.
     */
    _Atomic(uint64_t) refcnt;

    /**
     * True when this context was allocated by tl_py_handle_ctx_new().
     */
    uint8_t heap_allocated;

    /**
     * Interpreter that owns all PyObject references tracked by this context.
     * Drain/live-release paths must only DECREF while running on this
     * interpreter's attached Python thread state.
     */
    PyInterpreterState* interp;

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
     * Serializes active-pin transitions with retired-list claiming. The pin
     * counter is still atomic for cheap diagnostics, but the transition from
     * pins==0 to pins>0 must not race a drainer that has observed zero and is
     * about to claim retired PyObjects. The drainer takes this lock only long
     * enough to test pins and exchange the retired stack; Py_DECREF always runs
     * after unlocking.
     */
    tl_py_mutex_t pin_lock;

    /**
     * Live handle tracking (multiset by pointer identity).
     * Used to DECREF all remaining objects on close().
     *
     * MUTATION is protected by `live_lock`; callers must collect refs
     * under the lock and drop it before any Py_DECREF runs (a __del__
     * that touched the same context would otherwise deadlock).
     *
     * READING happens WITHOUT the lock: tp_traverse is a single
     * registered lock-free walk (it must never park or allocate — a
     * frozen thread during a free-threaded stop-the-world collection can
     * hold live_lock or even the libc arena lock forever; the v1.2 FT
     * deadlock). The table lives in a single allocation published via an
     * atomic pointer (`live_tab`); entries publish FULL with release and
     * retire with seq_cst; resized-out tables are only freed at ctx
     * teardown (`retired_tables` chain). See `traverse_readers` below for
     * the lifetime handshake.
     */
    _Atomic(struct tl_py_live_table*) live_tab;
    struct tl_py_live_table* retired_tables;
    size_t                  live_len;
    size_t                  live_tombstones;
    /**
     * Count of in-flight lock-free tp_traverse walkers. While nonzero,
     * drains DEFER their Py_DECREFs (re-pushing nodes to the retired
     * stack) and release_all waits, so a borrowed obj pointer observed by
     * a walker can never be freed mid-visit. Walkers never park, so the
     * counter is transient by construction.
     */
    _Atomic(size_t)         traverse_readers;
    /* Atomic so close-time consumers can sample without taking live_lock.
     * Writes happen under live_lock for ordering with table mutations. */
    _Atomic(uint8_t)        live_tracking_failed;

    /**
     * Lock protecting the live-handle table (entries, cap, len,
     * tombstones, tracking_failed). Mandatory under free-threaded
     * builds; on 3.12 with the PyThread_type_lock fallback it still
     * provides correctness under any in-process overlap path. Held
     * ONLY around bounded sections that mutate or scan the table;
     * never across Py_DECREF, warnings, weakref callbacks, or any
     * code that may execute Python.
     *
     * Lifetime invariant: no thread may be inside a live_lock-
     * protected section without holding a refcount on this ctx.
     * Refcount-zero destruction is guaranteed to happen only after
     * all such sections have unwound.
     */
    tl_py_mutex_t live_lock;

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
 * Allocate and initialize a refcounted handle context.
 *
 * @param drain_batch_limit Max objects per drain (0 = unlimited)
 * @return New context with refcount 1, or NULL with MemoryError set
 */
tl_py_handle_ctx_t* tl_py_handle_ctx_new(uint32_t drain_batch_limit);

/**
 * Increment/decrement a refcounted handle context.
 */
void tl_py_handle_ctx_incref(tl_py_handle_ctx_t* ctx);
void tl_py_handle_ctx_decref(tl_py_handle_ctx_t* ctx);

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
 * Pin Tracking API
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
 * PRECONDITION: Caller runs on the owning interpreter with an attached
 * Python thread state (drain may run).
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
 * On-Drop Callback
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
 * Performs deferred DECREF on retired objects. Must be called on the owning
 * interpreter with an attached Python thread state.
 *===========================================================================*/

/**
 * Drain retired objects, performing DECREF for each.
 *
 * PRECONDITION: Caller runs on the owning interpreter with an attached
 * Python thread state.
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
 * Must be called on the owning interpreter with an attached Python thread
 * state.
 *
 * @return TL_OK on success, TL_ENOMEM on allocation failure.
 *         On failure, tracking is best-effort; caller should continue.
 */
tl_status_t tl_py_live_note_insert(tl_py_handle_ctx_t* ctx, PyObject* obj);

/**
 * Record that a handle was physically dropped (decrements count).
 * Must be called on the owning interpreter with an attached Python thread
 * state.
 */
void tl_py_live_note_drop(tl_py_handle_ctx_t* ctx, PyObject* obj);

/**
 * Release all remaining tracked objects (DECREF counts).
 * Must be called on the owning interpreter with an attached Python thread
 * state. Clears tracking table.
 */
void tl_py_live_release_all(tl_py_handle_ctx_t* ctx);

/**
 * GC traversal helper: visit all Python objects currently referenced by ctx.
 *
 * Single registered lock-free walk: never parks, never allocates, calls no
 * Python C-API, and is valid WITHOUT an attached thread state (it runs
 * during late-finalization GC too). Borrowed-pointer lifetime is guaranteed
 * by the traverse_readers handshake (drains defer Py_DECREFs, release_all
 * waits). The caller must hold a ctx refcount across the call.
 */
int tl_py_handle_ctx_traverse(tl_py_handle_ctx_t* ctx, visitproc visit, void* arg);

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
