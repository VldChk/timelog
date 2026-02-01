/*
============================================================================

   COMBINED HEADER FILE: bindings.h

   Generated from: bindings\cpython\include\timelogpy
   Generated at:   2026-02-01 01:57:22

   This file combines all .h files from the bindings/ subfolder.

   Files included:
 *   - py_errors.h
 *   - py_handle.h
 *   - py_iter.h
 *   - py_span.h
 *   - py_span_iter.h
 *   - py_span_objects.h
 *   - py_timelog.h

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: py_errors.h
/*   FROM: bindings/cpython/include/timelogpy/
/*
/******************************************************************************/
/**
 * @file py_errors.h
 * @brief Error translation from Timelog status codes to Python exceptions
 *
 * This module provides consistent mapping from tl_status_t codes to
 * appropriate Python exception types.
 *
 * Mapping (actual implementation):
 * - TL_OK / TL_EOF   -> No exception (success)
 * - TL_EINVAL        -> ValueError
 * - TL_ESTATE        -> TimelogError (API usage error)
 * - TL_EBUSY         -> TimelogBusyError (context-dependent busy/backpressure)
 * - TL_ENOMEM        -> MemoryError
 * - TL_EOVERFLOW     -> OverflowError
 * - TL_EINTERNAL     -> SystemError (bug in timelog)
 * - (other)          -> TimelogError (catch-all)
 */

#ifndef TL_PY_ERRORS_H
#define TL_PY_ERRORS_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelog/timelog.h"

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * Custom Exception Type
 *
 * We define a TimelogError base exception for Timelog-specific errors.
 * Subclasses map to specific tl_status_t categories.
 *===========================================================================*/

/**
 * Base exception for all Timelog errors.
 * Inherits from Exception.
 *
 * This is initialized during module init and must be called before
 * any error translation functions.
 */
extern PyObject* TlPy_TimelogError;

/**
 * Exception for resource busy / backpressure conditions (TL_EBUSY).
 * Inherits from TimelogError.
 *
 * IMPORTANT: Context-dependent semantics:
 * - For WRITE operations (append, extend, delete_range, delete_before):
 *   The write WAS accepted, but backpressure occurred. DO NOT RETRY -
 *   retrying would create duplicate records. Call flush() in manual mode,
 *   or wait for background maintenance to catch up.
 * - For tl_flush()/tl_compact()/tl_maint_step(): publish retry exhausted;
 *   no data loss, safe to retry later.
 * - For start_maintenance(): stop in progress - retry later is safe.
 *
 * Typical causes:
 * - Sealed memrun queue is full (backpressure)
 * - OOO head flush failed after insert (runset pressure)
 * - Publish retry exhausted (flush/maintenance)
 * - Maintenance stop in progress
 */
extern PyObject* TlPy_TimelogBusyError;

/**
 * Initialize exception types.
 * Must be called during module initialization (PyInit_...).
 *
 * @param module The module object to add exceptions to
 * @return 0 on success, -1 on failure (with Python exception set)
 */
int TlPy_InitErrors(PyObject* module);

/**
 * Clean up exception types.
 * Called during module deallocation.
 */
void TlPy_FiniErrors(void);

/*===========================================================================
 * Error Translation API
 *===========================================================================*/

/**
 * Raise a Python exception from a tl_status_t code.
 *
 * Sets the appropriate Python exception based on the status code.
 * Returns NULL for convenient use in return statements.
 *
 * @param status Timelog status code (should not be TL_OK or TL_EOF)
 * @return NULL (always)
 *
 * Usage:
 *   if (st != TL_OK) return TlPy_RaiseFromStatus(st);
 */
PyObject* TlPy_RaiseFromStatus(tl_status_t status);

/**
 * Raise a Python exception with custom message format.
 *
 * @param status Timelog status code
 * @param format Printf-style format string
 * @param ...    Format arguments
 * @return NULL (always)
 */
PyObject* TlPy_RaiseFromStatusFmt(tl_status_t status,
                                   const char* format, ...);

/**
 * Check if a status code indicates success (TL_OK or TL_EOF).
 *
 * @param status Timelog status code
 * @return 1 if success, 0 if error
 */
static inline int TlPy_StatusOK(tl_status_t status) {
    return status == TL_OK || status == TL_EOF;
}

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_ERRORS_H */

/------------------------------------------------------------------------------/
/*   END OF: py_errors.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_handle.h
/*   FROM: bindings/cpython/include/timelogpy/
/*
/******************************************************************************/
/**
 * @file py_handle.h
 * @brief Python handle and lifetime management subsystem (LLD-B1)
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
 * - on_drop callback: called from maintenance thread, NO GIL, NO Python C-API
 * - drain: called from Python thread with GIL held
 * - pins: atomic counter, safe from any thread
 *
 * See: docs/V2/timelog_v2_engineering_plan.md
 *      docs/V2/timelog_v2_c_software_design_spec.md
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
     * Producers: maintenance thread (on_drop callback)
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
     * Written by maintenance thread, read by Python thread.
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
 * Registered with Timelog via tl_config_t.on_drop_handle.
 * Called from maintenance thread when records are physically reclaimed.
 *
 * CRITICAL: This function does NOT acquire GIL, does NOT call Python C-API,
 * and does NOT re-enter Timelog. It only enqueues to the lock-free stack.
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

/------------------------------------------------------------------------------/
/*   END OF: py_handle.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_iter.h
/*   FROM: bindings/cpython/include/timelogpy/
/*
/******************************************************************************/
/**
 * @file py_iter.h
 * @brief PyTimelogIter CPython extension type declaration (LLD-B3)
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
 * See: docs/V2/timelog_v2_lld_read_path.md
 *      docs/V2/timelog_v2_c_software_design_spec.md
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
     *
     * DESIGN NOTE (HLD Divergence):
     * HLD specifies borrowed ref + open iterators counter on PyTimelog.
     * We use strong ref + pin tracking instead because:
     * 1. handle_ctx is EMBEDDED in PyTimelog (not pointer)
     * 2. Strong ref prevents UAF if user drops PyTimelog ref while iterator exists
     * 3. Pin tracking provides equivalent semantics for close() blocking
     */
    PyObject* owner;

    /**
     * Core snapshot (valid only when !closed).
     * Acquired via tl_snapshot_acquire, released on cleanup.
     */
    tl_snapshot_t* snapshot;

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

/------------------------------------------------------------------------------/
/*   END OF: py_iter.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_span.h
/*   FROM: bindings/cpython/include/timelogpy/
/*
/******************************************************************************/
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

/------------------------------------------------------------------------------/
/*   END OF: py_span.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_span_iter.h
/*   FROM: bindings/cpython/include/timelogpy/
/*
/******************************************************************************/
/**
 * @file py_span_iter.h
 * @brief PyPageSpanIter CPython extension type declaration (Core API Integration)
 *
 * This module provides the PyPageSpanIter type which wraps the core
 * tl_pagespan_iter_t for streaming iteration over page spans.
 *
 * Architecture (Post-Migration):
 *   The iterator delegates to the core tl_pagespan_iter_* API instead of
 *   pre-collecting span descriptors. This eliminates algorithm duplication
 *   and reduces memory usage for large result sets.
 *
 * Streaming Behavior:
 *   Each call to __next__ invokes tl_pagespan_iter_next() which returns
 *   the next span on-demand. No spans are pre-collected or cached.
 *
 * Thread Safety:
 *   A PageSpanIter instance is NOT thread-safe. Do not access the same
 *   instance from multiple threads without external synchronization.
 *
 * Lifetime:
 *   The iterator holds the core tl_pagespan_iter_t which holds one owner
 *   reference. When closed or exhausted, the iterator releases this ref.
 *   Individual PageSpan instances each hold their own owner ref, remaining
 *   valid after the iterator is closed.
 *
 * See: docs/V2/timelog_v2_lld_storage_pages.md
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
 * PyPageSpanIter Type
 *
 * Streaming iterator over page spans using core API.
 * Yields PyPageSpan instances.
 *
 * Cannot be instantiated directly; use Timelog.page_spans() factory.
 *===========================================================================*/

typedef struct {
    PyObject_HEAD

    /**
     * Core iterator (owned).
     * Wraps snapshot acquisition and span enumeration logic.
     * The core iterator holds one owner reference which is released on close.
     * NULL if closed.
     */
    tl_pagespan_iter_t* iter;

    /**
     * Strong reference to PyTimelog for GC visibility.
     * Required because core iterator is opaque and GC cannot traverse it.
     * Also used to pass timelog reference to created PageSpan instances.
     * NULL if closed.
     */
    PyObject* timelog;

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
 * Delegates to tl_pagespan_iter_open() which acquires a snapshot and
 * sets up streaming iteration. Spans are returned on-demand via __next__.
 *
 * Lifetime Protocol:
 *   1. Calls pins_enter() before core iter_open
 *   2. Sets up release hook to call pins_exit on owner destruction
 *   3. On failure: cleans up hook context and calls pins_exit
 *
 * @param timelog PyTimelog instance
 * @param t1      Range start (inclusive)
 * @param t2      Range end (exclusive)
 * @param kind    "segment" (currently supported value)
 * @return New PageSpanIter object, or NULL on error with exception set
 */
PyObject* PyPageSpanIter_Create(PyObject* timelog,
                                tl_ts_t t1,
                                tl_ts_t t2,
                                const char* kind);

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_SPAN_ITER_H */

/------------------------------------------------------------------------------/
/*   END OF: py_span_iter.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_span_objects.h
/*   FROM: bindings/cpython/include/timelogpy/
/*
/******************************************************************************/
/**
 * @file py_span_objects.h
 * @brief PyPageSpanObjectsView CPython extension type declaration (Core API Integration)
 *
 * This module provides the PyPageSpanObjectsView type which provides
 * lazy access to decoded Python objects from a PageSpan.
 *
 * No-Copy Access:
 *   The objects view does NOT allocate a list of objects.
 *   It decodes handles lazily on indexing/iteration via span->h[].
 *   Use .copy() to materialize a list when needed.
 *
 * Thread Safety:
 *   A PageSpanObjectsView instance is NOT thread-safe. Do not access the same
 *   instance from multiple threads without external synchronization.
 *
 * Lifetime:
 *   The view holds a strong reference to its parent PageSpan.
 *   The PageSpan must remain open for the view to function.
 *
 * See: docs/V2/timelog_v2_lld_storage_pages.md
 */

#ifndef TL_PY_SPAN_OBJECTS_H
#define TL_PY_SPAN_OBJECTS_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * PyPageSpanObjectsView Type
 *
 * Lazy sequence view over handles decoded to PyObject*.
 * Supports len(), indexing, and iteration.
 *
 * Cannot be instantiated directly; use PageSpan.objects() factory.
 *===========================================================================*/

typedef struct {
    PyObject_HEAD

    /**
     * Strong reference to parent PageSpan.
     * The span's h[] pointer is used for handle decoding.
     */
    PyObject* span;

} PyPageSpanObjectsView;

/*===========================================================================
 * Type Object
 *===========================================================================*/

/**
 * PyPageSpanObjectsView type object.
 * Defined in py_span_objects.c.
 */
extern PyTypeObject PyPageSpanObjectsView_Type;

/**
 * PyPageSpanObjectsViewIter type object.
 * Internal iterator type for PageSpanObjectsView.
 * Must be readied by module init.
 */
extern PyTypeObject PyPageSpanObjectsViewIter_Type;

/**
 * Type check macro.
 */
#define PyPageSpanObjectsView_Check(op) PyObject_TypeCheck(op, &PyPageSpanObjectsView_Type)

/*===========================================================================
 * Factory Function (Internal)
 *
 * Creates a PageSpanObjectsView from a PageSpan.
 * Called by PageSpan.objects() method.
 *===========================================================================*/

/**
 * Create a PageSpanObjectsView for the given span.
 *
 * @param span PyPageSpan instance (takes strong ref)
 * @return New PageSpanObjectsView object, or NULL on error
 */
PyObject* PyPageSpanObjectsView_Create(PyObject* span);

#ifdef __cplusplus
}
#endif

#endif /* TL_PY_SPAN_OBJECTS_H */

/------------------------------------------------------------------------------/
/*   END OF: py_span_objects.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_timelog.h
/*   FROM: bindings/cpython/include/timelogpy/
/*
/******************************************************************************/
/**
 * @file py_timelog.h
 * @brief PyTimelog CPython extension type declaration (LLD-B2)
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

/------------------------------------------------------------------------------/
/*   END OF: py_timelog.h
/------------------------------------------------------------------------------/
