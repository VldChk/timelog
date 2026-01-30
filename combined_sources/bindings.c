/*
============================================================================

   COMBINED SOURCE FILE: bindings.c

   Generated from: bindings\cpython\src
   Generated at:   2026-01-26 20:20:58

   This file combines all .c files from the bindings/ subfolder.

   Files included:
 *   - module.c
 *   - py_errors.c
 *   - py_handle.c
 *   - py_iter.c
 *   - py_span.c
 *   - py_span_iter.c
 *   - py_span_objects.c
 *   - py_timelog.c

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: module.c
/*   FROM: bindings/cpython/src/
/*
/******************************************************************************/
/**
 * @file module.c
 * @brief CPython extension module initialization (LLD-B2, B3, B4)
 *
 * This module provides PyInit__timelog() which initializes the timelog._timelog
 * extension module and registers the PyTimelog, PyTimelogIter, and PageSpan types.
 *
 * Module name: timelog._timelog
 *   - Fully qualified name for correct __module__ attributes
 *   - Init function remains PyInit__timelog (last component rule)
 *   - Public Python package imports: from timelog._timelog import Timelog
 *
 * See: docs/timelog_v1_lld_B2_pytimelog_engine_wrapper.md
 *      docs/timelog_v1_lld_B4_pagespan_zero_copy.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_timelog.h"
#include "timelogpy/py_iter.h"
#include "timelogpy/py_errors.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_span_iter.h"
#include "timelogpy/py_span_objects.h"

/*===========================================================================
 * Module Definition
 *
 * No module-level methods - all functionality via PyTimelog type.
 * m_size = -1 means no per-interpreter state (simple global state).
 *===========================================================================*/

static struct PyModuleDef timelog_module = {
    PyModuleDef_HEAD_INIT,
    "timelog._timelog",                   /* m_name */
    "Timelog C extension module.\n\n"     /* m_doc */
    "Provides the Timelog type for time-indexed storage.\n\n"
    "Usage:\n"
    "    from timelog._timelog import Timelog\n"
    "    tl = Timelog()\n"
    "    tl.append(1234567890, my_object)\n"
    "    tl.close()\n\n"
    "See timelog package for the full Python API.",
    -1,                                   /* m_size (no per-module state) */
    NULL,                                 /* m_methods (none at module level) */
    NULL,                                 /* m_slots */
    NULL,                                 /* m_traverse */
    NULL,                                 /* m_clear */
    NULL                                  /* m_free */
};

/*===========================================================================
 * Module Initialization
 *
 * Called by Python when importing _timelog.
 * Order is critical:
 *   1. Create module
 *   2. Initialize error types (they need module for qualified name)
 *   3. Ready the type object
 *   4. Add type to module
 *===========================================================================*/

PyMODINIT_FUNC PyInit__timelog(void)
{
    PyObject* m = NULL;

    /* Create module */
    m = PyModule_Create(&timelog_module);
    if (m == NULL) {
        return NULL;
    }

    /*
     * Initialize error types (TimelogError, TimelogBusyError).
     * Must happen before any error translation can be used.
     * TlPy_InitErrors adds exceptions to the module namespace.
     */
    if (TlPy_InitErrors(m) < 0) {
        goto error;
    }

    /*
     * Ready the PyTimelog type.
     * PyType_Ready fills in tp_dict, tp_bases, etc.
     * Must be called before the type can be used.
     */
    if (PyType_Ready(&PyTimelog_Type) < 0) {
        goto error;
    }

    /*
     * Add PyTimelog type to module.
     * Exposed as timelog._timelog.Timelog in Python.
     *
     * We INCREF because PyModule_AddObject steals a reference only on
     * success. On failure, we need to own the type to DECREF it.
     */
    Py_INCREF(&PyTimelog_Type);
    if (PyModule_AddObject(m, "Timelog", (PyObject*)&PyTimelog_Type) < 0) {
        Py_DECREF(&PyTimelog_Type);
        goto error;
    }

    /*
     * Ready and add PyTimelogIter type (LLD-B3).
     * Exposed as timelog._timelog.TimelogIter in Python.
     *
     * Note: TimelogIter cannot be instantiated directly (tp_new raises TypeError).
     * It is only created via factory methods on Timelog (range, since, etc.).
     */
    if (PyType_Ready(&PyTimelogIter_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyTimelogIter_Type);
    if (PyModule_AddObject(m, "TimelogIter", (PyObject*)&PyTimelogIter_Type) < 0) {
        Py_DECREF(&PyTimelogIter_Type);
        goto error;
    }

    /*
     * Ready and add PyPageSpan type (LLD-B4).
     * Exposed as timelog._timelog.PageSpan in Python.
     *
     * Note: PageSpan cannot be instantiated directly (tp_new raises TypeError).
     * It is only created via Timelog.page_spans() factory method.
     */
    if (PyType_Ready(&PyPageSpan_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyPageSpan_Type);
    if (PyModule_AddObject(m, "PageSpan", (PyObject*)&PyPageSpan_Type) < 0) {
        Py_DECREF(&PyPageSpan_Type);
        goto error;
    }

    /*
     * Ready and add PyPageSpanIter type (LLD-B4).
     * Exposed as timelog._timelog.PageSpanIter in Python.
     */
    if (PyType_Ready(&PyPageSpanIter_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyPageSpanIter_Type);
    if (PyModule_AddObject(m, "PageSpanIter", (PyObject*)&PyPageSpanIter_Type) < 0) {
        Py_DECREF(&PyPageSpanIter_Type);
        goto error;
    }

    /*
     * Ready and add PyPageSpanObjectsView type (LLD-B4).
     * Exposed as timelog._timelog.PageSpanObjectsView in Python.
     */
    if (PyType_Ready(&PyPageSpanObjectsView_Type) < 0) {
        goto error;
    }
    Py_INCREF(&PyPageSpanObjectsView_Type);
    if (PyModule_AddObject(m, "PageSpanObjectsView", (PyObject*)&PyPageSpanObjectsView_Type) < 0) {
        Py_DECREF(&PyPageSpanObjectsView_Type);
        goto error;
    }

    /*
     * Ready PyPageSpanObjectsViewIter type (internal iterator).
     * Not exported to module namespace but must be ready before use.
     * This avoids a race condition in py_span_objects.c.
     */
    if (PyType_Ready(&PyPageSpanObjectsViewIter_Type) < 0) {
        goto error;
    }

    return m;

error:
    Py_XDECREF(m);
    return NULL;
}

/------------------------------------------------------------------------------/
/*   END OF: module.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_errors.c
/*   FROM: bindings/cpython/src/
/*
/******************************************************************************/
/**
 * @file py_errors.c
 * @brief Error translation from Timelog status codes to Python exceptions
 */

#include "timelogpy/py_errors.h"

#include <assert.h>
#include <stdarg.h>

/*===========================================================================
 * Exception Types
 *===========================================================================*/

/**
 * Base TimelogError exception.
 * All Timelog-specific errors inherit from this.
 */
PyObject* TlPy_TimelogError = NULL;

/**
 * TimelogBusyError exception for TL_EBUSY.
 * Inherits from TimelogError.
 * IMPORTANT: For write operations, this means the write succeeded but
 * backpressure occurred - DO NOT RETRY (would create duplicates).
 */
PyObject* TlPy_TimelogBusyError = NULL;

/*===========================================================================
 * Module Initialization
 *===========================================================================*/

int TlPy_InitErrors(PyObject* module)
{
    /*
     * Create TimelogError exception type.
     *
     * The qualified name should match the module that exposes it.
     * For a package structure like:
     *   timelog/
     *     __init__.py  (imports from _timelog)
     *     _timelog.so  (C extension)
     *
     * We use "timelog._timelog.TimelogError" since CMake installs the
     * extension as timelog/_timelog. Python __init__.py re-exports it
     * as "timelog.TimelogError".
     */
    TlPy_TimelogError = PyErr_NewException(
        "timelog._timelog.TimelogError",  /* name (installed path: timelog/_timelog) */
        NULL,                              /* base (Exception) */
        NULL                               /* dict */
    );

    if (TlPy_TimelogError == NULL) {
        return -1;
    }

    /* Add to module */
    if (PyModule_AddObject(module, "TimelogError", TlPy_TimelogError) < 0) {
        Py_DECREF(TlPy_TimelogError);
        TlPy_TimelogError = NULL;
        return -1;
    }

    /* Note: PyModule_AddObject steals reference on success */
    Py_INCREF(TlPy_TimelogError);

    /*
     * Create TimelogBusyError as a subclass of TimelogError.
     * Used for TL_EBUSY (backpressure / resource busy).
     */
    TlPy_TimelogBusyError = PyErr_NewException(
        "timelog._timelog.TimelogBusyError",  /* name */
        TlPy_TimelogError,                     /* base (TimelogError) */
        NULL                                   /* dict */
    );

    if (TlPy_TimelogBusyError == NULL) {
        Py_DECREF(TlPy_TimelogError);
        TlPy_TimelogError = NULL;
        return -1;
    }

    if (PyModule_AddObject(module, "TimelogBusyError", TlPy_TimelogBusyError) < 0) {
        Py_DECREF(TlPy_TimelogBusyError);
        TlPy_TimelogBusyError = NULL;
        Py_DECREF(TlPy_TimelogError);
        TlPy_TimelogError = NULL;
        return -1;
    }

    Py_INCREF(TlPy_TimelogBusyError);

    return 0;
}

void TlPy_FiniErrors(void)
{
    Py_CLEAR(TlPy_TimelogBusyError);
    Py_CLEAR(TlPy_TimelogError);
}

/*===========================================================================
 * Error Translation
 *===========================================================================*/

/**
 * Map tl_status_t to Python exception type.
 *
 * Mapping rationale:
 * - TL_EINVAL   -> ValueError (bad arguments from user)
 * - TL_ESTATE   -> TimelogError (API usage error)
 * - TL_EBUSY    -> TimelogBusyError (backpressure - see header for context)
 * - TL_ENOMEM   -> MemoryError (system resource)
 * - TL_EOVERFLOW-> OverflowError (arithmetic)
 * - TL_EINTERNAL-> SystemError (bug in timelog)
 * - Others      -> TimelogError (catch-all)
 */
static PyObject* status_to_exception_type(tl_status_t status)
{
    switch (status) {
        case TL_EINVAL:
            return PyExc_ValueError;

        case TL_EBUSY:
            /* Transient condition: backpressure, stop in progress, etc. */
            return TlPy_TimelogBusyError ? TlPy_TimelogBusyError
                                          : PyExc_RuntimeError;

        case TL_ENOMEM:
            return PyExc_MemoryError;

        case TL_EOVERFLOW:
            return PyExc_OverflowError;

        case TL_EINTERNAL:
            return PyExc_SystemError;

        case TL_ESTATE:
        default:
            /* Use our custom exception for Timelog-specific errors */
            return TlPy_TimelogError ? TlPy_TimelogError : PyExc_RuntimeError;
    }
}

PyObject* TlPy_RaiseFromStatus(tl_status_t status)
{
#ifndef NDEBUG
    /* Defensive: caller should not pass success codes */
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromStatus called with success status");
#endif

    PyObject* exc_type = status_to_exception_type(status);
    const char* msg = tl_strerror(status);

    PyErr_SetString(exc_type, msg);
    return NULL;
}

PyObject* TlPy_RaiseFromStatusFmt(tl_status_t status,
                                   const char* format, ...)
{
#ifndef NDEBUG
    /* Defensive: caller should not pass success codes */
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromStatusFmt called with success status");
#endif

    PyObject* exc_type = status_to_exception_type(status);

    va_list args;
    va_start(args, format);

    /*
     * Build message string.
     * Format: "user message: tl_strerror(status)"
     */
    char buffer[512];
    int n = vsnprintf(buffer, sizeof(buffer) - 64, format, args);
    va_end(args);

    /*
     * Append status message if there's room.
     * Note: n < 0 indicates encoding error; n >= sizeof - 64 means truncated.
     * In both cases, we still set the error with what we have.
     */
    if (n >= 0 && (size_t)n < sizeof(buffer) - 64) {
        const char* status_msg = tl_strerror(status);
        size_t remaining = sizeof(buffer) - (size_t)n;
        snprintf(buffer + n, remaining, ": %s", status_msg);
    }

    PyErr_SetString(exc_type, buffer);
    return NULL;
}

/------------------------------------------------------------------------------/
/*   END OF: py_errors.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_handle.c
/*   FROM: bindings/cpython/src/
/*
/******************************************************************************/
/**
 * @file py_handle.c
 * @brief Python handle and lifetime management subsystem implementation
 *
 * Implements the LLD-B1 specification for storing CPython objects as
 * tl_handle_t values with correct lifetime management.
 *
 * Key design decisions:
 * - Lock-free Treiber stack for retired object queue (MPSC pattern)
 * - Pin counter prevents drain while snapshots are active
 * - on_drop callback does NOT acquire GIL or call Python C-API
 * - All Py_DECREF happens in drain() on Python threads with GIL held
 *
 * Memory ordering model:
 * - Pin increment: RELAXED (gating counter, not a publication barrier;
 *   actual sync happens via Timelog snapshot acquisition)
 * - Pin decrement: RELEASE (ensures iterator operations visible to drain)
 * - Stack push CAS: RELEASE (make node fields visible)
 * - Stack exchange (drain): ACQ_REL (see all pushed nodes)
 *
 * See: docs/timelog_v1_lld_B1_python_handle_lifetime.md
 */

#include "timelogpy/py_handle.h"

#include <assert.h>   /* assert for debug checks */
#include <inttypes.h> /* PRIu64 for portable uint64_t formatting */
#include <stdio.h>    /* fprintf, stderr */
#include <stdlib.h>   /* malloc, free - NOT Python allocators (no GIL in on_drop) */
#include <string.h>   /* memset */

/*===========================================================================
 * Compile-Time Validation
 *===========================================================================*/

/**
 * Verify that we have proper C11/C17 atomics.
 * The Python.h include already requires a modern compiler, so this should
 * always succeed. If not, we need to add MSVC intrinsics fallback.
 */
#if !defined(__STDC_VERSION__) || __STDC_VERSION__ < 201112L
    #error "C11 or later required for stdatomic.h"
#endif

#if defined(__STDC_NO_ATOMICS__)
    #error "Compiler does not support C11 atomics"
#endif

/*===========================================================================
 * Lifecycle Implementation
 *===========================================================================*/

tl_status_t tl_py_handle_ctx_init(tl_py_handle_ctx_t* ctx,
                                   uint32_t drain_batch_limit)
{
    if (ctx == NULL) {
        return TL_EINVAL;
    }

    memset(ctx, 0, sizeof(*ctx));

    /* Initialize atomics */
    atomic_init(&ctx->retired_head, NULL);
    atomic_init(&ctx->pins, 0);
    atomic_init(&ctx->retired_count, 0);
    atomic_init(&ctx->drained_count, 0);
    atomic_init(&ctx->alloc_failures, 0);

    /* Store configuration (immutable after init) */
    ctx->drain_batch_limit = drain_batch_limit;

    return TL_OK;
}

void tl_py_handle_ctx_destroy(tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL) {
        return;
    }

    /*
     * Caller should have drained the queue before destruction.
     * If not, we have a leak but cannot safely DECREF without GIL.
     * Log a warning in debug builds.
     */
#ifndef NDEBUG
    tl_py_drop_node_t* remaining = atomic_load_explicit(
        &ctx->retired_head, memory_order_relaxed);
    if (remaining != NULL) {
        fprintf(stderr,
            "WARNING: tl_py_handle_ctx_destroy called with non-empty queue. "
            "Objects will leak.\n");
    }

    uint64_t pins = atomic_load_explicit(&ctx->pins, memory_order_relaxed);
    if (pins != 0) {
        fprintf(stderr,
            "WARNING: tl_py_handle_ctx_destroy called with pins=%" PRIu64 ". "
            "This indicates a snapshot/iterator leak.\n",
            pins);
    }
#endif

    memset(ctx, 0, sizeof(*ctx));
}

/*===========================================================================
 * Pin Tracking Implementation (Invariant I3)
 *
 * Memory ordering rationale:
 * - RELAXED on increment: gating counter only; Timelog snapshot provides sync
 * - RELEASE on decrement: ensures drain sees all our iterator operations
 *
 * GIL requirement:
 * - pins_exit_and_maybe_drain must be called with GIL held (may call drain)
 *===========================================================================*/

void tl_py_pins_enter(tl_py_handle_ctx_t* ctx)
{
    /*
     * Memory ordering: RELAXED is sufficient here.
     *
     * The critical synchronization point is tl_snapshot_acquire() which
     * has its own memory barriers. The pin increment just needs to be
     * visible before any subsequent drain checks.
     *
     * See LLD-B1 Section 7.2: "increment pins **before** acquiring a
     * Timelog snapshot" - the protocol, not the ordering, provides safety.
     */
    atomic_fetch_add_explicit(&ctx->pins, 1, memory_order_relaxed);
}

void tl_py_pins_exit_and_maybe_drain(tl_py_handle_ctx_t* ctx)
{
#ifndef NDEBUG
    /*
     * GIL enforcement: drain may run, which calls Py_DECREF.
     * PyGILState_Check() returns 1 if current thread holds the GIL.
     */
    assert(PyGILState_Check() &&
           "tl_py_pins_exit_and_maybe_drain requires GIL");
#endif

    uint64_t old_pins = atomic_fetch_sub_explicit(
        &ctx->pins, 1, memory_order_release);

#ifndef NDEBUG
    /*
     * Pin underflow detection: if old_pins was 0, we wrapped to UINT64_MAX.
     * This indicates a misuse (exit without enter) and will deadlock drain.
     */
    assert(old_pins > 0 &&
           "Pin underflow: tl_py_pins_exit called without matching enter");
#endif

    /*
     * If we were the last pin holder (old_pins == 1 means new pins == 0),
     * opportunistically drain retired objects.
     */
    if (old_pins == 1) {
        (void)tl_py_drain_retired(ctx, 0);
    }
}

uint64_t tl_py_pins_count(const tl_py_handle_ctx_t* ctx)
{
    /*
     * Cast away const for atomic_load_explicit.
     * This is safe because atomic load doesn't modify semantic state.
     * The const qualifier on ctx is for API clarity, not memory safety.
     */
    return atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->pins,
        memory_order_relaxed);
}

/*===========================================================================
 * On-Drop Callback Implementation (Invariant I4)
 *
 * CRITICAL CONSTRAINTS:
 * - Called from maintenance thread (NOT a Python thread)
 * - Does NOT hold the GIL
 * - Must NOT call any Python C-API functions
 * - Must NOT call back into Timelog APIs
 * - Must NOT block for extended periods
 *
 * Note: This is NOT async-signal-safe (uses malloc). It is only safe to
 * call from Timelog's maintenance thread context.
 *
 * Implementation uses Treiber stack (lock-free LIFO):
 * 1. Allocate node with libc malloc (NOT Python allocator)
 * 2. Initialize node fields
 * 3. CAS loop to push onto stack head
 *===========================================================================*/

void tl_py_on_drop_handle(void* on_drop_ctx, tl_ts_t ts, tl_handle_t handle)
{
    if (on_drop_ctx == NULL) {
        /* Misconfiguration: callback registered without context. Silent fail. */
        return;
    }

    tl_py_handle_ctx_t* ctx = (tl_py_handle_ctx_t*)on_drop_ctx;

    /*
     * Allocate node with libc malloc.
     * We cannot use Python allocators here because:
     * 1. We don't hold the GIL
     * 2. Python allocator state may not be thread-safe without GIL
     */
    tl_py_drop_node_t* node = (tl_py_drop_node_t*)malloc(sizeof(*node));
    if (node == NULL) {
        /*
         * Allocation failure: increment counter and leak the object.
         * This is unfortunate but necessary to avoid use-after-free.
         * The object will never be DECREF'd, causing a memory leak.
         *
         * Policy rationale: leaking is safer than UAF. If we cannot
         * enqueue the drop, we cannot safely DECREF (no GIL), and we
         * cannot defer DECREF because we have nowhere to record it.
         */
        atomic_fetch_add_explicit(&ctx->alloc_failures, 1, memory_order_relaxed);
        return;
    }

    /* Initialize node fields BEFORE making visible via CAS */
    node->obj = tl_py_handle_decode(handle);
    node->ts = ts;

    /*
     * Treiber stack push (lock-free)
     *
     * Memory ordering:
     * - RELAXED load of head: no ordering needed, just reading current value
     * - RELEASE CAS: makes node fields visible to drain thread
     * - RELAXED failure: will retry with updated expected value
     *
     * Using weak CAS is fine since we're in a loop anyway.
     */
    tl_py_drop_node_t* head;
    do {
        head = atomic_load_explicit(&ctx->retired_head, memory_order_relaxed);
        node->next = head;
    } while (!atomic_compare_exchange_weak_explicit(
                &ctx->retired_head,
                &head,
                node,
                memory_order_release,
                memory_order_relaxed));

    /* Update metrics (relaxed is fine for counters) */
    atomic_fetch_add_explicit(&ctx->retired_count, 1, memory_order_relaxed);
}

/*===========================================================================
 * Drain Implementation
 *
 * PRECONDITION: Caller must hold the GIL.
 *
 * This function performs the actual Py_DECREF operations for retired
 * objects. It runs on a Python thread to ensure:
 * 1. Finalizers (__del__) run on a proper Python thread
 * 2. No GIL acquisition needed (already held)
 * 3. Proper integration with Python's GC
 *===========================================================================*/

size_t tl_py_drain_retired(tl_py_handle_ctx_t* ctx, int force)
{
#ifndef NDEBUG
    /*
     * GIL enforcement: Py_DECREF can run arbitrary Python code via __del__.
     * This MUST be called from a Python thread holding the GIL.
     */
    assert(PyGILState_Check() &&
           "tl_py_drain_retired requires GIL");
#endif

    /*
     * Check pin count before draining.
     *
     * If pins > 0, snapshots/iterators are active and might still yield
     * objects from the retired queue. Draining would cause use-after-free.
     *
     * Exception: force=1 is used during close() after verifying all
     * iterators are released.
     */
    uint64_t pins = atomic_load_explicit(&ctx->pins, memory_order_acquire);
    if (pins != 0 && !force) {
        return 0;
    }

    /*
     * Atomically claim the entire retired list.
     *
     * Memory ordering:
     * - ACQ_REL: acquire semantics to see node fields written by on_drop,
     *            release semantics to make our NULL write visible
     *
     * This makes the queue empty for subsequent on_drop calls.
     * We process the claimed list exclusively.
     */
    tl_py_drop_node_t* list = atomic_exchange_explicit(
        &ctx->retired_head, NULL, memory_order_acq_rel);

    if (list == NULL) {
        return 0;  /* Nothing to drain */
    }

    size_t count = 0;

    /*
     * Batch limit: 0 = unlimited.
     * When force=1 (close path), always drain everything regardless of limit.
     * This prevents leaking objects when ctx is about to be destroyed.
     */
    uint32_t batch_limit = force ? 0 : ctx->drain_batch_limit;

    while (list != NULL) {
        /* Check batch limit (0 = unlimited) */
        if (batch_limit != 0 && count >= batch_limit) {
            /*
             * Batch limit reached. Re-attach remaining nodes to queue.
             * Must be done atomically in case on_drop is concurrent.
             */
            tl_py_drop_node_t* remaining = list;
            tl_py_drop_node_t* tail = list;

            /* Find tail of remaining list */
            while (tail->next != NULL) {
                tail = tail->next;
            }

            /* Atomically prepend remaining to current queue head */
            tl_py_drop_node_t* current_head;
            do {
                current_head = atomic_load_explicit(
                    &ctx->retired_head, memory_order_relaxed);
                tail->next = current_head;
            } while (!atomic_compare_exchange_weak_explicit(
                        &ctx->retired_head,
                        &current_head,
                        remaining,
                        memory_order_release,
                        memory_order_relaxed));
            break;
        }

        /* Process one node */
        tl_py_drop_node_t* node = list;
        list = node->next;

        /*
         * CRITICAL: Py_DECREF may run arbitrary Python code via __del__.
         *
         * This is safe because:
         * 1. We hold the GIL (precondition)
         * 2. We're on a Python thread
         * 3. The object is no longer reachable from Timelog
         * 4. pins == 0 (no iterator can yield this object)
         */
        Py_DECREF(node->obj);

        /* Free the node (allocated with libc malloc) */
        free(node);
        count++;
    }

    /* Update metrics */
    atomic_fetch_add_explicit(&ctx->drained_count, count, memory_order_relaxed);

    return count;
}

/*===========================================================================
 * Metrics Implementation
 *===========================================================================*/

uint64_t tl_py_retired_queue_len(const tl_py_handle_ctx_t* ctx)
{
    /*
     * Cast away const for atomic_load_explicit.
     * Note: drained_count is updated after re-attachment in batch mode,
     * so this metric may briefly undercount. This is documented as approximate.
     */
    uint64_t retired = atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->retired_count,
        memory_order_relaxed);
    uint64_t drained = atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->drained_count,
        memory_order_relaxed);

    /* Underflow protection (should never happen but defensive) */
    if (drained > retired) {
        return 0;
    }

    return retired - drained;
}

uint64_t tl_py_alloc_failures(const tl_py_handle_ctx_t* ctx)
{
    return atomic_load_explicit(
        (_Atomic(uint64_t)*)&ctx->alloc_failures,
        memory_order_relaxed);
}

/------------------------------------------------------------------------------/
/*   END OF: py_handle.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_iter.c
/*   FROM: bindings/cpython/src/
/*
/******************************************************************************/
/**
 * @file py_iter.c
 * @brief PyTimelogIter CPython extension type implementation (LLD-B3)
 *
 * Implements snapshot-based iteration over timelog records.
 *
 * See: docs/timelog_v1_lld_B3_pytimelogiter_snapshot_iterator.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_iter.h"
#include "timelogpy/py_errors.h"
#include "timelogpy/py_handle.h"
#include "timelog/timelog.h"

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static void pytimelogiter_cleanup(PyTimelogIter* self);

/*===========================================================================
 * Block Direct Construction
 *
 * Iterators are only created via factory methods (range, since, etc.).
 *===========================================================================*/

static PyObject* PyTimelogIter_new_error(PyTypeObject* type,
                                          PyObject* args,
                                          PyObject* kwds)
{
    (void)type;
    (void)args;
    (void)kwds;

    PyErr_SetString(PyExc_TypeError,
        "TimelogIter cannot be instantiated directly; "
        "use Timelog.range(), .since(), .until(), .all(), etc.");
    return NULL;
}

/*===========================================================================
 * Cleanup Routine (Single Source of Truth)
 *
 * All resource release goes through this routine:
 * - close() calls it
 * - exhaustion calls it
 * - tp_clear calls it
 * - tp_dealloc calls it
 *
 * It is idempotent (safe to call multiple times).
 *===========================================================================*/

static void pytimelogiter_cleanup(PyTimelogIter* self)
{
    if (self->closed) {
        return;  /* Already cleaned up */
    }
    self->closed = 1;

    /*
     * Clear pointers BEFORE operations that may run Python code.
     * This prevents reentrancy issues if Py_DECREF triggers __del__.
     */
    tl_iter_t* it = self->iter;
    self->iter = NULL;

    tl_snapshot_t* snap = self->snapshot;
    self->snapshot = NULL;

    tl_py_handle_ctx_t* ctx = self->handle_ctx;
    /* Don't NULL handle_ctx - it's borrowed, and we need it for pin exit */

    PyObject* owner = self->owner;
    self->owner = NULL;

    /*
     * Release resources in order:
     * 1. Destroy iterator (no Python code)
     * 2. Release snapshot (no Python code)
     * 3. Exit pins - may drain retired objects (runs Python code via Py_DECREF)
     * 4. DECREF owner (runs Python code)
     */
    if (it) {
        tl_iter_destroy(it);
    }

    if (snap) {
        tl_snapshot_release(snap);
    }

    /*
     * Preserve exception state across operations that may run arbitrary Python
     * code (drain, owner DECREF). This ensures:
     * - TL_EOF path stays a clean StopIteration (no exception)
     * - __exit__ path doesn't corrupt the propagating exception
     * - Bad finalizers in __del__ don't clobber our exception state
     */
    PyObject *exc_type, *exc_value, *exc_tb;
    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);

    if (ctx) {
        tl_py_pins_exit_and_maybe_drain(ctx);
    }

    Py_XDECREF(owner);

    PyErr_Restore(exc_type, exc_value, exc_tb);
}

/*===========================================================================
 * GC Support
 *===========================================================================*/

static int PyTimelogIter_traverse(PyTimelogIter* self, visitproc visit, void* arg)
{
    Py_VISIT(self->owner);
    return 0;
}

static int PyTimelogIter_clear(PyTimelogIter* self)
{
    pytimelogiter_cleanup(self);
    return 0;
}

static void PyTimelogIter_dealloc(PyTimelogIter* self)
{
    PyObject_GC_UnTrack(self);
    pytimelogiter_cleanup(self);  /* Idempotent */
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * Iterator Protocol
 *===========================================================================*/

static PyObject* PyTimelogIter_iternext(PyTimelogIter* self)
{
    /*
     * Closed iterator returns NULL with no exception set.
     * Per CPython convention, this signals StopIteration.
     */
    if (self->closed) {
        return NULL;
    }

    tl_record_t rec;
    tl_status_t st = tl_iter_next(self->iter, &rec);

    if (st == TL_OK) {
        /* Decode handle to PyObject* and take new reference */
        PyObject* obj = Py_NewRef(tl_py_handle_decode(rec.handle));

        PyObject* ts = PyLong_FromLongLong((long long)rec.ts);
        if (!ts) {
            Py_DECREF(obj);
            return NULL;
        }

        PyObject* tup = PyTuple_New(2);
        if (!tup) {
            Py_DECREF(ts);
            Py_DECREF(obj);
            return NULL;
        }

        /* PyTuple_SET_ITEM steals references */
        PyTuple_SET_ITEM(tup, 0, ts);
        PyTuple_SET_ITEM(tup, 1, obj);
        return tup;
    }

    if (st == TL_EOF) {
        /* Exhaustion - cleanup and signal StopIteration */
        pytimelogiter_cleanup(self);
        return NULL;  /* No exception = StopIteration */
    }

    /* Error path - cleanup and raise */
    pytimelogiter_cleanup(self);
    return TlPy_RaiseFromStatus(st);
}

/*===========================================================================
 * Methods
 *===========================================================================*/

static PyObject* PyTimelogIter_close(PyTimelogIter* self, PyObject* noargs)
{
    (void)noargs;
    pytimelogiter_cleanup(self);
    Py_RETURN_NONE;
}

static PyObject* PyTimelogIter_enter(PyTimelogIter* self, PyObject* noargs)
{
    (void)noargs;
    return Py_NewRef((PyObject*)self);
}

static PyObject* PyTimelogIter_exit(PyTimelogIter* self, PyObject* args)
{
    (void)args;
    pytimelogiter_cleanup(self);
    Py_RETURN_FALSE;  /* Don't suppress exceptions */
}

static PyObject* PyTimelogIter_next_batch(PyTimelogIter* self, PyObject* arg_n)
{
    Py_ssize_t n = PyLong_AsSsize_t(arg_n);
    if (n == -1 && PyErr_Occurred()) {
        return NULL;  /* Conversion error */
    }

    /* Negative n is an error (unlike zero which returns empty list) */
    if (n < 0) {
        PyErr_SetString(PyExc_ValueError, "next_batch size must be >= 0");
        return NULL;
    }

    if (n == 0 || self->closed) {
        return PyList_New(0);
    }

    PyObject* list = PyList_New(n);
    if (!list) {
        return NULL;
    }

    Py_ssize_t i = 0;
    for (; i < n; i++) {
        tl_record_t rec;
        tl_status_t st = tl_iter_next(self->iter, &rec);

        if (st == TL_OK) {
            PyObject* obj = Py_NewRef(tl_py_handle_decode(rec.handle));

            PyObject* ts = PyLong_FromLongLong((long long)rec.ts);
            if (!ts) {
                Py_DECREF(obj);
                goto fail;
            }

            PyObject* tup = PyTuple_New(2);
            if (!tup) {
                Py_DECREF(ts);
                Py_DECREF(obj);
                goto fail;
            }

            PyTuple_SET_ITEM(tup, 0, ts);
            PyTuple_SET_ITEM(tup, 1, obj);
            PyList_SET_ITEM(list, i, tup);
            continue;
        }

        if (st == TL_EOF) {
            pytimelogiter_cleanup(self);
            break;
        }

        /* Error path */
        pytimelogiter_cleanup(self);
        TlPy_RaiseFromStatus(st);
        goto fail;
    }

    /* Shrink list if early EOF */
    if (i < n) {
        if (PyList_SetSlice(list, i, n, NULL) < 0) {
            goto fail;
        }
    }

    return list;

fail:
    Py_DECREF(list);
    return NULL;
}

/*===========================================================================
 * Getters/Setters
 *===========================================================================*/

static PyObject* PyTimelogIter_get_closed(PyTimelogIter* self, void* closure)
{
    (void)closure;
    return PyBool_FromLong(self->closed);
}

/*===========================================================================
 * Method/GetSet Tables
 *===========================================================================*/

static PyMethodDef PyTimelogIter_methods[] = {
    {"close", (PyCFunction)PyTimelogIter_close, METH_NOARGS,
     "close() -> None\n\nRelease iterator resources. Idempotent."},
    {"next_batch", (PyCFunction)PyTimelogIter_next_batch, METH_O,
     "next_batch(n) -> list[tuple[int, object]]\n\n"
     "Return up to n records. Empty list on exhaustion."},
    {"__enter__", (PyCFunction)PyTimelogIter_enter, METH_NOARGS,
     "Context manager entry."},
    {"__exit__", (PyCFunction)PyTimelogIter_exit, METH_VARARGS,
     "Context manager exit (closes iterator)."},
    {NULL, NULL, 0, NULL}
};

static PyGetSetDef PyTimelogIter_getset[] = {
    {"closed", (getter)PyTimelogIter_get_closed, NULL,
     "True if iterator is closed or exhausted.", NULL},
    {NULL, NULL, NULL, NULL, NULL}
};

/*===========================================================================
 * Type Object
 *===========================================================================*/

PyTypeObject PyTimelogIter_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.TimelogIter",
    .tp_doc = PyDoc_STR(
        "Snapshot-based iterator over timelog records.\n\n"
        "Yields (timestamp, object) tuples. Cannot be instantiated directly;\n"
        "use Timelog.range(), .since(), .until(), .all() factory methods."
    ),
    .tp_basicsize = sizeof(PyTimelogIter),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_GC,
    .tp_new = PyTimelogIter_new_error,  /* Block direct construction */
    .tp_dealloc = (destructor)PyTimelogIter_dealloc,
    .tp_traverse = (traverseproc)PyTimelogIter_traverse,
    .tp_clear = (inquiry)PyTimelogIter_clear,
    .tp_free = PyObject_GC_Del,         /* Explicit for GC-allocated types */
    .tp_iter = PyObject_SelfIter,
    .tp_iternext = (iternextfunc)PyTimelogIter_iternext,
    .tp_methods = PyTimelogIter_methods,
    .tp_getset = PyTimelogIter_getset,
};

/------------------------------------------------------------------------------/
/*   END OF: py_iter.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_span.c
/*   FROM: bindings/cpython/src/
/*
/******************************************************************************/
/**
 * @file py_span.c
 * @brief PyPageSpan CPython extension type implementation (Core API Integration)
 *
 * Implements zero-copy timestamp exposure via the CPython buffer protocol.
 * Delegates ownership management to core tl_pagespan_owner_t.
 *
 * See: docs/timelog_v2_lld_pagespan_cpython_bindings_update.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <string.h>  /* For memset */

#include "timelogpy/py_span.h"
#include "timelogpy/py_span_objects.h"
#include "timelogpy/py_handle.h"
#include "timelogpy/py_timelog.h"

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static void pagespan_cleanup(PyPageSpan* self);

/*===========================================================================
 * Block Direct Construction
 *
 * PageSpans are only created via factory (page_spans iterator).
 *===========================================================================*/

static PyObject* PyPageSpan_new_error(PyTypeObject* type,
                                       PyObject* args,
                                       PyObject* kwds)
{
    (void)type;
    (void)args;
    (void)kwds;

    PyErr_SetString(PyExc_TypeError,
        "PageSpan cannot be instantiated directly; "
        "use Timelog.page_spans()");
    return NULL;
}

/*===========================================================================
 * PageSpan Creation from Core View
 *
 * This replaces PyPageSpan_Create which took page pointer + row indices.
 * Now we take a core view and CONSUME its owner reference.
 *===========================================================================*/

PyObject* PyPageSpan_FromView(tl_pagespan_view_t* view, PyObject* timelog)
{
    /*
     * Validate inputs.
     * On any failure, the caller must call tl_pagespan_view_release().
     */
    if (view == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "view is NULL");
        return NULL;
    }
    if (view->owner == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "view->owner is NULL");
        return NULL;
    }
    if (timelog == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "timelog is NULL");
        return NULL;
    }
    if (!PyTimelog_Check(timelog)) {
        PyErr_SetString(PyExc_TypeError, "expected PyTimelog");
        return NULL;
    }

    /*
     * Allocate the Python object with GC support.
     */
    PyPageSpan* self = PyObject_GC_New(PyPageSpan, &PyPageSpan_Type);
    if (self == NULL) {
        /* Allocation failed - caller must release view */
        return NULL;
    }

    /*
     * Transfer ownership from view to span.
     * The view's owner reference is CONSUMED - no incref needed.
     * We set view->owner = NULL to prevent accidental double-decref.
     */
    self->owner = view->owner;
    view->owner = NULL;

    /*
     * Store strong reference to timelog for GC visibility.
     * The core owner is opaque, so GC cannot traverse it.
     */
    self->timelog = Py_NewRef(timelog);

    /*
     * Copy view pointers. These are borrowed from the owner's snapshot
     * and remain valid as long as the owner is alive.
     */
    self->ts = view->ts;
    self->h = view->h;
    self->len = view->len;
    self->first_ts = view->first_ts;
    self->last_ts = view->last_ts;

    /*
     * Initialize buffer protocol state.
     */
    self->shape[0] = 0;
    self->strides[0] = 0;
    self->exports = 0;
    self->closed = 0;

    /*
     * Track with GC after all fields are initialized.
     */
    PyObject_GC_Track((PyObject*)self);
    return (PyObject*)self;
}

/*===========================================================================
 * Cleanup (Single Source of Truth)
 *
 * Releases owner reference and clears borrowed pointers.
 * The core owner's release hook (set during iterator creation) handles
 * pins_exit and Py_DECREF of the iteration-level timelog reference.
 *===========================================================================*/

static void pagespan_cleanup(PyPageSpan* self)
{
    if (self->closed) {
        return;
    }
    self->closed = 1;

    /*
     * Clear borrowed pointers first (before releasing owner).
     * After owner is released, snapshot may be freed and pointers invalid.
     */
    self->ts = NULL;
    self->h = NULL;

    /*
     * Release owner reference via core API.
     * When refcount reaches 0, core calls the release hook which handles
     * pins_exit and Py_DECREF of the hook context's timelog reference.
     */
    tl_pagespan_owner_t* owner = self->owner;
    self->owner = NULL;

    if (owner != NULL) {
        tl_pagespan_owner_decref(owner);
    }

    /*
     * Clear our direct timelog reference (for GC visibility).
     * This is separate from the hook context's reference.
     *
     * Exception preservation: Py_CLEAR may trigger __del__ which can
     * clobber active exceptions (e.g., when __exit__ calls cleanup).
     * Per LLD-B6, preserve exception state across cleanup.
     */
    {
        PyObject *exc_type, *exc_value, *exc_tb;
        PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
        Py_CLEAR(self->timelog);
        PyErr_Restore(exc_type, exc_value, exc_tb);
    }
}

/*===========================================================================
 * GC Support
 *===========================================================================*/

static int PyPageSpan_traverse(PyPageSpan* self, visitproc visit, void* arg)
{
    /*
     * Visit timelog for GC cycle detection.
     * The core owner is opaque and cannot be traversed directly.
     */
    Py_VISIT(self->timelog);
    return 0;
}

static int PyPageSpan_clear(PyPageSpan* self)
{
    /*
     * GC clear - called to break reference cycles.
     * Cannot cleanup if buffers are exported.
     */
    if (self->exports > 0) {
        return 0;
    }
    pagespan_cleanup(self);
    return 0;
}

static void PyPageSpan_dealloc(PyPageSpan* self)
{
    PyObject_GC_UnTrack(self);
    /*
     * Note: if exports > 0 at dealloc, something went very wrong.
     * We cleanup anyway to avoid leaks.
     */
    pagespan_cleanup(self);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * Buffer Protocol
 *
 * Exposes timestamps as a read-only 1D array of int64.
 * Uses span->ts and span->len instead of page pointer + row indices.
 *===========================================================================*/

/* Static format string - must outlive buffer view */
static const char* PAGESPAN_TS_FORMAT = "q";

static int pagespan_getbuffer(PyObject* exporter, Py_buffer* view, int flags)
{
    PyPageSpan* self = (PyPageSpan*)exporter;

    /*
     * CPython contract: on error, view->obj must be NULL.
     */
    view->obj = NULL;

    if (self->closed || self->ts == NULL) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return -1;
    }
    if (flags & PyBUF_WRITABLE) {
        PyErr_SetString(PyExc_BufferError, "PageSpan buffer is read-only");
        return -1;
    }

    const Py_ssize_t n = (Py_ssize_t)self->len;
    void* ptr = (void*)self->ts;

    /*
     * Overflow guard: ensure n * sizeof(tl_ts_t) doesn't overflow Py_ssize_t.
     * This is defensive - page sizes should never approach this limit.
     */
    if (n > PY_SSIZE_T_MAX / (Py_ssize_t)sizeof(tl_ts_t)) {
        PyErr_SetString(PyExc_OverflowError, "PageSpan too large for buffer");
        return -1;
    }

    /*
     * Request-independent fields (ALWAYS set per CPython docs).
     */
    view->obj = Py_NewRef(exporter);
    view->buf = ptr;
    view->len = n * (Py_ssize_t)sizeof(tl_ts_t);
    view->readonly = 1;
    view->itemsize = (Py_ssize_t)sizeof(tl_ts_t);
    view->ndim = 1;  /* ALWAYS 1 - request-independent */

    /*
     * Request-dependent fields.
     */
    view->format = (flags & PyBUF_FORMAT) ? (char*)PAGESPAN_TS_FORMAT : NULL;

    if (flags & PyBUF_ND) {
        self->shape[0] = n;
        view->shape = self->shape;
    } else {
        view->shape = NULL;
    }

    if (flags & PyBUF_STRIDES) {
        self->strides[0] = (Py_ssize_t)sizeof(tl_ts_t);
        view->strides = self->strides;
    } else {
        view->strides = NULL;
    }

    view->suboffsets = NULL;
    view->internal = NULL;

    self->exports++;
    return 0;
}

static void pagespan_releasebuffer(PyObject* exporter, Py_buffer* view)
{
    PyPageSpan* self = (PyPageSpan*)exporter;
    (void)view;

    if (self->exports > 0) {
        self->exports--;
    }
}

static PyBufferProcs pagespan_as_buffer = {
    .bf_getbuffer = pagespan_getbuffer,
    .bf_releasebuffer = pagespan_releasebuffer,
};

/*===========================================================================
 * Methods
 *===========================================================================*/

static PyObject* PyPageSpan_close(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;

    if (self->exports > 0) {
        PyErr_SetString(PyExc_BufferError,
            "cannot close PageSpan: buffer is exported");
        return NULL;
    }

    pagespan_cleanup(self);
    Py_RETURN_NONE;
}

static PyObject* PyPageSpan_enter(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;
    return Py_NewRef((PyObject*)self);
}

static PyObject* PyPageSpan_exit(PyPageSpan* self, PyObject* args)
{
    (void)args;

    if (self->exports > 0) {
        /*
         * Per Python convention, __exit__ should NOT raise for cleanup
         * issues that aren't actual exceptions being propagated.
         * Users who need strict error checking should call close() explicitly,
         * which DOES raise BufferError when exports > 0.
         *
         * Returning False signals "do not suppress any exception".
         */
        Py_RETURN_FALSE;
    }

    pagespan_cleanup(self);
    Py_RETURN_FALSE;  /* Don't suppress exceptions */
}

static PyObject* PyPageSpan_objects(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /*
     * Fail early if handles are not available.
     * This gives a clear error at .objects() rather than deferring
     * to the first access (which would raise RuntimeError).
     */
    if (self->h == NULL) {
        PyErr_SetString(PyExc_RuntimeError,
            "handles not available in this span");
        return NULL;
    }

    return PyPageSpanObjectsView_Create((PyObject*)self);
}

static PyObject* PyPageSpan_copy_timestamps(PyPageSpan* self, PyObject* noargs)
{
    (void)noargs;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    const Py_ssize_t n = (Py_ssize_t)self->len;
    PyObject* list = PyList_New(n);
    if (list == NULL) {
        return NULL;
    }

    for (Py_ssize_t i = 0; i < n; i++) {
        PyObject* val = PyLong_FromLongLong((long long)self->ts[i]);
        if (val == NULL) {
            Py_DECREF(list);
            return NULL;
        }
        PyList_SET_ITEM(list, i, val);
    }

    return list;
}

static PyObject* PyPageSpan_copy(PyPageSpan* self, PyObject* noargs)
{
    /* For V1, copy() returns same as copy_timestamps() */
    return PyPageSpan_copy_timestamps(self, noargs);
}

/*===========================================================================
 * Sequence Protocol (__len__)
 *===========================================================================*/

static Py_ssize_t PyPageSpan_length(PyPageSpan* self)
{
    if (self->closed) {
        return 0;
    }
    return (Py_ssize_t)self->len;
}

static PySequenceMethods pagespan_as_sequence = {
    .sq_length = (lenfunc)PyPageSpan_length,
};

/*===========================================================================
 * Properties
 *
 * Use cached first_ts/last_ts instead of page pointer dereference.
 *===========================================================================*/

static PyObject* PyPageSpan_get_timestamps(PyPageSpan* self, void* closure)
{
    (void)closure;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    return PyMemoryView_FromObject((PyObject*)self);
}

static PyObject* PyPageSpan_get_start_ts(PyPageSpan* self, void* closure)
{
    (void)closure;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /*
     * Use cached first_ts from view - no pointer dereference needed.
     * For valid spans, len > 0 is guaranteed by core iter_next.
     */
    return PyLong_FromLongLong((long long)self->first_ts);
}

static PyObject* PyPageSpan_get_end_ts(PyPageSpan* self, void* closure)
{
    (void)closure;

    if (self->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /*
     * Use cached last_ts from view - no pointer dereference needed.
     * For valid spans, len > 0 is guaranteed by core iter_next.
     */
    return PyLong_FromLongLong((long long)self->last_ts);
}

static PyObject* PyPageSpan_get_closed(PyPageSpan* self, void* closure)
{
    (void)closure;
    return PyBool_FromLong(self->closed);
}

/*===========================================================================
 * Method/GetSet Tables
 *===========================================================================*/

static PyMethodDef PyPageSpan_methods[] = {
    {"close", (PyCFunction)PyPageSpan_close, METH_NOARGS,
     "close() -> None\n\n"
     "Release span resources. Raises BufferError if buffers are exported."},
    {"objects", (PyCFunction)PyPageSpan_objects, METH_NOARGS,
     "objects() -> PageSpanObjectsView\n\n"
     "Return a lazy sequence view over decoded Python objects."},
    {"copy_timestamps", (PyCFunction)PyPageSpan_copy_timestamps, METH_NOARGS,
     "copy_timestamps() -> list[int]\n\n"
     "Return a copy of timestamps as a Python list."},
    {"copy", (PyCFunction)PyPageSpan_copy, METH_NOARGS,
     "copy() -> list[int]\n\n"
     "Return a copy of timestamps as a Python list."},
    {"__enter__", (PyCFunction)PyPageSpan_enter, METH_NOARGS,
     "Context manager entry."},
    {"__exit__", (PyCFunction)PyPageSpan_exit, METH_VARARGS,
     "Context manager exit (closes span if no buffers exported)."},
    {NULL, NULL, 0, NULL}
};

static PyGetSetDef PyPageSpan_getset[] = {
    {"timestamps", (getter)PyPageSpan_get_timestamps, NULL,
     "Read-only memoryview of timestamps (int64).", NULL},
    {"start_ts", (getter)PyPageSpan_get_start_ts, NULL,
     "First timestamp in this span.", NULL},
    {"end_ts", (getter)PyPageSpan_get_end_ts, NULL,
     "Last timestamp in this span.", NULL},
    {"closed", (getter)PyPageSpan_get_closed, NULL,
     "True if span is closed.", NULL},
    {NULL, NULL, NULL, NULL, NULL}
};

/*===========================================================================
 * Type Object
 *===========================================================================*/

PyTypeObject PyPageSpan_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.PageSpan",
    .tp_doc = PyDoc_STR(
        "Zero-copy view of timestamps from a single page slice.\n\n"
        "The .timestamps property returns a memoryview directly backed by\n"
        "page memory. Cannot be instantiated directly; use Timelog.page_spans()."
    ),
    .tp_basicsize = sizeof(PyPageSpan),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_GC,
    .tp_new = PyPageSpan_new_error,
    .tp_dealloc = (destructor)PyPageSpan_dealloc,
    .tp_traverse = (traverseproc)PyPageSpan_traverse,
    .tp_clear = (inquiry)PyPageSpan_clear,
    .tp_free = PyObject_GC_Del,
    .tp_as_buffer = &pagespan_as_buffer,
    .tp_as_sequence = &pagespan_as_sequence,
    .tp_methods = PyPageSpan_methods,
    .tp_getset = PyPageSpan_getset,
};

/------------------------------------------------------------------------------/
/*   END OF: py_span.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_span_iter.c
/*   FROM: bindings/cpython/src/
/*
/******************************************************************************/
/**
 * @file py_span_iter.c
 * @brief PyPageSpanIter CPython extension type implementation (Core API Integration)
 *
 * Implements streaming iteration over page spans using core tl_pagespan_iter_*.
 * Delegates span enumeration and ownership management to core.
 *
 * See: docs/timelog_v2_lld_pagespan_cpython_bindings_update.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <string.h>  /* For strcmp, memset */

#include "timelogpy/py_span_iter.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_timelog.h"
#include "timelogpy/py_errors.h"

/*
 * Core API for pagespan iteration.
 * This is the ONLY core dependency needed - no storage internals.
 */
#include "query/tl_pagespan_iter.h"

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static void pagespaniter_cleanup(PyPageSpanIter* self);

/*===========================================================================
 * Release Hook Context
 *
 * The core owner calls our hook when refcount reaches 0.
 * The hook handles:
 *   1. pins_exit_and_maybe_drain() - allow handle cleanup
 *   2. Py_DECREF(timelog) - release our strong reference
 *   3. PyMem_Free(ctx) - free this context struct
 *
 * The "armed" flag prevents double cleanup if core calls the hook during
 * iter_open failure paths before we've completed setup.
 *===========================================================================*/

typedef struct tl_py_pagespan_hook_ctx {
    PyObject* timelog;          /**< Strong ref, decref on release */
    tl_py_handle_ctx_t* ctx;    /**< Borrowed handle context */
    int armed;                  /**< 0 until iter_open succeeds */
} tl_py_pagespan_hook_ctx_t;

/**
 * Release hook called by core when owner refcount reaches 0.
 *
 * CRITICAL INVARIANTS:
 *   1. GIL must be held (all CPython code paths that decref hold GIL)
 *   2. Exception state must be preserved (may run during GC/unwinding)
 *   3. Hook runs AFTER owner struct is freed (no UAF)
 */
static void tl_py_pagespan_on_release(void* user)
{
    tl_py_pagespan_hook_ctx_t* hook_ctx = (tl_py_pagespan_hook_ctx_t*)user;
    if (hook_ctx == NULL) {
        return;
    }

    /*
     * Check armed flag.
     * If iter_open failed after creating owner but before we armed,
     * the hook may be called but should be a no-op. The binding
     * error path handles cleanup in that case.
     */
    if (!hook_ctx->armed) {
        return;
    }

    /*
     * EXCEPTION PRESERVATION:
     * The hook may run during GC or exception unwinding when an
     * exception is already set. Py_DECREF can run arbitrary finalizers
     * that might clobber exception state. Save and restore to avoid
     * losing the user's exception context.
     */
    PyObject *exc_type, *exc_value, *exc_tb;
    PyErr_Fetch(&exc_type, &exc_value, &exc_tb);

    /*
     * Exit pins and drain retired handles.
     * This may run Py_DECREF on retired objects.
     */
    if (hook_ctx->ctx != NULL) {
        tl_py_pins_exit_and_maybe_drain(hook_ctx->ctx);
    }

    /*
     * Release our strong reference to timelog.
     * This may trigger timelog dealloc if we held the last ref.
     */
    Py_XDECREF(hook_ctx->timelog);

    /*
     * Free the hook context itself.
     */
    PyMem_Free(hook_ctx);

    /*
     * Restore exception state.
     */
    PyErr_Restore(exc_type, exc_value, exc_tb);
}

/*===========================================================================
 * Block Direct Construction
 *
 * PageSpanIter is only created via page_spans() factory.
 *===========================================================================*/

static PyObject* PyPageSpanIter_new_error(PyTypeObject* type,
                                           PyObject* args,
                                           PyObject* kwds)
{
    (void)type;
    (void)args;
    (void)kwds;

    PyErr_SetString(PyExc_TypeError,
        "PageSpanIter cannot be instantiated directly; "
        "use Timelog.page_spans()");
    return NULL;
}

/*===========================================================================
 * Factory Function
 *
 * Creates a streaming iterator using core tl_pagespan_iter_open().
 * Sets up release hook to handle pins and timelog ref on cleanup.
 *===========================================================================*/

PyObject* PyPageSpanIter_Create(PyObject* timelog,
                                tl_ts_t t1,
                                tl_ts_t t2,
                                const char* kind)
{
    /*
     * Step 1: Validate kind parameter.
     * Only "segment" is supported (B4 constraint).
     */
    if (kind == NULL || strcmp(kind, "segment") != 0) {
        PyErr_Format(PyExc_ValueError,
            "page_spans: kind must be 'segment', got '%s'", kind ? kind : "(null)");
        return NULL;
    }

    /*
     * Step 1b: Validate timelog type.
     * This is defensive - the public API (PyTimelog.page_spans) guarantees
     * correct type, but internal C callers could misuse. Fail early.
     */
    if (!PyTimelog_Check(timelog)) {
        PyErr_SetString(PyExc_TypeError,
            "page_spans: expected Timelog instance");
        return NULL;
    }

    PyTimelog* tl_obj = (PyTimelog*)timelog;

    /*
     * Step 2: Check if timelog is closed.
     * Use formatted message for consistency with CHECK_CLOSED macro.
     */
    if (tl_obj->closed || tl_obj->tl == NULL) {
        TlPy_RaiseFromStatusFmt(TL_ESTATE, "Timelog is closed");
        return NULL;
    }

    /*
     * Step 3: Enter pins BEFORE iter_open.
     * This closes the window where compaction could drain retired handles
     * while we're acquiring the snapshot. See py_handle.h protocol docs.
     */
    tl_py_pins_enter(&tl_obj->handle_ctx);

    /*
     * Step 4: Allocate hook context.
     * We store a strong ref to timelog and the handle_ctx pointer.
     * The armed flag is initially 0 to prevent double cleanup.
     */
    tl_py_pagespan_hook_ctx_t* hook_ctx = PyMem_Malloc(sizeof(*hook_ctx));
    if (hook_ctx == NULL) {
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        PyErr_NoMemory();
        return NULL;
    }
    hook_ctx->timelog = Py_NewRef((PyObject*)tl_obj);
    hook_ctx->ctx = &tl_obj->handle_ctx;
    hook_ctx->armed = 0;

    /*
     * Step 5: Set up hooks for core owner.
     */
    tl_pagespan_owner_hooks_t hooks = {
        .user = hook_ctx,
        .on_release = tl_py_pagespan_on_release
    };

    /*
     * Step 6: Call core iter_open.
     * This acquires a snapshot, creates owner, and sets up streaming iteration.
     * The core copies our hooks into the owner struct.
     */
    uint32_t flags = TL_PAGESPAN_DEFAULT;
    tl_pagespan_iter_t* core_iter = NULL;

    tl_status_t st = tl_pagespan_iter_open(tl_obj->tl, t1, t2, flags, &hooks, &core_iter);

    if (st != TL_OK) {
        /*
         * CRITICAL: iter_open failed.
         * The core does NOT arm the hook until iter_open succeeds, so
         * the hook will NOT be invoked. We must clean up manually.
         */
        Py_DECREF(hook_ctx->timelog);
        PyMem_Free(hook_ctx);
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        TlPy_RaiseFromStatus(st);
        return NULL;
    }

    /*
     * Step 7: Arm the hook.
     * From this point, the core owns the hook context and will call it
     * when the owner refcount reaches 0.
     */
    hook_ctx->armed = 1;

    /*
     * Step 8: Allocate Python iterator object.
     */
    PyPageSpanIter* self = PyObject_GC_New(PyPageSpanIter, &PyPageSpanIter_Type);
    if (self == NULL) {
        /*
         * Python allocation failed.
         * Close core iter to trigger cleanup (which will invoke our hook).
         */
        tl_pagespan_iter_close(core_iter);
        return NULL;
    }

    /*
     * Step 9: Initialize iterator fields.
     */
    self->iter = core_iter;
    self->timelog = Py_NewRef((PyObject*)tl_obj);
    self->closed = 0;

    /*
     * Step 10: Track with GC.
     */
    PyObject_GC_Track((PyObject*)self);
    return (PyObject*)self;
}

/*===========================================================================
 * Cleanup (Single Source of Truth)
 *
 * Closes core iterator and clears Python references.
 * The core iter_close releases the iterator's owner ref, which may trigger
 * the release hook if that was the last ref.
 *===========================================================================*/

static void pagespaniter_cleanup(PyPageSpanIter* self)
{
    if (self->closed) {
        return;
    }
    self->closed = 1;

    /*
     * Close core iterator.
     * This releases the iterator's owner reference. If no spans are holding
     * refs, the owner is destroyed and our release hook is called.
     */
    tl_pagespan_iter_t* iter = self->iter;
    self->iter = NULL;

    if (iter != NULL) {
        tl_pagespan_iter_close(iter);
    }

    /*
     * Clear our timelog reference (for GC visibility).
     * Note: The hook context also holds a timelog ref which is released
     * by the hook when the owner is destroyed.
     *
     * Exception preservation: Py_CLEAR may trigger __del__ which can
     * clobber active exceptions (e.g., when __exit__ calls cleanup).
     * Per LLD-B6, preserve exception state across cleanup.
     */
    {
        PyObject *exc_type, *exc_value, *exc_tb;
        PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
        Py_CLEAR(self->timelog);
        PyErr_Restore(exc_type, exc_value, exc_tb);
    }
}

/*===========================================================================
 * GC Support
 *===========================================================================*/

static int PyPageSpanIter_traverse(PyPageSpanIter* self, visitproc visit, void* arg)
{
    /*
     * Visit timelog for GC cycle detection.
     * The core iterator is opaque and cannot be traversed.
     */
    Py_VISIT(self->timelog);
    return 0;
}

static int PyPageSpanIter_clear(PyPageSpanIter* self)
{
    pagespaniter_cleanup(self);
    return 0;
}

static void PyPageSpanIter_dealloc(PyPageSpanIter* self)
{
    PyObject_GC_UnTrack(self);
    pagespaniter_cleanup(self);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * Iterator Protocol
 *
 * Each __next__ call invokes core iter_next to get the next span on-demand.
 * This is streaming - no pre-collection of spans.
 *===========================================================================*/

static PyObject* PyPageSpanIter_iternext(PyPageSpanIter* self)
{
    /*
     * Check if closed or exhausted.
     */
    if (self->closed || self->iter == NULL) {
        return NULL;  /* StopIteration */
    }

    /*
     * Get next span from core iterator.
     */
    tl_pagespan_view_t view;
    memset(&view, 0, sizeof(view));

    tl_status_t st = tl_pagespan_iter_next(self->iter, &view);

    if (st == TL_OK) {
        /*
         * Got a span. Create PyPageSpan which CONSUMES the view's owner ref.
         * On success, PyPageSpan_FromView sets view.owner = NULL.
         */
        PyObject* span = PyPageSpan_FromView(&view, self->timelog);
        if (span == NULL) {
            /*
             * Creation failed - release the owner ref we received.
             */
            tl_pagespan_view_release(&view);
            return NULL;
        }
        return span;
    }

    if (st == TL_EOF) {
        /*
         * Exhausted - cleanup iterator.
         */
        pagespaniter_cleanup(self);
        return NULL;  /* StopIteration */
    }

    /*
     * Error - cleanup and raise.
     */
    pagespaniter_cleanup(self);
    TlPy_RaiseFromStatus(st);
    return NULL;
}

/*===========================================================================
 * Methods
 *===========================================================================*/

static PyObject* PyPageSpanIter_close(PyPageSpanIter* self, PyObject* noargs)
{
    (void)noargs;
    pagespaniter_cleanup(self);
    Py_RETURN_NONE;
}

static PyObject* PyPageSpanIter_enter(PyPageSpanIter* self, PyObject* noargs)
{
    (void)noargs;
    return Py_NewRef((PyObject*)self);
}

static PyObject* PyPageSpanIter_exit(PyPageSpanIter* self, PyObject* args)
{
    (void)args;
    pagespaniter_cleanup(self);
    Py_RETURN_FALSE;
}

/*===========================================================================
 * Properties
 *===========================================================================*/

static PyObject* PyPageSpanIter_get_closed(PyPageSpanIter* self, void* closure)
{
    (void)closure;
    return PyBool_FromLong(self->closed);
}

/*===========================================================================
 * Method/GetSet Tables
 *===========================================================================*/

static PyMethodDef PyPageSpanIter_methods[] = {
    {"close", (PyCFunction)PyPageSpanIter_close, METH_NOARGS,
     "close() -> None\n\nRelease iterator resources. Idempotent."},
    {"__enter__", (PyCFunction)PyPageSpanIter_enter, METH_NOARGS,
     "Context manager entry."},
    {"__exit__", (PyCFunction)PyPageSpanIter_exit, METH_VARARGS,
     "Context manager exit (closes iterator)."},
    {NULL, NULL, 0, NULL}
};

static PyGetSetDef PyPageSpanIter_getset[] = {
    {"closed", (getter)PyPageSpanIter_get_closed, NULL,
     "True if iterator is closed or exhausted.", NULL},
    {NULL, NULL, NULL, NULL, NULL}
};

/*===========================================================================
 * Type Object
 *===========================================================================*/

PyTypeObject PyPageSpanIter_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.PageSpanIter",
    .tp_doc = PyDoc_STR(
        "Streaming iterator yielding PageSpan objects for a time range.\n\n"
        "Cannot be instantiated directly; use Timelog.page_spans()."
    ),
    .tp_basicsize = sizeof(PyPageSpanIter),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_GC,
    .tp_new = PyPageSpanIter_new_error,
    .tp_dealloc = (destructor)PyPageSpanIter_dealloc,
    .tp_traverse = (traverseproc)PyPageSpanIter_traverse,
    .tp_clear = (inquiry)PyPageSpanIter_clear,
    .tp_free = PyObject_GC_Del,
    .tp_iter = PyObject_SelfIter,
    .tp_iternext = (iternextfunc)PyPageSpanIter_iternext,
    .tp_methods = PyPageSpanIter_methods,
    .tp_getset = PyPageSpanIter_getset,
};

/------------------------------------------------------------------------------/
/*   END OF: py_span_iter.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_span_objects.c
/*   FROM: bindings/cpython/src/
/*
/******************************************************************************/
/**
 * @file py_span_objects.c
 * @brief PyPageSpanObjectsView CPython extension type implementation (Core API Integration)
 *
 * Implements lazy access to decoded Python objects from a PageSpan.
 * Uses span->h[] pointer directly (borrowed from core owner's snapshot).
 *
 * See: docs/timelog_v2_lld_pagespan_cpython_bindings_update.md
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_span_objects.h"
#include "timelogpy/py_span.h"
#include "timelogpy/py_handle.h"

/*
 * NO storage headers needed - span->h and span->len provide direct access.
 */

/*===========================================================================
 * Py_NewRef Compatibility
 *===========================================================================*/

#if PY_VERSION_HEX < 0x030A0000
#ifndef TL_Py_NewRef_DEFINED
#define TL_Py_NewRef_DEFINED
static inline PyObject* TL_Py_NewRef_OV(PyObject* obj) {
    Py_INCREF(obj);
    return obj;
}
#define Py_NewRef TL_Py_NewRef_OV
#endif
#endif

/*===========================================================================
 * Block Direct Construction
 *===========================================================================*/

static PyObject* PyPageSpanObjectsView_new_error(PyTypeObject* type,
                                                  PyObject* args,
                                                  PyObject* kwds)
{
    (void)type;
    (void)args;
    (void)kwds;

    PyErr_SetString(PyExc_TypeError,
        "PageSpanObjectsView cannot be instantiated directly; "
        "use PageSpan.objects()");
    return NULL;
}

/*===========================================================================
 * Factory Function
 *===========================================================================*/

PyObject* PyPageSpanObjectsView_Create(PyObject* span)
{
    if (!PyPageSpan_Check(span)) {
        PyErr_SetString(PyExc_TypeError, "expected PageSpan");
        return NULL;
    }

    PyPageSpan* span_obj = (PyPageSpan*)span;
    if (span_obj->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    PyPageSpanObjectsView* self = PyObject_New(PyPageSpanObjectsView,
                                                &PyPageSpanObjectsView_Type);
    if (!self) {
        return NULL;
    }

    self->span = Py_NewRef(span);
    return (PyObject*)self;
}

/*===========================================================================
 * Dealloc
 *===========================================================================*/

static void PyPageSpanObjectsView_dealloc(PyPageSpanObjectsView* self)
{
    Py_XDECREF(self->span);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * Sequence Protocol
 *===========================================================================*/

static Py_ssize_t PyPageSpanObjectsView_length(PyPageSpanObjectsView* self)
{
    PyPageSpan* span = (PyPageSpan*)self->span;
    if (span->closed) {
        return 0;
    }
    return (Py_ssize_t)span->len;
}

static PyObject* PyPageSpanObjectsView_getitem(PyPageSpanObjectsView* self,
                                                Py_ssize_t index)
{
    PyPageSpan* span = (PyPageSpan*)self->span;

    if (span->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /*
     * Check handle pointer availability.
     * span->h may be NULL if handles are unavailable (future-proofing).
     */
    if (span->h == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }

    const Py_ssize_t len = (Py_ssize_t)span->len;

    /* Handle negative indices */
    if (index < 0) {
        index += len;
    }

    if (index < 0 || index >= len) {
        PyErr_SetString(PyExc_IndexError, "index out of range");
        return NULL;
    }

    /*
     * Access handle directly via span->h[index].
     * This is borrowed from the owner's snapshot and valid while span is open.
     */
    tl_handle_t h = span->h[index];
    PyObject* obj = tl_py_handle_decode(h);

    /* Defensive NULL check (handle could be corrupted) */
    if (!obj) {
        PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
        return NULL;
    }

    return Py_NewRef(obj);
}

static PySequenceMethods objectsview_as_sequence = {
    .sq_length = (lenfunc)PyPageSpanObjectsView_length,
    .sq_item = (ssizeargfunc)PyPageSpanObjectsView_getitem,
};

/*===========================================================================
 * Iterator Protocol
 *===========================================================================*/

typedef struct {
    PyObject_HEAD
    PyObject* view;     /* Strong ref to objects view */
    Py_ssize_t index;   /* Current position */
} PyPageSpanObjectsViewIter;

/* Forward declaration (non-static, exported via header) */
extern PyTypeObject PyPageSpanObjectsViewIter_Type;

static void objectsviewiter_dealloc(PyPageSpanObjectsViewIter* self)
{
    Py_XDECREF(self->view);
    Py_TYPE(self)->tp_free((PyObject*)self);
}

static PyObject* objectsviewiter_next(PyPageSpanObjectsViewIter* self)
{
    PyPageSpanObjectsView* view = (PyPageSpanObjectsView*)self->view;
    PyPageSpan* span = (PyPageSpan*)view->span;

    if (span->closed) {
        return NULL;  /* StopIteration */
    }

    /*
     * Check handle pointer availability.
     * span->h may be NULL if handles are unavailable (future-proofing).
     */
    if (span->h == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }

    const Py_ssize_t len = (Py_ssize_t)span->len;

    if (self->index >= len) {
        return NULL;  /* StopIteration */
    }

    /*
     * Access handle directly via span->h[index].
     * This is borrowed from the owner's snapshot and valid while span is open.
     */
    tl_handle_t h = span->h[self->index];
    PyObject* obj = tl_py_handle_decode(h);

    /* Defensive NULL check (handle could be corrupted) */
    if (!obj) {
        PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
        return NULL;
    }

    self->index++;
    return Py_NewRef(obj);
}

/* Exported (non-static) so module.c can call PyType_Ready */
PyTypeObject PyPageSpanObjectsViewIter_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.PageSpanObjectsViewIter",
    .tp_basicsize = sizeof(PyPageSpanObjectsViewIter),
    .tp_dealloc = (destructor)objectsviewiter_dealloc,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_iter = PyObject_SelfIter,
    .tp_iternext = (iternextfunc)objectsviewiter_next,
};

static PyObject* PyPageSpanObjectsView_iter(PyPageSpanObjectsView* self)
{
    /* Type is readied by module init (module.c) - no lazy init needed.
     * This avoids a potential race condition in free-threaded Python builds.
     */

    PyPageSpanObjectsViewIter* iter = PyObject_New(PyPageSpanObjectsViewIter,
                                                    &PyPageSpanObjectsViewIter_Type);
    if (!iter) {
        return NULL;
    }

    iter->view = Py_NewRef((PyObject*)self);
    iter->index = 0;

    return (PyObject*)iter;
}

/*===========================================================================
 * Methods
 *===========================================================================*/

static PyObject* PyPageSpanObjectsView_copy(PyPageSpanObjectsView* self,
                                             PyObject* noargs)
{
    (void)noargs;

    PyPageSpan* span = (PyPageSpan*)self->span;

    if (span->closed) {
        PyErr_SetString(PyExc_ValueError, "PageSpan is closed");
        return NULL;
    }

    /*
     * Check handle pointer availability.
     * span->h may be NULL if handles are unavailable (future-proofing).
     */
    if (span->h == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "handles not available in this span");
        return NULL;
    }

    const Py_ssize_t len = (Py_ssize_t)span->len;

    PyObject* list = PyList_New(len);
    if (!list) {
        return NULL;
    }

    for (Py_ssize_t i = 0; i < len; i++) {
        /*
         * Access handle directly via span->h[i].
         * This is borrowed from the owner's snapshot and valid while span is open.
         */
        tl_handle_t h = span->h[i];
        PyObject* obj = tl_py_handle_decode(h);

        /* Defensive NULL check */
        if (!obj) {
            Py_DECREF(list);
            PyErr_SetString(PyExc_RuntimeError, "invalid handle in span");
            return NULL;
        }

        PyList_SET_ITEM(list, i, Py_NewRef(obj));
    }

    return list;
}

static PyMethodDef PyPageSpanObjectsView_methods[] = {
    {"copy", (PyCFunction)PyPageSpanObjectsView_copy, METH_NOARGS,
     "copy() -> list[object]\n\n"
     "Return a copy of all objects as a Python list."},
    {NULL, NULL, 0, NULL}
};

/*===========================================================================
 * Type Object
 *===========================================================================*/

PyTypeObject PyPageSpanObjectsView_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.PageSpanObjectsView",
    .tp_doc = PyDoc_STR(
        "Lazy sequence view over decoded Python objects from a PageSpan.\n\n"
        "Supports len(), indexing, and iteration.\n"
        "Cannot be instantiated directly; use PageSpan.objects()."
    ),
    .tp_basicsize = sizeof(PyPageSpanObjectsView),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT,
    .tp_new = PyPageSpanObjectsView_new_error,
    .tp_dealloc = (destructor)PyPageSpanObjectsView_dealloc,
    .tp_as_sequence = &objectsview_as_sequence,
    .tp_iter = (getiterfunc)PyPageSpanObjectsView_iter,
    .tp_methods = PyPageSpanObjectsView_methods,
};

/------------------------------------------------------------------------------/
/*   END OF: py_span_objects.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: py_timelog.c
/*   FROM: bindings/cpython/src/
/*
/******************************************************************************/
/**
 * @file py_timelog.c
 * @brief PyTimelog CPython extension implementation (LLD-B2)
 *
 * Implementation of the PyTimelog type which wraps tl_timelog_t*.
 * Follows the engineering plan in docs/engineering_plan_B2_pytimelog.md
 *
 * CRITICAL SEMANTICS:
 * - TL_EBUSY from write operations means record/tombstone WAS inserted
 * - Do NOT rollback INCREF on TL_EBUSY
 * - Do NOT retry on TL_EBUSY (would create duplicates)
 *
 * Thread Safety:
 * - GIL released only for: flush, compact, stop_maintenance, close
 * - All write operations hold GIL throughout
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_timelog.h"
#include "timelogpy/py_iter.h"
#include "timelogpy/py_span_iter.h"  /* LLD-B4: PageSpan factory */
#include "timelogpy/py_handle.h"
#include "timelogpy/py_errors.h"
#include "timelog/timelog.h"

#include <string.h>
#include <stdint.h>

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static PyObject* PyTimelog_close(PyTimelog* self, PyObject* Py_UNUSED(args));

/*===========================================================================
 * Config Parsing Helpers
 *===========================================================================*/

/**
 * Parse time_unit string to tl_time_unit_t.
 *
 * IMPORTANT: Don't override engine default when omitted.
 * Engine defaults to TL_TIME_MS.
 *
 * @param s         Input string (may be NULL)
 * @param out       Output time unit
 * @param was_set   Output: 1 if explicitly set, 0 if using default
 * @return 0 on success, -1 on error (exception set)
 */
static int parse_time_unit(const char* s, tl_time_unit_t* out, int* was_set)
{
    *was_set = 0;
    if (s == NULL) {
        return 0;  /* Leave at engine default (TL_TIME_MS) */
    }
    *was_set = 1;
    if (strcmp(s, "s") == 0)  { *out = TL_TIME_S;  return 0; }
    if (strcmp(s, "ms") == 0) { *out = TL_TIME_MS; return 0; }
    if (strcmp(s, "us") == 0) { *out = TL_TIME_US; return 0; }
    if (strcmp(s, "ns") == 0) { *out = TL_TIME_NS; return 0; }
    PyErr_Format(PyExc_ValueError,
        "Invalid time_unit: '%s' (expected 's', 'ms', 'us', or 'ns')", s);
    return -1;
}

/**
 * Parse maintenance mode string to tl_maint_mode_t.
 */
static int parse_maint_mode(const char* s, tl_maint_mode_t* out)
{
    if (s == NULL) {
        *out = TL_MAINT_BACKGROUND;
        return 0;
    }
    if (strcmp(s, "disabled") == 0) {
        *out = TL_MAINT_DISABLED;
        return 0;
    }
    if (strcmp(s, "background") == 0) {
        *out = TL_MAINT_BACKGROUND;
        return 0;
    }
    PyErr_Format(PyExc_ValueError,
        "Invalid maintenance mode: '%s' (expected 'disabled' or 'background')", s);
    return -1;
}

/**
 * Parse busy_policy string to tl_py_busy_policy_t.
 */
static int parse_busy_policy(const char* s, tl_py_busy_policy_t* out)
{
    if (s == NULL || strcmp(s, "raise") == 0) {
        *out = TL_PY_BUSY_RAISE;
        return 0;
    }
    if (strcmp(s, "silent") == 0) {
        *out = TL_PY_BUSY_SILENT;
        return 0;
    }
    if (strcmp(s, "flush") == 0) {
        *out = TL_PY_BUSY_FLUSH;
        return 0;
    }
    PyErr_Format(PyExc_ValueError,
        "Invalid busy_policy: '%s' (expected 'raise', 'silent', or 'flush')", s);
    return -1;
}

/*===========================================================================
 * PyTimelog_init (tp_init)
 *===========================================================================*/

static int
PyTimelog_init(PyTimelog* self, PyObject* args, PyObject* kwds)
{
    /* Check if already initialized (re-init not allowed) */
    if (self->tl != NULL) {
        PyErr_SetString(PyExc_TypeError, "Timelog already initialized");
        return -1;
    }

    static char* kwlist[] = {
        "time_unit",           /* s - string */
        "maintenance",         /* s - string */
        "memtable_max_bytes",  /* n - Py_ssize_t */
        "target_page_bytes",   /* n - Py_ssize_t */
        "sealed_max_runs",     /* n - Py_ssize_t */
        "drain_batch_limit",   /* n - Py_ssize_t */
        "busy_policy",         /* s - string */
        NULL
    };

    const char* time_unit_str = NULL;
    const char* maint_str = NULL;
    Py_ssize_t memtable_max_bytes = -1;
    Py_ssize_t target_page_bytes = -1;
    Py_ssize_t sealed_max_runs = -1;
    Py_ssize_t drain_batch_limit = -1;
    const char* busy_policy_str = NULL;

    /* CRITICAL: 7 converters for 7 kwargs */
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|ssnnnns", kwlist,
            &time_unit_str, &maint_str,
            &memtable_max_bytes, &target_page_bytes, &sealed_max_runs,
            &drain_batch_limit, &busy_policy_str)) {
        return -1;
    }

    /* Validate drain_batch_limit range */
    if (drain_batch_limit != -1) {
        if (drain_batch_limit < 0 || (uint64_t)drain_batch_limit > UINT32_MAX) {
            PyErr_SetString(PyExc_ValueError,
                "drain_batch_limit must be 0-4294967295");
            return -1;
        }
    }

    /* Map -1 (unset) to 0 (unlimited) for ctx init */
    uint32_t drain_limit = (drain_batch_limit == -1) ? 0 : (uint32_t)drain_batch_limit;

    /* Initialize handle context first */
    tl_status_t st = tl_py_handle_ctx_init(&self->handle_ctx, drain_limit);
    if (st != TL_OK) {
        TlPy_RaiseFromStatus(st);
        return -1;
    }

    /* Build tl_config_t */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    /* Parse and apply time_unit */
    int time_unit_set;
    if (parse_time_unit(time_unit_str, &cfg.time_unit, &time_unit_set) < 0) {
        tl_py_handle_ctx_destroy(&self->handle_ctx);
        return -1;
    }

    /* Parse and apply maintenance mode */
    if (parse_maint_mode(maint_str, &cfg.maintenance_mode) < 0) {
        tl_py_handle_ctx_destroy(&self->handle_ctx);
        return -1;
    }

    /* Parse and apply busy_policy */
    if (parse_busy_policy(busy_policy_str, &self->busy_policy) < 0) {
        tl_py_handle_ctx_destroy(&self->handle_ctx);
        return -1;
    }

    /*
     * Apply numeric overrides with validation.
     * -1 = unset (use default), 0 or negative = ValueError, positive = apply.
     * Also check for overflow on platforms where size_t < Py_ssize_t.
     */
    if (memtable_max_bytes != -1) {
        if (memtable_max_bytes <= 0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "memtable_max_bytes must be positive");
            return -1;
        }
        if ((size_t)memtable_max_bytes != (uint64_t)memtable_max_bytes) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_OverflowError,
                "memtable_max_bytes too large for this platform");
            return -1;
        }
        cfg.memtable_max_bytes = (size_t)memtable_max_bytes;
    }
    if (target_page_bytes != -1) {
        if (target_page_bytes <= 0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "target_page_bytes must be positive");
            return -1;
        }
        if ((size_t)target_page_bytes != (uint64_t)target_page_bytes) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_OverflowError,
                "target_page_bytes too large for this platform");
            return -1;
        }
        cfg.target_page_bytes = (size_t)target_page_bytes;
    }
    if (sealed_max_runs != -1) {
        if (sealed_max_runs <= 0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "sealed_max_runs must be positive");
            return -1;
        }
        if ((size_t)sealed_max_runs != (uint64_t)sealed_max_runs) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_OverflowError,
                "sealed_max_runs too large for this platform");
            return -1;
        }
        cfg.sealed_max_runs = (size_t)sealed_max_runs;
    }

    /* Wire up drop callback */
    cfg.on_drop_handle = tl_py_on_drop_handle;
    cfg.on_drop_ctx = &self->handle_ctx;

    /* Open the timelog */
    st = tl_open(&cfg, &self->tl);
    if (st != TL_OK) {
        tl_py_handle_ctx_destroy(&self->handle_ctx);
        self->tl = NULL;
        self->closed = 1;
        TlPy_RaiseFromStatus(st);
        return -1;
    }

    /* Success - store introspection fields */
    self->closed = 0;
    self->time_unit = time_unit_set ? cfg.time_unit : TL_TIME_MS;
    self->maint_mode = cfg.maintenance_mode;

    /* Auto-start maintenance when in background mode. */
    if (self->maint_mode == TL_MAINT_BACKGROUND) {
        st = tl_maint_start(self->tl);
        if (st != TL_OK) {
            tl_maint_stop(self->tl);
            tl_close(self->tl);
            self->tl = NULL;
            self->closed = 1;
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            TlPy_RaiseFromStatus(st);
            return -1;
        }
    }

    return 0;
}

/*===========================================================================
 * PyTimelog_close
 *===========================================================================*/

static PyObject*
PyTimelog_close(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    /* Idempotent - already closed */
    if (self->closed) {
        Py_RETURN_NONE;
    }

    /* Handle case where tl is already NULL */
    if (self->tl == NULL) {
        self->closed = 1;
        tl_py_handle_ctx_destroy(&self->handle_ctx);
        Py_RETURN_NONE;
    }

    /*
     * Check pins BEFORE any irreversible operations.
     * This prevents the inconsistent state where maintenance is stopped
     * but we rollback because of active pins.
     */
    uint64_t pins = tl_py_pins_count(&self->handle_ctx);
    if (pins != 0) {
        return TlPy_RaiseFromStatusFmt(TL_ESTATE,
            "Cannot close: %llu active snapshots/iterators",
            (unsigned long long)pins);
    }

    /* Mark closed (reentrancy guard) - after pins check passes */
    self->closed = 1;

    /*
     * Stop maintenance (release GIL).
     * Ignore return value - close is a "must complete" operation.
     * Any maint_stop failure is logged internally but shouldn't
     * prevent cleanup from proceeding.
     */
    Py_BEGIN_ALLOW_THREADS
    tl_maint_stop(self->tl);
    Py_END_ALLOW_THREADS

    /* Close engine (may release GIL if slow) */
    Py_BEGIN_ALLOW_THREADS
    tl_close(self->tl);
    Py_END_ALLOW_THREADS

    /* Clear pointer */
    self->tl = NULL;

    /*
     * Drain retired objects (force=1).
     * Preserve exception state: drain executes Py_DECREF which can
     * trigger __del__ methods that may clobber active exceptions
     * (e.g., when close() is called from __exit__).
     */
    {
        PyObject *exc_type, *exc_value, *exc_tb;
        PyErr_Fetch(&exc_type, &exc_value, &exc_tb);

        tl_py_drain_retired(&self->handle_ctx, 1);

        PyErr_Restore(exc_type, exc_value, exc_tb);
    }

    /* Destroy handle context */
    tl_py_handle_ctx_destroy(&self->handle_ctx);

    Py_RETURN_NONE;
}

/*===========================================================================
 * PyTimelog_dealloc (tp_dealloc)
 *===========================================================================*/

static void
PyTimelog_dealloc(PyTimelog* self)
{
    /*
     * Best-effort close if not already closed.
     *
     * Note: The condition `!self->closed && self->tl != NULL` is carefully
     * chosen. If init() fails after handle_ctx_init but before tl_open,
     * handle_ctx is destroyed in init(), and self->tl remains NULL.
     * This condition correctly skips cleanup in that case.
     */
    if (!self->closed && self->tl != NULL) {
        uint64_t pins = tl_py_pins_count(&self->handle_ctx);
        if (pins == 0) {
            Py_BEGIN_ALLOW_THREADS
            tl_maint_stop(self->tl);
            tl_close(self->tl);
            Py_END_ALLOW_THREADS

            /*
             * Drain retired objects with exception preservation.
             * Per LLD-B6: Py_DECREF in drain can trigger __del__ that
             * may clobber active exceptions during finalization.
             */
            {
                PyObject *exc_type, *exc_value, *exc_tb;
                PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
                tl_py_drain_retired(&self->handle_ctx, 1);
                PyErr_Restore(exc_type, exc_value, exc_tb);
            }

            tl_py_handle_ctx_destroy(&self->handle_ctx);
        } else {
            /* WARNING: leaking resources (pins active) */
#ifndef NDEBUG
            fprintf(stderr, "WARNING: PyTimelog dealloc with pins=%llu\n",
                    (unsigned long long)pins);
#endif
        }
    }

    /* Free object */
    Py_TYPE(self)->tp_free((PyObject*)self);
}

/*===========================================================================
 * PyTimelog_append
 *
 * CRITICAL: TL_EBUSY means record WAS inserted.
 * - Do NOT rollback INCREF on EBUSY
 * - Do NOT retry on EBUSY
 *===========================================================================*/

static PyObject*
PyTimelog_append(PyTimelog* self, PyObject* args)
{
    CHECK_CLOSED(self);

    long long ts_ll;
    PyObject* obj;
    if (!PyArg_ParseTuple(args, "LO", &ts_ll, &obj)) {
        return NULL;
    }

    /* Validate timestamp range */
    if (ts_ll < TL_TS_MIN || ts_ll > TL_TS_MAX) {
        return PyErr_Format(PyExc_OverflowError,
            "timestamp %lld out of int64 range", ts_ll);
    }

    /* INCREF object (engine-owned reference) */
    Py_INCREF(obj);

    /* Encode and append */
    tl_handle_t h = tl_py_handle_encode(obj);
    tl_ts_t ts = (tl_ts_t)ts_ll;
    tl_status_t st = tl_append(self->tl, ts, h);

    if (st == TL_OK) {
        goto success;
    }

    if (st == TL_EBUSY) {
        /*
         * CRITICAL: EBUSY means record WAS inserted, but backpressure occurred.
         * This only happens in manual maintenance mode.
         *
         * DO NOT rollback INCREF - record is in engine.
         * DO NOT retry - would create duplicate.
         */
        if (self->busy_policy == TL_PY_BUSY_RAISE) {
            /* Raise informational exception - record IS in log */
            PyErr_SetString(TlPy_TimelogBusyError,
                "Record inserted but backpressure occurred. "
                "Call flush() or run maintenance to relieve.");
            return NULL;
        }

        /* SILENT: fall through to success */

        if (self->busy_policy == TL_PY_BUSY_FLUSH) {
            /* Flush to relieve backpressure (record already safe) */
            tl_status_t flush_st;
            Py_BEGIN_ALLOW_THREADS
            flush_st = tl_flush(self->tl);
            Py_END_ALLOW_THREADS

            if (flush_st != TL_OK && flush_st != TL_EOF) {
#ifndef NDEBUG
                fprintf(stderr, "WARNING: flush after EBUSY failed: %d\n", flush_st);
#endif
            }
            /* Record is safe regardless of flush result */
        }
        goto success;
    }

    /* True failure - rollback INCREF */
    Py_DECREF(obj);
    return TlPy_RaiseFromStatus(st);

success:
    /* Opportunistic drain */
    tl_py_drain_retired(&self->handle_ctx, 0);
    Py_RETURN_NONE;
}

/*===========================================================================
 * PyTimelog_extend
 *
 * CRITICAL: obj is borrowed from item. INCREF obj BEFORE DECREF item.
 *===========================================================================*/

static PyObject*
PyTimelog_extend(PyTimelog* self, PyObject* iterable)
{
    CHECK_CLOSED(self);

    PyObject* iter = PyObject_GetIter(iterable);
    if (iter == NULL) {
        return NULL;
    }

    PyObject* item;
    while ((item = PyIter_Next(iter)) != NULL) {
        long long ts_ll;
        PyObject* obj;

        /* Parse (ts, obj) from item */
        if (!PyArg_ParseTuple(item, "LO", &ts_ll, &obj)) {
            Py_DECREF(item);
            Py_DECREF(iter);
            return NULL;
        }

        /*
         * CRITICAL FIX: INCREF obj BEFORE DECREF item
         * obj is a borrowed reference from item. If we decref item first,
         * obj may be freed (use-after-free).
         */
        Py_INCREF(obj);
        Py_DECREF(item);

        /* Validate timestamp range */
        if (ts_ll < TL_TS_MIN || ts_ll > TL_TS_MAX) {
            Py_DECREF(obj);
            Py_DECREF(iter);
            return PyErr_Format(PyExc_OverflowError,
                "timestamp %lld out of int64 range", ts_ll);
        }

        /* Append to engine */
        tl_handle_t h = tl_py_handle_encode(obj);
        tl_status_t st = tl_append(self->tl, (tl_ts_t)ts_ll, h);

        /*
         * Handle result - EBUSY means success!
         * Only rollback on TRUE failure.
         */
        if (st != TL_OK && st != TL_EBUSY) {
            Py_DECREF(obj);  /* Rollback only on true failure */
            Py_DECREF(iter);
            return TlPy_RaiseFromStatus(st);
        }

        /* Handle EBUSY (record IS inserted, just backpressure) */
        if (st == TL_EBUSY) {
            if (self->busy_policy == TL_PY_BUSY_RAISE) {
                Py_DECREF(iter);
                PyErr_SetString(TlPy_TimelogBusyError,
                    "Backpressure during batch insert. "
                    "Records up to and including this one are committed; "
                    "remaining records were not attempted. "
                    "Call flush() or run maintenance to relieve.");
                return NULL;
            }

            /* FLUSH policy: flush to relieve backpressure */
            if (self->busy_policy == TL_PY_BUSY_FLUSH) {
                tl_status_t flush_st;
                Py_BEGIN_ALLOW_THREADS
                flush_st = tl_flush(self->tl);
                Py_END_ALLOW_THREADS

                if (flush_st != TL_OK && flush_st != TL_EOF) {
#ifndef NDEBUG
                    fprintf(stderr, "WARNING: flush after EBUSY failed: %d\n", flush_st);
#endif
                }
            }
            /* SILENT: continue to next item */
        }
    }

    Py_DECREF(iter);

    /* Check for iteration error */
    if (PyErr_Occurred()) {
        return NULL;
    }

    /* Opportunistic drain */
    tl_py_drain_retired(&self->handle_ctx, 0);
    Py_RETURN_NONE;
}

/*===========================================================================
 * PyTimelog_delete_range
 *
 * CRITICAL: Same TL_EBUSY semantics as append.
 *===========================================================================*/

static PyObject*
PyTimelog_delete_range(PyTimelog* self, PyObject* args)
{
    CHECK_CLOSED(self);

    long long t1_ll, t2_ll;
    if (!PyArg_ParseTuple(args, "LL", &t1_ll, &t2_ll)) {
        return NULL;
    }

    /* Validate: t1 > t2 is invalid, but t1 == t2 is allowed (empty range, no-op) */
    if (t1_ll > t2_ll) {
        return PyErr_Format(PyExc_ValueError,
            "t1 (%lld) must be <= t2 (%lld)", t1_ll, t2_ll);
    }

    tl_status_t st = tl_delete_range(self->tl, (tl_ts_t)t1_ll, (tl_ts_t)t2_ll);

    if (st == TL_OK) {
        goto success;
    }

    if (st == TL_EBUSY) {
        /*
         * CRITICAL: EBUSY means tombstone WAS inserted, but backpressure.
         * Same handling as append.
         */
        if (self->busy_policy == TL_PY_BUSY_RAISE) {
            PyErr_SetString(TlPy_TimelogBusyError,
                "Tombstone inserted but backpressure occurred. "
                "Call flush() or run maintenance to relieve.");
            return NULL;
        }
        if (self->busy_policy == TL_PY_BUSY_FLUSH) {
            tl_status_t flush_st;
            Py_BEGIN_ALLOW_THREADS
            flush_st = tl_flush(self->tl);
            Py_END_ALLOW_THREADS

            if (flush_st != TL_OK && flush_st != TL_EOF) {
#ifndef NDEBUG
                fprintf(stderr, "WARNING: flush after EBUSY failed: %d\n", flush_st);
#endif
            }
        }
        goto success;
    }

    return TlPy_RaiseFromStatus(st);

success:
    tl_py_drain_retired(&self->handle_ctx, 0);
    Py_RETURN_NONE;
}

/*===========================================================================
 * PyTimelog_delete_before
 *===========================================================================*/

static PyObject*
PyTimelog_delete_before(PyTimelog* self, PyObject* args)
{
    CHECK_CLOSED(self);

    long long cutoff_ll;
    if (!PyArg_ParseTuple(args, "L", &cutoff_ll)) {
        return NULL;
    }

    tl_status_t st = tl_delete_before(self->tl, (tl_ts_t)cutoff_ll);

    if (st == TL_OK) {
        goto success;
    }

    if (st == TL_EBUSY) {
        /* Same handling as delete_range */
        if (self->busy_policy == TL_PY_BUSY_RAISE) {
            PyErr_SetString(TlPy_TimelogBusyError,
                "Tombstone inserted but backpressure occurred. "
                "Call flush() or run maintenance to relieve.");
            return NULL;
        }
        if (self->busy_policy == TL_PY_BUSY_FLUSH) {
            tl_status_t flush_st;
            Py_BEGIN_ALLOW_THREADS
            flush_st = tl_flush(self->tl);
            Py_END_ALLOW_THREADS

            if (flush_st != TL_OK && flush_st != TL_EOF) {
#ifndef NDEBUG
                fprintf(stderr, "WARNING: flush after EBUSY failed: %d\n", flush_st);
#endif
            }
        }
        goto success;
    }

    return TlPy_RaiseFromStatus(st);

success:
    tl_py_drain_retired(&self->handle_ctx, 0);
    Py_RETURN_NONE;
}

/*===========================================================================
 * PyTimelog_flush
 *===========================================================================*/

static PyObject*
PyTimelog_flush(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_status_t st;
    Py_BEGIN_ALLOW_THREADS
    st = tl_flush(self->tl);
    Py_END_ALLOW_THREADS

    if (st != TL_OK && st != TL_EOF) {
        return TlPy_RaiseFromStatus(st);
    }

    /* Drain under GIL */
    tl_py_drain_retired(&self->handle_ctx, 0);

    Py_RETURN_NONE;
}

/*===========================================================================
 * PyTimelog_compact
 *===========================================================================*/

static PyObject*
PyTimelog_compact(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_status_t st;
    Py_BEGIN_ALLOW_THREADS
    st = tl_compact(self->tl);
    Py_END_ALLOW_THREADS

    if (st != TL_OK && st != TL_EOF) {
        return TlPy_RaiseFromStatus(st);
    }

    /*
     * Note: In manual mode (maintenance='disabled'), compact() only requests
     * compaction. The actual work happens when the background worker runs
     * (if later started) or the application calls tl_maint_step() externally.
     *
     * For V1, we do NOT expose maint_step() to Python. Manual mode is for
     * advanced use cases where the caller controls the maintenance loop.
     * Typical Python usage should use maintenance='background'.
     */

    /* Opportunistic drain after compact */
    tl_py_drain_retired(&self->handle_ctx, 0);

    Py_RETURN_NONE;
}

/*===========================================================================
 * PyTimelog_start_maint
 *===========================================================================*/

static PyObject*
PyTimelog_start_maint(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    if (self->maint_mode != TL_MAINT_BACKGROUND) {
        return TlPy_RaiseFromStatusFmt(TL_ESTATE,
            "start_maintenance requires maintenance='background'");
    }

    tl_status_t st = tl_maint_start(self->tl);

    /* TL_OK = started or already running (idempotent) */
    if (st == TL_OK) {
        Py_RETURN_NONE;
    }

    /* TL_EBUSY = stop in progress, caller should retry */
    return TlPy_RaiseFromStatus(st);
}

/*===========================================================================
 * PyTimelog_stop_maint
 *===========================================================================*/

static PyObject*
PyTimelog_stop_maint(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_status_t st;
    Py_BEGIN_ALLOW_THREADS
    st = tl_maint_stop(self->tl);  /* Blocks until worker exits */
    Py_END_ALLOW_THREADS

    if (st != TL_OK) {
        return TlPy_RaiseFromStatus(st);
    }

    /* Drain after stop - no more on_drop callbacks possible */
    tl_py_drain_retired(&self->handle_ctx, 0);

    Py_RETURN_NONE;
}

/*===========================================================================
 * Context Manager
 *===========================================================================*/

static PyObject*
PyTimelog_enter(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    if (self->closed) {
        return TlPy_RaiseFromStatusFmt(TL_ESTATE, "Timelog is closed");
    }

    /*
     * Auto-start maintenance worker when in background mode.
     *
     * When users create a Timelog with maintenance="background" and use the
     * context manager, they expect background maintenance to run automatically.
     * Without this, writes that trigger backpressure would wait on a condvar
     * that never gets signaled (because the worker isn't running), causing
     * writes to take 100ms each (the sealed_wait_ms timeout).
     *
     * Note: close() (called by __exit__) already calls tl_maint_stop().
     */
    if (self->maint_mode == TL_MAINT_BACKGROUND) {
        tl_status_t st = tl_maint_start(self->tl);
        if (st != TL_OK && st != TL_EBUSY) {
            /* TL_EBUSY means stop in progress - shouldn't happen on fresh open.
             * Any other error is a real problem. */
            return TlPy_RaiseFromStatus(st);
        }
        /* TL_OK = started (or already running - idempotent) */
    }

    Py_INCREF(self);
    return (PyObject*)self;
}

/*
 * __exit__ error handling rules:
 * - If `with` block raised: suppress close() errors, propagate original
 * - If `with` block succeeded: propagate close() errors
 */
static PyObject*
PyTimelog_exit(PyTimelog* self, PyObject* args)
{
    PyObject* exc_type = NULL;
    PyObject* exc_val = NULL;
    PyObject* exc_tb = NULL;

    if (!PyArg_ParseTuple(args, "OOO", &exc_type, &exc_val, &exc_tb)) {
        return NULL;
    }

    PyObject* result = PyTimelog_close(self, NULL);

    if (result == NULL) {
        /* close() raised an exception */
        if (exc_type == Py_None) {
            /*
             * No original exception from the with block.
             * Propagate the close() error.
             */
            return NULL;
        }
        /*
         * Original exception exists from with block.
         * Suppress close() error to preserve original context.
         */
        PyErr_Clear();
        Py_RETURN_FALSE;
    }

    Py_DECREF(result);
    Py_RETURN_FALSE;  /* Don't suppress original exception */
}

/*===========================================================================
 * Iterator Factory (LLD-B3)
 *
 * Creates PyTimelogIter instances for range queries.
 * Follows the protocol: pins_enter → snapshot_acquire → iter_create → track
 *===========================================================================*/

/**
 * Iterator mode enumeration.
 */
typedef enum {
    ITER_MODE_RANGE,
    ITER_MODE_SINCE,
    ITER_MODE_UNTIL,
    ITER_MODE_EQUAL,
    ITER_MODE_POINT
} iter_mode_t;

/**
 * Internal factory: create a PyTimelogIter for the given mode and timestamps.
 *
 * @param self   The PyTimelog instance
 * @param mode   Iterator mode (range, since, until, equal, point)
 * @param t1     First timestamp (interpretation depends on mode)
 * @param t2     Second timestamp (only used by ITER_MODE_RANGE)
 * @return       New reference to PyTimelogIter, or NULL on error
 */
static PyObject* pytimelog_make_iter(PyTimelog* self,
                                     iter_mode_t mode,
                                     tl_ts_t t1, tl_ts_t t2)
{
    CHECK_CLOSED(self);

    tl_py_handle_ctx_t* ctx = &self->handle_ctx;  /* NOTE: & for embedded */

    /* Enter pins BEFORE acquiring snapshot */
    tl_py_pins_enter(ctx);

    /* Acquire snapshot */
    tl_snapshot_t* snap = NULL;
    tl_status_t st = tl_snapshot_acquire(self->tl, &snap);
    if (st != TL_OK) {
        tl_py_pins_exit_and_maybe_drain(ctx);
        return TlPy_RaiseFromStatus(st);
    }

    /* Create core iterator */
    tl_iter_t* it = NULL;
    switch (mode) {
        case ITER_MODE_RANGE:
            st = tl_iter_range(snap, t1, t2, &it);
            break;
        case ITER_MODE_SINCE:
            st = tl_iter_since(snap, t1, &it);
            break;
        case ITER_MODE_UNTIL:
            st = tl_iter_until(snap, t2, &it);
            break;
        case ITER_MODE_EQUAL:
            st = tl_iter_equal(snap, t1, &it);
            break;
        case ITER_MODE_POINT:
            st = tl_iter_point(snap, t1, &it);
            break;

        default:
            /* Unreachable: enum covers all cases, but satisfy -Wswitch-default */
            tl_snapshot_release(snap);
            tl_py_pins_exit_and_maybe_drain(ctx);
            PyErr_SetString(PyExc_SystemError, "Invalid iterator mode");
            return NULL;
    }

    if (st != TL_OK) {
        tl_snapshot_release(snap);
        tl_py_pins_exit_and_maybe_drain(ctx);
        return TlPy_RaiseFromStatus(st);
    }

    /* Allocate Python iterator object */
    PyTimelogIter* pyit = PyObject_GC_New(PyTimelogIter, &PyTimelogIter_Type);
    if (!pyit) {
        tl_iter_destroy(it);
        tl_snapshot_release(snap);
        tl_py_pins_exit_and_maybe_drain(ctx);
        return PyErr_NoMemory();
    }

    /* Initialize fields */
    pyit->owner = Py_NewRef((PyObject*)self);
    pyit->snapshot = snap;
    pyit->iter = it;
    pyit->handle_ctx = ctx;  /* borrowed pointer, safe due to strong owner ref */
    pyit->closed = 0;

    /* Enable GC tracking */
    PyObject_GC_Track((PyObject*)pyit);

    return (PyObject*)pyit;
}

/**
 * Timelog.range(t1, t2) -> TimelogIter
 *
 * Create an iterator for records in [t1, t2).
 * If t1 >= t2, returns empty iterator (mirrors core behavior).
 */
static PyObject* PyTimelog_range(PyTimelog* self, PyObject* args)
{
    long long t1, t2;

    if (!PyArg_ParseTuple(args, "LL", &t1, &t2)) {
        return NULL;
    }

    return pytimelog_make_iter(self, ITER_MODE_RANGE, (tl_ts_t)t1, (tl_ts_t)t2);
}

/**
 * Timelog.since(t) -> TimelogIter
 *
 * Create an iterator for records with ts >= t.
 */
static PyObject* PyTimelog_since(PyTimelog* self, PyObject* args)
{
    long long t;

    if (!PyArg_ParseTuple(args, "L", &t)) {
        return NULL;
    }

    return pytimelog_make_iter(self, ITER_MODE_SINCE, (tl_ts_t)t, 0);
}

/**
 * Timelog.until(t) -> TimelogIter
 *
 * Create an iterator for records with ts < t.
 */
static PyObject* PyTimelog_until(PyTimelog* self, PyObject* args)
{
    long long t;

    if (!PyArg_ParseTuple(args, "L", &t)) {
        return NULL;
    }

    return pytimelog_make_iter(self, ITER_MODE_UNTIL, 0, (tl_ts_t)t);
}

/**
 * Timelog.all() -> TimelogIter
 *
 * Create an iterator for all records.
 */
static PyObject* PyTimelog_all(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    /* all() is since(TL_TS_MIN) */
    return pytimelog_make_iter(self, ITER_MODE_SINCE, TL_TS_MIN, 0);
}

/**
 * Timelog.equal(t) -> TimelogIter
 *
 * Create an iterator for records with ts == t.
 */
static PyObject* PyTimelog_equal(PyTimelog* self, PyObject* args)
{
    long long t;

    if (!PyArg_ParseTuple(args, "L", &t)) {
        return NULL;
    }

    return pytimelog_make_iter(self, ITER_MODE_EQUAL, (tl_ts_t)t, 0);
}

/**
 * Timelog.point(t) -> TimelogIter
 *
 * Create an iterator for records at exact timestamp t.
 * Alias for equal() for semantic clarity in point queries.
 */
static PyObject* PyTimelog_point(PyTimelog* self, PyObject* args)
{
    long long t;

    if (!PyArg_ParseTuple(args, "L", &t)) {
        return NULL;
    }

    return pytimelog_make_iter(self, ITER_MODE_POINT, (tl_ts_t)t, 0);
}

/*===========================================================================
 * PageSpan Factory Methods (LLD-B4)
 *===========================================================================*/

/**
 * Timelog.page_spans(t1, t2, *, kind="segment") -> PageSpanIter
 *
 * Create an iterator yielding PageSpan objects for zero-copy timestamp access.
 *
 * Each yielded PageSpan exposes a contiguous slice of page memory as a
 * read-only memoryview via the buffer protocol.
 *
 * @param t1   Range start (inclusive)
 * @param t2   Range end (exclusive)
 * @param kind "segment" (only supported value in V1)
 * @return PageSpanIter iterator
 */
static PyObject* PyTimelog_page_spans(PyTimelog* self,
                                       PyObject* args,
                                       PyObject* kwds)
{
    static char* kwlist[] = {"t1", "t2", "kind", NULL};
    long long t1, t2;
    const char* kind = "segment";

    CHECK_CLOSED(self);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "LL|s", kwlist,
                                     &t1, &t2, &kind)) {
        return NULL;
    }

    return PyPageSpanIter_Create((PyObject*)self, (tl_ts_t)t1, (tl_ts_t)t2, kind);
}

/*===========================================================================
 * Property Getters
 *===========================================================================*/

static PyObject* PyTimelog_get_closed(PyTimelog* self, void* Py_UNUSED(closure))
{
    return PyBool_FromLong(self->closed);
}

static PyObject* PyTimelog_get_time_unit(PyTimelog* self, void* Py_UNUSED(closure))
{
    const char* unit_str;
    switch (self->time_unit) {
        case TL_TIME_S:  unit_str = "s";  break;
        case TL_TIME_MS: unit_str = "ms"; break;
        case TL_TIME_US: unit_str = "us"; break;
        case TL_TIME_NS: unit_str = "ns"; break;
        default:         unit_str = "unknown"; break;
    }
    return PyUnicode_FromString(unit_str);
}

static PyObject* PyTimelog_get_maintenance_mode(PyTimelog* self, void* Py_UNUSED(closure))
{
    const char* mode_str;
    switch (self->maint_mode) {
        case TL_MAINT_DISABLED:   mode_str = "disabled";   break;
        case TL_MAINT_BACKGROUND: mode_str = "background"; break;
        default:                  mode_str = "unknown";    break;
    }
    return PyUnicode_FromString(mode_str);
}

static PyObject* PyTimelog_get_busy_policy(PyTimelog* self, void* Py_UNUSED(closure))
{
    const char* policy_str;
    switch (self->busy_policy) {
        case TL_PY_BUSY_RAISE:  policy_str = "raise";  break;
        case TL_PY_BUSY_SILENT: policy_str = "silent"; break;
        case TL_PY_BUSY_FLUSH:  policy_str = "flush";  break;
        default:                policy_str = "unknown"; break;
    }
    return PyUnicode_FromString(policy_str);
}

static PyObject* PyTimelog_get_retired_queue_len(PyTimelog* self, void* Py_UNUSED(closure))
{
    uint64_t len = tl_py_retired_queue_len(&self->handle_ctx);
    return PyLong_FromUnsignedLongLong(len);
}

static PyObject* PyTimelog_get_alloc_failures(PyTimelog* self, void* Py_UNUSED(closure))
{
    uint64_t failures = tl_py_alloc_failures(&self->handle_ctx);
    return PyLong_FromUnsignedLongLong(failures);
}

/*===========================================================================
 * Property Table
 *===========================================================================*/

static PyGetSetDef PyTimelog_getset[] = {
    {"closed", (getter)PyTimelog_get_closed, NULL,
     "True if the timelog has been closed.", NULL},

    {"time_unit", (getter)PyTimelog_get_time_unit, NULL,
     "Time unit for timestamps ('s', 'ms', 'us', or 'ns').", NULL},

    {"maintenance_mode", (getter)PyTimelog_get_maintenance_mode, NULL,
     "Maintenance mode ('disabled' or 'background').", NULL},

    {"busy_policy", (getter)PyTimelog_get_busy_policy, NULL,
     "Backpressure policy ('raise', 'silent', or 'flush').", NULL},

    {"retired_queue_len", (getter)PyTimelog_get_retired_queue_len, NULL,
     "Approximate number of objects in retired queue awaiting DECREF.", NULL},

    {"alloc_failures", (getter)PyTimelog_get_alloc_failures, NULL,
     "Number of allocation failures in on_drop callback (objects leaked).", NULL},

    {NULL, NULL, NULL, NULL, NULL}
};

/*===========================================================================
 * Method Table
 *===========================================================================*/

static PyMethodDef PyTimelog_methods[] = {
    {"append", (PyCFunction)PyTimelog_append, METH_VARARGS,
     "append(ts, obj) -> None\n\n"
     "Append a record at timestamp ts with payload obj."},

    {"extend", (PyCFunction)PyTimelog_extend, METH_O,
     "extend(iterable) -> None\n\n"
     "Append multiple (ts, obj) records from an iterable.\n"
     "Non-atomic: prior successful inserts remain on failure."},

    {"delete_range", (PyCFunction)PyTimelog_delete_range, METH_VARARGS,
     "delete_range(t1, t2) -> None\n\n"
     "Mark records in [t1, t2) for deletion (tombstone)."},

    {"delete_before", (PyCFunction)PyTimelog_delete_before, METH_VARARGS,
     "delete_before(cutoff) -> None\n\n"
     "Mark records in [MIN, cutoff) for deletion."},

    {"flush", (PyCFunction)PyTimelog_flush, METH_NOARGS,
     "flush() -> None\n\n"
     "Synchronously flush memtable to L0 segments."},

    {"compact", (PyCFunction)PyTimelog_compact, METH_NOARGS,
     "compact() -> None\n\n"
     "Request compaction (maintenance must be running or manual step called)."},

    {"start_maintenance", (PyCFunction)PyTimelog_start_maint, METH_NOARGS,
     "start_maintenance() -> None\n\n"
     "Start background maintenance worker (background mode only)."},

    {"stop_maintenance", (PyCFunction)PyTimelog_stop_maint, METH_NOARGS,
     "stop_maintenance() -> None\n\n"
     "Stop background maintenance worker and wait for it to exit."},

    {"close", (PyCFunction)PyTimelog_close, METH_NOARGS,
     "close() -> None\n\n"
     "Close the timelog. Idempotent. Releases all resources.\n\n"
     "WARNING: Records not yet flushed will be lost. In Python-object mode,\n"
     "this also means those objects will leak. Call flush() before close()."},

    /* Iterator factory methods (LLD-B3) */
    {"range", (PyCFunction)PyTimelog_range, METH_VARARGS,
     "range(t1, t2) -> TimelogIter\n\n"
     "Return an iterator over records in [t1, t2).\n"
     "If t1 >= t2, returns an empty iterator."},

    {"since", (PyCFunction)PyTimelog_since, METH_VARARGS,
     "since(t) -> TimelogIter\n\n"
     "Return an iterator over records with ts >= t."},

    {"until", (PyCFunction)PyTimelog_until, METH_VARARGS,
     "until(t) -> TimelogIter\n\n"
     "Return an iterator over records with ts < t."},

    {"all", (PyCFunction)PyTimelog_all, METH_NOARGS,
     "all() -> TimelogIter\n\n"
     "Return an iterator over all records."},

    {"equal", (PyCFunction)PyTimelog_equal, METH_VARARGS,
     "equal(t) -> TimelogIter\n\n"
     "Return an iterator over records with ts == t."},

    {"point", (PyCFunction)PyTimelog_point, METH_VARARGS,
     "point(t) -> TimelogIter\n\n"
     "Return an iterator for the exact timestamp t.\n"
     "Alias for equal() for point query semantics."},

    /* PageSpan factory methods (LLD-B4) */
    {"page_spans", (PyCFunction)PyTimelog_page_spans, METH_VARARGS | METH_KEYWORDS,
     "page_spans(t1, t2, *, kind='segment') -> PageSpanIter\n\n"
     "Return an iterator yielding PageSpan objects for [t1, t2).\n"
     "Each PageSpan exposes a contiguous slice of page timestamps\n"
     "as a read-only memoryview (zero-copy). Use for bulk timestamp\n"
     "access without per-record Python object allocation.\n\n"
     "Parameters:\n"
     "  t1: Range start (inclusive)\n"
     "  t2: Range end (exclusive)\n"
     "  kind: 'segment' (only supported value in V1)\n\n"
     "Returns:\n"
     "  PageSpanIter yielding PageSpan objects"},

    {"__enter__", (PyCFunction)PyTimelog_enter, METH_NOARGS,
     "Context manager entry."},

    {"__exit__", (PyCFunction)PyTimelog_exit, METH_VARARGS,
     "Context manager exit (closes the timelog)."},

    {NULL, NULL, 0, NULL}
};

/*===========================================================================
 * Type Object Definition
 *===========================================================================*/

PyTypeObject PyTimelog_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.Timelog",
    .tp_doc = PyDoc_STR(
        "Timelog engine wrapper.\n\n"
        "A time-indexed multimap for (timestamp, object) records.\n\n"
        "Thread Safety:\n"
        "    A Timelog instance is NOT thread-safe. Do not access the same\n"
        "    instance from multiple threads without external synchronization.\n"
        "    This is consistent with Python's sqlite3.Connection and file objects.\n"
    ),
    .tp_basicsize = sizeof(PyTimelog),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,
    .tp_new = PyType_GenericNew,
    .tp_init = (initproc)PyTimelog_init,
    .tp_dealloc = (destructor)PyTimelog_dealloc,
    .tp_methods = PyTimelog_methods,
    .tp_getset = PyTimelog_getset,
};

/------------------------------------------------------------------------------/
/*   END OF: py_timelog.c
/------------------------------------------------------------------------------/
