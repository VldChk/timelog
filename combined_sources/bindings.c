/*
============================================================================

   COMBINED SOURCE FILE: bindings.c

   Generated from: bindings\cpython\src
   Generated at:   2026-02-01 01:57:22

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
 * See: docs/V2/timelog_v2_engineering_plan.md
 *      docs/V2/timelog_v2_lld_storage_pages.md
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
    int errors_inited = 0;

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
    errors_inited = 1;

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
    if (errors_inited) {
        TlPy_FiniErrors();
    }
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
 * IMPORTANT:
 * - Writes: record/tombstone was inserted; do NOT retry.
 * - Flush/maintenance: publish retry exhausted; safe to retry later.
 * - start_maintenance: stop in progress; retry later.
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
 * - TL_EBUSY    -> TimelogBusyError (backpressure/publish-retry - see header for context)
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
            /* Transient condition: backpressure, publish retry, stop in progress. */
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
 * See: docs/V2/timelog_v2_engineering_plan.md
 *      docs/V2/timelog_v2_c_software_design_spec.md
 */

#include "timelogpy/py_handle.h"

#include <assert.h>   /* assert for debug checks */
#include <inttypes.h> /* PRIu64 for portable uint64_t formatting */
#include <stdio.h>    /* fprintf, stderr */
#include <stdlib.h>   /* malloc, free - NOT Python allocators (no GIL in on_drop) */
#include <string.h>   /* memset */

/*===========================================================================
 * Live Handle Tracking (multiset)
 *===========================================================================*/

/* Hash table entry states */
#define TL_PY_LIVE_EMPTY     0
#define TL_PY_LIVE_FULL      1
#define TL_PY_LIVE_TOMBSTONE 2

struct tl_py_live_entry {
    PyObject* obj;
    uint64_t  count;
    uint8_t   state;
};

static size_t tl_py_live_hash_ptr(const void* ptr)
{
    uintptr_t x = (uintptr_t)ptr;
    /* Simple mix; sufficient for pointer keys */
    x ^= x >> 17;
    x *= (uintptr_t)0xed5ad4bbU;
    x ^= x >> 11;
    x *= (uintptr_t)0xac4c1b51U;
    x ^= x >> 15;
    return (size_t)x;
}

static tl_status_t tl_py_live_rehash(tl_py_handle_ctx_t* ctx, size_t new_cap)
{
    tl_py_live_entry_t* old_entries = ctx->live_entries;
    size_t old_cap = ctx->live_cap;

    tl_py_live_entry_t* entries = (tl_py_live_entry_t*)calloc(
        new_cap, sizeof(*entries));
    if (entries == NULL) {
        return TL_ENOMEM;
    }

    ctx->live_entries = entries;
    ctx->live_cap = new_cap;
    ctx->live_len = 0;
    ctx->live_tombstones = 0;

    if (old_entries != NULL) {
        for (size_t i = 0; i < old_cap; i++) {
            if (old_entries[i].state == TL_PY_LIVE_FULL) {
                /* Reinsert */
                PyObject* obj = old_entries[i].obj;
                uint64_t count = old_entries[i].count;
                size_t mask = ctx->live_cap - 1;
                size_t idx = tl_py_live_hash_ptr(obj) & mask;
                for (;;) {
                    tl_py_live_entry_t* e = &ctx->live_entries[idx];
                    if (e->state == TL_PY_LIVE_EMPTY) {
                        e->state = TL_PY_LIVE_FULL;
                        e->obj = obj;
                        e->count = count;
                        ctx->live_len++;
                        break;
                    }
                    idx = (idx + 1) & mask;
                }
            }
        }
        free(old_entries);
    }

    return TL_OK;
}

static tl_status_t tl_py_live_ensure(tl_py_handle_ctx_t* ctx, size_t needed)
{
    size_t cap = ctx->live_cap;
    if (cap == 0) {
        size_t init_cap = 64;
        if (init_cap < needed) {
            while (init_cap < needed) {
                init_cap *= 2;
            }
        }
        return tl_py_live_rehash(ctx, init_cap);
    }

    /* Keep load factor <= ~0.7 (including tombstones) */
    size_t used = ctx->live_len + ctx->live_tombstones + needed;
    if (used * 10 <= cap * 7) {
        return TL_OK;
    }

    size_t new_cap = cap * 2;
    if (new_cap < cap) {
        return TL_EOVERFLOW;
    }
    return tl_py_live_rehash(ctx, new_cap);
}
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

    /* Initialize atomics */
    atomic_init(&ctx->retired_head, NULL);
    atomic_init(&ctx->pins, 0);
    atomic_init(&ctx->retired_count, 0);
    atomic_init(&ctx->drained_count, 0);
    atomic_init(&ctx->alloc_failures, 0);
    atomic_flag_clear_explicit(&ctx->drain_guard, memory_order_release);

    /* Store configuration (immutable after init) */
    ctx->drain_batch_limit = drain_batch_limit;
    ctx->live_entries = NULL;
    ctx->live_cap = 0;
    ctx->live_len = 0;
    ctx->live_tombstones = 0;
    ctx->live_tracking_failed = 0;

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

    if (ctx->live_len != 0) {
        fprintf(stderr,
            "WARNING: tl_py_handle_ctx_destroy called with %zu live objects. "
            "Did you forget to call tl_py_live_release_all()?\n",
            ctx->live_len);
    }
#endif

    if (ctx->live_entries != NULL) {
        free(ctx->live_entries);
    }

    ctx->live_entries = NULL;
    ctx->live_cap = 0;
    ctx->live_len = 0;
    ctx->live_tombstones = 0;
    ctx->live_tracking_failed = 0;
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
     * Reentrancy guard: prevent nested drains triggered via __del__.
     * If already draining, bail out immediately.
     */
    if (atomic_flag_test_and_set_explicit(
            &ctx->drain_guard, memory_order_acquire)) {
        return 0;
    }

    size_t count = 0;

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
        goto out;
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
        goto out;  /* Nothing to drain */
    }

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

        /* Update live tracking before DECREF */
        tl_py_live_note_drop(ctx, node->obj);

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

out:
    atomic_flag_clear_explicit(&ctx->drain_guard, memory_order_release);
    return count;
}

/*===========================================================================
 * Live Handle Tracking (multiset) Implementation
 *===========================================================================*/

tl_status_t tl_py_live_note_insert(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
#ifndef NDEBUG
    assert(PyGILState_Check() &&
           "tl_py_live_note_insert requires GIL");
#endif

    if (ctx == NULL || obj == NULL) {
        return TL_EINVAL;
    }

    tl_status_t st = tl_py_live_ensure(ctx, 1);
    if (st != TL_OK) {
        ctx->live_tracking_failed = 1;
        return st;
    }

    size_t mask = ctx->live_cap - 1;
    size_t idx = tl_py_live_hash_ptr(obj) & mask;
    size_t first_tombstone = (size_t)-1;

    for (;;) {
        tl_py_live_entry_t* e = &ctx->live_entries[idx];
        if (e->state == TL_PY_LIVE_EMPTY) {
            if (first_tombstone != (size_t)-1) {
                e = &ctx->live_entries[first_tombstone];
                ctx->live_tombstones--;
            }
            e->state = TL_PY_LIVE_FULL;
            e->obj = obj;
            e->count = 1;
            ctx->live_len++;
            return TL_OK;
        }
        if (e->state == TL_PY_LIVE_TOMBSTONE) {
            if (first_tombstone == (size_t)-1) {
                first_tombstone = idx;
            }
        } else if (e->obj == obj) {
            e->count++;
            return TL_OK;
        }
        idx = (idx + 1) & mask;
    }
}

void tl_py_live_note_drop(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
#ifndef NDEBUG
    assert(PyGILState_Check() &&
           "tl_py_live_note_drop requires GIL");
#endif

    if (ctx == NULL || obj == NULL || ctx->live_cap == 0) {
        return;
    }

    size_t mask = ctx->live_cap - 1;
    size_t idx = tl_py_live_hash_ptr(obj) & mask;

    for (;;) {
        tl_py_live_entry_t* e = &ctx->live_entries[idx];
        if (e->state == TL_PY_LIVE_EMPTY) {
            return;
        }
        if (e->state == TL_PY_LIVE_FULL && e->obj == obj) {
            if (e->count > 1) {
                e->count--;
                return;
            }
            e->obj = NULL;
            e->count = 0;
            e->state = TL_PY_LIVE_TOMBSTONE;
            ctx->live_len--;
            ctx->live_tombstones++;
            return;
        }
        idx = (idx + 1) & mask;
    }
}

void tl_py_live_release_all(tl_py_handle_ctx_t* ctx)
{
#ifndef NDEBUG
    assert(PyGILState_Check() &&
           "tl_py_live_release_all requires GIL");
#endif

    if (ctx == NULL || ctx->live_entries == NULL) {
        return;
    }

#ifndef NDEBUG
    if (ctx->live_tracking_failed) {
        fprintf(stderr,
            "WARNING: live handle tracking encountered allocation failures; "
            "some objects may leak.\n");
    }
#endif

    for (size_t i = 0; i < ctx->live_cap; i++) {
        tl_py_live_entry_t* e = &ctx->live_entries[i];
        if (e->state == TL_PY_LIVE_FULL) {
            for (uint64_t c = e->count; c > 0; c--) {
                Py_DECREF(e->obj);
            }
            e->obj = NULL;
            e->count = 0;
            e->state = TL_PY_LIVE_EMPTY;
        }
    }

    free(ctx->live_entries);
    ctx->live_entries = NULL;
    ctx->live_cap = 0;
    ctx->live_len = 0;
    ctx->live_tombstones = 0;
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
 * See: docs/V2/timelog_v2_lld_read_path.md
 *      docs/V2/timelog_v2_c_software_design_spec.md
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
 * See: docs/V2/timelog_v2_lld_storage_pages.md
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
    /* Current behavior: copy() returns the same as copy_timestamps(). */
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

static PyObject* PyPageSpan_get_last_ts(PyPageSpan* self, void* closure)
{
    return PyPageSpan_get_end_ts(self, closure);
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
     "Last (inclusive) timestamp in this span.", NULL},
    {"last_ts", (getter)PyPageSpan_get_last_ts, NULL,
     "Alias for end_ts (inclusive last timestamp).", NULL},
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
 * See: docs/V2/timelog_v2_lld_storage_pages.md
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

    if (tl_py_lock_checked(tl_obj) < 0) {
        Py_DECREF(hook_ctx->timelog);
        PyMem_Free(hook_ctx);
        tl_py_pins_exit_and_maybe_drain(&tl_obj->handle_ctx);
        return NULL;
    }
    tl_status_t st = tl_pagespan_iter_open(tl_obj->tl, t1, t2, flags, &hooks, &core_iter);
    TL_PY_UNLOCK(tl_obj);

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
 * See: docs/V2/timelog_v2_lld_storage_pages.md
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
 * See docs/V2/timelog_v2_engineering_plan.md for current design intent.
 *
 * CRITICAL SEMANTICS:
 * - TL_EBUSY from write operations means record/tombstone WAS inserted
 * - Do NOT rollback INCREF on TL_EBUSY
 * - Do NOT retry on TL_EBUSY (would create duplicates)
 *
 * Thread Safety:
 * - Single-writer model: external synchronization required for writes
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

#include <limits.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>

/*===========================================================================
 * Exception Preservation Helpers
 *===========================================================================*/

#define TL_PY_PRESERVE_EXC_BEGIN \
    PyObject *exc_type = NULL, *exc_value = NULL, *exc_tb = NULL; \
    PyErr_Fetch(&exc_type, &exc_value, &exc_tb)

#define TL_PY_PRESERVE_EXC_END \
    PyErr_Restore(exc_type, exc_value, exc_tb)

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static PyObject* PyTimelog_close(PyTimelog* self, PyObject* Py_UNUSED(args));

static PyObject* PyTimelog_stats(PyTimelog* self, PyObject* Py_UNUSED(args));
static PyObject* PyTimelog_maint_step(PyTimelog* self, PyObject* Py_UNUSED(args));
static PyObject* PyTimelog_min_ts(PyTimelog* self, PyObject* Py_UNUSED(args));
static PyObject* PyTimelog_max_ts(PyTimelog* self, PyObject* Py_UNUSED(args));
static PyObject* PyTimelog_next_ts(PyTimelog* self, PyObject* args);
static PyObject* PyTimelog_prev_ts(PyTimelog* self, PyObject* args);
static PyObject* PyTimelog_validate(PyTimelog* self, PyObject* Py_UNUSED(args));

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

/**
 * Validate timestamp range (defense-in-depth).
 *
 * PyArg_ParseTuple("L") already enforces LLONG range; this keeps
 * error handling consistent with append() and future-proofs if
 * TL_TS_* diverge from LLONG limits.
 */
static int tl_py_validate_ts(long long v, const char* name)
{
    if (v < TL_TS_MIN || v > TL_TS_MAX) {
        PyErr_Format(PyExc_OverflowError,
            "%s %lld out of int64 range", name, v);
        return -1;
    }
    return 0;
}

/**
 * Handle TL_EBUSY for write operations.
 *
 * Returns 0 to continue, -1 if an exception was raised.
 * Caller must NOT rollback references on TL_EBUSY.
 */
static int tl_py_handle_write_ebusy(PyTimelog* self, const char* msg)
{
    if (self->busy_policy == TL_PY_BUSY_RAISE) {
        PyErr_SetString(TlPy_TimelogBusyError, msg);
        return -1;
    }

    if (self->busy_policy == TL_PY_BUSY_FLUSH) {
        tl_status_t flush_st = TL_ESTATE;
        TL_PY_LOCK(self);
        if (!self->closed && self->tl != NULL) {
            Py_BEGIN_ALLOW_THREADS
            flush_st = tl_flush(self->tl);
            /*
             * Release core_lock BEFORE re-acquiring GIL to prevent ABBA
             * deadlock: Thread A holds core_lock + wants GIL, Thread B
             * holds GIL + wants core_lock.
             */
            PyThread_release_lock(self->core_lock);
            Py_END_ALLOW_THREADS
        } else {
            TL_PY_UNLOCK(self);
        }

        if (flush_st != TL_OK && flush_st != TL_EOF) {
#ifndef NDEBUG
            fprintf(stderr, "WARNING: flush after EBUSY failed: %d\n", flush_st);
#endif
        }
    }

    return 0;
}

/**
 * Acquire core lock and re-check closed state.
 *
 * Returns 0 on success, -1 on closed (exception set).
 */
int tl_py_lock_checked(PyTimelog* self)
{
    TL_PY_LOCK(self);
    if (self->closed || self->tl == NULL) {
        TL_PY_UNLOCK(self);
        TlPy_RaiseFromStatusFmt(TL_ESTATE, "Timelog is closed");
        return -1;
    }
    return 0;
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

    self->core_lock = NULL;

    static char* kwlist[] = {
        "time_unit",             /* s - string */
        "maintenance",           /* s - string */
        "memtable_max_bytes",    /* n - Py_ssize_t */
        "target_page_bytes",     /* n - Py_ssize_t */
        "sealed_max_runs",       /* n - Py_ssize_t */
        "drain_batch_limit",     /* n - Py_ssize_t */
        "busy_policy",           /* s - string */
        "ooo_budget_bytes",      /* n - Py_ssize_t */
        "sealed_wait_ms",        /* n - Py_ssize_t */
        "maintenance_wakeup_ms", /* n - Py_ssize_t */
        "max_delta_segments",    /* n - Py_ssize_t */
        "window_size",           /* L - long long */
        "window_origin",         /* L - long long */
        "delete_debt_threshold", /* d - double */
        "compaction_target_bytes", /* n - Py_ssize_t */
        "max_compaction_inputs", /* n - Py_ssize_t */
        "max_compaction_windows",/* n - Py_ssize_t */
        "adaptive_target_records", /* n - Py_ssize_t */
        "adaptive_min_window",     /* L - long long */
        "adaptive_max_window",     /* L - long long */
        "adaptive_hysteresis_pct", /* n - Py_ssize_t */
        "adaptive_window_quantum", /* L - long long */
        "adaptive_alpha",          /* d - double */
        "adaptive_warmup_flushes", /* n - Py_ssize_t */
        "adaptive_stale_flushes",  /* n - Py_ssize_t */
        "adaptive_failure_backoff_threshold", /* n - Py_ssize_t */
        "adaptive_failure_backoff_pct",       /* n - Py_ssize_t */
        NULL
    };

    const char* time_unit_str = NULL;
    const char* maint_str = NULL;
    Py_ssize_t memtable_max_bytes = -1;
    Py_ssize_t target_page_bytes = -1;
    Py_ssize_t sealed_max_runs = -1;
    Py_ssize_t drain_batch_limit = -1;
    const char* busy_policy_str = NULL;
    Py_ssize_t ooo_budget_bytes = -1;
    Py_ssize_t sealed_wait_ms = -1;
    Py_ssize_t maintenance_wakeup_ms = -1;
    Py_ssize_t max_delta_segments = -1;
    long long window_size = LLONG_MIN;
    long long window_origin = LLONG_MIN;
    double delete_debt_threshold = -1.0;
    Py_ssize_t compaction_target_bytes = -1;
    Py_ssize_t max_compaction_inputs = -1;
    Py_ssize_t max_compaction_windows = -1;
    Py_ssize_t adaptive_target_records = -1;
    long long adaptive_min_window = LLONG_MIN;
    long long adaptive_max_window = LLONG_MIN;
    Py_ssize_t adaptive_hysteresis_pct = -1;
    long long adaptive_window_quantum = LLONG_MIN;
    double adaptive_alpha = -1.0;
    Py_ssize_t adaptive_warmup_flushes = -1;
    Py_ssize_t adaptive_stale_flushes = -1;
    Py_ssize_t adaptive_failure_backoff_threshold = -1;
    Py_ssize_t adaptive_failure_backoff_pct = -1;

    /* CRITICAL: 27 converters for 27 kwargs */
    if (!PyArg_ParseTupleAndKeywords(args, kwds,
            "|ssnnnnsnnnnLLdnnnnLLnLdnnnn", kwlist,
            &time_unit_str, &maint_str,
            &memtable_max_bytes, &target_page_bytes, &sealed_max_runs,
            &drain_batch_limit, &busy_policy_str,
            &ooo_budget_bytes, &sealed_wait_ms, &maintenance_wakeup_ms,
            &max_delta_segments, &window_size, &window_origin,
            &delete_debt_threshold, &compaction_target_bytes,
            &max_compaction_inputs, &max_compaction_windows,
            &adaptive_target_records, &adaptive_min_window, &adaptive_max_window,
            &adaptive_hysteresis_pct, &adaptive_window_quantum,
            &adaptive_alpha, &adaptive_warmup_flushes, &adaptive_stale_flushes,
            &adaptive_failure_backoff_threshold, &adaptive_failure_backoff_pct)) {
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
     * -1 = unset (use default), 0 allowed where supported by core config.
     * Also check for overflow on platforms where size_t < Py_ssize_t.
     */
    if (memtable_max_bytes != -1) {
        if (memtable_max_bytes < 0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "memtable_max_bytes must be >= 0");
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
        if (target_page_bytes < 0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "target_page_bytes must be >= 0");
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
        if (sealed_max_runs < 0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "sealed_max_runs must be >= 0");
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

    if (ooo_budget_bytes != -1) {
        if (ooo_budget_bytes < 0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "ooo_budget_bytes must be >= 0");
            return -1;
        }
        if ((size_t)ooo_budget_bytes != (uint64_t)ooo_budget_bytes) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_OverflowError,
                "ooo_budget_bytes too large for this platform");
            return -1;
        }
        cfg.ooo_budget_bytes = (size_t)ooo_budget_bytes;
    }

    if (sealed_wait_ms != -1) {
        if (sealed_wait_ms < 0 || (uint64_t)sealed_wait_ms > UINT32_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "sealed_wait_ms must be 0-4294967295");
            return -1;
        }
        cfg.sealed_wait_ms = (uint32_t)sealed_wait_ms;
    }

    if (maintenance_wakeup_ms != -1) {
        if (maintenance_wakeup_ms < 0 || (uint64_t)maintenance_wakeup_ms > UINT32_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "maintenance_wakeup_ms must be 0-4294967295");
            return -1;
        }
        cfg.maintenance_wakeup_ms = (uint32_t)maintenance_wakeup_ms;
    }

    if (max_delta_segments != -1) {
        if (max_delta_segments < 0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "max_delta_segments must be >= 0");
            return -1;
        }
        if ((size_t)max_delta_segments != (uint64_t)max_delta_segments) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_OverflowError,
                "max_delta_segments too large for this platform");
            return -1;
        }
        cfg.max_delta_segments = (size_t)max_delta_segments;
    }

    if (window_size != LLONG_MIN) {
        if (window_size < 0 || window_size > (long long)TL_TS_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "window_size must be in [0, INT64_MAX]");
            return -1;
        }
        cfg.window_size = (tl_ts_t)window_size;
    }

    if (window_origin != LLONG_MIN) {
        if (window_origin < (long long)TL_TS_MIN ||
            window_origin > (long long)TL_TS_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_OverflowError,
                "window_origin out of int64 range");
            return -1;
        }
        cfg.window_origin = (tl_ts_t)window_origin;
    }

    if (delete_debt_threshold != -1.0) {
        if (delete_debt_threshold < 0.0 || delete_debt_threshold > 1.0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "delete_debt_threshold must be in [0.0, 1.0]");
            return -1;
        }
        cfg.delete_debt_threshold = delete_debt_threshold;
    }

    if (compaction_target_bytes != -1) {
        if (compaction_target_bytes < 0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "compaction_target_bytes must be >= 0");
            return -1;
        }
        if ((size_t)compaction_target_bytes != (uint64_t)compaction_target_bytes) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_OverflowError,
                "compaction_target_bytes too large for this platform");
            return -1;
        }
        cfg.compaction_target_bytes = (size_t)compaction_target_bytes;
    }

    if (max_compaction_inputs != -1) {
        if (max_compaction_inputs < 0 || (uint64_t)max_compaction_inputs > UINT32_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "max_compaction_inputs must be 0-4294967295");
            return -1;
        }
        cfg.max_compaction_inputs = (uint32_t)max_compaction_inputs;
    }

    if (max_compaction_windows != -1) {
        if (max_compaction_windows < 0 || (uint64_t)max_compaction_windows > UINT32_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "max_compaction_windows must be 0-4294967295");
            return -1;
        }
        cfg.max_compaction_windows = (uint32_t)max_compaction_windows;
    }

    if (adaptive_target_records != -1) {
        if (adaptive_target_records < 0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_target_records must be >= 0");
            return -1;
        }
        cfg.adaptive.target_records = (uint64_t)adaptive_target_records;
    }

    if (adaptive_min_window != LLONG_MIN) {
        if (adaptive_min_window < 0 || adaptive_min_window > (long long)TL_TS_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_min_window must be in [0, INT64_MAX]");
            return -1;
        }
        cfg.adaptive.min_window = (tl_ts_t)adaptive_min_window;
    }

    if (adaptive_max_window != LLONG_MIN) {
        if (adaptive_max_window < 0 || adaptive_max_window > (long long)TL_TS_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_max_window must be in [0, INT64_MAX]");
            return -1;
        }
        cfg.adaptive.max_window = (tl_ts_t)adaptive_max_window;
    }

    if (adaptive_hysteresis_pct != -1) {
        if (adaptive_hysteresis_pct < 0 || (uint64_t)adaptive_hysteresis_pct > UINT32_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_hysteresis_pct must be 0-4294967295");
            return -1;
        }
        cfg.adaptive.hysteresis_pct = (uint32_t)adaptive_hysteresis_pct;
    }

    if (adaptive_window_quantum != LLONG_MIN) {
        if (adaptive_window_quantum < 0 || adaptive_window_quantum > (long long)TL_TS_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_window_quantum must be in [0, INT64_MAX]");
            return -1;
        }
        cfg.adaptive.window_quantum = (tl_ts_t)adaptive_window_quantum;
    }

    if (adaptive_alpha != -1.0) {
        if (adaptive_alpha < 0.0 || adaptive_alpha > 1.0) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_alpha must be in [0.0, 1.0]");
            return -1;
        }
        cfg.adaptive.alpha = adaptive_alpha;
    }

    if (adaptive_warmup_flushes != -1) {
        if (adaptive_warmup_flushes < 0 || (uint64_t)adaptive_warmup_flushes > UINT32_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_warmup_flushes must be 0-4294967295");
            return -1;
        }
        cfg.adaptive.warmup_flushes = (uint32_t)adaptive_warmup_flushes;
    }

    if (adaptive_stale_flushes != -1) {
        if (adaptive_stale_flushes < 0 || (uint64_t)adaptive_stale_flushes > UINT32_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_stale_flushes must be 0-4294967295");
            return -1;
        }
        cfg.adaptive.stale_flushes = (uint32_t)adaptive_stale_flushes;
    }

    if (adaptive_failure_backoff_threshold != -1) {
        if (adaptive_failure_backoff_threshold < 0 ||
            (uint64_t)adaptive_failure_backoff_threshold > UINT32_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_failure_backoff_threshold must be 0-4294967295");
            return -1;
        }
        cfg.adaptive.failure_backoff_threshold =
            (uint32_t)adaptive_failure_backoff_threshold;
    }

    if (adaptive_failure_backoff_pct != -1) {
        if (adaptive_failure_backoff_pct < 0 ||
            (uint64_t)adaptive_failure_backoff_pct > UINT32_MAX) {
            tl_py_handle_ctx_destroy(&self->handle_ctx);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_failure_backoff_pct must be 0-4294967295");
            return -1;
        }
        cfg.adaptive.failure_backoff_pct =
            (uint32_t)adaptive_failure_backoff_pct;
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

    /* Allocate per-instance core lock */
    self->core_lock = PyThread_allocate_lock();
    if (self->core_lock == NULL) {
        /* Best-effort shutdown on allocation failure */
        tl_maint_stop(self->tl);
        tl_close(self->tl);
        self->tl = NULL;
        self->closed = 1;
        tl_py_handle_ctx_destroy(&self->handle_ctx);
        PyErr_NoMemory();
        return -1;
    }

    /* Success - store introspection fields */
    self->closed = 0;
    self->time_unit = time_unit_set ? cfg.time_unit : TL_TIME_MS;
    self->maint_mode = cfg.maintenance_mode;

    /* tl_open() auto-starts maintenance in background mode. */

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
    TL_PY_LOCK(self);
    Py_BEGIN_ALLOW_THREADS
    tl_maint_stop(self->tl);
    tl_close(self->tl);
    /*
     * Release core_lock BEFORE re-acquiring GIL to prevent ABBA
     * deadlock: Thread A holds core_lock + wants GIL, Thread B
     * holds GIL + wants core_lock.
     */
    PyThread_release_lock(self->core_lock);
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
        TL_PY_PRESERVE_EXC_BEGIN;
        tl_py_drain_retired(&self->handle_ctx, 1);
        tl_py_live_release_all(&self->handle_ctx);
        TL_PY_PRESERVE_EXC_END;
    }

    /* Destroy handle context */
    tl_py_handle_ctx_destroy(&self->handle_ctx);

    if (self->core_lock) {
        PyThread_free_lock(self->core_lock);
        self->core_lock = NULL;
    }

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
            TL_PY_LOCK(self);
            if (self->tl != NULL) {
                Py_BEGIN_ALLOW_THREADS
                tl_maint_stop(self->tl);
                tl_close(self->tl);
                PyThread_release_lock(self->core_lock);
                Py_END_ALLOW_THREADS
                self->tl = NULL;
            } else {
                TL_PY_UNLOCK(self);
            }

            /*
             * Drain retired objects with exception preservation.
             * Per LLD-B6: Py_DECREF in drain can trigger __del__ that
             * may clobber active exceptions during finalization.
             */
            {
                TL_PY_PRESERVE_EXC_BEGIN;
                tl_py_drain_retired(&self->handle_ctx, 1);
                tl_py_live_release_all(&self->handle_ctx);
                TL_PY_PRESERVE_EXC_END;
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

    if (self->core_lock) {
        PyThread_free_lock(self->core_lock);
        self->core_lock = NULL;
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
    if (tl_py_validate_ts(ts_ll, "timestamp") < 0) {
        return NULL;
    }

    /* INCREF object (engine-owned reference) */
    Py_INCREF(obj);

    /* Encode and append */
    tl_handle_t h = tl_py_handle_encode(obj);
    tl_ts_t ts = (tl_ts_t)ts_ll;
    tl_status_t st;
    if (tl_py_lock_checked(self) < 0) {
        Py_DECREF(obj);
        return NULL;
    }
    st = tl_append(self->tl, ts, h);
    TL_PY_UNLOCK(self);

    if (st == TL_OK) {
        (void)tl_py_live_note_insert(&self->handle_ctx, obj);
        goto success;
    }

    if (st == TL_EBUSY) {
        /*
         * CRITICAL: EBUSY means record WAS inserted, but backpressure occurred.
         * This can happen in background mode (sealed queue timeout) or after
         * an OOO head flush failure. DO NOT retry - would create duplicates.
         *
         * DO NOT rollback INCREF - record is in engine.
         */
        (void)tl_py_live_note_insert(&self->handle_ctx, obj);

        if (tl_py_handle_write_ebusy(self,
                "Record inserted but backpressure occurred. "
                "Call flush() or wait for background maintenance to relieve.") < 0) {
            return NULL;
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
PyTimelog_extend(PyTimelog* self, PyObject* args, PyObject* kwds)
{
    CHECK_CLOSED(self);

    PyObject* iterable = NULL;
    int mostly_ordered = 0;
    static char* kwlist[] = {"iterable", "mostly_ordered", NULL};

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|p", kwlist,
                                     &iterable, &mostly_ordered)) {
        return NULL;
    }

    /* Fast path for concrete sequences (no materialization cost). */
    if (PyList_CheckExact(iterable) || PyTuple_CheckExact(iterable)) {
        PyObject* seq = PySequence_Fast(iterable,
                                        "extend() expects an iterable of (ts, obj)");
        if (seq == NULL) {
            return NULL;
        }

        Py_ssize_t n = PySequence_Fast_GET_SIZE(seq);
        if (n == 0) {
            Py_DECREF(seq);
            Py_RETURN_NONE;
        }

        if ((size_t)n > SIZE_MAX / sizeof(tl_record_t)) {
            Py_DECREF(seq);
            return PyErr_Format(PyExc_OverflowError, "batch size too large");
        }

        tl_record_t* records = (tl_record_t*)malloc((size_t)n * sizeof(tl_record_t));
        PyObject** objs = (PyObject**)malloc((size_t)n * sizeof(PyObject*));
        if (records == NULL || objs == NULL) {
            free(records);
            free(objs);
            Py_DECREF(seq);
            return PyErr_NoMemory();
        }
        memset(objs, 0, (size_t)n * sizeof(PyObject*));

        for (Py_ssize_t i = 0; i < n; i++) {
            PyObject* item = PySequence_Fast_GET_ITEM(seq, i); /* borrowed */
            long long ts_ll;
            PyObject* obj;

            if (PyArg_ParseTuple(item, "LO", &ts_ll, &obj)) {
                /* Parsed tuple directly */
            } else {
                PyErr_Clear();
                PyObject* pair = PySequence_Fast(item, "extend() expects (ts, obj)");
                if (pair == NULL) {
                    goto error_seq;
                }
                if (PySequence_Fast_GET_SIZE(pair) != 2) {
                    Py_DECREF(pair);
                    PyErr_SetString(PyExc_ValueError,
                        "extend() expects (ts, obj) pairs");
                    goto error_seq;
                }
                PyObject* ts_obj = PySequence_Fast_GET_ITEM(pair, 0);
                obj = PySequence_Fast_GET_ITEM(pair, 1);
                ts_ll = PyLong_AsLongLong(ts_obj);
                Py_DECREF(pair);
                if (PyErr_Occurred()) {
                    goto error_seq;
                }
            }

            if (tl_py_validate_ts(ts_ll, "timestamp") < 0) {
                goto error_seq;
            }

            Py_INCREF(obj);
            objs[i] = obj;
            records[i].ts = (tl_ts_t)ts_ll;
            records[i].handle = tl_py_handle_encode(obj);
        }

        {
            uint32_t flags = mostly_ordered ? TL_APPEND_HINT_MOSTLY_IN_ORDER : 0;
            tl_status_t st;
            if (tl_py_lock_checked(self) < 0) {
                for (Py_ssize_t i = 0; i < n; i++) {
                    Py_DECREF(objs[i]);
                }
                free(records);
                free(objs);
                Py_DECREF(seq);
                return NULL;
            }
            st = tl_append_batch(self->tl, records, (size_t)n, flags);
            TL_PY_UNLOCK(self);

            if (st == TL_OK || st == TL_EBUSY) {
                for (Py_ssize_t i = 0; i < n; i++) {
                    (void)tl_py_live_note_insert(&self->handle_ctx, objs[i]);
                }

                if (st == TL_EBUSY) {
                    if (tl_py_handle_write_ebusy(self,
                            "Backpressure during batch insert. "
                            "All records were committed. "
                            "Call flush() or wait for background maintenance to relieve.") < 0) {
                        free(records);
                        free(objs);
                        Py_DECREF(seq);
                        return NULL;
                    }
                }

                free(records);
                free(objs);
                Py_DECREF(seq);
                tl_py_drain_retired(&self->handle_ctx, 0);
                Py_RETURN_NONE;
            }

            /* True failure: rollback INCREFs */
            for (Py_ssize_t i = 0; i < n; i++) {
                Py_DECREF(objs[i]);
            }
            free(records);
            free(objs);
            Py_DECREF(seq);
            return TlPy_RaiseFromStatus(st);
        }

error_seq:
        for (Py_ssize_t i = 0; i < n; i++) {
            if (objs[i] != NULL) {
                Py_DECREF(objs[i]);
            }
        }
        free(records);
        free(objs);
        Py_DECREF(seq);
        return NULL;
    }

    /* Streaming path for non-sequence iterables (generator-friendly). */
    PyObject* it = PyObject_GetIter(iterable);
    if (it == NULL) {
        return NULL;
    }

    const size_t chunk_cap = 1024;
    tl_record_t* records = (tl_record_t*)malloc(chunk_cap * sizeof(tl_record_t));
    PyObject** objs = (PyObject**)malloc(chunk_cap * sizeof(PyObject*));
    if (records == NULL || objs == NULL) {
        free(records);
        free(objs);
        Py_DECREF(it);
        return PyErr_NoMemory();
    }

    size_t n = 0;
    uint32_t flags = mostly_ordered ? TL_APPEND_HINT_MOSTLY_IN_ORDER : 0;

    for (;;) {
        PyObject* item = PyIter_Next(it); /* new ref or NULL */
        if (item == NULL) {
            if (PyErr_Occurred()) {
                goto error_stream;
            }
            break; /* end of iterator */
        }

        long long ts_ll;
        PyObject* obj;
        if (PyArg_ParseTuple(item, "LO", &ts_ll, &obj)) {
            /*
             * CRITICAL: obj is borrowed from item (the tuple).
             * INCREF obj BEFORE DECREF item to prevent UAF.
             * Generators yield fresh tuples (refcount=1); DECREF would
             * free the tuple and transitively free obj.
             */
            Py_INCREF(obj);
        } else {
            PyErr_Clear();
            PyObject* pair = PySequence_Fast(item, "extend() expects (ts, obj)");
            if (pair == NULL) {
                Py_DECREF(item);
                goto error_stream;
            }
            if (PySequence_Fast_GET_SIZE(pair) != 2) {
                Py_DECREF(pair);
                Py_DECREF(item);
                PyErr_SetString(PyExc_ValueError,
                    "extend() expects (ts, obj) pairs");
                goto error_stream;
            }
            PyObject* ts_obj = PySequence_Fast_GET_ITEM(pair, 0);
            obj = PySequence_Fast_GET_ITEM(pair, 1);
            ts_ll = PyLong_AsLongLong(ts_obj);
            /*
             * CRITICAL: obj is borrowed from pair.
             * INCREF obj BEFORE DECREF pair to prevent UAF.
             */
            Py_INCREF(obj);
            Py_DECREF(pair);
            if (PyErr_Occurred()) {
                Py_DECREF(obj);
                Py_DECREF(item);
                goto error_stream;
            }
        }
        /* obj is now a strong reference (INCREF'd above in both paths) */
        Py_DECREF(item);

        if (tl_py_validate_ts(ts_ll, "timestamp") < 0) {
            Py_DECREF(obj);
            goto error_stream;
        }

        objs[n] = obj;
        records[n].ts = (tl_ts_t)ts_ll;
        records[n].handle = tl_py_handle_encode(obj);
        n++;

        if (n == chunk_cap) {
            tl_status_t st;
            if (tl_py_lock_checked(self) < 0) {
                goto error_stream;
            }
            st = tl_append_batch(self->tl, records, n, flags);
            TL_PY_UNLOCK(self);

            if (st == TL_OK || st == TL_EBUSY) {
                for (size_t i = 0; i < n; i++) {
                    (void)tl_py_live_note_insert(&self->handle_ctx, objs[i]);
                }
                if (st == TL_EBUSY) {
                    if (tl_py_handle_write_ebusy(self,
                            "Backpressure during batch insert. "
                            "All records were committed. "
                            "Call flush() or wait for background maintenance to relieve.") < 0) {
                        free(records);
                        free(objs);
                        Py_DECREF(it);
                        return NULL;
                    }
                }
                n = 0;
                continue;
            }

            /* True failure: rollback this chunk */
            goto error_stream;
        }
    }

    /* Flush remaining chunk */
    if (n > 0) {
        tl_status_t st;
        if (tl_py_lock_checked(self) < 0) {
            goto error_stream;
        }
        st = tl_append_batch(self->tl, records, n, flags);
        TL_PY_UNLOCK(self);

        if (st == TL_OK || st == TL_EBUSY) {
            for (size_t i = 0; i < n; i++) {
                (void)tl_py_live_note_insert(&self->handle_ctx, objs[i]);
            }
            if (st == TL_EBUSY) {
                if (tl_py_handle_write_ebusy(self,
                        "Backpressure during batch insert. "
                        "All records were committed. "
                        "Call flush() or wait for background maintenance to relieve.") < 0) {
                    free(records);
                    free(objs);
                    Py_DECREF(it);
                    return NULL;
                }
            }
        } else {
            goto error_stream;
        }
    }

    free(records);
    free(objs);
    Py_DECREF(it);
    tl_py_drain_retired(&self->handle_ctx, 0);
    Py_RETURN_NONE;

error_stream:
    for (size_t i = 0; i < n; i++) {
        Py_DECREF(objs[i]);
    }
    free(records);
    free(objs);
    Py_DECREF(it);
    return NULL;
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

    if (tl_py_validate_ts(t1_ll, "t1") < 0 ||
        tl_py_validate_ts(t2_ll, "t2") < 0) {
        return NULL;
    }

    /* Validate: t1 > t2 is invalid, but t1 == t2 is allowed (empty range, no-op) */
    if (t1_ll > t2_ll) {
        return PyErr_Format(PyExc_ValueError,
            "t1 (%lld) must be <= t2 (%lld)", t1_ll, t2_ll);
    }

    tl_status_t st;
    if (tl_py_lock_checked(self) < 0) {
        return NULL;
    }
    st = tl_delete_range(self->tl, (tl_ts_t)t1_ll, (tl_ts_t)t2_ll);
    TL_PY_UNLOCK(self);

    if (st == TL_OK) {
        goto success;
    }

    if (st == TL_EBUSY) {
        /*
         * CRITICAL: EBUSY means tombstone WAS inserted, but backpressure.
         * Same handling as append.
         */
        if (tl_py_handle_write_ebusy(self,
                "Tombstone inserted but backpressure occurred. "
                "Call flush() or wait for background maintenance to relieve.") < 0) {
            return NULL;
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

    if (tl_py_validate_ts(cutoff_ll, "cutoff") < 0) {
        return NULL;
    }

    tl_status_t st;
    if (tl_py_lock_checked(self) < 0) {
        return NULL;
    }
    st = tl_delete_before(self->tl, (tl_ts_t)cutoff_ll);
    TL_PY_UNLOCK(self);

    if (st == TL_OK) {
        goto success;
    }

    if (st == TL_EBUSY) {
        /* Same handling as delete_range */
        if (tl_py_handle_write_ebusy(self,
                "Tombstone inserted but backpressure occurred. "
                "Call flush() or wait for background maintenance to relieve.") < 0) {
            return NULL;
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
    if (tl_py_lock_checked(self) < 0) {
        return NULL;
    }
    Py_BEGIN_ALLOW_THREADS
    st = tl_flush(self->tl);
    PyThread_release_lock(self->core_lock);
    Py_END_ALLOW_THREADS

    if (st == TL_EBUSY) {
        return TlPy_RaiseFromStatusFmt(TL_EBUSY,
            "Flush publish retry exhausted (safe to retry)");
    }
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
    if (tl_py_lock_checked(self) < 0) {
        return NULL;
    }
    Py_BEGIN_ALLOW_THREADS
    st = tl_compact(self->tl);
    PyThread_release_lock(self->core_lock);
    Py_END_ALLOW_THREADS

    if (st != TL_OK && st != TL_EOF) {
        return TlPy_RaiseFromStatus(st);
    }

    /*
     * Note: In manual mode (maintenance='disabled'), compact() only requests
     * compaction. Use maint_step() to perform the work explicitly.
     */

    /* Opportunistic drain after compact */
    tl_py_drain_retired(&self->handle_ctx, 0);

    Py_RETURN_NONE;
}

/*===========================================================================
 * PyTimelog_stats
 *===========================================================================*/

#define TL_PY_SET_U64(dict, key, value) do { \
    PyObject* _v = PyLong_FromUnsignedLongLong((unsigned long long)(value)); \
    if (_v == NULL || PyDict_SetItemString((dict), (key), _v) < 0) { \
        Py_XDECREF(_v); \
        goto stats_error; \
    } \
    Py_DECREF(_v); \
} while (0)

#define TL_PY_SET_I64(dict, key, value) do { \
    PyObject* _v = PyLong_FromLongLong((long long)(value)); \
    if (_v == NULL || PyDict_SetItemString((dict), (key), _v) < 0) { \
        Py_XDECREF(_v); \
        goto stats_error; \
    } \
    Py_DECREF(_v); \
} while (0)

#define TL_PY_SET_DBL(dict, key, value) do { \
    PyObject* _v = PyFloat_FromDouble((double)(value)); \
    if (_v == NULL || PyDict_SetItemString((dict), (key), _v) < 0) { \
        Py_XDECREF(_v); \
        goto stats_error; \
    } \
    Py_DECREF(_v); \
} while (0)

static PyObject*
PyTimelog_stats(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_snapshot_t* snap = NULL;
    tl_stats_t stats;

    tl_py_pins_enter(&self->handle_ctx);
    if (tl_py_lock_checked(self) < 0) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return NULL;
    }
    tl_status_t st = tl_snapshot_acquire(self->tl, &snap);
    TL_PY_UNLOCK(self);
    if (st != TL_OK) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return TlPy_RaiseFromStatus(st);
    }

    st = tl_stats(snap, &stats);
    tl_snapshot_release(snap);
    tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);

    if (st != TL_OK) {
        return TlPy_RaiseFromStatus(st);
    }

    PyObject* out = PyDict_New();
    PyObject* storage = PyDict_New();
    PyObject* memtable = PyDict_New();
    PyObject* operational = PyDict_New();
    PyObject* selection = PyDict_New();
    PyObject* adaptive = PyDict_New();

    if (!out || !storage || !memtable || !operational || !selection || !adaptive) {
        Py_XDECREF(out);
        Py_XDECREF(storage);
        Py_XDECREF(memtable);
        Py_XDECREF(operational);
        Py_XDECREF(selection);
        Py_XDECREF(adaptive);
        return PyErr_NoMemory();
    }

    /* storage */
    TL_PY_SET_U64(storage, "segments_l0", stats.segments_l0);
    TL_PY_SET_U64(storage, "segments_l1", stats.segments_l1);
    TL_PY_SET_U64(storage, "pages_total", stats.pages_total);
    TL_PY_SET_U64(storage, "records_estimate", stats.records_estimate);
    TL_PY_SET_I64(storage, "min_ts", stats.min_ts);
    TL_PY_SET_I64(storage, "max_ts", stats.max_ts);
    TL_PY_SET_U64(storage, "tombstone_count", stats.tombstone_count);

    /* memtable */
    TL_PY_SET_U64(memtable, "active_records", stats.memtable_active_records);
    TL_PY_SET_U64(memtable, "ooo_records", stats.memtable_ooo_records);
    TL_PY_SET_U64(memtable, "sealed_runs", stats.memtable_sealed_runs);

    /* operational */
    TL_PY_SET_U64(operational, "seals_total", stats.seals_total);
    TL_PY_SET_U64(operational, "ooo_budget_hits", stats.ooo_budget_hits);
    TL_PY_SET_U64(operational, "backpressure_waits", stats.backpressure_waits);
    TL_PY_SET_U64(operational, "flushes_total", stats.flushes_total);
    TL_PY_SET_U64(operational, "compactions_total", stats.compactions_total);
    TL_PY_SET_U64(operational, "compaction_retries", stats.compaction_retries);
    TL_PY_SET_U64(operational, "compaction_publish_ebusy", stats.compaction_publish_ebusy);

    /* compaction selection */
    TL_PY_SET_U64(selection, "select_calls", stats.compaction_select_calls);
    TL_PY_SET_U64(selection, "select_l0_inputs", stats.compaction_select_l0_inputs);
    TL_PY_SET_U64(selection, "select_l1_inputs", stats.compaction_select_l1_inputs);
    TL_PY_SET_U64(selection, "select_no_work", stats.compaction_select_no_work);

    /* adaptive */
    TL_PY_SET_I64(adaptive, "window", stats.adaptive_window);
    TL_PY_SET_DBL(adaptive, "ewma_density", stats.adaptive_ewma_density);
    TL_PY_SET_U64(adaptive, "flush_count", stats.adaptive_flush_count);
    TL_PY_SET_U64(adaptive, "failures", stats.adaptive_failures);

    if (PyDict_SetItemString(out, "storage", storage) < 0 ||
        PyDict_SetItemString(out, "memtable", memtable) < 0 ||
        PyDict_SetItemString(out, "operational", operational) < 0 ||
        PyDict_SetItemString(out, "compaction_selection", selection) < 0 ||
        PyDict_SetItemString(out, "adaptive", adaptive) < 0) {
        goto stats_error;
    }

    Py_DECREF(storage);
    Py_DECREF(memtable);
    Py_DECREF(operational);
    Py_DECREF(selection);
    Py_DECREF(adaptive);
    return out;

stats_error:
    Py_XDECREF(out);
    Py_XDECREF(storage);
    Py_XDECREF(memtable);
    Py_XDECREF(operational);
    Py_XDECREF(selection);
    Py_XDECREF(adaptive);
    return NULL;
}

#undef TL_PY_SET_U64
#undef TL_PY_SET_I64
#undef TL_PY_SET_DBL

/*===========================================================================
 * PyTimelog_maint_step
 *===========================================================================*/

static PyObject*
PyTimelog_maint_step(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_status_t st;
    if (tl_py_lock_checked(self) < 0) {
        return NULL;
    }
    Py_BEGIN_ALLOW_THREADS
    st = tl_maint_step(self->tl);
    PyThread_release_lock(self->core_lock);
    Py_END_ALLOW_THREADS

    if (st == TL_OK) {
        tl_py_drain_retired(&self->handle_ctx, 0);
        Py_RETURN_TRUE;
    }
    if (st == TL_EOF) {
        Py_RETURN_FALSE;
    }
    return TlPy_RaiseFromStatus(st);
}

/*===========================================================================
 * Timestamp navigation helpers
 *===========================================================================*/

static PyObject*
PyTimelog_min_ts(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_snapshot_t* snap = NULL;
    tl_ts_t out;

    tl_py_pins_enter(&self->handle_ctx);
    if (tl_py_lock_checked(self) < 0) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return NULL;
    }
    tl_status_t st = tl_snapshot_acquire(self->tl, &snap);
    TL_PY_UNLOCK(self);
    if (st != TL_OK) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return TlPy_RaiseFromStatus(st);
    }

    st = tl_min_ts(snap, &out);
    tl_snapshot_release(snap);
    tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);

    if (st == TL_EOF) {
        Py_RETURN_NONE;
    }
    if (st != TL_OK) {
        return TlPy_RaiseFromStatus(st);
    }
    return PyLong_FromLongLong((long long)out);
}

static PyObject*
PyTimelog_max_ts(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_snapshot_t* snap = NULL;
    tl_ts_t out;

    tl_py_pins_enter(&self->handle_ctx);
    if (tl_py_lock_checked(self) < 0) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return NULL;
    }
    tl_status_t st = tl_snapshot_acquire(self->tl, &snap);
    TL_PY_UNLOCK(self);
    if (st != TL_OK) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return TlPy_RaiseFromStatus(st);
    }

    st = tl_max_ts(snap, &out);
    tl_snapshot_release(snap);
    tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);

    if (st == TL_EOF) {
        Py_RETURN_NONE;
    }
    if (st != TL_OK) {
        return TlPy_RaiseFromStatus(st);
    }
    return PyLong_FromLongLong((long long)out);
}

static PyObject*
PyTimelog_next_ts(PyTimelog* self, PyObject* args)
{
    CHECK_CLOSED(self);

    long long ts_ll;
    if (!PyArg_ParseTuple(args, "L", &ts_ll)) {
        return NULL;
    }

    if (tl_py_validate_ts(ts_ll, "ts") < 0) {
        return NULL;
    }

    tl_snapshot_t* snap = NULL;
    tl_ts_t out;

    tl_py_pins_enter(&self->handle_ctx);
    if (tl_py_lock_checked(self) < 0) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return NULL;
    }
    tl_status_t st = tl_snapshot_acquire(self->tl, &snap);
    TL_PY_UNLOCK(self);
    if (st != TL_OK) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return TlPy_RaiseFromStatus(st);
    }

    st = tl_next_ts(snap, (tl_ts_t)ts_ll, &out);
    tl_snapshot_release(snap);
    tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);

    if (st == TL_EOF) {
        Py_RETURN_NONE;
    }
    if (st != TL_OK) {
        return TlPy_RaiseFromStatus(st);
    }
    return PyLong_FromLongLong((long long)out);
}

static PyObject*
PyTimelog_prev_ts(PyTimelog* self, PyObject* args)
{
    CHECK_CLOSED(self);

    long long ts_ll;
    if (!PyArg_ParseTuple(args, "L", &ts_ll)) {
        return NULL;
    }

    if (tl_py_validate_ts(ts_ll, "ts") < 0) {
        return NULL;
    }

    tl_snapshot_t* snap = NULL;
    tl_ts_t out;

    tl_py_pins_enter(&self->handle_ctx);
    if (tl_py_lock_checked(self) < 0) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return NULL;
    }
    tl_status_t st = tl_snapshot_acquire(self->tl, &snap);
    TL_PY_UNLOCK(self);
    if (st != TL_OK) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return TlPy_RaiseFromStatus(st);
    }

    st = tl_prev_ts(snap, (tl_ts_t)ts_ll, &out);
    tl_snapshot_release(snap);
    tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);

    if (st == TL_EOF) {
        Py_RETURN_NONE;
    }
    if (st != TL_OK) {
        return TlPy_RaiseFromStatus(st);
    }
    return PyLong_FromLongLong((long long)out);
}

/*===========================================================================
 * PyTimelog_validate
 *===========================================================================*/

static PyObject*
PyTimelog_validate(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_snapshot_t* snap = NULL;

    tl_py_pins_enter(&self->handle_ctx);
    if (tl_py_lock_checked(self) < 0) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return NULL;
    }
    tl_status_t st = tl_snapshot_acquire(self->tl, &snap);
    TL_PY_UNLOCK(self);
    if (st != TL_OK) {
        tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);
        return TlPy_RaiseFromStatus(st);
    }

    st = tl_validate(snap);
    tl_snapshot_release(snap);
    tl_py_pins_exit_and_maybe_drain(&self->handle_ctx);

    if (st != TL_OK) {
        return TlPy_RaiseFromStatus(st);
    }

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

    tl_status_t st;
    if (tl_py_lock_checked(self) < 0) {
        return NULL;
    }
    st = tl_maint_start(self->tl);
    TL_PY_UNLOCK(self);

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
    if (tl_py_lock_checked(self) < 0) {
        return NULL;
    }
    Py_BEGIN_ALLOW_THREADS
    st = tl_maint_stop(self->tl);  /* Blocks until worker exits */
    PyThread_release_lock(self->core_lock);
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
     * Ensure maintenance worker is running in background mode.
     *
     * tl_open() auto-starts the worker, and tl_maint_start() is idempotent,
     * so this is a safe no-op in the common case. It also allows users who
     * previously stopped maintenance to re-enable it by re-entering the
     * context manager.
     *
     * Note: close() (called by __exit__) already calls tl_maint_stop().
     */
    if (self->maint_mode == TL_MAINT_BACKGROUND) {
        tl_status_t st;
        if (tl_py_lock_checked(self) < 0) {
            return NULL;
        }
        st = tl_maint_start(self->tl);
        TL_PY_UNLOCK(self);
        if (st != TL_OK) {
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
    if (tl_py_lock_checked(self) < 0) {
        tl_py_pins_exit_and_maybe_drain(ctx);
        return NULL;
    }
    tl_status_t st = tl_snapshot_acquire(self->tl, &snap);
    TL_PY_UNLOCK(self);
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
 * If t1 > t2, raises ValueError; t1 == t2 yields empty iterator.
 */
static PyObject* PyTimelog_range(PyTimelog* self, PyObject* args)
{
    long long t1, t2;

    if (!PyArg_ParseTuple(args, "LL", &t1, &t2)) {
        return NULL;
    }

    if (tl_py_validate_ts(t1, "t1") < 0 ||
        tl_py_validate_ts(t2, "t2") < 0) {
        return NULL;
    }
    if (t1 > t2) {
        return PyErr_Format(PyExc_ValueError,
            "t1 (%lld) must be <= t2 (%lld)", t1, t2);
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

    if (tl_py_validate_ts(t, "t") < 0) {
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

    if (tl_py_validate_ts(t, "t") < 0) {
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

    if (tl_py_validate_ts(t, "t") < 0) {
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

    if (tl_py_validate_ts(t, "t") < 0) {
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
 * @param kind "segment" (currently supported value)
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

    if (tl_py_validate_ts(t1, "t1") < 0 ||
        tl_py_validate_ts(t2, "t2") < 0) {
        return NULL;
    }
    if (t1 > t2) {
        return PyErr_Format(PyExc_ValueError,
            "t1 (%lld) must be <= t2 (%lld)", t1, t2);
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
     "Append a record at timestamp ts with payload obj.\n\n"
     "Note: TimelogBusyError means the record WAS committed; do not retry."},

    {"extend", (PyCFunction)PyTimelog_extend, METH_VARARGS | METH_KEYWORDS,
     "extend(iterable, *, mostly_ordered=False) -> None\n\n"
     "Append multiple (ts, obj) records from an iterable.\n"
     "For sequences, uses a single batch append (all-or-nothing).\n"
     "For generators, uses chunked batches; records from completed chunks\n"
     "are committed even if a later chunk fails.\n"
     "If mostly_ordered=True, provides a hint to optimize OOO handling.\n\n"
     "Note: TimelogBusyError means the records WERE committed; do not retry."},

    {"delete_range", (PyCFunction)PyTimelog_delete_range, METH_VARARGS,
     "delete_range(t1, t2) -> None\n\n"
     "Mark records in [t1, t2) for deletion (tombstone).\n\n"
     "Note: TimelogBusyError means the tombstone WAS committed; do not retry."},

    {"delete_before", (PyCFunction)PyTimelog_delete_before, METH_VARARGS,
     "delete_before(cutoff) -> None\n\n"
     "Mark records in [MIN, cutoff) for deletion.\n\n"
     "Note: TimelogBusyError means the tombstone WAS committed; do not retry."},

    {"flush", (PyCFunction)PyTimelog_flush, METH_NOARGS,
     "flush() -> None\n\n"
     "Synchronously flush memtable to L0 segments.\n"
     "Raises TimelogBusyError if publish retry is exhausted (safe to retry)."},

    {"compact", (PyCFunction)PyTimelog_compact, METH_NOARGS,
     "compact() -> None\n\n"
     "Request compaction. In maintenance='disabled', call maint_step()\n"
     "to perform the work explicitly."},

    {"maint_step", (PyCFunction)PyTimelog_maint_step, METH_NOARGS,
     "maint_step() -> bool\n\n"
     "Perform one unit of maintenance work in manual mode.\n"
     "Returns True if work was done, False if no work was needed."},

    {"stats", (PyCFunction)PyTimelog_stats, METH_NOARGS,
     "stats() -> dict\n\n"
     "Return nested statistics dict by category (storage, memtable,\n"
     "operational, compaction_selection, adaptive)."},

    {"start_maintenance", (PyCFunction)PyTimelog_start_maint, METH_NOARGS,
     "start_maintenance() -> None\n\n"
     "Start background maintenance worker (background mode only)."},

    {"stop_maintenance", (PyCFunction)PyTimelog_stop_maint, METH_NOARGS,
     "stop_maintenance() -> None\n\n"
     "Stop background maintenance worker and wait for it to exit."},

    {"close", (PyCFunction)PyTimelog_close, METH_NOARGS,
     "close() -> None\n\n"
     "Close the timelog. Idempotent. Releases all resources.\n\n"
     "WARNING: Records not yet flushed will be lost. All Python objects\n"
     "still owned by the engine are released on close.\n\n"
     "Note: close() should not raise TimelogBusyError."},

    /* Iterator factory methods (LLD-B3) */
    {"range", (PyCFunction)PyTimelog_range, METH_VARARGS,
     "range(t1, t2) -> TimelogIter\n\n"
     "Return an iterator over records in [t1, t2).\n"
     "If t1 > t2, raises ValueError; t1 == t2 yields an empty iterator."},

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

    {"min_ts", (PyCFunction)PyTimelog_min_ts, METH_NOARGS,
     "min_ts() -> int | None\n\n"
     "Return minimum timestamp in snapshot, or None if empty."},

    {"max_ts", (PyCFunction)PyTimelog_max_ts, METH_NOARGS,
     "max_ts() -> int | None\n\n"
     "Return maximum timestamp in snapshot, or None if empty.\n"
     "WARNING: O(N) complexity."},

    {"next_ts", (PyCFunction)PyTimelog_next_ts, METH_VARARGS,
     "next_ts(ts) -> int | None\n\n"
     "Return next timestamp strictly greater than ts, or None."},

    {"prev_ts", (PyCFunction)PyTimelog_prev_ts, METH_VARARGS,
     "prev_ts(ts) -> int | None\n\n"
     "Return previous timestamp strictly less than ts, or None.\n"
     "WARNING: O(N) complexity."},

    {"validate", (PyCFunction)PyTimelog_validate, METH_NOARGS,
     "validate() -> None\n\n"
     "Run snapshot validation; raises TimelogError on invariant failure."},

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
     "  kind: 'segment' (currently supported value)\n\n"
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
        "    Single-writer model. External synchronization is required for\n"
        "    concurrent writes or lifecycle operations. Snapshot-based iterators\n"
        "    are safe for concurrent reads.\n"
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
