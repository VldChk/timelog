/**
 * @file py_timelog.c
 * @brief PyTimelog CPython extension implementation
 *
 * Implementation of the PyTimelog type which wraps tl_timelog_t*.
 * Coordinates lifetimes between the Python object graph and core snapshots.
 *
 * CRITICAL SEMANTICS:
 * - TL_EBUSY from write operations means record/tombstone WAS inserted
 * - Do NOT rollback INCREF on TL_EBUSY
 * - Do NOT retry on TL_EBUSY (would create duplicates)
 *
 * Thread Safety:
 * - Single-writer model: external synchronization required for writes
 * - CPython entry points require an attached thread state; on free-threaded
 *   builds there may be no process-wide GIL.
 * - Core calls are serialized by core_lock and mutable Python-object fields use
 *   per-object critical sections / atomics where they can race.
 * - Thread state is detached, releasing a GIL where present, around long
 *   core calls: flush, compact, maint_step, stop_maintenance, explicit
 *   close() — after preserving Python lifetimes. Iterator range-count
 *   precomputation deliberately stays attached (GIL-fairness; v1.3).
 *   Finalizer/dealloc cleanup keeps the thread state attached.
 * - Write operations keep the caller's Python thread state attached throughout
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

#include "timelogpy/py_timelog.h"
#include "timelogpy/py_iter.h"
#include "timelogpy/py_span_iter.h"  /* PageSpan factory */
#include "timelogpy/py_handle.h"
#include "timelogpy/py_errors.h"
#include "timelogpy/py_module_state.h"
#include "timelogpy/py_compat.h"
#include "timelog/timelog.h"

#include <limits.h>
#include <time.h>   /* timespec_get for in-C auto-timestamp (append fold) */
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

static PyObject* PyTimelog_close(PyTimelog* self, PyObject* Py_UNUSED(args));

static PyObject* PyTimelog_stats(PyTimelog* self, PyObject* Py_UNUSED(args));
static PyObject* PyTimelog_maint_step(PyTimelog* self, PyObject* Py_UNUSED(args));
static PyObject* PyTimelog_min_ts(PyTimelog* self, PyObject* Py_UNUSED(args));
static PyObject* PyTimelog_max_ts(PyTimelog* self, PyObject* Py_UNUSED(args));
static PyObject* PyTimelog_bulk_append(PyTimelog* self, PyObject *const *args,
                                       Py_ssize_t nargs, PyObject* kwnames);
static PyObject* PyTimelog_next_ts(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs);
static PyObject* PyTimelog_prev_ts(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs);
static PyObject* PyTimelog_validate(PyTimelog* self, PyObject* Py_UNUSED(args));
static void PyTimelog_finalize(PyObject* self_obj);
typedef tl_status_t (*tl_py_core_call_fn)(tl_timelog_t*);
static int tl_py_core_call_strict(PyTimelog* self,
                                  tl_py_core_call_fn fn,
                                  tl_status_t* out_status);
static tl_status_t tl_py_core_call_best_effort(PyTimelog* self,
                                                tl_py_core_call_fn fn);

/* Internal non-throwing close helper */
static uint64_t pytimelog_close_no_raise(PyTimelog* self, int from_finalizer);
static void tl_py_timelog_drop_handle_ctx(PyTimelog* self);
static void tl_py_timelog_drop_engine_ctx(PyTimelog* self);

#define TL_PY_RAISE_STATUS(self, status) \
    TlPy_RaiseFromObject((PyObject*)(self), (status))

#define TL_PY_RAISE_STATUS_FMT(self, status, ...) \
    TlPy_RaiseFromObjectFmt((PyObject*)(self), (status), __VA_ARGS__)

static void tl_py_timelog_drop_handle_ctx(PyTimelog* self)
{
    if (self == NULL) {
        return;
    }
    /* Atomically detach so this is consistent with the atomic field used by
     * the lock-free mutation/maintenance capture paths. */
    tl_py_handle_ctx_t* ctx =
        atomic_exchange_explicit(&self->handle_ctx, NULL, memory_order_acq_rel);
    if (ctx == NULL) {
        return;
    }
    tl_py_handle_ctx_decref(ctx);
}

tl_py_engine_ctx_t* tl_py_engine_ctx_new(tl_timelog_t* tl)
{
    tl_py_engine_ctx_t* ctx = PyMem_Malloc(sizeof(*ctx));
    if (ctx == NULL) {
        PyErr_NoMemory();
        return NULL;
    }

    atomic_init(&ctx->refcnt, 1);
    ctx->tl = tl;
    return ctx;
}

void tl_py_engine_ctx_incref(tl_py_engine_ctx_t* ctx)
{
    if (ctx == NULL) {
        return;
    }
    atomic_fetch_add_explicit(&ctx->refcnt, 1, memory_order_relaxed);
}

void tl_py_engine_ctx_close(tl_py_engine_ctx_t* ctx, int allow_threads)
{
    if (ctx == NULL || ctx->tl == NULL) {
        return;
    }

    tl_timelog_t* tl = ctx->tl;
    ctx->tl = NULL;

    if (allow_threads) {
        Py_BEGIN_ALLOW_THREADS
        tl_close(tl);
        Py_END_ALLOW_THREADS
    } else {
        tl_close(tl);
    }
}

void tl_py_engine_ctx_decref(tl_py_engine_ctx_t* ctx)
{
    if (ctx == NULL) {
        return;
    }

    uint64_t old_refcnt = atomic_fetch_sub_explicit(
        &ctx->refcnt, 1, memory_order_acq_rel);

#ifndef NDEBUG
    assert(old_refcnt > 0 && "engine context refcount underflow");
#endif

    if (old_refcnt != 1) {
        return;
    }

    /*
     * During interpreter finalization this may join the core maintenance
     * worker without releasing the current Python thread state. The core
     * worker must remain Python-agnostic and must never call Python C-API.
     */
    tl_py_engine_ctx_close(ctx, !TL_PY_IS_FINALIZING());
    PyMem_Free(ctx);
}

static void tl_py_timelog_drop_engine_ctx(PyTimelog* self)
{
    if (self == NULL || self->engine_ctx == NULL) {
        return;
    }

    tl_py_engine_ctx_t* ctx = self->engine_ctx;
    self->engine_ctx = NULL;
    tl_py_engine_ctx_decref(ctx);
}

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

static int
tl_py_dict_get_item_string_ref(PyObject* dict, const char* key, PyObject** out)
{
    *out = NULL;
#if PY_VERSION_HEX >= 0x030D0000
    return PyDict_GetItemStringRef(dict, key, out) < 0 ? -1 : 0;
#else
    PyObject* val = PyDict_GetItemString(dict, key);
    if (val == NULL) {
        return PyErr_Occurred() ? -1 : 0;
    }
    *out = Py_NewRef(val);
    return 0;
#endif
}

static int
tl_py_dict_has_key_string(PyObject* dict, const char* key, int* out)
{
    PyObject* val = NULL;
    if (tl_py_dict_get_item_string_ref(dict, key, &val) < 0) {
        return -1;
    }
    *out = val != NULL;
    Py_XDECREF(val);
    return 0;
}

/**
 * Check whether a kwarg was provided (positional or keyword).
 *
 * Returns 0 on success, -1 on error (exception set).
 */
static int
kwarg_was_provided(PyObject* args, PyObject* kwds,
                   int index, const char* name, int* out)
{
    *out = 0;
    if (kwds != NULL) {
        if (tl_py_dict_has_key_string(kwds, name, out) < 0) {
            return -1;
        }
        if (*out) return 0;
    }
    if (args != NULL) {
        Py_ssize_t nargs = PyTuple_GET_SIZE(args);
        if (nargs > index) {
            *out = 1;
        }
    }
    return 0;
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
 * Extract an int64 from a single METH_FASTCALL argument, matching
 * PyArg_ParseTuple "L" semantics exactly. PyLong_AsLongLong, like "L", is
 * __index__-based since CPython 3.10 (requires-python >= 3.12, so always):
 * it accepts int and __index__-able objects, rejects float/str/None with
 * TypeError, and raises OverflowError beyond the int64 range. Returns 0 on
 * success (*out set), or -1 with a Python exception set on failure.
 */
static int tl_py_fast_i64(PyObject* arg, long long* out)
{
    long long v = PyLong_AsLongLong(arg);
    if (v == -1 && PyErr_Occurred()) {
        return -1;
    }
    *out = v;
    return 0;
}

/**
 * Coerce a timestamp argument matching the facade _coerce_ts EXACTLY:
 * reject bool -> TypeError("timestamp must be int (bool not allowed)");
 * coerce via __index__ (PyNumber_Index) so float/str/None -> TypeError; and on
 * out-of-int64 raise OverflowError with the facade's exact message. Used by the
 * append fold's explicit-ts paths. (Distinct from tl_py_fast_i64, which ACCEPTS
 * bool, for the idea-2 query/delete methods.) Returns 0 (*out set) or -1 w/ exc.
 */
static int tl_py_coerce_ts(PyObject* x, long long* out)
{
    if (PyBool_Check(x)) {
        PyErr_SetString(PyExc_TypeError,
            "timestamp must be int (bool not allowed)");
        return -1;
    }
    PyObject* idx = PyNumber_Index(x);   /* == operator.index(x) */
    if (idx == NULL) {
        /* Teaching errors for the two most common wrong inputs, matching
         * the facade's _coerce_ts so the C-folded append() and the
         * FASTCALL query/delete methods read identically to
         * __setitem__/at() (v1.3 usability lab: the most-used write
         * method gave the bare CPython index error). */
        if (PyErr_ExceptionMatches(PyExc_TypeError)) {
            if (PyFloat_Check(x)) {
                PyErr_Clear();
                PyErr_Format(PyExc_TypeError,
                    "timestamps are integers in the log's time_unit, not "
                    "float (%R); use int(x), or a finer time_unit", x);
            } else if (strcmp(Py_TYPE(x)->tp_name, "datetime.datetime") == 0
                       || strcmp(Py_TYPE(x)->tp_name, "datetime.date") == 0) {
                PyErr_Clear();
                PyErr_SetString(PyExc_TypeError,
                    "timestamps are integers in the log's time_unit; for a "
                    "datetime use int(dt.timestamp() * 1000) with "
                    "time_unit='ms' (UTC-aware recommended)");
            }
        }
        return -1;
    }
    long long v = PyLong_AsLongLong(idx);
    if (v == -1 && PyErr_Occurred()) {
        if (PyErr_ExceptionMatches(PyExc_OverflowError)) {
            PyErr_Clear();
            PyErr_Format(PyExc_OverflowError,
                "timestamp %S is outside int64 range [%lld, %lld]",
                idx, (long long)TL_TS_MIN, (long long)TL_TS_MAX);
        }
        Py_DECREF(idx);
        return -1;
    }
    Py_DECREF(idx);
    *out = v;
    return 0;
}

/**
 * Wall-clock auto-timestamp matching the facade _now_ts: time.time_ns() scaled
 * by the instance's time_unit. time.time_ns() is CLOCK_REALTIME-based; use the
 * portable C11 timespec_get(TIME_UTC) (works on Linux/macOS/Windows). The clock
 * is non-negative, so integer division == floor (matching Python's //).
 */
static long long tl_py_floor_div_ll(long long value, long long divisor)
{
    long long q = value / divisor;
    long long r = value % divisor;
    return (r != 0 && value < 0) ? q - 1 : q;
}

static int tl_py_now_ts(const PyTimelog* self, long long* out)
{
    struct timespec tsp = {0, 0};
    if (timespec_get(&tsp, TIME_UTC) != TIME_UTC) {
        PyErr_SetString(PyExc_RuntimeError, "failed to read system clock");
        return -1;
    }

    long double sec_ld = (long double)tsp.tv_sec;
    if (sec_ld > ((long double)LLONG_MAX / 1000000000.0L) ||
        sec_ld < ((long double)LLONG_MIN / 1000000000.0L)) {
        PyErr_SetString(PyExc_OverflowError,
            "auto timestamp is outside int64 range");
        return -1;
    }

    long long sec = (long long)tsp.tv_sec;
    long long ns;
    if (sec > 0 &&
        sec > (LLONG_MAX - (long long)tsp.tv_nsec) / 1000000000LL) {
        PyErr_SetString(PyExc_OverflowError,
            "auto timestamp is outside int64 range");
        return -1;
    }
    if (sec < 0 &&
        sec < (LLONG_MIN + (long long)tsp.tv_nsec) / 1000000000LL) {
        PyErr_SetString(PyExc_OverflowError,
            "auto timestamp is outside int64 range");
        return -1;
    }
    ns = sec * 1000000000LL + (long long)tsp.tv_nsec;

    switch (atomic_load_explicit(&self->time_unit, memory_order_acquire)) {
        case TL_TIME_S:  *out = tl_py_floor_div_ll(ns, 1000000000LL); break;
        case TL_TIME_MS: *out = tl_py_floor_div_ll(ns, 1000000LL); break;
        case TL_TIME_US: *out = tl_py_floor_div_ll(ns, 1000LL); break;
        case TL_TIME_NS: default: *out = ns; break;
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
    /* Count every surfaced write-path EBUSY regardless of policy so
     * operators can alert on chronic backpressure even under 'silent'
     * or 'flush' (v1.3 usability lab: stats offered no trace). */
    atomic_fetch_add_explicit(&self->busy_events, 1, memory_order_relaxed);

    if (self->busy_policy == TL_PY_BUSY_RAISE) {
        TL_PY_RAISE_STATUS_FMT(self, TL_EBUSY, "%s", msg);
        return -1;
    }

    if (self->busy_policy == TL_PY_BUSY_FLUSH) {
        tl_status_t flush_st = tl_py_core_call_best_effort(self, tl_flush);

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
        TL_PY_RAISE_STATUS_FMT(self, TL_ESTATE, "Timelog is closed");
        return -1;
    }
    return 0;
}

/*
 * Capture an OWNED reference to handle_ctx while core_lock is already held by
 * the caller. The owned ref keeps the context (and its live/retired tables)
 * alive across post-unlock bookkeeping even if a concurrent close() drops the
 * canonical reference. Returns NULL if the context has already been dropped.
 *
 * Pairs with tl_py_handle_ctx_decref(), which the caller MUST invoke once the
 * bookkeeping is complete (with no locks held — the final decref may run the
 * live-table teardown, which performs Py_DECREF).
 */
static tl_py_handle_ctx_t* tl_py_own_handle_ctx_locked(PyTimelog* self)
{
    tl_py_handle_ctx_t* h =
        atomic_load_explicit(&self->handle_ctx, memory_order_acquire);
    if (h != NULL) {
        tl_py_handle_ctx_incref(h);
    }
    return h;
}

/*
 * Same, but acquires core_lock itself. For paths (flush/compact/maintenance)
 * that release the lock inside a core-call helper before draining.
 */
static tl_py_handle_ctx_t* tl_py_acquire_owned_handle_ctx(PyTimelog* self)
{
    TL_PY_LOCK(self);
    tl_py_handle_ctx_t* h = tl_py_own_handle_ctx_locked(self);
    TL_PY_UNLOCK(self);
    return h;
}

/*
 * Non-blocking variant for tp_traverse, which must never park: during a
 * free-threaded stop-the-world collection core_lock can be held by a FROZEN
 * thread that will only run again after the GC finishes — and the GC cannot
 * finish while traverse is parked on the lock. Returns NULL when the lock
 * is contended; the caller under-reports for this GC cycle (over-retention
 * for one cycle, which is always sound).
 */
static tl_py_handle_ctx_t* tl_py_try_acquire_owned_handle_ctx(PyTimelog* self)
{
    if (!TL_PY_TRYLOCK(self)) {
        return NULL;
    }
    tl_py_handle_ctx_t* h = tl_py_own_handle_ctx_locked(self);
    TL_PY_UNLOCK(self);
    return h;
}

/*
 * Opportunistic post-core-call drain. Own a handle_ctx reference (so a
 * concurrent close() cannot free it mid-drain), drain retired Python refs
 * best-effort (force=0), then drop the reference. Runs with no lock held:
 * the drain may Py_DECREF, so it must never be called under core_lock.
 */
static void tl_py_drain_owned(PyTimelog* self)
{
    tl_py_handle_ctx_t* dctx = tl_py_acquire_owned_handle_ctx(self);
    if (dctx != NULL) {
        tl_py_drain_retired(dctx, 0);
        tl_py_handle_ctx_decref(dctx);
    }
}

static int
tl_py_core_call_strict(PyTimelog* self, tl_py_core_call_fn fn, tl_status_t* out_status)
{
    if (self == NULL || fn == NULL || out_status == NULL) {
        return -1;
    }

    if (tl_py_lock_checked(self) < 0) {
        return -1;
    }

    Py_BEGIN_ALLOW_THREADS
    *out_status = fn(self->tl);
    /* Release core_lock before re-attaching the thread state to prevent an
     * ABBA deadlock on GIL builds. */
    PyThread_release_lock(self->core_lock);
    Py_END_ALLOW_THREADS

    return 0;
}

static tl_status_t
tl_py_core_call_best_effort(PyTimelog* self, tl_py_core_call_fn fn)
{
    if (self == NULL || fn == NULL) {
        return TL_EINVAL;
    }

    tl_status_t st = TL_ESTATE;
    TL_PY_LOCK(self);
    if (!self->closed && self->tl != NULL) {
        Py_BEGIN_ALLOW_THREADS
        st = fn(self->tl);
        /*
         * Release core_lock BEFORE re-attaching the thread state to prevent
         * ABBA deadlock on GIL builds: Thread A holds core_lock + wants the
         * GIL, Thread B holds the GIL + wants core_lock.
         */
        PyThread_release_lock(self->core_lock);
        Py_END_ALLOW_THREADS
    } else {
        TL_PY_UNLOCK(self);
    }

    return st;
}

/*
 * Acquire a consistent snapshot with all lifetime guards taken atomically
 * under core_lock — without the lock, a concurrent close() could free
 * handle_ctx or engine_ctx in the window between checking the open state
 * and pinning them.
 *
 * Under the lock we:
 *   - own a reference on handle_ctx (so drain bookkeeping survives the
 *     unlock even if close() nulls self->handle_ctx);
 *   - own a reference on engine_ctx (so the core tl_timelog_t cannot be
 *     freed by a concurrent close's final engine_ctx_decref while our
 *     snapshot still points into it — tl_close asserts snapshot_count==0);
 *   - enter the pin (blocks retired-object drain while the snapshot lives);
 *   - acquire the snapshot itself.
 *
 * On success returns 0 and the caller owns (snap, hctx, ectx); it MUST
 * release them via tl_py_release_snapshot_pinned(). On failure returns -1
 * with a Python exception set and no guards held.
 */
static int tl_py_acquire_snapshot_pinned(PyTimelog* self,
                                         tl_snapshot_t** out_snap,
                                         tl_py_handle_ctx_t** out_hctx,
                                         tl_py_engine_ctx_t** out_ectx)
{
    *out_snap = NULL;
    *out_hctx = NULL;
    *out_ectx = NULL;

    if (tl_py_lock_checked(self) < 0) {
        return -1;
    }

    /* Under core_lock: self->handle_ctx / engine_ctx / tl are all stable. */
    tl_py_handle_ctx_t* hctx =
        atomic_load_explicit(&self->handle_ctx, memory_order_acquire);
    tl_py_engine_ctx_t* ectx = self->engine_ctx;
    tl_py_handle_ctx_incref(hctx);
    tl_py_engine_ctx_incref(ectx);
    tl_py_pins_enter(hctx);

    tl_status_t st = tl_snapshot_acquire(self->tl, out_snap);
    TL_PY_UNLOCK(self);

    if (st != TL_OK) {
        tl_py_pins_exit_and_maybe_drain(hctx);
        tl_py_engine_ctx_decref(ectx);
        tl_py_handle_ctx_decref(hctx);
        TL_PY_RAISE_STATUS(self, st);
        return -1;
    }

    *out_hctx = hctx;
    *out_ectx = ectx;
    return 0;
}

static void tl_py_release_snapshot_pinned(tl_snapshot_t* snap,
                                          tl_py_handle_ctx_t* hctx,
                                          tl_py_engine_ctx_t* ectx)
{
    /* Order: release the snapshot first (drops engine snapshot_count) so
     * that if our engine_ctx_decref below is the last ref and triggers
     * tl_close, snapshot_count is already 0. Then exit the pin (may drain),
     * then drop the ctx refs. None of this runs under core_lock. */
    if (snap != NULL) {
        tl_snapshot_release(snap);
    }
    tl_py_pins_exit_and_maybe_drain(hctx);
    tl_py_engine_ctx_decref(ectx);
    tl_py_handle_ctx_decref(hctx);
}

/*===========================================================================
 * Dict kwarg helpers for grouped config (adaptive={...}, compaction={...})
 *===========================================================================*/

/**
 * Get an optional integer value from a Python dict.
 * Returns 0 on success, -1 on error (exception set).
 * If key is not present, *out is unchanged.
 */
static int
dict_get_ssize(PyObject* dict, const char* key, Py_ssize_t* out)
{
    PyObject* val = NULL;
    if (tl_py_dict_get_item_string_ref(dict, key, &val) < 0) {
        return -1;
    }
    if (val == NULL) {
        return 0;
    }
    Py_ssize_t v = PyLong_AsSsize_t(val);
    Py_DECREF(val);
    if (v == -1 && PyErr_Occurred()) return -1;
    *out = v;
    return 0;
}

/**
 * Get an optional long long value from a Python dict.
 */
static int
dict_get_llong(PyObject* dict, const char* key, long long* out)
{
    PyObject* val = NULL;
    if (tl_py_dict_get_item_string_ref(dict, key, &val) < 0) {
        return -1;
    }
    if (val == NULL) return 0;
    long long v = PyLong_AsLongLong(val);
    Py_DECREF(val);
    if (v == -1 && PyErr_Occurred()) return -1;
    *out = v;
    return 0;
}

/**
 * Get an optional double value from a Python dict.
 */
static int
dict_get_double(PyObject* dict, const char* key, double* out)
{
    PyObject* val = NULL;
    if (tl_py_dict_get_item_string_ref(dict, key, &val) < 0) {
        return -1;
    }
    if (val == NULL) return 0;
    double v = PyFloat_AsDouble(val);
    Py_DECREF(val);
    if (v == -1.0 && PyErr_Occurred()) return -1;
    *out = v;
    return 0;
}

/**
 * Validate that a dict contains only known keys.
 * Returns 0 on success, -1 on error (exception set).
 */
static int
dict_validate_keys(PyObject* dict, const char* dict_name,
                   const char* const* known_keys, size_t nkeys)
{
    PyObject *key, *value;
    Py_ssize_t pos = 0;
    while (PyDict_Next(dict, &pos, &key, &value)) {
        if (!PyUnicode_Check(key)) {
            PyErr_Format(PyExc_TypeError,
                "%s keys must be str", dict_name);
            return -1;
        }
        const char* ks = PyUnicode_AsUTF8(key);
        if (ks == NULL) return -1;
        int found = 0;
        for (size_t i = 0; i < nkeys; i++) {
            if (strcmp(ks, known_keys[i]) == 0) { found = 1; break; }
        }
        if (!found) {
            PyErr_Format(PyExc_ValueError,
                "Unknown key '%s' in %s dict", ks, dict_name);
            return -1;
        }
    }
    return 0;
}

/*===========================================================================
 * PyTimelog_init (tp_init)
 *===========================================================================*/

static int
PyTimelog_init(PyTimelog* self, PyObject* args, PyObject* kwds)
{
    /* Re-init not allowed. */
    if (atomic_load_explicit(&self->tl, memory_order_acquire) != NULL) {
        PyErr_SetString(PyExc_TypeError, "Timelog already initialized");
        return -1;
    }

    /* Keep partially initialized and facade-reopened instances observably
     * closed until every lifetime guard (handle_ctx, engine_ctx, core_lock)
     * has been installed. A subclass can leak `self` from __new__ under a
     * free-threaded build; methods seeing this object during __init__ must
     * fail closed rather than running with a half-published core pointer. */
    atomic_store_explicit(&self->closed, 1, memory_order_release);

    /* core_lock is per-PyObject, not per-engine. A closed instance may be
     * reopened by the Python facade, so preserve an existing lock instead of
     * losing its pointer and leaking it. Fresh tp_alloc memory is already
     * zeroed, so new instances still start with core_lock == NULL. */
    atomic_store_explicit(&self->handle_ctx, NULL, memory_order_release);
    self->engine_ctx = NULL;

    if (TlPy_StateFromObject((PyObject*)self) == NULL) {
        return -1;
    }

    if (self->core_lock == NULL) {
        self->core_lock = PyThread_allocate_lock();
        if (self->core_lock == NULL) {
            PyErr_NoMemory();
            return -1;
        }
    }

    enum {
        KW_TIME_UNIT = 0,
        KW_MAINTENANCE,
        KW_MEMTABLE_MAX_BYTES,
        KW_TARGET_PAGE_BYTES,
        KW_SEALED_MAX_RUNS,
        KW_DRAIN_BATCH_LIMIT,
        KW_BUSY_POLICY,
        KW_OOO_BUDGET_BYTES,
        KW_SEALED_WAIT_MS,
        KW_MAINTENANCE_WAKEUP_MS,
        KW_MAX_DELTA_SEGMENTS,
        KW_WINDOW_SIZE,
        KW_WINDOW_ORIGIN,
        KW_DELETE_DEBT_THRESHOLD,
        KW_COMPACTION_TARGET_BYTES,
        KW_MAX_COMPACTION_INPUTS,
        KW_MAX_COMPACTION_WINDOWS,
        KW_ADAPTIVE_TARGET_RECORDS,
        KW_ADAPTIVE_MIN_WINDOW,
        KW_ADAPTIVE_MAX_WINDOW,
        KW_ADAPTIVE_HYSTERESIS_PCT,
        KW_ADAPTIVE_WINDOW_QUANTUM,
        KW_ADAPTIVE_ALPHA,
        KW_ADAPTIVE_WARMUP_FLUSHES,
        KW_ADAPTIVE_STALE_FLUSHES,
        KW_ADAPTIVE_FAILURE_BACKOFF_THRESHOLD,
        KW_ADAPTIVE_FAILURE_BACKOFF_PCT,
        KW_ADAPTIVE_DICT,
        KW_COMPACTION_DICT
    };

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
        "adaptive",              /* O - dict */
        "compaction",            /* O - dict */
        NULL
    };

    const char* time_unit_str = NULL;
    const char* maint_str = NULL;
    Py_ssize_t memtable_max_bytes = PY_SSIZE_T_MIN;
    Py_ssize_t target_page_bytes = PY_SSIZE_T_MIN;
    Py_ssize_t sealed_max_runs = PY_SSIZE_T_MIN;
    Py_ssize_t drain_batch_limit = PY_SSIZE_T_MIN;
    const char* busy_policy_str = NULL;
    Py_ssize_t ooo_budget_bytes = PY_SSIZE_T_MIN;
    Py_ssize_t sealed_wait_ms = PY_SSIZE_T_MIN;
    Py_ssize_t maintenance_wakeup_ms = PY_SSIZE_T_MIN;
    Py_ssize_t max_delta_segments = PY_SSIZE_T_MIN;
    long long window_size = LLONG_MIN;
    long long window_origin = LLONG_MIN;
    double delete_debt_threshold = -1.0;
    Py_ssize_t compaction_target_bytes = PY_SSIZE_T_MIN;
    Py_ssize_t max_compaction_inputs = PY_SSIZE_T_MIN;
    Py_ssize_t max_compaction_windows = PY_SSIZE_T_MIN;
    Py_ssize_t adaptive_target_records = PY_SSIZE_T_MIN;
    long long adaptive_min_window = LLONG_MIN;
    long long adaptive_max_window = LLONG_MIN;
    Py_ssize_t adaptive_hysteresis_pct = PY_SSIZE_T_MIN;
    long long adaptive_window_quantum = LLONG_MIN;
    double adaptive_alpha = -1.0;
    Py_ssize_t adaptive_warmup_flushes = PY_SSIZE_T_MIN;
    Py_ssize_t adaptive_stale_flushes = PY_SSIZE_T_MIN;
    Py_ssize_t adaptive_failure_backoff_threshold = PY_SSIZE_T_MIN;
    Py_ssize_t adaptive_failure_backoff_pct = PY_SSIZE_T_MIN;
    PyObject* adaptive_dict = NULL;
    PyObject* compaction_dict = NULL;

    if (!PyArg_ParseTupleAndKeywords(args, kwds,
            "|ssnnnnsnnnnLLdnnnnLLnLdnnnnOO", kwlist,
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
            &adaptive_failure_backoff_threshold, &adaptive_failure_backoff_pct,
            &adaptive_dict, &compaction_dict)) {
        return -1;
    }

    int delete_debt_threshold_set = 0;
    int adaptive_alpha_flat_set = 0;
    int adaptive_alpha_set = 0;
    if (kwarg_was_provided(args, kwds, KW_DELETE_DEBT_THRESHOLD,
                           "delete_debt_threshold", &delete_debt_threshold_set) < 0) {
        return -1;
    }
    if (kwarg_was_provided(args, kwds, KW_ADAPTIVE_ALPHA,
                           "adaptive_alpha", &adaptive_alpha_flat_set) < 0) {
        return -1;
    }
    adaptive_alpha_set = adaptive_alpha_flat_set;

    /*
     * Parse adaptive={...} dict kwarg.
     * Values from the dict override flat adaptive_* kwargs.
     * Passing both a flat kwarg and the same key in the dict is an error.
     */
    if (adaptive_dict != NULL && adaptive_dict != Py_None) {
        if (!PyDict_Check(adaptive_dict)) {
            PyErr_SetString(PyExc_TypeError,
                "adaptive must be a dict or None");
            return -1;
        }

        static const char* const adaptive_keys[] = {
            "target_records", "min_window", "max_window",
            "hysteresis_pct", "window_quantum", "alpha",
            "warmup_flushes", "stale_flushes",
            "failure_backoff_threshold", "failure_backoff_pct",
        };
        if (dict_validate_keys(adaptive_dict, "adaptive",
                adaptive_keys, 10) < 0)
            return -1;

        /* Conflict detection: flat kwarg vs dict key */
#define CHECK_ADAPTIVE_CONFLICT(flat_var, sentinel, key_name)           \
        do {                                                            \
            if ((flat_var) != (sentinel)) {                             \
                int _present = 0;                                       \
                if (tl_py_dict_has_key_string(                          \
                        adaptive_dict, key_name, &_present) < 0) {      \
                    return -1;                                          \
                }                                                       \
                if (_present) {                                         \
                    PyErr_Format(PyExc_ValueError,                      \
                        "Cannot specify both adaptive_%s and "          \
                        "adaptive={'%s': ...}", key_name, key_name);    \
                    return -1;                                          \
                }                                                       \
            }                                                           \
        } while (0)

        CHECK_ADAPTIVE_CONFLICT(adaptive_target_records, PY_SSIZE_T_MIN, "target_records");
        CHECK_ADAPTIVE_CONFLICT(adaptive_min_window, LLONG_MIN, "min_window");
        CHECK_ADAPTIVE_CONFLICT(adaptive_max_window, LLONG_MIN, "max_window");
        CHECK_ADAPTIVE_CONFLICT(adaptive_hysteresis_pct, PY_SSIZE_T_MIN, "hysteresis_pct");
        CHECK_ADAPTIVE_CONFLICT(adaptive_window_quantum, LLONG_MIN, "window_quantum");
        CHECK_ADAPTIVE_CONFLICT(adaptive_warmup_flushes, PY_SSIZE_T_MIN, "warmup_flushes");
        CHECK_ADAPTIVE_CONFLICT(adaptive_stale_flushes, PY_SSIZE_T_MIN, "stale_flushes");
        CHECK_ADAPTIVE_CONFLICT(adaptive_failure_backoff_threshold, PY_SSIZE_T_MIN, "failure_backoff_threshold");
        CHECK_ADAPTIVE_CONFLICT(adaptive_failure_backoff_pct, PY_SSIZE_T_MIN, "failure_backoff_pct");

        if (adaptive_alpha_flat_set) {
            int _present = 0;
            if (tl_py_dict_has_key_string(adaptive_dict, "alpha",
                                          &_present) < 0) {
                return -1;
            }
            if (_present) {
                PyErr_Format(PyExc_ValueError,
                    "Cannot specify both adaptive_alpha and "
                    "adaptive={'alpha': ...}");
                return -1;
            }
        }
#undef CHECK_ADAPTIVE_CONFLICT

        /* Extract values from dict into the flat variables */
        if (dict_get_ssize(adaptive_dict, "target_records", &adaptive_target_records) < 0 ||
            dict_get_llong(adaptive_dict, "min_window", &adaptive_min_window) < 0 ||
            dict_get_llong(adaptive_dict, "max_window", &adaptive_max_window) < 0 ||
            dict_get_ssize(adaptive_dict, "hysteresis_pct", &adaptive_hysteresis_pct) < 0 ||
            dict_get_llong(adaptive_dict, "window_quantum", &adaptive_window_quantum) < 0 ||
            dict_get_double(adaptive_dict, "alpha", &adaptive_alpha) < 0 ||
            dict_get_ssize(adaptive_dict, "warmup_flushes", &adaptive_warmup_flushes) < 0 ||
            dict_get_ssize(adaptive_dict, "stale_flushes", &adaptive_stale_flushes) < 0 ||
            dict_get_ssize(adaptive_dict, "failure_backoff_threshold", &adaptive_failure_backoff_threshold) < 0 ||
            dict_get_ssize(adaptive_dict, "failure_backoff_pct", &adaptive_failure_backoff_pct) < 0) {
            return -1;
        }

        int alpha_present = 0;
        if (tl_py_dict_has_key_string(adaptive_dict, "alpha",
                                      &alpha_present) < 0) {
            return -1;
        }
        if (alpha_present) {
            adaptive_alpha_set = 1;
        }
    }

    /*
     * Parse compaction={...} dict kwarg.
     */
    if (compaction_dict != NULL && compaction_dict != Py_None) {
        if (!PyDict_Check(compaction_dict)) {
            PyErr_SetString(PyExc_TypeError,
                "compaction must be a dict or None");
            return -1;
        }

        static const char* const compaction_keys[] = {
            "target_bytes", "max_inputs", "max_windows",
        };
        if (dict_validate_keys(compaction_dict, "compaction",
                compaction_keys, 3) < 0)
            return -1;

        /* Conflict detection */
#define CHECK_COMPACTION_CONFLICT(flat_var, sentinel, key_name, flat_name) \
        do {                                                              \
            if ((flat_var) != (sentinel)) {                               \
                int _present = 0;                                         \
                if (tl_py_dict_has_key_string(                            \
                        compaction_dict, key_name, &_present) < 0) {      \
                    return -1;                                            \
                }                                                         \
                if (_present) {                                           \
                    PyErr_Format(PyExc_ValueError,                        \
                        "Cannot specify both %s and "                     \
                        "compaction={'%s': ...}", flat_name, key_name);   \
                    return -1;                                            \
                }                                                         \
            }                                                             \
        } while (0)

        CHECK_COMPACTION_CONFLICT(compaction_target_bytes, PY_SSIZE_T_MIN,
            "target_bytes", "compaction_target_bytes");
        CHECK_COMPACTION_CONFLICT(max_compaction_inputs, PY_SSIZE_T_MIN,
            "max_inputs", "max_compaction_inputs");
        CHECK_COMPACTION_CONFLICT(max_compaction_windows, PY_SSIZE_T_MIN,
            "max_windows", "max_compaction_windows");
#undef CHECK_COMPACTION_CONFLICT

        /* Extract values */
        if (dict_get_ssize(compaction_dict, "target_bytes", &compaction_target_bytes) < 0 ||
            dict_get_ssize(compaction_dict, "max_inputs", &max_compaction_inputs) < 0 ||
            dict_get_ssize(compaction_dict, "max_windows", &max_compaction_windows) < 0) {
            return -1;
        }
    }

    /* Validate drain_batch_limit range */
    if (drain_batch_limit != PY_SSIZE_T_MIN) {
        if (drain_batch_limit < 0 || (uint64_t)drain_batch_limit > UINT32_MAX) {
            PyErr_SetString(PyExc_ValueError,
                "drain_batch_limit must be 0-4294967295");
            return -1;
        }
    }

    /* Map unset to 0 (unlimited) for ctx init */
    uint32_t drain_limit = (drain_batch_limit == PY_SSIZE_T_MIN) ? 0
        : (uint32_t)drain_batch_limit;

    /* Initialize handle context first. */
    tl_py_handle_ctx_t* hctx = tl_py_handle_ctx_new(drain_limit);
    if (hctx == NULL) {
        return -1;
    }
    atomic_store_explicit(&self->handle_ctx, hctx, memory_order_release);

    /* Build tl_config_t */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    /* Parse and apply time_unit */
    int time_unit_set;
    if (parse_time_unit(time_unit_str, &cfg.time_unit, &time_unit_set) < 0) {
        tl_py_timelog_drop_handle_ctx(self);
        return -1;
    }

    /* Parse and apply maintenance mode */
    if (parse_maint_mode(maint_str, &cfg.maintenance_mode) < 0) {
        tl_py_timelog_drop_handle_ctx(self);
        return -1;
    }

    /* Parse and apply busy_policy */
    if (parse_busy_policy(busy_policy_str, &self->busy_policy) < 0) {
        tl_py_timelog_drop_handle_ctx(self);
        return -1;
    }
    /* Fresh engine (init or reopen): backpressure counter starts at zero. */
    atomic_store_explicit(&self->busy_events, 0, memory_order_relaxed);

    /* Apply numeric overrides with range/overflow validation. */
    if (memtable_max_bytes != PY_SSIZE_T_MIN) {
        if (memtable_max_bytes < 0) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "memtable_max_bytes must be >= 0");
            return -1;
        }
        if ((size_t)memtable_max_bytes != (uint64_t)memtable_max_bytes) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_OverflowError,
                "memtable_max_bytes too large for this platform");
            return -1;
        }
        cfg.memtable_max_bytes = (size_t)memtable_max_bytes;
    }
    if (target_page_bytes != PY_SSIZE_T_MIN) {
        if (target_page_bytes < 0) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "target_page_bytes must be >= 0");
            return -1;
        }
        if ((size_t)target_page_bytes != (uint64_t)target_page_bytes) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_OverflowError,
                "target_page_bytes too large for this platform");
            return -1;
        }
        cfg.target_page_bytes = (size_t)target_page_bytes;
    }
    if (sealed_max_runs != PY_SSIZE_T_MIN) {
        if (sealed_max_runs < 0) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "sealed_max_runs must be >= 0");
            return -1;
        }
        if ((size_t)sealed_max_runs != (uint64_t)sealed_max_runs) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_OverflowError,
                "sealed_max_runs too large for this platform");
            return -1;
        }
        cfg.sealed_max_runs = (size_t)sealed_max_runs;
    }

    if (ooo_budget_bytes != PY_SSIZE_T_MIN) {
        if (ooo_budget_bytes < 0) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "ooo_budget_bytes must be >= 0");
            return -1;
        }
        if ((size_t)ooo_budget_bytes != (uint64_t)ooo_budget_bytes) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_OverflowError,
                "ooo_budget_bytes too large for this platform");
            return -1;
        }
        cfg.ooo_budget_bytes = (size_t)ooo_budget_bytes;
    }

    if (sealed_wait_ms != PY_SSIZE_T_MIN) {
        if (sealed_wait_ms < 0 || (uint64_t)sealed_wait_ms > UINT32_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "sealed_wait_ms must be 0-4294967295");
            return -1;
        }
        cfg.sealed_wait_ms = (uint32_t)sealed_wait_ms;
    }

    if (maintenance_wakeup_ms != PY_SSIZE_T_MIN) {
        if (maintenance_wakeup_ms < 0 || (uint64_t)maintenance_wakeup_ms > UINT32_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "maintenance_wakeup_ms must be 0-4294967295");
            return -1;
        }
        cfg.maintenance_wakeup_ms = (uint32_t)maintenance_wakeup_ms;
    }

    if (max_delta_segments != PY_SSIZE_T_MIN) {
        if (max_delta_segments < 0) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "max_delta_segments must be >= 0");
            return -1;
        }
        if ((size_t)max_delta_segments != (uint64_t)max_delta_segments) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_OverflowError,
                "max_delta_segments too large for this platform");
            return -1;
        }
        cfg.max_delta_segments = (size_t)max_delta_segments;
    }

    if (window_size != LLONG_MIN) {
        if (window_size < 0 || window_size > (long long)TL_TS_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "window_size must be in [0, INT64_MAX]");
            return -1;
        }
        cfg.window_size = (tl_ts_t)window_size;
    }

    if (window_origin != LLONG_MIN) {
        if (window_origin < (long long)TL_TS_MIN ||
            window_origin > (long long)TL_TS_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_OverflowError,
                "window_origin out of int64 range");
            return -1;
        }
        cfg.window_origin = (tl_ts_t)window_origin;
    }

    if (delete_debt_threshold_set) {
        if (!isfinite(delete_debt_threshold)) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "delete_debt_threshold must be finite");
            return -1;
        }
        if (delete_debt_threshold < 0.0 || delete_debt_threshold > 1.0) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "delete_debt_threshold must be in [0.0, 1.0]");
            return -1;
        }
        cfg.delete_debt_threshold = delete_debt_threshold;
    }

    if (compaction_target_bytes != PY_SSIZE_T_MIN) {
        if (compaction_target_bytes < 0) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "compaction_target_bytes must be >= 0");
            return -1;
        }
        if ((size_t)compaction_target_bytes != (uint64_t)compaction_target_bytes) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_OverflowError,
                "compaction_target_bytes too large for this platform");
            return -1;
        }
        cfg.compaction_target_bytes = (size_t)compaction_target_bytes;
    }

    if (max_compaction_inputs != PY_SSIZE_T_MIN) {
        if (max_compaction_inputs < 0 || (uint64_t)max_compaction_inputs > UINT32_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "max_compaction_inputs must be 0-4294967295");
            return -1;
        }
        cfg.max_compaction_inputs = (uint32_t)max_compaction_inputs;
    }

    if (max_compaction_windows != PY_SSIZE_T_MIN) {
        if (max_compaction_windows < 0 || (uint64_t)max_compaction_windows > UINT32_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "max_compaction_windows must be 0-4294967295");
            return -1;
        }
        cfg.max_compaction_windows = (uint32_t)max_compaction_windows;
    }

    if (adaptive_target_records != PY_SSIZE_T_MIN) {
        if (adaptive_target_records < 0) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_target_records must be >= 0");
            return -1;
        }
        cfg.adaptive.target_records = (uint64_t)adaptive_target_records;
    }

    if (adaptive_min_window != LLONG_MIN) {
        if (adaptive_min_window < 0 || adaptive_min_window > (long long)TL_TS_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_min_window must be in [0, INT64_MAX]");
            return -1;
        }
        cfg.adaptive.min_window = (tl_ts_t)adaptive_min_window;
    }

    if (adaptive_max_window != LLONG_MIN) {
        if (adaptive_max_window < 0 || adaptive_max_window > (long long)TL_TS_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_max_window must be in [0, INT64_MAX]");
            return -1;
        }
        cfg.adaptive.max_window = (tl_ts_t)adaptive_max_window;
    }

    if (adaptive_hysteresis_pct != PY_SSIZE_T_MIN) {
        if (adaptive_hysteresis_pct < 0 || (uint64_t)adaptive_hysteresis_pct > UINT32_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_hysteresis_pct must be 0-4294967295");
            return -1;
        }
        cfg.adaptive.hysteresis_pct = (uint32_t)adaptive_hysteresis_pct;
    }

    if (adaptive_window_quantum != LLONG_MIN) {
        if (adaptive_window_quantum < 0 || adaptive_window_quantum > (long long)TL_TS_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_window_quantum must be in [0, INT64_MAX]");
            return -1;
        }
        cfg.adaptive.window_quantum = (tl_ts_t)adaptive_window_quantum;
    }

    if (adaptive_alpha_set) {
        if (!isfinite(adaptive_alpha)) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_alpha must be finite");
            return -1;
        }
        if (adaptive_alpha < 0.0 || adaptive_alpha > 1.0) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_alpha must be in [0.0, 1.0]");
            return -1;
        }
        cfg.adaptive.alpha = adaptive_alpha;
    }

    if (adaptive_warmup_flushes != PY_SSIZE_T_MIN) {
        if (adaptive_warmup_flushes < 0 || (uint64_t)adaptive_warmup_flushes > UINT32_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_warmup_flushes must be 0-4294967295");
            return -1;
        }
        cfg.adaptive.warmup_flushes = (uint32_t)adaptive_warmup_flushes;
    }

    if (adaptive_stale_flushes != PY_SSIZE_T_MIN) {
        if (adaptive_stale_flushes < 0 || (uint64_t)adaptive_stale_flushes > UINT32_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_stale_flushes must be 0-4294967295");
            return -1;
        }
        cfg.adaptive.stale_flushes = (uint32_t)adaptive_stale_flushes;
    }

    if (adaptive_failure_backoff_threshold != PY_SSIZE_T_MIN) {
        if (adaptive_failure_backoff_threshold < 0 ||
            (uint64_t)adaptive_failure_backoff_threshold > UINT32_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_failure_backoff_threshold must be 0-4294967295");
            return -1;
        }
        cfg.adaptive.failure_backoff_threshold =
            (uint32_t)adaptive_failure_backoff_threshold;
    }

    if (adaptive_failure_backoff_pct != PY_SSIZE_T_MIN) {
        if (adaptive_failure_backoff_pct < 0 ||
            (uint64_t)adaptive_failure_backoff_pct > UINT32_MAX) {
            tl_py_timelog_drop_handle_ctx(self);
            PyErr_SetString(PyExc_ValueError,
                "adaptive_failure_backoff_pct must be 0-4294967295");
            return -1;
        }
        cfg.adaptive.failure_backoff_pct =
            (uint32_t)adaptive_failure_backoff_pct;
    }

    /* Wire up drop callback */
    cfg.on_drop_handle = tl_py_on_drop_handle;
    cfg.on_drop_ctx = hctx;

    /* Open the timelog. tl_open writes its result through a plain
     * tl_timelog_t** out-parameter; self->tl is _Atomic so we can't take
     * its address directly (would be UB per C11). Stage through a local
     * and publish under memory_order_release once the engine is open. */
    tl_timelog_t* tl_local = NULL;
    tl_status_t st = tl_open(&cfg, &tl_local);
    if (st != TL_OK) {
        tl_py_timelog_drop_handle_ctx(self);
        atomic_store_explicit(&self->tl, NULL, memory_order_release);
        atomic_store_explicit(&self->closed, 1, memory_order_release);
        TL_PY_RAISE_STATUS(self, st);
        return -1;
    }

    self->engine_ctx = tl_py_engine_ctx_new(tl_local);
    if (self->engine_ctx == NULL) {
        tl_close(tl_local);
        atomic_store_explicit(&self->tl, NULL, memory_order_release);
        atomic_store_explicit(&self->closed, 1, memory_order_release);
        tl_py_timelog_drop_handle_ctx(self);
        return -1;
    }

    /* Success - store introspection fields */
    atomic_store_explicit(&self->time_unit,
                          time_unit_set ? cfg.time_unit : TL_TIME_MS,
                          memory_order_release);
    atomic_store_explicit(&self->tl, tl_local, memory_order_release);
    atomic_store_explicit(&self->closed, 0, memory_order_release);
    self->maint_mode = cfg.maintenance_mode;
    /* Deliberately do NOT reset the min_ts floor here. Fresh tp_alloc memory is
     * already zeroed (no guard); on reopen the facade re-applies the floor via
     * _set_min_ts_floor() as the sole authority. Resetting here would briefly
     * expose a no-guard window if an append raced a reopen. Leaving the prior
     * floor preserves the pre-fold facade's persistent `_min_ts` slot until the
     * new floor is applied. Writes racing lifecycle/reopen are outside the
     * public single-writer/lifecycle serialization contract. */

    /* tl_open() auto-starts maintenance in background mode. */

    return 0;
}

/*===========================================================================
 * PyTimelog_close
 *===========================================================================*/

/**
 * Non-throwing close helper (close, finalizer, dealloc).
 * Skips Python handle drain during interpreter finalization.
 */
static uint64_t
pytimelog_close_no_raise(PyTimelog* self, int from_finalizer)
{
    if (self == NULL) {
        return 0;
    }

    /* Idempotence guard (unlocked fast path). Gate only on the atomic
     * lifecycle fields; engine_ctx is a plain pointer written under
     * core_lock, so reading it unlocked here would be a data race. The
     * atomic closed/tl loads are sufficient — engine_ctx transitions to
     * NULL in lockstep with tl under core_lock, and the authoritative
     * re-check below runs under the lock. */
    if (atomic_load_explicit(&self->closed, memory_order_acquire) ||
        atomic_load_explicit(&self->tl, memory_order_acquire) == NULL) {
        return 0;
    }
    int finalizing = TL_PY_IS_FINALIZING();
    int allow_threads = (!finalizing && !from_finalizer);
    uint64_t pins = 0;
    int defer_engine_close = 0;
    tl_py_engine_ctx_t* engine_ctx = NULL;
    tl_py_handle_ctx_t* handle_ctx = NULL;

    TL_PY_LOCK(self);
    if (self->closed || self->tl == NULL || self->engine_ctx == NULL) {
        TL_PY_UNLOCK(self);
        return 0;
    }
    handle_ctx = atomic_load_explicit(&self->handle_ctx, memory_order_acquire);
    pins = handle_ctx != NULL ? tl_py_pins_count(handle_ctx) : 0;
    /*
     * Finalizer/GC paths must not destroy the core engine while active
     * snapshots exist. Sample pins while holding core_lock so an iterator
     * cannot acquire a snapshot between the sample and close detach.
     * Iterators/PageSpan owners hold engine_ctx refs and will close the
     * engine after releasing their snapshots. Explicit close() rejects pins
     * here while holding the same lock used by snapshot acquisition, so it
     * cannot accidentally detach the contexts after a stale unlocked sample.
     */
    if (!from_finalizer && pins != 0) {
        TL_PY_UNLOCK(self);
        return pins;
    }
    defer_engine_close = (pins != 0);
    atomic_store_explicit(&self->closed, 1, memory_order_release);
    atomic_store_explicit(&self->tl, NULL, memory_order_release);
    engine_ctx = self->engine_ctx;
    self->engine_ctx = NULL;
    /*
     * Detach handle_ctx UNDER core_lock as well. Mutation/maintenance paths
     * capture an owned reference under this same lock before doing post-commit
     * bookkeeping off the lock, so detaching here means a concurrent path
     * either captured a ref before us (keeping the context alive until it
     * decrefs) or sees the field already NULL and skips. Either way there is
     * no torn field read and no teardown racing in-flight bookkeeping.
     */
    atomic_store_explicit(&self->handle_ctx, NULL, memory_order_release);
    TL_PY_UNLOCK(self);

    if (!defer_engine_close) {
        tl_py_engine_ctx_close(engine_ctx, allow_threads);
    }

    tl_py_engine_ctx_decref(engine_ctx);

    /* Degradation metrics read from our captured ref (field already NULL). */
    uint64_t alloc_failures = handle_ctx != NULL ?
        tl_py_alloc_failures(handle_ctx) : 0;
    int live_tracking_failed = 0;
    if (handle_ctx != NULL) {
        live_tracking_failed = atomic_load_explicit(
            &handle_ctx->live_tracking_failed,
            memory_order_acquire) != 0;
    }

    /*
     * Drop the canonical handle_ctx reference. We deliberately do NOT drain
     * the retired stack or release the live table here: that teardown lives in
     * the refcount destructor (refcnt -> 0), which by construction runs only
     * once no other reference is outstanding. If a concurrent mutation or
     * maintenance path captured an owned ref (under core_lock, above), it keeps
     * the context alive until it finishes its bookkeeping and decrefs; whoever
     * drops the last reference triggers teardown with no concurrent access. In
     * the common single-threaded close, this decref IS the last reference, so
     * teardown happens synchronously here. PRESERVE_EXC because the destructor
     * may run Py_DECREF (object finalizers).
     */
    if (handle_ctx != NULL) {
        TL_PY_PRESERVE_EXC_BEGIN;
        tl_py_handle_ctx_decref(handle_ctx);
        TL_PY_PRESERVE_EXC_END;
    }

    if (!finalizing && (alloc_failures > 0 || live_tracking_failed)) {
        TL_PY_PRESERVE_EXC_BEGIN;
        if (PyErr_WarnFormat(PyExc_ResourceWarning, 1,
                             "Timelog close detected handle-tracking degradation "
                             "(live_tracking_failed=%d, alloc_failures=%llu)",
                             live_tracking_failed,
                             (unsigned long long)alloc_failures) < 0) {
            PyErr_Clear();
        }
        TL_PY_PRESERVE_EXC_END;
    }

    /*
     * Do NOT free core_lock here. close() runs while the PyTimelog is still
     * reachable from Python: a concurrent thread can pass the unlocked
     * preflight in a method, then this thread frees core_lock, then the
     * other thread's TL_PY_LOCK dereferences freed lock storage (UAF) — or
     * worse, TL_PY_LOCK becomes a silent no-op (core_lock==NULL) and the
     * method runs its locked section unsynchronized. core_lock is freed
     * only in tp_dealloc, when refcount has reached zero and no other thread
     * can reach the object. After close, methods still acquire the live
     * lock and bail on the atomic closed flag.
     */
    return 0;
}

static PyObject*
PyTimelog_close(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    if (atomic_load_explicit(&self->closed, memory_order_acquire)) {
        Py_RETURN_NONE;
    }

    /* Engine already NULL (partial init failure). */
    if (atomic_load_explicit(&self->tl, memory_order_acquire) == NULL) {
        atomic_store_explicit(&self->closed, 1, memory_order_release);
        tl_py_timelog_drop_engine_ctx(self);
        tl_py_timelog_drop_handle_ctx(self);
        Py_RETURN_NONE;
    }

    /* Reject close with active pins to avoid inconsistent state. The helper
     * performs this check under core_lock so the handle context cannot be
     * detached between loading it and counting pins. */
    uint64_t pins = pytimelog_close_no_raise(self, 0);
    if (pins != 0) {
        return TL_PY_RAISE_STATUS_FMT(self, TL_ESTATE,
            "Cannot close: %llu active reader(s) still pinned "
            "(iterators, PageSpans, or exported memoryviews); exhaust, "
            "del, or .close() them, then call close() again",
            (unsigned long long)pins);
    }

    Py_RETURN_NONE;
}

/*===========================================================================
 * PyTimelog_dealloc (tp_dealloc)
 *===========================================================================*/

/** tp_finalize (PEP 442): best-effort cleanup. */
static void
PyTimelog_finalize(PyObject* self_obj)
{
    PyTimelog* self = (PyTimelog*)self_obj;
    TL_PY_PRESERVE_EXC_BEGIN;
    pytimelog_close_no_raise(self, 1);
    if (PyErr_Occurred()) {
        PyErr_WriteUnraisable(self_obj);
    }
    TL_PY_PRESERVE_EXC_END;
}

static void
PyTimelog_dealloc(PyTimelog* self)
{
    PyTypeObject* tp = Py_TYPE(self);

    PyObject_GC_UnTrack((PyObject*)self);

    /* Run tp_finalize before deallocation. */
    if (PyObject_CallFinalizerFromDealloc((PyObject*)self) < 0) {
        return;
    }

    /* Resurrected by finalizer. */
    if (Py_REFCNT(self) > 0) {
        return;
    }

    PyObject_ClearWeakRefs((PyObject*)self);

    if (self->core_lock) {
        PyThread_type_lock lk = self->core_lock;
        self->core_lock = NULL;
        PyThread_free_lock(lk);
    }

    tl_py_timelog_drop_engine_ctx(self);
    tl_py_timelog_drop_handle_ctx(self);

    tp->tp_free((PyObject*)self);
    Py_DECREF(tp);
}

static int
PyTimelog_traverse(PyTimelog* self, visitproc visit, void* arg)
{
    Py_VISIT(Py_TYPE(self));

    /* MUST be the non-blocking acquire: tp_traverse parking on core_lock
     * during a stop-the-world collection is a deadlock (the holder may be a
     * frozen thread). NULL (contended or already closed) => under-report
     * this cycle, which only over-retains. */
    tl_py_handle_ctx_t* hctx = tl_py_try_acquire_owned_handle_ctx(self);
    if (hctx == NULL) {
        return 0;
    }

    int rc = tl_py_handle_ctx_traverse(hctx, visit, arg);
    tl_py_handle_ctx_decref(hctx);
    return rc;
}

static int
PyTimelog_clear(PyTimelog* self)
{
    /*
     * tp_finalize performs lifecycle close. tp_clear only breaks Python
     * reference cycles after the object is already API-closed, avoiding
     * maintenance-thread joins from the GC clear phase.
     */
    if (self->closed || self->tl == NULL) {
        tl_py_timelog_drop_handle_ctx(self);
    }
    return 0;
}

/*===========================================================================
 * PyTimelog_append
 *
 * CRITICAL: TL_EBUSY means record WAS inserted.
 * - Do NOT rollback INCREF on EBUSY
 * - Do NOT retry on EBUSY
 *===========================================================================*/

static PyObject*
PyTimelog_append(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs,
                 PyObject* kwnames)
{
    /* Folded facade append: 3 signatures (idea 3).
     *   append(obj)          -> auto-timestamp from the wall clock
     *   append(obj, ts=X)    -> explicit keyword timestamp
     *   append(ts, obj)      -> legacy 2-positional
     * Matches the (now-deleted) Python override, including: ts=None means
     * auto-timestamp; a ts= kw is IGNORED when the object is provided via the
     * second positional/obj_or_none path; and the old exposed parameter names
     * obj_or_ts / obj_or_none remain accepted for compatibility. */
    Py_ssize_t n = PyVectorcall_NARGS(nargs);
    Py_ssize_t nkw = (kwnames == NULL) ? 0 : PyTuple_GET_SIZE(kwnames);

    PyObject* obj_or_ts = NULL;     /* borrowed */
    PyObject* obj_or_none = NULL;   /* borrowed, NULL means sentinel */
    PyObject* ts_kw = NULL;         /* borrowed value of ts=, if present */

    if (n > 2) {
        PyErr_Format(PyExc_TypeError,
            "append() takes 1 or 2 positional arguments but %zd were given", n);
        return NULL;
    }
    if (n >= 1) {
        obj_or_ts = args[0];
    }
    if (n == 2) {
        obj_or_none = args[1];
    }

    for (Py_ssize_t i = 0; i < nkw; i++) {
        PyObject* name = PyTuple_GET_ITEM(kwnames, i);
        if (PyUnicode_CompareWithASCIIString(name, "ts") == 0) {
            if (ts_kw != NULL) {
                PyErr_SetString(PyExc_TypeError,
                    "append() got multiple values for keyword argument 'ts'");
                return NULL;
            }
            ts_kw = args[n + i];
        } else if (PyUnicode_CompareWithASCIIString(name, "obj_or_ts") == 0) {
            if (obj_or_ts != NULL) {
                PyErr_SetString(PyExc_TypeError,
                    "append() got multiple values for argument 'obj_or_ts'");
                return NULL;
            }
            obj_or_ts = args[n + i];
        } else if (PyUnicode_CompareWithASCIIString(name, "obj_or_none") == 0) {
            if (obj_or_none != NULL) {
                PyErr_SetString(PyExc_TypeError,
                    "append() got multiple values for argument 'obj_or_none'");
                return NULL;
            }
            obj_or_none = args[n + i];
        } else {
            PyErr_Format(PyExc_TypeError,
                "append() got an unexpected keyword argument '%S'", name);
            return NULL;
        }
    }

    long long ts_ll;
    PyObject* obj;
    if (obj_or_ts == NULL) {
        PyErr_SetString(PyExc_TypeError,
            "append() missing required argument 'obj_or_ts'");
        return NULL;
    }

    if (obj_or_none == NULL) {
        obj = obj_or_ts;
        if (ts_kw != NULL && ts_kw != Py_None) {   /* append(obj, ts=X) */
            if (tl_py_coerce_ts(ts_kw, &ts_ll) < 0) {
                return NULL;
            }
        } else {                                  /* append(obj) or append(obj, ts=None) */
            if (tl_py_now_ts(self, &ts_ll) < 0) {
                return NULL;
            }
        }
    } else {                                       /* append(ts, obj); ts= kw ignored, like the facade */
        if (tl_py_coerce_ts(obj_or_ts, &ts_ll) < 0) {
            return NULL;
        }
        obj = obj_or_none;
    }

    /* min_ts floor guard (single source of truth; matches facade _check_min_ts).
     * Atomic acquire-load with flag-before-value ordering, paired with the
     * release stores in _set_min_ts_floor, so append never observes the flag set
     * against a torn bound. Lifecycle/reopen still require external
     * serialization against concurrent writers. */
    if (atomic_load_explicit(&self->has_min_ts_floor, memory_order_acquire)) {
        long long floor = atomic_load_explicit(&self->min_ts_floor,
                                                memory_order_acquire);
        if (ts_ll < floor) {
            PyErr_Format(PyExc_ValueError,
                "timestamp %lld is below min_ts boundary (%lld)",
                ts_ll, floor);
            return NULL;
        }
    }

    /* Validate timestamp range (defense-in-depth) */
    if (tl_py_validate_ts(ts_ll, "timestamp") < 0) {
        return NULL;
    }

    /* Preserve the old facade ordering: Python argument binding/coercion and
     * the min_ts guard ran before super().append() observed closed state. */
    CHECK_CLOSED(self);

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
    /* Own handle_ctx under core_lock so post-unlock bookkeeping is immune to a
     * concurrent close() dropping/freeing the context. */
    tl_py_handle_ctx_t* hctx = tl_py_own_handle_ctx_locked(self);
    st = tl_append(self->tl, ts, h);
    TL_PY_UNLOCK(self);

    if (st == TL_OK) {
        (void)tl_py_live_note_insert(hctx, obj);
        goto success;
    }

    if (st == TL_EBUSY) {
        /* Record IS in engine; do NOT rollback INCREF or retry. */
        (void)tl_py_live_note_insert(hctx, obj);

        if (tl_py_handle_write_ebusy(self,
                "Record inserted but backpressure occurred. "
                "Call flush() or wait for background maintenance to relieve.") < 0) {
            tl_py_handle_ctx_decref(hctx);
            return NULL;
        }
        goto success;
    }

    /* True failure - rollback INCREF */
    Py_DECREF(obj);
    tl_py_handle_ctx_decref(hctx);
    return TL_PY_RAISE_STATUS(self, st);

success:
    /* Opportunistic drain, then release our owned handle_ctx ref. */
    tl_py_drain_retired(hctx, 0);
    tl_py_handle_ctx_decref(hctx);
    Py_RETURN_NONE;
}

/*===========================================================================
 * PyTimelog_extend
 *
 * CRITICAL: concrete caller-owned sequences are snapshotted before borrowed
 * item access. PySequence_Fast(list) would return the original list, which is
 * not safe under Py_GIL_DISABLED if another thread mutates it concurrently.
 *
 * CRITICAL: obj is borrowed from item/pair. INCREF obj BEFORE DECREF item/pair.
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

    /* Fast path for concrete sequences. Snapshot the outer list/tuple so later
     * borrowed item access is from our owned immutable tuple, not a mutable
     * caller list that another free-threaded thread can rewrite underneath us. */
    if (PyList_CheckExact(iterable) || PyTuple_CheckExact(iterable)) {
        PyObject* seq = PySequence_Tuple(iterable);
        if (seq == NULL) {
            return NULL;
        }

        Py_ssize_t n = PyTuple_GET_SIZE(seq);
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
            PyObject* item = PyTuple_GET_ITEM(seq, i); /* borrowed from our tuple */
            long long ts_ll;
            PyObject* obj;
            int obj_is_strong = 0;

            if (PyArg_ParseTuple(item, "LO", &ts_ll, &obj)) {
                /* Parsed tuple directly */
            } else {
                PyErr_Clear();
                PyObject* pair = PySequence_Tuple(item);
                if (pair == NULL) {
                    goto error_seq;
                }
                if (PyTuple_GET_SIZE(pair) != 2) {
                    Py_DECREF(pair);
                    PyErr_SetString(PyExc_ValueError,
                        "extend() expects (ts, obj) pairs");
                    goto error_seq;
                }
                PyObject* ts_obj = PyTuple_GET_ITEM(pair, 0);
                obj = PyTuple_GET_ITEM(pair, 1);
                ts_ll = PyLong_AsLongLong(ts_obj);
                if (PyErr_Occurred()) {
                    Py_DECREF(pair);
                    goto error_seq;
                }
                /* obj may be owned only by this temporary tuple. */
                Py_INCREF(obj);
                obj_is_strong = 1;
                Py_DECREF(pair);
            }

            if (tl_py_validate_ts(ts_ll, "timestamp") < 0) {
                if (obj_is_strong) {
                    Py_DECREF(obj);
                }
                goto error_seq;
            }

            if (!obj_is_strong) {
                Py_INCREF(obj);
            }
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
            tl_py_handle_ctx_t* hctx = tl_py_own_handle_ctx_locked(self);
            st = tl_append_batch(self->tl, records, (size_t)n, flags);
            TL_PY_UNLOCK(self);

            if (st == TL_OK || st == TL_EBUSY) {
                for (Py_ssize_t i = 0; i < n; i++) {
                    (void)tl_py_live_note_insert(hctx, objs[i]);
                }

                if (st == TL_EBUSY) {
                    if (tl_py_handle_write_ebusy(self,
                            "Backpressure during batch insert. "
                            "All records were committed. "
                            "Call flush() or wait for background maintenance to relieve.") < 0) {
                        tl_py_handle_ctx_decref(hctx);
                        free(records);
                        free(objs);
                        Py_DECREF(seq);
                        return NULL;
                    }
                }

                free(records);
                free(objs);
                Py_DECREF(seq);
                tl_py_drain_retired(hctx, 0);
                tl_py_handle_ctx_decref(hctx);
                Py_RETURN_NONE;
            }

            /* True failure: rollback INCREFs */
            for (Py_ssize_t i = 0; i < n; i++) {
                Py_DECREF(objs[i]);
            }
            tl_py_handle_ctx_decref(hctx);
            free(records);
            free(objs);
            Py_DECREF(seq);
            return TL_PY_RAISE_STATUS(self, st);
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
            /* INCREF obj before DECREF item: obj is borrowed from tuple. */
            Py_INCREF(obj);
        } else {
            PyErr_Clear();
            PyObject* pair = PySequence_Tuple(item);
            if (pair == NULL) {
                Py_DECREF(item);
                goto error_stream;
            }
            if (PyTuple_GET_SIZE(pair) != 2) {
                Py_DECREF(pair);
                Py_DECREF(item);
                PyErr_SetString(PyExc_ValueError,
                    "extend() expects (ts, obj) pairs");
                goto error_stream;
            }
            PyObject* ts_obj = PyTuple_GET_ITEM(pair, 0);
            obj = PyTuple_GET_ITEM(pair, 1);
            ts_ll = PyLong_AsLongLong(ts_obj);
            /* INCREF obj before DECREF pair: obj is borrowed from pair. */
            Py_INCREF(obj);
            Py_DECREF(pair);
            if (PyErr_Occurred()) {
                Py_DECREF(obj);
                Py_DECREF(item);
                goto error_stream;
            }
        }
        /* obj is a strong reference from either path above. */
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
            tl_py_handle_ctx_t* hctx = tl_py_own_handle_ctx_locked(self);
            st = tl_append_batch(self->tl, records, n, flags);
            TL_PY_UNLOCK(self);

            if (st == TL_OK || st == TL_EBUSY) {
                for (size_t i = 0; i < n; i++) {
                    (void)tl_py_live_note_insert(hctx, objs[i]);
                }
                if (st == TL_EBUSY) {
                    if (tl_py_handle_write_ebusy(self,
                            "Backpressure during batch insert. "
                            "All records were committed. "
                            "Call flush() or wait for background maintenance to relieve.") < 0) {
                        tl_py_handle_ctx_decref(hctx);
                        free(records);
                        free(objs);
                        Py_DECREF(it);
                        return NULL;
                    }
                }
                tl_py_handle_ctx_decref(hctx);
                n = 0;
                continue;
            }

            /* True failure: rollback this chunk */
            tl_py_handle_ctx_decref(hctx);
            goto error_stream;
        }
    }

    /* Flush remaining chunk */
    if (n > 0) {
        tl_status_t st;
        if (tl_py_lock_checked(self) < 0) {
            goto error_stream;
        }
        tl_py_handle_ctx_t* hctx = tl_py_own_handle_ctx_locked(self);
        st = tl_append_batch(self->tl, records, n, flags);
        TL_PY_UNLOCK(self);

        if (st == TL_OK || st == TL_EBUSY) {
            for (size_t i = 0; i < n; i++) {
                (void)tl_py_live_note_insert(hctx, objs[i]);
            }
            if (st == TL_EBUSY) {
                if (tl_py_handle_write_ebusy(self,
                        "Backpressure during batch insert. "
                        "All records were committed. "
                        "Call flush() or wait for background maintenance to relieve.") < 0) {
                    tl_py_handle_ctx_decref(hctx);
                    free(records);
                    free(objs);
                    Py_DECREF(it);
                    return NULL;
                }
            }
            tl_py_handle_ctx_decref(hctx);
        } else {
            tl_py_handle_ctx_decref(hctx);
            goto error_stream;
        }
    }

    free(records);
    free(objs);
    Py_DECREF(it);
    tl_py_drain_owned(self);
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
 * PyTimelog_bulk_append
 *
 * Typed-buffer bulk append fast path:
 *   bulk_append(timestamps, objects, *, mostly_ordered=<instance default>)
 *
 * timestamps: contiguous 1-D buffer of NATIVE-endian int64 ('q'/'l',
 * itemsize 8). objects: concrete ordered sequence (list/tuple) of equal
 * length; str/bytes/iterators are rejected. Single all-or-nothing
 * tl_append_batch. TL_EBUSY => all records committed; never rolled back.
 *
 * Free-threaded safety: `objects` is snapshotted with PySequence_Tuple()
 * before any borrowed-item access, so concurrent mutation of a caller-owned
 * list cannot tear reads. For exact lists the copy is a single
 * critical-section snapshot (PyList_AsTuple under the list's per-object
 * lock on free-threaded builds); for other sequences PySequence_Tuple
 * falls back to itemwise iteration, which is memory-safe via owned
 * references but not an atomic point-in-time copy. All later item reads
 * go through our owned tuple.
 *===========================================================================*/

#if !defined(PY_BIG_ENDIAN) || !defined(PY_LITTLE_ENDIAN)
#  error "pyport.h byte-order macros are required (CPython >= 3.12)"
#endif

static int
tl_py_buffer_fmt_is_native_i64(const char* fmt)
{
    if (fmt == NULL) {
        return 0;
    }
    const char* p = fmt;
    if (*p == '@' || *p == '=') {
        p++;                          /* native order, explicitly */
    } else if (*p == '<' || *p == '>' || *p == '!') {
#if PY_BIG_ENDIAN
        if (*p == '<') {
            return -1;                /* little-endian buffer on BE host */
        }
#else
        if (*p == '>' || *p == '!') {
            return -1;                /* big-endian buffer on LE host */
        }
#endif
        p++;
    }
    if ((p[0] == 'q' || p[0] == 'l') && p[1] == '\0') {
        return 1;
    }
    return 0;
}

static PyObject*
PyTimelog_bulk_append(PyTimelog* self, PyObject *const *args,
                      Py_ssize_t nargs, PyObject* kwnames)
{
    CHECK_CLOSED(self);

    /* Hand-rolled FASTCALL+kwnames parsing, mirroring append() above. */
    Py_ssize_t n_pos = PyVectorcall_NARGS(nargs);
    Py_ssize_t nkw = (kwnames == NULL) ? 0 : PyTuple_GET_SIZE(kwnames);

    PyObject* ts_obj = NULL;             /* borrowed */
    PyObject* objects = NULL;            /* borrowed */
    PyObject* mostly_ordered_obj = NULL; /* borrowed; NULL = not given */

    if (n_pos > 2) {
        PyErr_Format(PyExc_TypeError,
            "bulk_append() takes 2 positional arguments but %zd were given",
            n_pos);
        return NULL;
    }
    if (n_pos >= 1) {
        ts_obj = args[0];
    }
    if (n_pos == 2) {
        objects = args[1];
    }

    for (Py_ssize_t i = 0; i < nkw; i++) {
        PyObject* name = PyTuple_GET_ITEM(kwnames, i);
        if (PyUnicode_CompareWithASCIIString(name, "timestamps") == 0) {
            if (ts_obj != NULL) {
                PyErr_SetString(PyExc_TypeError,
                    "bulk_append() got multiple values for argument "
                    "'timestamps'");
                return NULL;
            }
            ts_obj = args[n_pos + i];
        } else if (PyUnicode_CompareWithASCIIString(name, "objects") == 0) {
            if (objects != NULL) {
                PyErr_SetString(PyExc_TypeError,
                    "bulk_append() got multiple values for argument "
                    "'objects'");
                return NULL;
            }
            objects = args[n_pos + i];
        } else if (PyUnicode_CompareWithASCIIString(name,
                                                    "mostly_ordered") == 0) {
            if (mostly_ordered_obj != NULL) {
                PyErr_SetString(PyExc_TypeError,
                    "bulk_append() got multiple values for argument "
                    "'mostly_ordered'");
                return NULL;
            }
            mostly_ordered_obj = args[n_pos + i];
        } else {
            PyErr_Format(PyExc_TypeError,
                "bulk_append() got an unexpected keyword argument '%S'",
                name);
            return NULL;
        }
    }
    if (ts_obj == NULL || objects == NULL) {
        PyErr_SetString(PyExc_TypeError,
            "bulk_append() missing required arguments 'timestamps' and "
            "'objects'");
        return NULL;
    }

    /* Objects policy: a parallel array needs a stable order and per-item
     * payloads. Reject text/bytes (would insert characters) and anything
     * that is not a real sequence (sets, dicts, generators, iterators). */
    if (PyUnicode_Check(objects) || PyBytes_Check(objects) ||
        PyByteArray_Check(objects)) {
        PyErr_SetString(PyExc_TypeError,
            "bulk_append() objects must be a sequence of payload objects, "
            "not str/bytes");
        return NULL;
    }
    if (!PySequence_Check(objects)) {
        PyErr_SetString(PyExc_TypeError,
            "bulk_append() objects must be a concrete sequence "
            "(use extend() for streaming/iterator input)");
        return NULL;
    }

    /* Immutable snapshot (owned): FT-safe borrowed access from here on. */
    PyObject* seq = PySequence_Tuple(objects);
    if (seq == NULL) {
        return NULL;
    }

    Py_buffer ts_view;
    if (PyObject_GetBuffer(ts_obj, &ts_view,
                           PyBUF_FORMAT | PyBUF_C_CONTIGUOUS) < 0) {
        /* numpy datetime64 — the most likely real pandas-user input — has
         * a buffer interface that refuses dtype 'M' with a raw numpy
         * message. Replace it with the conversion recipe. */
        if (PyObject_CheckBuffer(ts_obj) &&
            PyErr_ExceptionMatches(PyExc_ValueError)) {
            PyObject* exc = PyErr_GetRaisedException();
            PyObject* str = exc ? PyObject_Str(exc) : NULL;
            const char* msg = str ? PyUnicode_AsUTF8(str) : NULL;
            if (msg != NULL && (strstr(msg, "dtype 'M'") != NULL ||
                                strstr(msg, "dtype 'm'") != NULL)) {
                Py_XDECREF(str);
                Py_XDECREF(exc);
                Py_DECREF(seq);
                PyErr_SetString(PyExc_ValueError,
                    "bulk_append() timestamps must be int64; for a numpy "
                    "datetime64/timedelta64 array use arr.view('int64') "
                    "(or astype('int64')) with a matching time_unit");
                return NULL;
            }
            Py_XDECREF(str);
            if (exc != NULL) {
                PyErr_SetRaisedException(exc);
            }
        }
        /* The most likely user mistake is passing a plain list/tuple of
         * ints; CPython's generic "a bytes-like object is required" gives
         * no remedy, so replace it with an actionable message — but ONLY
         * for objects with no buffer protocol at all. Real buffer producers
         * (e.g. a strided numpy view) raise accurate errors of their own. */
        if (!PyObject_CheckBuffer(ts_obj)) {
            PyErr_Format(PyExc_TypeError,
                "bulk_append() timestamps must be an int64 buffer "
                "(e.g. numpy int64 array or array.array('q')), not %.80s; "
                "build one with array.array('q', ts) or "
                "np.asarray(ts, dtype=np.int64), or use extend()",
                Py_TYPE(ts_obj)->tp_name);
        }
        Py_DECREF(seq);
        return NULL;
    }
    if (ts_view.ndim != 1) {
        PyBuffer_Release(&ts_view);
        Py_DECREF(seq);
        PyErr_SetString(PyExc_ValueError,
            "bulk_append() timestamps must be a 1-D buffer");
        return NULL;
    }
    /* Reading through an int64_t* requires natural alignment; a sliced
     * byte-buffer cast (e.g. memoryview(bytearray(...))[1:9].cast("q")) can
     * be 8-byte-itemsize yet misaligned, which is C undefined behavior on
     * load. Real producers (numpy, array.array) are always aligned. */
    if (ts_view.len > 0 &&
        ((uintptr_t)ts_view.buf % _Alignof(int64_t)) != 0) {
        PyBuffer_Release(&ts_view);
        Py_DECREF(seq);
        PyErr_SetString(PyExc_ValueError,
            "bulk_append() timestamps buffer must be 8-byte aligned");
        return NULL;
    }
    if (ts_view.itemsize != (Py_ssize_t)sizeof(int64_t)) {
        PyBuffer_Release(&ts_view);
        Py_DECREF(seq);
        PyErr_SetString(PyExc_ValueError,
            "bulk_append() timestamps must have 8-byte items (int64)");
        return NULL;
    }
    switch (tl_py_buffer_fmt_is_native_i64(ts_view.format)) {
    case 1:
        break;
    case -1:
        PyBuffer_Release(&ts_view);
        Py_DECREF(seq);
        PyErr_SetString(PyExc_ValueError,
            "bulk_append() timestamps must be native byte order "
            "(byteswap the array first)");
        return NULL;
    default:
        PyBuffer_Release(&ts_view);
        Py_DECREF(seq);
        PyErr_SetString(PyExc_ValueError,
            "bulk_append() timestamps must be int64 "
            "(buffer format 'q' or 'l')");
        return NULL;
    }

    Py_ssize_t bn = ts_view.shape[0];
    if (PyTuple_GET_SIZE(seq) != bn) {
        PyErr_Format(PyExc_ValueError,
            "bulk_append() length mismatch: %zd timestamps, %zd objects",
            bn, PyTuple_GET_SIZE(seq));
        PyBuffer_Release(&ts_view);
        Py_DECREF(seq);
        return NULL;
    }
    if (bn == 0) {
        PyBuffer_Release(&ts_view);
        Py_DECREF(seq);
        Py_RETURN_NONE;
    }
    if ((size_t)bn > SIZE_MAX / sizeof(tl_record_t)) {
        PyBuffer_Release(&ts_view);
        Py_DECREF(seq);
        return PyErr_Format(PyExc_OverflowError, "batch size too large");
    }

    /* Resolve mostly_ordered: explicit argument wins (None = use default);
     * omitted/None -> the facade's _mostly_ordered_default (extend parity);
     * attribute absent (raw _CTimelog) -> false. */
    int mostly_ordered = 0;
    if (mostly_ordered_obj != NULL && mostly_ordered_obj != Py_None) {
        mostly_ordered = PyObject_IsTrue(mostly_ordered_obj);
        if (mostly_ordered < 0) {
            PyBuffer_Release(&ts_view);
            Py_DECREF(seq);
            return NULL;
        }
    } else {
        PyObject* dflt = PyObject_GetAttrString((PyObject*)self,
                                                "_mostly_ordered_default");
        if (dflt == NULL) {
            /* Only a missing attribute (raw _CTimelog) is expected; anything
             * else (MemoryError, a raising facade property) must propagate,
             * not be silently swallowed. */
            if (!PyErr_ExceptionMatches(PyExc_AttributeError)) {
                PyBuffer_Release(&ts_view);
                Py_DECREF(seq);
                return NULL;
            }
            PyErr_Clear();
        } else {
            mostly_ordered = PyObject_IsTrue(dflt);
            Py_DECREF(dflt);
            if (mostly_ordered < 0) {
                PyBuffer_Release(&ts_view);
                Py_DECREF(seq);
                return NULL;
            }
        }
    }

    /* min_ts floor: snapshotted once per call with the same acquire pairing
     * as append(). close()/reopen()/configure() are documented as externally
     * serialized against all other users of the instance, so the floor
     * cannot legally change mid-call; a caller who violates that contract
     * gets unspecified floor application, never memory-unsafety. */
    int has_floor = atomic_load_explicit(&self->has_min_ts_floor,
                                         memory_order_acquire);
    long long floor_v = has_floor
        ? atomic_load_explicit(&self->min_ts_floor, memory_order_acquire)
        : 0;

    tl_record_t* records =
        (tl_record_t*)PyMem_Malloc((size_t)bn * sizeof(tl_record_t));
    if (records == NULL) {
        PyBuffer_Release(&ts_view);
        Py_DECREF(seq);
        return PyErr_NoMemory();
    }

    const int64_t* ts_arr = (const int64_t*)ts_view.buf;
    for (Py_ssize_t i = 0; i < bn; i++) {
        long long ts_ll = (long long)ts_arr[i];
        if (tl_py_validate_ts(ts_ll, "timestamp") < 0 ||
            (has_floor && ts_ll < floor_v)) {
            if (!PyErr_Occurred()) {
                PyErr_Format(PyExc_ValueError,
                    "bulk_append() timestamp %lld at index %zd is below "
                    "min_ts %lld", ts_ll, i, floor_v);
            }
            for (Py_ssize_t j = 0; j < i; j++) {
                Py_DECREF(PyTuple_GET_ITEM(seq, j));
            }
            PyMem_Free(records);
            PyBuffer_Release(&ts_view);
            Py_DECREF(seq);
            return NULL;
        }
        PyObject* obj = PyTuple_GET_ITEM(seq, i); /* borrowed from OUR tuple */
        Py_INCREF(obj);                           /* ownership -> the log */
        records[i].ts = (tl_ts_t)ts_ll;
        records[i].handle = tl_py_handle_encode(obj);
    }
    PyBuffer_Release(&ts_view);

    {
        uint32_t flags = mostly_ordered ? TL_APPEND_HINT_MOSTLY_IN_ORDER : 0;
        tl_status_t st;
        if (tl_py_lock_checked(self) < 0) {
            for (Py_ssize_t i = 0; i < bn; i++) {
                Py_DECREF(PyTuple_GET_ITEM(seq, i));
            }
            PyMem_Free(records);
            Py_DECREF(seq);
            return NULL;
        }
        tl_py_handle_ctx_t* hctx = tl_py_own_handle_ctx_locked(self);
        st = tl_append_batch(self->tl, records, (size_t)bn, flags);
        TL_PY_UNLOCK(self);

        if (st == TL_OK || st == TL_EBUSY) {
            for (Py_ssize_t i = 0; i < bn; i++) {
                (void)tl_py_live_note_insert(hctx, PyTuple_GET_ITEM(seq, i));
            }
            PyMem_Free(records);
            if (st == TL_EBUSY) {
                if (tl_py_handle_write_ebusy(self,
                        "Backpressure during bulk insert. "
                        "All records were committed. "
                        "Call flush() or wait for background maintenance "
                        "to relieve.") < 0) {
                    tl_py_drain_retired(hctx, 0);
                    tl_py_handle_ctx_decref(hctx);
                    Py_DECREF(seq);
                    return NULL;
                }
            }
            tl_py_drain_retired(hctx, 0);
            tl_py_handle_ctx_decref(hctx);
            Py_DECREF(seq);
            Py_RETURN_NONE;
        }

        /* True failure (ENOMEM/EOVERFLOW/...): engine inserted nothing. */
        for (Py_ssize_t i = 0; i < bn; i++) {
            Py_DECREF(PyTuple_GET_ITEM(seq, i));
        }
        tl_py_handle_ctx_decref(hctx);
        PyMem_Free(records);
        Py_DECREF(seq);
        return TL_PY_RAISE_STATUS(self, st);
    }
}

/*===========================================================================
 * PyTimelog_delete_range
 *
 * CRITICAL: Same TL_EBUSY semantics as append.
 *===========================================================================*/

/*
 * Finish a tombstone write (delete_range / delete_before) after the core call
 * returned and core_lock was released. Consumes the owned hctx reference
 * (always decrefs it). Mirrors the append EBUSY contract: on TL_EBUSY the
 * tombstone IS already in the log, so the busy policy is applied and the write
 * is never rolled back. On success (TL_OK or backpressure-handled EBUSY) the
 * retired refs are drained and None is returned; otherwise NULL is returned
 * with a Python exception set.
 */
static PyObject*
tl_py_finish_tombstone_write(PyTimelog* self, tl_py_handle_ctx_t* hctx,
                             tl_status_t st)
{
    if (st != TL_OK) {
        if (st != TL_EBUSY) {
            tl_py_handle_ctx_decref(hctx);
            return TL_PY_RAISE_STATUS(self, st);
        }
        if (tl_py_handle_write_ebusy(self,
                "Tombstone inserted but backpressure occurred. "
                "Call flush() or wait for background maintenance to relieve.") < 0) {
            tl_py_handle_ctx_decref(hctx);
            return NULL;
        }
    }

    tl_py_drain_retired(hctx, 0);
    tl_py_handle_ctx_decref(hctx);
    Py_RETURN_NONE;
}

static PyObject*
PyTimelog_delete_range(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs)
{
    CHECK_CLOSED(self);

    Py_ssize_t n = PyVectorcall_NARGS(nargs);
    if (n != 2) {
        PyErr_Format(PyExc_TypeError,
            "delete_range() takes exactly 2 arguments (%zd given)", n);
        return NULL;
    }
    long long t1_ll, t2_ll;
    if (tl_py_fast_i64(args[0], &t1_ll) < 0 ||
        tl_py_fast_i64(args[1], &t2_ll) < 0) {
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
    tl_py_handle_ctx_t* hctx = tl_py_own_handle_ctx_locked(self);
    st = tl_delete_range(self->tl, (tl_ts_t)t1_ll, (tl_ts_t)t2_ll);
    TL_PY_UNLOCK(self);

    return tl_py_finish_tombstone_write(self, hctx, st);
}

/*===========================================================================
 * PyTimelog_delete_before
 *===========================================================================*/

static PyObject*
PyTimelog_delete_before(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs)
{
    CHECK_CLOSED(self);

    Py_ssize_t n = PyVectorcall_NARGS(nargs);
    if (n != 1) {
        PyErr_Format(PyExc_TypeError,
            "delete_before() takes exactly 1 argument (%zd given)", n);
        return NULL;
    }
    long long cutoff_ll;
    if (tl_py_fast_i64(args[0], &cutoff_ll) < 0) {
        return NULL;
    }

    if (tl_py_validate_ts(cutoff_ll, "cutoff") < 0) {
        return NULL;
    }

    tl_status_t st;
    if (tl_py_lock_checked(self) < 0) {
        return NULL;
    }
    tl_py_handle_ctx_t* hctx = tl_py_own_handle_ctx_locked(self);
    st = tl_delete_before(self->tl, (tl_ts_t)cutoff_ll);
    TL_PY_UNLOCK(self);

    return tl_py_finish_tombstone_write(self, hctx, st);
}

/*===========================================================================
 * PyTimelog_flush
 *===========================================================================*/

static PyObject*
PyTimelog_flush(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_status_t st;
    if (tl_py_core_call_strict(self, tl_flush, &st) < 0) {
        return NULL;
    }

    if (st == TL_EBUSY) {
        return TL_PY_RAISE_STATUS_FMT(self, TL_EBUSY,
            "Flush publish retry exhausted (safe to retry)");
    }
    if (st != TL_OK && st != TL_EOF) {
        return TL_PY_RAISE_STATUS(self, st);
    }

    /* Drain under GIL, holding an owned handle_ctx ref so a concurrent
     * close() cannot free the context mid-drain. */
    tl_py_drain_owned(self);

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
    if (tl_py_core_call_strict(self, tl_compact, &st) < 0) {
        return NULL;
    }

    if (st != TL_OK && st != TL_EOF) {
        return TL_PY_RAISE_STATUS(self, st);
    }

    /* Opportunistic drain after compact (owned ref guards against a
     * concurrent close() freeing the context). */
    tl_py_drain_owned(self);

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
    tl_py_handle_ctx_t* hctx = NULL;
    tl_py_engine_ctx_t* ectx = NULL;
    tl_stats_t stats;

    if (tl_py_acquire_snapshot_pinned(self, &snap, &hctx, &ectx) < 0) {
        return NULL;
    }

    tl_status_t st = tl_stats(snap, &stats);
    tl_py_release_snapshot_pinned(snap, hctx, ectx);

    if (st != TL_OK) {
        return TL_PY_RAISE_STATUS(self, st);
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
    if (tl_py_core_call_strict(self, tl_maint_step, &st) < 0) {
        return NULL;
    }

    if (st == TL_OK) {
        tl_py_drain_owned(self);
        Py_RETURN_TRUE;
    }
    if (st == TL_EOF) {
        Py_RETURN_FALSE;
    }
    return TL_PY_RAISE_STATUS(self, st);
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

    tl_py_handle_ctx_t* hctx = NULL;
    tl_py_engine_ctx_t* ectx = NULL;
    if (tl_py_acquire_snapshot_pinned(self, &snap, &hctx, &ectx) < 0) {
        return NULL;
    }

    tl_status_t st = tl_min_ts(snap, &out);
    tl_py_release_snapshot_pinned(snap, hctx, ectx);

    if (st == TL_EOF) {
        Py_RETURN_NONE;
    }
    if (st != TL_OK) {
        return TL_PY_RAISE_STATUS(self, st);
    }
    return PyLong_FromLongLong((long long)out);
}

static PyObject*
PyTimelog_max_ts(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_snapshot_t* snap = NULL;
    tl_ts_t out;

    tl_py_handle_ctx_t* hctx = NULL;
    tl_py_engine_ctx_t* ectx = NULL;
    if (tl_py_acquire_snapshot_pinned(self, &snap, &hctx, &ectx) < 0) {
        return NULL;
    }

    tl_status_t st = tl_max_ts(snap, &out);
    tl_py_release_snapshot_pinned(snap, hctx, ectx);

    if (st == TL_EOF) {
        Py_RETURN_NONE;
    }
    if (st != TL_OK) {
        return TL_PY_RAISE_STATUS(self, st);
    }
    return PyLong_FromLongLong((long long)out);
}

/*===========================================================================
 * min_ts floor guard (single source of truth; facade `_min_ts` property)
 *
 * NOTE: distinct from min_ts() above, which returns the engine's smallest
 * stored timestamp. The "floor" is the facade's lower-bound REJECTION guard.
 *===========================================================================*/

static PyObject*
PyTimelog__set_min_ts_floor(PyTimelog* self, PyObject* value)
{
    /* Accepts None (clear the guard) or an int (already coerced by the facade
     * via _coerce_ts). Plain field state -> no CHECK_CLOSED (valid during
     * reopen() on a closed instance). */
    if (value == Py_None) {
        atomic_store_explicit(&self->has_min_ts_floor, 0, memory_order_release);
        atomic_store_explicit(&self->min_ts_floor, 0, memory_order_release);
        Py_RETURN_NONE;
    }
    long long v = PyLong_AsLongLong(value);
    if (v == -1 && PyErr_Occurred()) {
        return NULL;
    }
    /* Store the bound before the flag (release) so an append that acquires
     * has_min_ts_floor==1 is guaranteed to observe the matching min_ts_floor. */
    atomic_store_explicit(&self->min_ts_floor, v, memory_order_release);
    atomic_store_explicit(&self->has_min_ts_floor, 1, memory_order_release);
    Py_RETURN_NONE;
}

static PyObject*
PyTimelog__min_ts_floor(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    if (!atomic_load_explicit(&self->has_min_ts_floor, memory_order_acquire)) {
        Py_RETURN_NONE;
    }
    return PyLong_FromLongLong(
        atomic_load_explicit(&self->min_ts_floor, memory_order_acquire));
}

static PyObject*
PyTimelog_next_ts(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs)
{
    CHECK_CLOSED(self);

    Py_ssize_t n = PyVectorcall_NARGS(nargs);
    if (n != 1) {
        PyErr_Format(PyExc_TypeError,
            "next_ts() takes exactly 1 argument (%zd given)", n);
        return NULL;
    }
    long long ts_ll;
    if (tl_py_fast_i64(args[0], &ts_ll) < 0) {
        return NULL;
    }

    if (tl_py_validate_ts(ts_ll, "ts") < 0) {
        return NULL;
    }

    tl_snapshot_t* snap = NULL;
    tl_ts_t out;

    tl_py_handle_ctx_t* hctx = NULL;
    tl_py_engine_ctx_t* ectx = NULL;
    if (tl_py_acquire_snapshot_pinned(self, &snap, &hctx, &ectx) < 0) {
        return NULL;
    }

    tl_status_t st = tl_next_ts(snap, (tl_ts_t)ts_ll, &out);
    tl_py_release_snapshot_pinned(snap, hctx, ectx);

    if (st == TL_EOF) {
        Py_RETURN_NONE;
    }
    if (st != TL_OK) {
        return TL_PY_RAISE_STATUS(self, st);
    }
    return PyLong_FromLongLong((long long)out);
}

static PyObject*
PyTimelog_prev_ts(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs)
{
    CHECK_CLOSED(self);

    Py_ssize_t n = PyVectorcall_NARGS(nargs);
    if (n != 1) {
        PyErr_Format(PyExc_TypeError,
            "prev_ts() takes exactly 1 argument (%zd given)", n);
        return NULL;
    }
    long long ts_ll;
    if (tl_py_fast_i64(args[0], &ts_ll) < 0) {
        return NULL;
    }

    if (tl_py_validate_ts(ts_ll, "ts") < 0) {
        return NULL;
    }

    tl_snapshot_t* snap = NULL;
    tl_ts_t out;

    tl_py_handle_ctx_t* hctx = NULL;
    tl_py_engine_ctx_t* ectx = NULL;
    if (tl_py_acquire_snapshot_pinned(self, &snap, &hctx, &ectx) < 0) {
        return NULL;
    }

    tl_status_t st = tl_prev_ts(snap, (tl_ts_t)ts_ll, &out);
    tl_py_release_snapshot_pinned(snap, hctx, ectx);

    if (st == TL_EOF) {
        Py_RETURN_NONE;
    }
    if (st != TL_OK) {
        return TL_PY_RAISE_STATUS(self, st);
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
    tl_py_handle_ctx_t* hctx = NULL;
    tl_py_engine_ctx_t* ectx = NULL;
    if (tl_py_acquire_snapshot_pinned(self, &snap, &hctx, &ectx) < 0) {
        return NULL;
    }

    tl_status_t st = tl_validate(snap);
    tl_py_release_snapshot_pinned(snap, hctx, ectx);

    if (st != TL_OK) {
        return TL_PY_RAISE_STATUS(self, st);
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
        return TL_PY_RAISE_STATUS_FMT(self, TL_ESTATE,
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
    return TL_PY_RAISE_STATUS(self, st);
}

/*===========================================================================
 * PyTimelog_stop_maint
 *===========================================================================*/

static PyObject*
PyTimelog_stop_maint(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_status_t st;
    if (tl_py_core_call_strict(self, tl_maint_stop, &st) < 0) {
        return NULL;
    }

    if (st != TL_OK) {
        return TL_PY_RAISE_STATUS(self, st);
    }

    /* Drain after stop - no more on_drop callbacks possible. Owned ref guards
     * against a concurrent close() freeing the context mid-drain. */
    tl_py_drain_owned(self);

    Py_RETURN_NONE;
}

/*===========================================================================
 * Context Manager
 *===========================================================================*/

static PyObject*
PyTimelog_enter(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    if (self->closed) {
        return TL_PY_RAISE_STATUS_FMT(self, TL_ESTATE, "Timelog is closed");
    }

    /* Idempotent: re-starts maintenance if previously stopped. */
    if (self->maint_mode == TL_MAINT_BACKGROUND) {
        tl_status_t st;
        if (tl_py_lock_checked(self) < 0) {
            return NULL;
        }
        st = tl_maint_start(self->tl);
        TL_PY_UNLOCK(self);
        if (st != TL_OK) {
            return TL_PY_RAISE_STATUS(self, st);
        }
    }

    Py_INCREF(self);
    return (PyObject*)self;
}

/* Propagate close() errors only if `with` block succeeded. */
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
        if (exc_type == Py_None) {
            return NULL;  /* Propagate close() error. */
        }
        /* Suppress close() error to preserve original exception. */
        PyErr_Clear();
        Py_RETURN_FALSE;
    }

    Py_DECREF(result);
    Py_RETURN_FALSE;
}

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

/*===========================================================================
 * Iterator Factory
 *
 * Creates PyTimelogIter instances for range queries.
 * Follows the protocol: pins_enter -> snapshot_acquire -> iter_create -> track
 *===========================================================================*/

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

    tl_py_module_state_t* mod_st = TlPy_StateFromObject((PyObject*)self);
    if (mod_st == NULL) {
        return NULL;
    }

    /* Acquire snapshot + pin + owned handle_ctx/engine_ctx refs atomically
     * under core_lock so a concurrent close() cannot free the contexts
     * between pin entry and snapshot acquisition. On success these owned
     * refs and the pin are TRANSFERRED to the iterator below — no
     * additional incref — so the iterator's cleanup releases them exactly
     * once. */
    tl_snapshot_t* snap = NULL;
    tl_py_handle_ctx_t* hctx = NULL;
    tl_py_engine_ctx_t* ectx = NULL;
    if (tl_py_acquire_snapshot_pinned(self, &snap, &hctx, &ectx) < 0) {
        return NULL;
    }
    tl_status_t st;

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
            tl_py_release_snapshot_pinned(snap, hctx, ectx);
            PyErr_SetString(PyExc_SystemError, "Invalid iterator mode");
            return NULL;
    }

    if (st != TL_OK) {
        tl_py_release_snapshot_pinned(snap, hctx, ectx);
        return TL_PY_RAISE_STATUS(self, st);
    }

    PyTypeObject* iter_type = (PyTypeObject*)mod_st->type_timelog_iter;
    PyTimelogIter* pyit = (PyTimelogIter*)iter_type->tp_alloc(iter_type, 0);
    if (!pyit) {
        tl_iter_destroy(it);
        tl_py_release_snapshot_pinned(snap, hctx, ectx);
        return PyErr_NoMemory();
    }

    /* Transfer the helper's owned pin + handle_ctx/engine_ctx refs and the
     * snapshot to the iterator. No extra incref: the iterator's cleanup
     * (pins_exit + decref both ctxs + snapshot release) balances exactly. */
    pyit->owner = Py_NewRef((PyObject*)self);
    pyit->pinned_snapshot = snap;
    pyit->iter = it;
    pyit->handle_ctx = hctx;
    pyit->engine_ctx = ectx;
    pyit->remaining_count = 0;
    pyit->remaining_valid = 0;
    pyit->closed = 0;

    /* Normalized range for view() and __len__. */
    switch (mode) {
        case ITER_MODE_RANGE:  pyit->range_t1 = t1; pyit->range_t2 = t2; break;
        case ITER_MODE_SINCE:  pyit->range_t1 = t1; pyit->range_t2 = TL_TS_MAX; break;
        case ITER_MODE_UNTIL:  pyit->range_t1 = TL_TS_MIN; pyit->range_t2 = t2; break;
        case ITER_MODE_EQUAL:
        case ITER_MODE_POINT:  pyit->range_t1 = t1; pyit->range_t2 = (t1 < TL_TS_MAX) ? t1 + 1 : TL_TS_MAX; break;
        default:               pyit->range_t1 = TL_TS_MIN; pyit->range_t2 = TL_TS_MAX; break;
    }

    /* Precompute remaining count with the thread state detached for the long
     * core computation. */
    {
        tl_ts_t count_t1, count_t2;
        int count_unbounded;
        switch (mode) {
            case ITER_MODE_RANGE:
                count_t1 = t1; count_t2 = t2; count_unbounded = 0;
                break;
            case ITER_MODE_SINCE:
                count_t1 = t1; count_t2 = 0; count_unbounded = 1;
                break;
            case ITER_MODE_UNTIL:
                count_t1 = TL_TS_MIN; count_t2 = t2; count_unbounded = 0;
                break;
            case ITER_MODE_EQUAL:
            case ITER_MODE_POINT:
                count_t1 = t1;
                count_t2 = (t1 < TL_TS_MAX) ? t1 + 1 : 0;
                count_unbounded = (t1 == TL_TS_MAX) ? 1 : 0;
                break;
            default:
                count_t1 = TL_TS_MIN; count_t2 = 0; count_unbounded = 1;
                break;
        }

        /* Deliberately NO thread-state detach here. The count is a cheap
         * fence-pointer walk (O(K log P)), but detaching on EVERY iterator
         * creation signals the GIL condvar and resets other threads'
         * switch-interval timers: a hot reader loop creating slices
         * back-to-back then wins every GIL handoff race indefinitely,
         * starving the writer (measured 461x ingest collapse; v1.3
         * usability lab, hft persona). Keeping the state attached restores
         * normal ~5ms GIL fairness; on free-threaded builds there is no
         * GIL to release anyway. */
        st = tl_snapshot_count_range(snap, count_t1, count_t2,
                                      count_unbounded,
                                      &pyit->remaining_count);
    }
    if (st != TL_OK) {
        /* Clear the iterator's pointers before Py_DECREF so its cleanup
         * does not double-release the resources we release manually here
         * via tl_py_release_snapshot_pinned. */
        pyit->iter = NULL;
        pyit->pinned_snapshot = NULL;
        pyit->handle_ctx = NULL;
        pyit->engine_ctx = NULL;
        pyit->closed = 1;
        tl_iter_destroy(it);
        Py_DECREF(pyit->owner);
        pyit->owner = NULL;
        tl_py_release_snapshot_pinned(snap, hctx, ectx);
        Py_DECREF(pyit);
        return TL_PY_RAISE_STATUS(self, st);
    }
    pyit->remaining_valid = 1;

    return (PyObject*)pyit;
}

/**
 * Timelog.range(t1, t2) -> TimelogIter
 *
 * Create an iterator for records in [t1, t2).
 * If t1 > t2, raises ValueError; t1 == t2 yields empty iterator.
 */
static PyObject* PyTimelog_range(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs)
{
    Py_ssize_t n = PyVectorcall_NARGS(nargs);
    if (n != 2) {
        PyErr_Format(PyExc_TypeError,
            "range() takes exactly 2 arguments (%zd given)", n);
        return NULL;
    }
    long long t1, t2;
    if (tl_py_fast_i64(args[0], &t1) < 0 ||
        tl_py_fast_i64(args[1], &t2) < 0) {
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
static PyObject* PyTimelog_since(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs)
{
    Py_ssize_t n = PyVectorcall_NARGS(nargs);
    if (n != 1) {
        PyErr_Format(PyExc_TypeError,
            "since() takes exactly 1 argument (%zd given)", n);
        return NULL;
    }
    long long t;
    if (tl_py_fast_i64(args[0], &t) < 0) {
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
static PyObject* PyTimelog_until(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs)
{
    Py_ssize_t n = PyVectorcall_NARGS(nargs);
    if (n != 1) {
        PyErr_Format(PyExc_TypeError,
            "until() takes exactly 1 argument (%zd given)", n);
        return NULL;
    }
    long long t;
    if (tl_py_fast_i64(args[0], &t) < 0) {
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
static PyObject* PyTimelog_equal(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs)
{
    Py_ssize_t n = PyVectorcall_NARGS(nargs);
    if (n != 1) {
        PyErr_Format(PyExc_TypeError,
            "equal() takes exactly 1 argument (%zd given)", n);
        return NULL;
    }
    long long t;
    if (tl_py_fast_i64(args[0], &t) < 0) {
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
static PyObject* PyTimelog_point(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs)
{
    Py_ssize_t n = PyVectorcall_NARGS(nargs);
    if (n != 1) {
        PyErr_Format(PyExc_TypeError,
            "point() takes exactly 1 argument (%zd given)", n);
        return NULL;
    }
    long long t;
    if (tl_py_fast_i64(args[0], &t) < 0) {
        return NULL;
    }

    if (tl_py_validate_ts(t, "t") < 0) {
        return NULL;
    }

    return pytimelog_make_iter(self, ITER_MODE_POINT, (tl_ts_t)t, 0);
}

/*===========================================================================
 * PageSpan Factory Methods
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
    /* Unlocked read; must be atomic so concurrent Python threads (e.g.,
     * one reading .closed while another runs .close()) cannot race. */
    uint8_t c = atomic_load_explicit(&self->closed, memory_order_acquire);
    return PyBool_FromLong((long)c);
}

static PyObject* PyTimelog_get_time_unit(PyTimelog* self, void* Py_UNUSED(closure))
{
    const char* unit_str;
    switch (atomic_load_explicit(&self->time_unit, memory_order_acquire)) {
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
    tl_py_handle_ctx_t* hctx = tl_py_acquire_owned_handle_ctx(self);
    uint64_t len = hctx != NULL ? tl_py_retired_queue_len(hctx) : 0;
    if (hctx != NULL) {
        tl_py_handle_ctx_decref(hctx);
    }
    return PyLong_FromUnsignedLongLong(len);
}

static PyObject* PyTimelog_get_alloc_failures(PyTimelog* self, void* Py_UNUSED(closure))
{
    tl_py_handle_ctx_t* hctx = tl_py_acquire_owned_handle_ctx(self);
    uint64_t failures = hctx != NULL ? tl_py_alloc_failures(hctx) : 0;
    if (hctx != NULL) {
        tl_py_handle_ctx_decref(hctx);
    }
    return PyLong_FromUnsignedLongLong(failures);
}

static PyObject* PyTimelog_get_busy_events(PyTimelog* self, void* Py_UNUSED(closure))
{
    uint64_t n = atomic_load_explicit(&self->busy_events, memory_order_relaxed);
    return PyLong_FromUnsignedLongLong(n);
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

    {"busy_events", (getter)PyTimelog_get_busy_events, NULL,
     "Cumulative write-path backpressure (TL_EBUSY) events, counted under "
     "every busy_policy.", NULL},

    {NULL, NULL, NULL, NULL, NULL}
};

/*===========================================================================
 * Method Table
 *===========================================================================*/

static PyMethodDef PyTimelog_methods[] = {
    {"append", (PyCFunction)(void(*)(void))PyTimelog_append,
     METH_FASTCALL | METH_KEYWORDS,
     "append($self, obj_or_ts, obj_or_none=None, *, ts=None)\n"
     "--\n\n"
     "append(obj) | append(obj, ts=X) | append(ts, obj) -> None\n\n"
     "Append a record. With one positional arg and no ts, the timestamp is\n"
     "taken from the wall clock (scaled by time_unit). 'ts' may be given as a\n"
     "keyword; the 2-positional form is (ts, obj).\n\n"
     "Note: TimelogBusyError means the record WAS committed; do not retry."},

    {"extend", (PyCFunction)PyTimelog_extend, METH_VARARGS | METH_KEYWORDS,
     "extend(iterable, *, mostly_ordered=False) -> None\n\n"
     "Append multiple (ts, obj) records from an iterable.\n"
     "For sequences, uses a single batch append (all-or-nothing).\n"
     "For generators, uses chunked batches; records from completed chunks\n"
     "are committed even if a later chunk fails.\n"
     "If mostly_ordered=True, provides a hint to optimize OOO handling.\n\n"
     "Note: TimelogBusyError means the records WERE committed; do not retry."},

    {"bulk_append", (PyCFunction)(void(*)(void))PyTimelog_bulk_append,
     METH_FASTCALL | METH_KEYWORDS,
     "bulk_append(timestamps, objects, *, mostly_ordered=None) -> None\n\n"
     "Fast-path bulk append from a contiguous 1-D native-endian int64\n"
     "timestamp buffer (numpy int64 array, array.array('q'), memoryview)\n"
     "and a parallel concrete sequence of payload objects.\n\n"
     "Single all-or-nothing batch append. mostly_ordered=None uses the\n"
     "instance's mostly_ordered_default. Respects min_ts.\n\n"
     "Note: TimelogBusyError means the records WERE committed; do not retry."},

    {"delete_range", (PyCFunction)(void(*)(void))PyTimelog_delete_range, METH_FASTCALL,
     "delete_range(t1, t2) -> None\n\n"
     "Mark records in [t1, t2) for deletion (tombstone).\n\n"
     "Note: TimelogBusyError means the tombstone WAS committed; do not retry."},

    {"delete_before", (PyCFunction)(void(*)(void))PyTimelog_delete_before, METH_FASTCALL,
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

    /* Iterator factory methods */
    {"range", (PyCFunction)(void(*)(void))PyTimelog_range, METH_FASTCALL,
     "range(t1, t2) -> TimelogIter\n\n"
     "Return an iterator over records in [t1, t2).\n"
     "If t1 > t2, raises ValueError; t1 == t2 yields an empty iterator."},

    {"since", (PyCFunction)(void(*)(void))PyTimelog_since, METH_FASTCALL,
     "since(t) -> TimelogIter\n\n"
     "Return an iterator over records with ts >= t."},

    {"until", (PyCFunction)(void(*)(void))PyTimelog_until, METH_FASTCALL,
     "until(t) -> TimelogIter\n\n"
     "Return an iterator over records with ts < t."},

    {"all", (PyCFunction)PyTimelog_all, METH_NOARGS,
     "all() -> TimelogIter\n\n"
     "Return an iterator over all records."},

    {"equal", (PyCFunction)(void(*)(void))PyTimelog_equal, METH_FASTCALL,
     "equal(t) -> TimelogIter\n\n"
     "Return an iterator over records with ts == t."},

    {"point", (PyCFunction)(void(*)(void))PyTimelog_point, METH_FASTCALL,
     "point(t) -> TimelogIter\n\n"
     "Return an iterator for the exact timestamp t.\n"
     "Alias for equal() for point query semantics."},

    {"min_ts", (PyCFunction)PyTimelog_min_ts, METH_NOARGS,
     "min_ts() -> int | None\n\n"
     "Return minimum timestamp in snapshot, or None if empty."},

    {"_set_min_ts_floor", (PyCFunction)PyTimelog__set_min_ts_floor, METH_O,
     "_set_min_ts_floor(value) -> None\n\n"
     "Internal: set (int) or clear (None) the min_ts rejection floor."},

    {"_min_ts_floor", (PyCFunction)PyTimelog__min_ts_floor, METH_NOARGS,
     "_min_ts_floor() -> int | None\n\n"
     "Internal: the min_ts rejection floor (None if unset)."},

    {"max_ts", (PyCFunction)PyTimelog_max_ts, METH_NOARGS,
     "max_ts() -> int | None\n\n"
     "Return maximum timestamp in snapshot, or None if empty.\n"
     "WARNING: O(N) complexity."},

    {"next_ts", (PyCFunction)(void(*)(void))PyTimelog_next_ts, METH_FASTCALL,
     "next_ts(ts) -> int | None\n\n"
     "Return next timestamp strictly greater than ts, or None."},

    {"prev_ts", (PyCFunction)(void(*)(void))PyTimelog_prev_ts, METH_FASTCALL,
     "prev_ts(ts) -> int | None\n\n"
     "Return previous timestamp strictly less than ts, or None.\n"
     "WARNING: O(N) complexity."},

    {"validate", (PyCFunction)PyTimelog_validate, METH_NOARGS,
     "validate() -> None\n\n"
     "Run snapshot validation; raises TimelogError on invariant failure."},

    /* PageSpan factory methods */
    {"page_spans", (PyCFunction)PyTimelog_page_spans, METH_VARARGS | METH_KEYWORDS,
     "page_spans(t1, t2, *, kind='segment') -> PageSpanIter\n\n"
     "Return an iterator yielding PageSpan objects for [t1, t2).\n"
     "Each PageSpan exposes a contiguous slice of page timestamps\n"
     "as a read-only memoryview (zero-copy). Use for bulk timestamp\n"
     "access without per-record Python object allocation.\n\n"
     "Only FLUSHED segments are visible: on a freshly-written log call\n"
     "flush() first, or this yields nothing while len(log) is non-zero.\n\n"
     "Parameters:\n"
     "  t1: Range start (inclusive)\n"
     "  t2: Range end (exclusive)\n"
     "  kind: 'segment' (currently supported value)\n\n"
     "Returns:\n"
     "  PageSpanIter yielding PageSpan objects"},

    {"views", (PyCFunction)PyTimelog_page_spans, METH_VARARGS | METH_KEYWORDS,
     "views(t1, t2, *, kind='segment') -> PageSpanIter\n\n"
     "Alias for page_spans()."},

    {"__enter__", (PyCFunction)PyTimelog_enter, METH_NOARGS,
     "Context manager entry."},

    {"__exit__", (PyCFunction)PyTimelog_exit, METH_VARARGS,
     "Context manager exit (closes the timelog)."},

    {NULL, NULL, 0, NULL}
};

/*===========================================================================
 * Type Specification
 *===========================================================================*/

static PyType_Slot PyTimelog_slots[] = {
    {Py_tp_doc, PyDoc_STR(
        "Timelog engine wrapper.\n\n"
        "A time-indexed multimap for (timestamp, object) records.\n\n"
        "Thread Safety:\n"
        "    Single-writer model. External synchronization is required for\n"
        "    concurrent writes or lifecycle operations. Snapshot-based iterators\n"
        "    are safe for concurrent reads.\n"
    )},
    {Py_tp_new, PyType_GenericNew},
    {Py_tp_init, (void*)PyTimelog_init},
    {Py_tp_dealloc, (void*)PyTimelog_dealloc},
    {Py_tp_finalize, (void*)PyTimelog_finalize},
    {Py_tp_traverse, (void*)PyTimelog_traverse},
    {Py_tp_clear, (void*)PyTimelog_clear},
    {Py_tp_methods, PyTimelog_methods},
    {Py_tp_getset, PyTimelog_getset},
    /* Deliberately NO Py_tp_call / vectorcall slot: Timelog instances are not
     * callable, and wiring tp_vectorcall on a heap type carries lifetime and
     * tp_vectorcall_offset hazards. The METH_FASTCALL methods are per-method
     * vectorcall (the correct, supported form). Regression-guarded by
     * test_hardening.py (Py_TPFLAGS_HAVE_VECTORCALL must stay clear). */
    {0, NULL}
};

static PyType_Spec PyTimelog_spec = {
    .name = "timelog._timelog.Timelog",
    .basicsize = sizeof(PyTimelog),
    .itemsize = 0,
    .flags = Py_TPFLAGS_DEFAULT |
             Py_TPFLAGS_BASETYPE |
             Py_TPFLAGS_HAVE_GC |
             Py_TPFLAGS_IMMUTABLETYPE |
             Py_TPFLAGS_MANAGED_WEAKREF,
    .slots = PyTimelog_slots,
};

PyObject* TlPy_CreateTimelogType(PyObject* module)
{
    return PyType_FromModuleAndSpec(module, &PyTimelog_spec, NULL);
}

TL_PY_DEFINE_CHECK(TlPyTimelog_Check, type_timelog)
