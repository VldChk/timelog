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
