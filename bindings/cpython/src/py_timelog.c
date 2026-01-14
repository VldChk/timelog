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
    if (s == NULL || strcmp(s, "disabled") == 0) {
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

    /* Drain retired objects (force=1) */
    tl_py_drain_retired(&self->handle_ctx, 1);

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
            tl_py_drain_retired(&self->handle_ctx, 1);
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
