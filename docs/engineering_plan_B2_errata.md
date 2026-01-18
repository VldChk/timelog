# Engineering Plan B2 - Errata and Critical Fixes

**Version:** 1.1
**Date:** 2026-01-13
**Status:** Fixes required before implementation

This document captures critical bugs and design issues identified during review of `engineering_plan_B2_pytimelog.md`. All issues must be addressed before implementation.

---

## 1. CRITICAL: TL_EBUSY Semantics Are Fundamentally Wrong

### Problem

The plan treats `TL_EBUSY` from `tl_append()` as a write failure and performs:
1. `Py_DECREF(obj)` rollback
2. Retry with AUTO_FLUSH policy

**This is WRONG.** Evidence from core implementation:

```c
// tl_timelog.c:566-568
/* Background mode: wait for flush to make space, then retry seal.
 * Must drop writer_mu while waiting to allow flush to proceed.
 * This is safe because the write already succeeded. */
```

And from `tl_memtable.h:178`:
```c
/* CRITICAL INVARIANT: On TL_ENOMEM or TL_EBUSY, active state is PRESERVED. */
```

**TL_EBUSY means:**
- In background mode: Should not occur (internal wait + retry)
- In manual mode: Record WAS inserted, but seal failed (queue full)

**Consequences of current plan:**
- `Py_DECREF` after successful insert → **Use-After-Free**
- Retry after successful insert → **Duplicate records**

### Fix

**For `tl_append()` result handling:**

```c
st = tl_append(self->tl, ts, h);

if (st == TL_OK) {
    /* Normal success */
    goto success;
}

if (st == TL_EBUSY) {
    /*
     * EBUSY from append = record WAS inserted, but backpressure occurred.
     * This only happens in manual maintenance mode.
     *
     * DO NOT rollback INCREF - record is in engine.
     * DO NOT retry - would create duplicate.
     *
     * Policy options:
     * - RAISE: Notify caller of backpressure (record is safe)
     * - SILENT: Return success, caller should check stats
     * - FLUSH: Trigger flush to relieve backpressure (record is safe)
     */
    if (self->busy_policy == TL_PY_BUSY_RAISE) {
        /* Raise informational exception - record IS in log */
        PyErr_SetString(TlPy_TimelogBusyError,
            "Record inserted but backpressure occurred. "
            "Call flush() or run maintenance to relieve.");
        return NULL;
    }
    /* SILENT or FLUSH: fall through to success */
    if (self->busy_policy == TL_PY_BUSY_FLUSH) {
        Py_BEGIN_ALLOW_THREADS
        tl_flush(self->tl);  /* Best-effort, ignore result */
        Py_END_ALLOW_THREADS
    }
    goto success;
}

/* True failure - rollback INCREF */
Py_DECREF(obj);
return TlPy_RaiseFromStatus(st);

success:
    tl_py_drain_retired(&self->handle_ctx, 0);
    Py_RETURN_NONE;
```

**Update busy_policy enum:**
```c
typedef enum {
    TL_PY_BUSY_RAISE  = 0,  /* Raise TimelogBusyError (record IS inserted) */
    TL_PY_BUSY_SILENT = 1,  /* Return success silently */
    TL_PY_BUSY_FLUSH  = 2   /* Flush to relieve backpressure, return success */
} tl_py_busy_policy_t;
```

**Remove AUTO_FLUSH retry logic entirely.**

### LLD-B2 Update Required

LLD-B2 Section 7.1 incorrectly states:
> "rollback any `INCREF`"

This must be updated to reflect that TL_EBUSY means write succeeded.

---

## 2. CRITICAL: PyArg_ParseTupleAndKeywords Format Mismatch

### Problem

```c
PyArg_ParseTupleAndKeywords(args, kwds, "|ssnnnnIs", ...)
```

Format string has **8 converters** (`s s n n n n I s`) but only **7 kwargs** in kwlist.
This is **undefined behavior** (varargs mismatch) and can cause runtime crashes.

Also, `I` (unsigned) silently truncates on overflow - unacceptable for config validation.

### Fix

```c
static char* kwlist[] = {
    "time_unit",           /* s */
    "maintenance",         /* s */
    "memtable_max_bytes",  /* n (Py_ssize_t) */
    "target_page_bytes",   /* n */
    "sealed_max_runs",     /* n */
    "drain_batch_limit",   /* n - NOT I */
    "busy_policy",         /* s */
    NULL
};

const char* time_unit_str = NULL;
const char* maint_str = NULL;
Py_ssize_t memtable_max_bytes = -1;
Py_ssize_t target_page_bytes = -1;
Py_ssize_t sealed_max_runs = -1;
Py_ssize_t drain_batch_limit = -1;  /* Changed from unsigned */
const char* busy_policy_str = NULL;

/* 7 converters for 7 kwargs */
if (!PyArg_ParseTupleAndKeywords(args, kwds, "|ssnnnns", kwlist,
        &time_unit_str, &maint_str,
        &memtable_max_bytes, &target_page_bytes, &sealed_max_runs,
        &drain_batch_limit, &busy_policy_str)) {
    return -1;
}

/* Validate drain_batch_limit range */
if (drain_batch_limit != -1) {
    if (drain_batch_limit < 0 || drain_batch_limit > UINT32_MAX) {
        PyErr_SetString(PyExc_ValueError,
            "drain_batch_limit must be 0-4294967295");
        return -1;
    }
}
```

---

## 3. CRITICAL: extend() Use-After-Free

### Problem

```c
if (!PyArg_ParseTuple(item, "LO", &ts_ll, &obj)):
    Py_DECREF(item)
    ...
Py_DECREF(item)    /* obj is BORROWED from item! */
Py_INCREF(obj)     /* TOO LATE - obj may be freed */
```

`obj` is a borrowed reference from `item`. Decrementing `item` before incrementing `obj` can free `obj`.

### Fix

```c
/* Parse item */
if (!PyArg_ParseTuple(item, "LO", &ts_ll, &obj)) {
    Py_DECREF(item);
    Py_DECREF(iter);
    return NULL;
}

/* INCREF obj BEFORE decref item (obj is borrowed from item) */
Py_INCREF(obj);
Py_DECREF(item);

/* Validate timestamp range (was missing) */
if (ts_ll < TL_TS_MIN || ts_ll > TL_TS_MAX) {
    Py_DECREF(obj);
    Py_DECREF(iter);
    return PyErr_Format(PyExc_OverflowError,
        "timestamp %lld out of int64 range", ts_ll);
}

/* Now append */
tl_handle_t h = tl_py_handle_encode(obj);
tl_status_t st = tl_append(self->tl, (tl_ts_t)ts_ll, h);

/* Handle result - NOTE: EBUSY means success! */
if (st != TL_OK && st != TL_EBUSY) {
    Py_DECREF(obj);  /* Rollback only on true failure */
    Py_DECREF(iter);
    return TlPy_RaiseFromStatus(st);
}
```

**Add regression test:** Create objects whose `__del__` crashes if called unexpectedly, pass only via tuple, run under ASan.

---

## 4. HIGH: auto-flush Ignores tl_flush() Return Value

### Problem

```c
if (st == TL_EBUSY && self->busy_policy == TL_PY_BUSY_AUTO_FLUSH) {
    Py_BEGIN_ALLOW_THREADS
    tl_flush(self->tl);  /* Ignored! */
    Py_END_ALLOW_THREADS
    st = tl_append(...);  /* Wrong: retry creates duplicate */
}
```

1. `tl_flush()` failure is silently ignored
2. Retry logic is wrong (see Issue #1)

### Fix

With corrected EBUSY semantics (Issue #1), auto-flush becomes:

```c
if (st == TL_EBUSY && self->busy_policy == TL_PY_BUSY_FLUSH) {
    /* Record already inserted. Flush to relieve backpressure. */
    tl_status_t flush_st;
    Py_BEGIN_ALLOW_THREADS
    flush_st = tl_flush(self->tl);
    Py_END_ALLOW_THREADS

    if (flush_st != TL_OK && flush_st != TL_EOF) {
        /* Flush failed, but record IS in log. Log warning, don't raise. */
        #ifndef NDEBUG
        fprintf(stderr, "WARNING: flush after EBUSY failed: %s\n",
                tl_strerror(flush_st));
        #endif
    }
    /* Fall through to success - record is safe */
}
```

---

## 5. HIGH: __exit__ Swallows Close Errors Unconditionally

### Problem

```c
static PyObject* PyTimelog_exit(PyTimelog* self, PyObject* args)
{
    (void)args;
    PyObject* result = PyTimelog_close(self, NULL);
    if (result == NULL) {
        PyErr_Clear();  /* Always clears! */
        Py_RETURN_FALSE;
    }
    ...
}
```

If the `with` block exits normally and `close()` fails, error is silently ignored.

### Fix

```c
static PyObject* PyTimelog_exit(PyTimelog* self, PyObject* args)
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
            /* No original exception - propagate close error */
            return NULL;
        }
        /* Original exception exists - suppress close error */
        PyErr_Clear();
        Py_RETURN_FALSE;
    }

    Py_DECREF(result);
    Py_RETURN_FALSE;  /* Don't suppress original exception */
}
```

---

## 6. MEDIUM: Default time_unit Overrides Engine Default

### Problem

```c
static int parse_time_unit(const char* s, tl_time_unit_t* out) {
    if (s == NULL || strcmp(s, "s") == 0) { *out = TL_TIME_S; return 0; }
    ...
}
```

When `time_unit` is omitted (`s == NULL`), this sets `TL_TIME_S`, but:
- Engine defaults to `TL_TIME_MS`
- HLD examples use `TL_TIME_MS`
- LLD-B2 says "likely milliseconds"

### Fix

Don't override when omitted:

```c
static int parse_time_unit(const char* s, tl_time_unit_t* out, int* was_set) {
    *was_set = 0;
    if (s == NULL) {
        return 0;  /* Leave cfg.time_unit at engine default */
    }
    *was_set = 1;
    if (strcmp(s, "s") == 0)  { *out = TL_TIME_S;  return 0; }
    if (strcmp(s, "ms") == 0) { *out = TL_TIME_MS; return 0; }
    if (strcmp(s, "us") == 0) { *out = TL_TIME_US; return 0; }
    if (strcmp(s, "ns") == 0) { *out = TL_TIME_NS; return 0; }
    PyErr_Format(PyExc_ValueError, "Invalid time_unit: '%s'", s);
    return -1;
}

/* In init: */
int time_unit_set;
if (parse_time_unit(time_unit_str, &cfg.time_unit, &time_unit_set) < 0) {
    return -1;
}
/* Only store for introspection if explicitly set */
self->time_unit = time_unit_set ? cfg.time_unit : TL_TIME_MS;  /* or read from cfg */
```

---

## 7. MEDIUM: Test Exception Type Mismatch

### Problem

Plan states: "Append with invalid ts type raises ValueError"

But `PyArg_ParseTuple(..., "L")` raises **TypeError** for wrong type, not ValueError.

### Fix

Update tests to expect TypeError:
```c
// TEST: Append with invalid ts type raises TypeError
// SETUP: append("not_an_int", obj)
// VERIFY: TypeError raised (not ValueError)
```

---

## 8. MEDIUM: Missing Specs for compact/start_maintenance/stop_maintenance

### Problem

Method table includes these but no implementation specs.

### Fix - Add to Section 4:

**4.9 PyTimelog_compact**
```c
PyObject* PyTimelog_compact(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_status_t st;
    Py_BEGIN_ALLOW_THREADS
    st = tl_compact(self->tl);  /* Request compaction */
    Py_END_ALLOW_THREADS

    if (st != TL_OK && st != TL_EOF) {
        return TlPy_RaiseFromStatus(st);
    }

    /*
     * In manual mode, caller must also call run_maintenance() to
     * execute the compaction. In background mode, worker handles it.
     */
    Py_RETURN_NONE;
}
```

**4.10 PyTimelog_start_maint**
```c
PyObject* PyTimelog_start_maint(PyTimelog* self, PyObject* Py_UNUSED(args))
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
```

**4.11 PyTimelog_stop_maint**
```c
PyObject* PyTimelog_stop_maint(PyTimelog* self, PyObject* Py_UNUSED(args))
{
    CHECK_CLOSED(self);

    tl_status_t st;
    Py_BEGIN_ALLOW_THREADS
    st = tl_maint_stop(self->tl);  /* Blocks until worker exits */
    Py_END_ALLOW_THREADS

    if (st != TL_OK) {
        return TlPy_RaiseFromStatus(st);
    }

    /* Drain after stop (no more on_drop callbacks possible) */
    tl_py_drain_retired(&self->handle_ctx, 0);

    Py_RETURN_NONE;
}
```

---

## 9. LOW: Concurrency / Single-Writer Discussion

### Feedback

Reviewer suggests adding internal write lock to prevent concurrent access when GIL is released.

### Decision: DISAGREE

**Rationale:**
1. Engine documents "single-writer external coordination required" - this is caller's responsibility
2. Python's standard library follows same pattern (sqlite3.Connection, file objects are not thread-safe)
3. Adding internal lock would:
   - Add complexity
   - Add overhead for single-threaded use (common case)
   - Hide threading model from users
4. GIL release during flush is to allow OTHER Python threads to run, not for concurrent Timelog access

**Action:** Document thread-safety requirements clearly:

```python
"""
Thread Safety:
    A Timelog instance is NOT thread-safe. Do not access the same instance
    from multiple threads without external synchronization. This is consistent
    with Python's sqlite3.Connection and file objects.

    The GIL is released during flush(), compact(), and stop_maintenance() to
    allow other Python threads to run, but the calling thread has exclusive
    access to the Timelog during these operations.
"""
```

---

## 10. LOW: Close-Time Reclamation Gap

### Issue

Core does not call on_drop for unflushed memtable records on close. B2 plan assumes drain completes cleanup.

### Current Status

Already documented in B1 engineering plan:
> "V1 requires `flush()` before `close()` in Python-object mode"

### Action

Add explicit check in close():

```c
/* Warn if unflushed records exist (they will leak) */
#ifndef NDEBUG
tl_stats_t stats;
if (tl_stats_quick(self->tl, &stats) == TL_OK) {
    if (stats.memtable_active_records > 0 || stats.memtable_sealed_runs > 0) {
        fprintf(stderr,
            "WARNING: closing with %llu unflushed records. "
            "Call flush() before close() to prevent leaks.\n",
            stats.memtable_active_records);
    }
}
#endif
```

Document in docstring:
```python
"""
close() -> None

Close the timelog and release resources.

WARNING: Records not yet flushed will be lost. In Python-object mode,
this also means those objects will leak (never DECREF'd). Call flush()
before close() to ensure all records are persisted and reclaimed properly.
"""
```

---

## 11. HLD vs B2 Conflict on on_drop

### Issue

HLD shows on_drop acquiring GIL + DECREF inline. B2 requires no Python C-API in on_drop.

### Decision

B1/B2 design is correct. HLD needs update but is not blocking for B2 implementation.

---

## Summary of Required Changes

| Issue | Severity | Status |
|-------|----------|--------|
| TL_EBUSY semantics wrong | CRITICAL | Fix in plan |
| PyArg format mismatch | CRITICAL | Fix in plan |
| extend() UAF | CRITICAL | Fix in plan |
| auto-flush ignore result | HIGH | Fix in plan |
| __exit__ swallows errors | HIGH | Fix in plan |
| Default time_unit | MEDIUM | Fix in plan |
| Test exception types | MEDIUM | Fix tests |
| Missing method specs | MEDIUM | Add to plan |
| Single-writer docs | LOW | Add documentation |
| Close-time leaks | LOW | Add warning/docs |
| HLD outdated | LOW | Future HLD update |
