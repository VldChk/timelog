# LLD-B2 PyTimelog Engine Wrapper - Engineering Plan

**Version:** 1.2 (All Reviews Integrated)
**Status:** Ready for Implementation
**Last Updated:** 2026-01-13

> **Note:** This version integrates all critical fixes from multiple review rounds.
> See Section 13 for complete errata summary.

---

## 1. Executive Summary

This document provides the complete engineering plan for implementing the PyTimelog CPython extension type (LLD-B2). The implementation wraps `tl_timelog_t*` and exposes a stable, low-overhead Python API for writes, deletes, and maintenance.

**Dependencies:**
- LLD-B1 (py_handle.h/c, py_errors.h/c) - COMPLETE
- Timelog C core (timelog.h) - STABLE

**Deliverables:**
1. `bindings/cpython/include/timelogpy/py_timelog.h` - Type declaration
2. `bindings/cpython/src/py_timelog.c` - Implementation
3. `bindings/cpython/src/module.c` - Module initialization
4. `bindings/cpython/tests/test_py_timelog.c` - C-level unit tests
5. Updated `CMakeLists.txt`

---

## 2. Test-Driven Design (Tests First)

### 2.1 Test Categories

| Category | Purpose | GIL State |
|----------|---------|-----------|
| Unit (C) | Test C implementation directly | Held (Python initialized) |
| Integration | Test via Python API | Held |
| Stress | Concurrent append/compact | Mixed |

### 2.2 Unit Test Cases (test_py_timelog.c)

```c
/*===========================================================================
 * Test Suite: Lifecycle
 *===========================================================================*/

// TEST: Default config creates valid instance
// SETUP: Initialize Python, call PyTimelog_new + init with no args
// VERIFY: self->tl != NULL, self->closed == 0
// CLEANUP: Close and dealloc

// TEST: Custom config values applied
// SETUP: Init with time_unit="ns", memtable_max_bytes=1024
// VERIFY: Internal config matches

// TEST: Re-init on open instance fails
// SETUP: Create instance, try tp_init again
// VERIFY: Returns -1 with TypeError set

// TEST: Close is idempotent
// SETUP: Create instance, close twice
// VERIFY: Both close() calls succeed, no crash

// TEST: Close sets tl=NULL and closed=1
// SETUP: Create and close
// VERIFY: self->tl == NULL && self->closed == 1

// TEST: Close drains retired queue
// SETUP: Append, compact, close
// VERIFY: retired_queue_len == 0 after close

// TEST: Close refuses with active pins
// SETUP: Create, pins_enter, try close
// VERIFY: Raises TimelogError, engine still open

// TEST: Dealloc handles unclosed instance
// SETUP: Create instance, don't close, dealloc
// VERIFY: No crash, resources freed (best effort)

/*===========================================================================
 * Test Suite: Append
 *===========================================================================*/

// TEST: Append increments refcount
// SETUP: Create obj, refcnt=N, append
// VERIFY: refcnt == N+1 (engine owns one ref)

// TEST: Append with invalid ts type raises TypeError
// SETUP: append("not_an_int", obj)
// VERIFY: TypeError raised (PyArg_ParseTuple raises TypeError for wrong type)

// TEST: Append with overflow ts raises OverflowError
// SETUP: append(2**63, obj) on platform where int64 max is smaller
// VERIFY: OverflowError raised

// TEST: Append failure rolls back refcount
// SETUP: Mock/inject failure in tl_append
// VERIFY: refcnt unchanged after failure

// TEST: Append after close raises TimelogError
// SETUP: Create, close, append
// VERIFY: TimelogError with "closed" message

// TEST: Append triggers opportunistic drain
// SETUP: Append many, compact (generates retires), append again
// VERIFY: drain called (queue len decreases)

/*===========================================================================
 * Test Suite: Extend (Batch)
 *===========================================================================*/

// TEST: Extend with empty iterable is no-op
// SETUP: extend([])
// VERIFY: Success, no records added

// TEST: Extend appends all items
// SETUP: extend([(1, a), (2, b), (3, c)])
// VERIFY: All three records exist

// TEST: Extend failure stops at first error
// SETUP: extend([(1, a), (bad, b), (3, c)])
// VERIFY: First succeeds, second fails, third not attempted

// TEST: Extend non-atomic (prior inserts remain)
// SETUP: extend([(1, a), (2, b)]) where (2, b) fails
// VERIFY: (1, a) is in the log

// TEST: Extend does not UAF on borrowed reference (CRITICAL REGRESSION)
// SETUP: Create object whose __del__ sets a flag if called unexpectedly
// VERIFY: Object survives INCREF/DECREF sequence without unexpected __del__

/*===========================================================================
 * Test Suite: Delete
 *===========================================================================*/

// TEST: delete_range with valid range succeeds
// SETUP: Append records, delete_range(t1, t2)
// VERIFY: TL_OK

// TEST: delete_range t1 >= t2 raises ValueError
// SETUP: delete_range(10, 5)
// VERIFY: ValueError

// TEST: delete_before valid cutoff succeeds
// SETUP: delete_before(1000)
// VERIFY: TL_OK

// TEST: delete after close raises TimelogError
// SETUP: close, delete_range
// VERIFY: TimelogError

// TEST: delete_range with t1 == t2 is allowed (empty range no-op)
// SETUP: delete_range(100, 100)
// VERIFY: Returns None (no error)

// TEST: TL_EBUSY from delete_range means tombstone IS inserted
// SETUP: Manual mode, fill sealed queue, delete_range
// VERIFY: TimelogBusyError raised but tombstone is in log

// TEST: delete_before TL_EBUSY means tombstone IS inserted
// SETUP: Manual mode, fill sealed queue, delete_before
// VERIFY: TimelogBusyError raised but tombstone is in log

/*===========================================================================
 * Test Suite: Flush/Compact
 *===========================================================================*/

// TEST: flush succeeds
// SETUP: Append, flush
// VERIFY: TL_OK

// TEST: flush releases GIL
// SETUP: Start another Python thread, flush in main
// VERIFY: Other thread can acquire GIL during flush
// (Smoke test: no hang)

// TEST: compact succeeds
// SETUP: Append, compact
// VERIFY: TL_OK

// TEST: flush after close raises TimelogError

/*===========================================================================
 * Test Suite: Maintenance
 *===========================================================================*/

// TEST: start_maintenance in background mode succeeds
// SETUP: Create with maintenance="background", start_maintenance
// VERIFY: TL_OK

// TEST: start_maintenance in manual mode raises TimelogError
// SETUP: Create with maintenance="disabled", start_maintenance
// VERIFY: TimelogError (TL_ESTATE)

// TEST: stop_maintenance is idempotent
// SETUP: start, stop, stop
// VERIFY: Both stops succeed

// TEST: stop_maintenance releases GIL
// SETUP: Start maint, stop from main thread
// VERIFY: No hang (maint thread can exit)

/*===========================================================================
 * Test Suite: Backpressure
 *
 * CRITICAL: TL_EBUSY means record WAS inserted, just backpressure occurred.
 * Tests must verify:
 * - Record IS in log after EBUSY
 * - Refcount NOT rolled back on EBUSY
 * - No retry (would create duplicate)
 *===========================================================================*/

// TEST: TL_EBUSY with RAISE policy raises TimelogBusyError but record IS inserted
// SETUP: Configure manual mode, fill sealed queue, append
// VERIFY: TimelogBusyError raised, BUT refcount is N+1 (record is in log)

// TEST: TL_EBUSY with SILENT policy returns success
// SETUP: busy_policy="silent", trigger EBUSY
// VERIFY: Returns None, record is in log

// TEST: TL_EBUSY with FLUSH policy flushes and returns success
// SETUP: busy_policy="flush", trigger EBUSY
// VERIFY: flush() called, returns None, record is in log

// TEST: TL_EBUSY does NOT duplicate record
// SETUP: Append, trigger EBUSY, iterate
// VERIFY: Record appears exactly once (no retry occurred)

/*===========================================================================
 * Test Suite: Context Manager
 *===========================================================================*/

// TEST: __enter__ returns self
// SETUP: with Timelog() as t:
// VERIFY: t is the Timelog instance

// TEST: __exit__ calls close
// SETUP: with Timelog() as t: pass
// VERIFY: t.closed == True after with block

// TEST: __exit__ with exception still closes
// SETUP: with Timelog() as t: raise Exception
// VERIFY: t.closed == True

// TEST: __exit__ propagates close error if no original exception
// SETUP: Create timelog, add pins (so close fails), exit with block normally
// VERIFY: Close error is raised, not swallowed

// TEST: __exit__ suppresses close error if original exception exists
// SETUP: Create timelog, add pins, raise in with block
// VERIFY: Original exception propagates, close error suppressed
```

### 2.3 Test Framework

Use the same minimal framework as test_py_handle.c:

```c
#define TEST(name) \
    static void test_##name(void); \
    static void run_##name(void) { \
        printf("  %s... ", #name); \
        fflush(stdout); \
        tests_run++; \
        test_##name(); \
        printf("PASS\n"); \
    } \
    static void test_##name(void)

#define ASSERT(cond) \
    do { \
        if (!(cond)) { \
            printf("FAIL\n    Assertion failed: %s\n    at %s:%d\n", \
                   #cond, __FILE__, __LINE__); \
            tests_failed++; \
            return; \
        } \
    } while(0)
```

---

## 3. Architecture

### 3.1 File Structure

```
bindings/cpython/
├── include/timelogpy/
│   ├── py_handle.h     # (existing) Handle/lifetime B1
│   ├── py_errors.h     # (existing) Error translation
│   └── py_timelog.h    # (NEW) PyTimelog type declaration
├── src/
│   ├── py_handle.c     # (existing)
│   ├── py_errors.c     # (existing)
│   ├── py_timelog.c    # (NEW) PyTimelog implementation
│   └── module.c        # (NEW) PyInit__timelog
├── tests/
│   ├── test_py_handle.c    # (existing)
│   └── test_py_timelog.c   # (NEW)
└── CMakeLists.txt      # (UPDATE)
```

### 3.2 PyTimelog Type Layout

```c
// py_timelog.h

typedef enum {
    TL_PY_BUSY_RAISE  = 0,  /* Raise TimelogBusyError (record IS inserted) */
    TL_PY_BUSY_SILENT = 1,  /* Return success silently */
    TL_PY_BUSY_FLUSH  = 2   /* Flush to relieve backpressure, return success */
} tl_py_busy_policy_t;

typedef struct {
    PyObject_HEAD

    /* Engine instance (NULL after close) */
    tl_timelog_t* tl;

    /* Lifecycle state */
    int closed;                         /* 0=open, 1=closed */

    /* Handle/lifetime context (embedded, not pointer) */
    tl_py_handle_ctx_t handle_ctx;

    /* Config introspection (optional, for debugging) */
    tl_time_unit_t time_unit;
    tl_maint_mode_t maint_mode;

    /* Backpressure policy */
    tl_py_busy_policy_t busy_policy;

} PyTimelog;

/* Type object (defined in py_timelog.c) */
extern PyTypeObject PyTimelog_Type;

/* Type check macro */
#define PyTimelog_Check(op) PyObject_TypeCheck(op, &PyTimelog_Type)
```

### 3.3 Module Structure

```c
// module.c

static struct PyModuleDef timelog_module = {
    PyModuleDef_HEAD_INIT,
    "_timelog",                           /* m_name */
    "Timelog C extension module",         /* m_doc */
    -1,                                   /* m_size (no per-module state) */
    NULL,                                 /* m_methods (none at module level) */
    NULL, NULL, NULL, NULL
};

PyMODINIT_FUNC PyInit__timelog(void)
{
    PyObject* m = PyModule_Create(&timelog_module);
    if (m == NULL) return NULL;

    /* Initialize error types */
    if (TlPy_InitErrors(m) < 0) {
        Py_DECREF(m);
        return NULL;
    }

    /* Initialize PyTimelog type */
    if (PyType_Ready(&PyTimelog_Type) < 0) {
        Py_DECREF(m);
        return NULL;
    }

    Py_INCREF(&PyTimelog_Type);
    if (PyModule_AddObject(m, "Timelog", (PyObject*)&PyTimelog_Type) < 0) {
        Py_DECREF(&PyTimelog_Type);
        Py_DECREF(m);
        return NULL;
    }

    return m;
}
```

---

## 4. Detailed Implementation Specifications

### 4.1 PyTimelog_init (tp_init)

**Signature:** `int PyTimelog_init(PyTimelog* self, PyObject* args, PyObject* kwds)`

**Parse kwargs:**
```c
static char* kwlist[] = {
    "time_unit",           /* s - string */
    "maintenance",         /* s - string */
    "memtable_max_bytes",  /* n - Py_ssize_t */
    "target_page_bytes",   /* n - Py_ssize_t */
    "sealed_max_runs",     /* n - Py_ssize_t */
    "drain_batch_limit",   /* n - Py_ssize_t (NOT I - avoids silent truncation) */
    "busy_policy",         /* s - string */
    NULL
};

const char* time_unit_str = NULL;
const char* maint_str = NULL;
Py_ssize_t memtable_max_bytes = -1;  /* -1 = use default */
Py_ssize_t target_page_bytes = -1;
Py_ssize_t sealed_max_runs = -1;
Py_ssize_t drain_batch_limit = -1;   /* Changed from unsigned int */
const char* busy_policy_str = NULL;

/* CRITICAL: 7 converters for 7 kwargs (was 8 converters - UB!) */
if (!PyArg_ParseTupleAndKeywords(args, kwds, "|ssnnnns", kwlist,
        &time_unit_str, &maint_str,
        &memtable_max_bytes, &target_page_bytes, &sealed_max_runs,
        &drain_batch_limit, &busy_policy_str)) {
    return -1;
}

/* Validate drain_batch_limit range (was silently truncated with 'I') */
if (drain_batch_limit != -1) {
    if (drain_batch_limit < 0 || drain_batch_limit > UINT32_MAX) {
        PyErr_SetString(PyExc_ValueError,
            "drain_batch_limit must be 0-4294967295");
        return -1;
    }
}

/* Map -1 (unset) to 0 (unlimited) for ctx init */
uint32_t drain_limit = (drain_batch_limit == -1) ? 0 : (uint32_t)drain_batch_limit;
```

**Busy policy parsing:**
```c
static int parse_busy_policy(const char* s, tl_py_busy_policy_t* out) {
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

/* In init, after config building: */
if (parse_busy_policy(busy_policy_str, &self->busy_policy) < 0) {
    tl_py_handle_ctx_destroy(&self->handle_ctx);
    return -1;
}
```

**Algorithm:**
```
1. If self->tl != NULL:
   - Set TypeError: "Timelog already initialized"
   - return -1

2. Initialize handle_ctx:
   - st = tl_py_handle_ctx_init(&self->handle_ctx, drain_batch_limit)
   - if st != TL_OK: raise, return -1

3. Build tl_config_t:
   - tl_config_init_defaults(&cfg)
   - Map time_unit_str to cfg.time_unit
   - Map maint_str to cfg.maintenance_mode
   - Apply numeric overrides (with validation > 0)
   - cfg.on_drop_handle = tl_py_on_drop_handle
   - cfg.on_drop_ctx = &self->handle_ctx

4. Call tl_open:
   - st = tl_open(&cfg, &self->tl)
   - if st != TL_OK:
     - tl_py_handle_ctx_destroy(&self->handle_ctx)
     - self->tl = NULL
     - self->closed = 1
     - TlPy_RaiseFromStatus(st)
     - return -1

5. Success:
   - self->closed = 0
   - Store introspection fields
   - return 0
```

**Time unit mapping:**
```c
/*
 * IMPORTANT: Don't override engine default when omitted.
 * Engine defaults to TL_TIME_MS; previous version incorrectly defaulted to TL_TIME_S.
 */
static int parse_time_unit(const char* s, tl_time_unit_t* out, int* was_set) {
    *was_set = 0;
    if (s == NULL) {
        return 0;  /* Leave cfg.time_unit at engine default (TL_TIME_MS) */
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

/* In init, use like this: */
int time_unit_set;
if (parse_time_unit(time_unit_str, &cfg.time_unit, &time_unit_set) < 0) {
    return -1;
}
/* Store for introspection (use engine default if not set) */
self->time_unit = time_unit_set ? cfg.time_unit : TL_TIME_MS;
```

### 4.2 PyTimelog_close

**Signature:** `PyObject* PyTimelog_close(PyTimelog* self, PyObject* Py_UNUSED(args))`

**Algorithm:**
```
1. If self->closed:
   - Py_RETURN_NONE (idempotent)

2. Mark closed early (reentrancy guard):
   - self->closed = 1

3. If self->tl == NULL:
   - tl_py_handle_ctx_destroy(&self->handle_ctx)
   - Py_RETURN_NONE

4. Stop maintenance (release GIL):
   - Py_BEGIN_ALLOW_THREADS
   - tl_maint_stop(self->tl)  // Safe even if not started
   - Py_END_ALLOW_THREADS

5. Check pins:
   - uint64_t pins = tl_py_pins_count(&self->handle_ctx)
   - if pins != 0:
     - self->closed = 0  // Rollback closed flag
     - Return TlPy_RaiseFromStatusFmt(TL_ESTATE,
         "Cannot close: %llu active snapshots/iterators", pins)

6. Close engine (may release GIL if slow):
   - Py_BEGIN_ALLOW_THREADS
   - tl_close(self->tl)
   - Py_END_ALLOW_THREADS

7. Clear pointer:
   - self->tl = NULL

8. Drain retired objects (force=1):
   - tl_py_drain_retired(&self->handle_ctx, 1)

9. Destroy handle context:
   - tl_py_handle_ctx_destroy(&self->handle_ctx)

10. Py_RETURN_NONE
```

### 4.3 PyTimelog_dealloc (tp_dealloc)

**Signature:** `void PyTimelog_dealloc(PyTimelog* self)`

**Algorithm:**
```
1. Best-effort close:
   - If !self->closed && self->tl != NULL:
     - uint64_t pins = tl_py_pins_count(&self->handle_ctx)
     - if pins == 0:
       - Py_BEGIN_ALLOW_THREADS
       - tl_maint_stop(self->tl)
       - tl_close(self->tl)
       - Py_END_ALLOW_THREADS
       - tl_py_drain_retired(&self->handle_ctx, 1)
       - tl_py_handle_ctx_destroy(&self->handle_ctx)
     - else:
       - // WARNING: leaking resources (pins active)
       - #ifndef NDEBUG
       - fprintf(stderr, "WARNING: PyTimelog dealloc with pins=%llu\n", pins)
       - #endif

2. Free object:
   - Py_TYPE(self)->tp_free((PyObject*)self)
```

### 4.4 PyTimelog_append

**Signature:** `PyObject* PyTimelog_append(PyTimelog* self, PyObject* args)`

**CRITICAL: TL_EBUSY Semantics**

TL_EBUSY from `tl_append()` means the record **WAS successfully inserted**, but
backpressure occurred (sealed queue full). Evidence from core:

```c
// tl_timelog.c:566-568
/* This is safe because the write already succeeded. */
```

Therefore:
- **DO NOT** rollback INCREF on EBUSY - record is in engine
- **DO NOT** retry on EBUSY - would create duplicate
- EBUSY is an informational signal, not a failure

**Algorithm:**
```c
PyObject* PyTimelog_append(PyTimelog* self, PyObject* args)
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
```

**CHECK_CLOSED macro:**
```c
#define CHECK_CLOSED(self) \
    do { \
        if ((self)->closed || (self)->tl == NULL) { \
            return TlPy_RaiseFromStatusFmt(TL_ESTATE, "Timelog is closed"); \
        } \
    } while (0)
```

### 4.5 PyTimelog_extend

**Signature:** `PyObject* PyTimelog_extend(PyTimelog* self, PyObject* iterable)`

**CRITICAL: Reference Order Fix**

`obj` is a borrowed reference from `item`. We MUST `Py_INCREF(obj)` BEFORE
`Py_DECREF(item)`, otherwise `obj` may be freed.

**Algorithm:**
```c
PyObject* PyTimelog_extend(PyTimelog* self, PyObject* iterable)
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

        /* Validate timestamp range (was missing in original plan) */
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
                    "All records in batch are committed. "
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
```

### 4.6 PyTimelog_delete_range

**Signature:** `PyObject* PyTimelog_delete_range(PyTimelog* self, PyObject* args)`

**CRITICAL: TL_EBUSY Semantics (Same as Append)**

Delete operations follow the same pattern as append: the tombstone is inserted
BEFORE `handle_seal_with_backpressure` is called. TL_EBUSY means the tombstone
IS in the memtable, just backpressure occurred.

```c
PyObject* PyTimelog_delete_range(PyTimelog* self, PyObject* args)
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
            Py_BEGIN_ALLOW_THREADS
            tl_flush(self->tl);
            Py_END_ALLOW_THREADS
        }
        goto success;
    }

    return TlPy_RaiseFromStatus(st);

success:
    tl_py_drain_retired(&self->handle_ctx, 0);
    Py_RETURN_NONE;
}
```

### 4.7 PyTimelog_delete_before

**Signature:** `PyObject* PyTimelog_delete_before(PyTimelog* self, PyObject* args)`

Same TL_EBUSY semantics as delete_range.

```c
PyObject* PyTimelog_delete_before(PyTimelog* self, PyObject* args)
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
            Py_BEGIN_ALLOW_THREADS
            tl_flush(self->tl);
            Py_END_ALLOW_THREADS
        }
        goto success;
    }

    return TlPy_RaiseFromStatus(st);

success:
    tl_py_drain_retired(&self->handle_ctx, 0);
    Py_RETURN_NONE;
}
```

### 4.8 PyTimelog_flush

**Signature:** `PyObject* PyTimelog_flush(PyTimelog* self, PyObject* Py_UNUSED(args))`

```
1. CHECK_CLOSED(self)

2. Release GIL and flush:
   - tl_status_t st
   - Py_BEGIN_ALLOW_THREADS
   - st = tl_flush(self->tl)
   - Py_END_ALLOW_THREADS

3. Check result:
   - if st != TL_OK: return TlPy_RaiseFromStatus(st)

4. Drain under GIL:
   - tl_py_drain_retired(&self->handle_ctx, 0)

5. Py_RETURN_NONE
```

### 4.8 Context Manager

```c
static PyObject* PyTimelog_enter(PyTimelog* self, PyObject* Py_UNUSED(args))
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
 *
 * Previous version always cleared close() errors - wrong!
 */
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
```

### 4.9 PyTimelog_compact

**Signature:** `PyObject* PyTimelog_compact(PyTimelog* self, PyObject* Py_UNUSED(args))`

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
     * Note: In manual mode (maintenance='disabled'), compact() only requests
     * compaction. The actual work happens when the background worker runs
     * (if later started) or the application calls tl_maint_step() externally.
     *
     * For V1, we do NOT expose maint_step() to Python. Manual mode is for
     * advanced use cases where the caller controls the maintenance loop.
     * Typical Python usage should use maintenance='background'.
     */
    Py_RETURN_NONE;
}
```

### 4.10 PyTimelog_start_maint

**Signature:** `PyObject* PyTimelog_start_maint(PyTimelog* self, PyObject* Py_UNUSED(args))`

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

### 4.11 PyTimelog_stop_maint

**Signature:** `PyObject* PyTimelog_stop_maint(PyTimelog* self, PyObject* Py_UNUSED(args))`

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

    /* Drain after stop - no more on_drop callbacks possible */
    tl_py_drain_retired(&self->handle_ctx, 0);

    Py_RETURN_NONE;
}
```

---

## 5. Method Table

```c
static PyMethodDef PyTimelog_methods[] = {
    {"append",           (PyCFunction)PyTimelog_append,      METH_VARARGS,
     "append(ts, obj) -> None\n\n"
     "Append a record at timestamp ts with payload obj."},

    {"extend",           (PyCFunction)PyTimelog_extend,      METH_O,
     "extend(iterable) -> None\n\n"
     "Append multiple (ts, obj) records from an iterable.\n"
     "Non-atomic: prior successful inserts remain on failure."},

    {"delete_range",     (PyCFunction)PyTimelog_delete_range, METH_VARARGS,
     "delete_range(t1, t2) -> None\n\n"
     "Mark records in [t1, t2) for deletion (tombstone)."},

    {"delete_before",    (PyCFunction)PyTimelog_delete_before, METH_VARARGS,
     "delete_before(cutoff) -> None\n\n"
     "Mark records in [MIN, cutoff) for deletion."},

    {"flush",            (PyCFunction)PyTimelog_flush,       METH_NOARGS,
     "flush() -> None\n\n"
     "Synchronously flush memtable to L0 segments."},

    {"compact",          (PyCFunction)PyTimelog_compact,     METH_NOARGS,
     "compact() -> None\n\n"
     "Request compaction (maintenance must be running or manual step called)."},

    {"start_maintenance",(PyCFunction)PyTimelog_start_maint, METH_NOARGS,
     "start_maintenance() -> None\n\n"
     "Start background maintenance worker (background mode only)."},

    {"stop_maintenance", (PyCFunction)PyTimelog_stop_maint,  METH_NOARGS,
     "stop_maintenance() -> None\n\n"
     "Stop background maintenance worker and wait for it to exit."},

    {"close",            (PyCFunction)PyTimelog_close,       METH_NOARGS,
     "close() -> None\n\n"
     "Close the timelog. Idempotent. Releases all resources."},

    {"__enter__",        (PyCFunction)PyTimelog_enter,       METH_NOARGS,
     "Context manager entry."},

    {"__exit__",         (PyCFunction)PyTimelog_exit,        METH_VARARGS,
     "Context manager exit (closes the timelog)."},

    {NULL, NULL, 0, NULL}
};
```

---

## 6. Type Object Definition

```c
PyTypeObject PyTimelog_Type = {
    PyVarObject_HEAD_INIT(NULL, 0)
    .tp_name = "timelog._timelog.Timelog",
    .tp_doc = "Timelog engine wrapper.\n\n"
              "A time-indexed multimap for (timestamp, object) records.\n",
    .tp_basicsize = sizeof(PyTimelog),
    .tp_itemsize = 0,
    .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,
    .tp_new = PyType_GenericNew,
    .tp_init = (initproc)PyTimelog_init,
    .tp_dealloc = (destructor)PyTimelog_dealloc,
    .tp_methods = PyTimelog_methods,
    /* No getset for now; add properties in V1.1 if needed */
};
```

---

## 7. Implementation Order (TDD)

### Phase 1: Skeleton + Compile
1. Create py_timelog.h with type declaration
2. Create py_timelog.c with empty implementations
3. Create module.c with PyInit__timelog
4. Update CMakeLists.txt
5. Verify clean compile

### Phase 2: Init + Close Tests
1. Write test_init_defaults
2. Implement PyTimelog_init (minimal)
3. Write test_close_idempotent
4. Implement PyTimelog_close
5. Implement PyTimelog_dealloc
6. Run tests, iterate

### Phase 3: Append Tests
1. Write test_append_incref
2. Write test_append_failure_rollback
3. Implement PyTimelog_append
4. Run tests, iterate

### Phase 4: Delete/Flush/Compact
1. Write tests for each
2. Implement each method
3. Verify GIL release for flush

### Phase 5: Maintenance
1. Write start/stop tests
2. Implement methods
3. Test GIL release for stop

### Phase 6: Backpressure
1. Write EBUSY tests
2. Implement policy handling
3. Test AUTO_FLUSH

### Phase 7: Context Manager
1. Write __enter__/__exit__ tests
2. Implement methods
3. Verify exception handling

### Phase 8: Integration
1. Build full module
2. Run Python-level smoke tests
3. Run with sanitizers

---

## 8. CMakeLists.txt Updates

```cmake
# Add new sources
set(TIMELOG_PY_SOURCES
    src/py_handle.c
    src/py_errors.c
    src/py_timelog.c    # NEW
    src/module.c        # NEW
)

# Add new test executable
if(TIMELOG_BUILD_PY_TESTS)
    # ... existing test_py_handle ...

    add_executable(test_py_timelog
        tests/test_py_timelog.c
    )
    target_include_directories(test_py_timelog PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${Python3_INCLUDE_DIRS}
    )
    target_link_libraries(test_py_timelog PRIVATE
        timelog
        ${Python3_LIBRARIES}
    )
    # ... sanitizer options ...
endif()
```

---

## 9. Invariants Checklist

| ID | Invariant | Verification |
|----|-----------|--------------|
| W1 | One INCREF per successful append | test_append_incref |
| W2 | No Python C-API in on_drop | Code review (B1 verified) |
| W3 | No DECREF while pins > 0 | test_close_refuses_with_pins |
| W4 | No engine calls after close | test_methods_after_close_raise |
| W5 | Close is idempotent | test_close_idempotent |
| W6 | No engine locks while calling Python | Design (drain after engine calls) |

---

## 10. Estimated Line Counts

| File | Lines (approx) |
|------|----------------|
| py_timelog.h | 60 |
| py_timelog.c | 500-600 |
| module.c | 80 |
| test_py_timelog.c | 400-500 |
| CMakeLists.txt updates | 30 |
| **Total new code** | ~1100-1300 |

---

## 11. Risk Mitigation

| Risk | Mitigation |
|------|------------|
| GIL release causes race | Only release for pure-C engine calls |
| Reentrancy from Py_DECREF | Mark closed early, drain after close |
| Memory ordering bugs | Use verified B1 patterns |
| Backpressure policy complexity | Default to simple RAISE |
| Config parsing errors | Validate all inputs explicitly |

---

## 12. Thread Safety and Documentation

### Thread Safety Model

A `Timelog` instance is **NOT** thread-safe. Do not access the same instance from
multiple threads without external synchronization. This is consistent with Python's
`sqlite3.Connection` and file objects.

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

**Rationale for no internal lock:**
1. Engine documents "single-writer external coordination required"
2. Adding internal lock would add overhead for single-threaded use (common case)
3. GIL release is to allow OTHER Python threads to run, not concurrent Timelog access

### Close Documentation

```python
"""
close() -> None

Close the timelog and release resources.

WARNING: Records not yet flushed will be lost. In Python-object mode,
this also means those objects will leak (never DECREF'd). Call flush()
before close() to ensure all records are persisted and reclaimed properly.
"""
```

**Debug-mode warning in close():**

Note: The core API does not expose a quick stats function. For V1, we document
the flush-before-close requirement rather than adding a warning. A future version
could add `tl_memtable_count()` or similar lightweight query.

```c
/*
 * V1: No runtime warning - document requirement instead.
 * V1.1 consideration: Add tl_memtable_count(tl) to core API for this check.
 */
```

**Documentation in close() docstring:**
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

## 13. Errata Summary (V1.2)

This section documents critical fixes applied during review. All issues from
`engineering_plan_B2_errata.md` and subsequent reviews have been integrated.

### V1.1 Fixes

| Issue | Severity | Section | Status |
|-------|----------|---------|--------|
| TL_EBUSY semantics wrong (rollback/retry = UAF/dupe) | CRITICAL | 4.4, 4.5 | FIXED |
| PyArg format mismatch (8 vs 7 converters = UB) | CRITICAL | 4.1 | FIXED |
| extend() UAF (DECREF item before INCREF obj) | CRITICAL | 4.5 | FIXED |
| auto-flush ignored result and retried | HIGH | 4.4 | FIXED |
| __exit__ swallowed all close errors | HIGH | 4.10 | FIXED |
| Default time_unit overrode engine default | MEDIUM | 4.1 | FIXED |
| Test expected ValueError, should be TypeError | MEDIUM | 2.2 | FIXED |
| Missing compact/start_maint/stop_maint specs | MEDIUM | 4.11-4.13 | FIXED |
| Thread safety undocumented | LOW | 12 | ADDED |
| Close-time leak warning missing | LOW | 12 | ADDED |

### V1.2 Fixes

| Issue | Severity | Section | Status |
|-------|----------|---------|--------|
| Delete APIs ignore TL_EBUSY (tombstone already inserted) | HIGH | 4.6, 4.7 | FIXED |
| busy_policy parsing unspecified | MEDIUM | 4.1 | FIXED |
| FLUSH policy missing in extend() | MEDIUM | 4.5 | FIXED |
| delete_range rejects t1==t2 (core allows) | MEDIUM | 4.6 | FIXED |
| delete_before spec missing | MEDIUM | 4.7 | ADDED |
| compact() references non-existent run_maintenance() | MEDIUM | 4.11 | FIXED |
| tl_stats_quick doesn't exist in core | LOW | 12 | FIXED |
| drain_batch_limit -1 not mapped to 0 | LOW | 4.1 | FIXED |

### Key Semantic Change: TL_EBUSY

**Previous (WRONG):** TL_EBUSY = failure, rollback INCREF, retry
**Correct:** TL_EBUSY = success with backpressure signal, NO rollback, NO retry

This applies to ALL write operations: `append`, `extend`, `delete_range`, `delete_before`.

Evidence: `tl_timelog.c:566-568`: "This is safe because the write already succeeded."
Also: `tl_timelog.c:698,732`: Delete operations call `handle_seal_with_backpressure` AFTER insert.

### Open Questions (Resolved)

**Q1: Should TL_EBUSY handling for delete_range/delete_before mirror append?**
**A:** YES. All write operations use the same `handle_seal_with_backpressure` pattern.
The busy_policy now applies uniformly to append, extend, delete_range, and delete_before.

**Q2: Is the module package-qualified (timelog._timelog) or top-level (_timelog)?**
**A:** Package-qualified: `timelog._timelog`. This matches:
- `PyModuleDef.m_name = "_timelog"` (bare name for import mechanism)
- `tp_name = "timelog._timelog.Timelog"` (qualified for repr/error messages)
- Exception: `timelog._timelog.TimelogError` (matches py_errors.c:46)

**Q3: HLD still shows on_drop acquiring GIL - will it be updated?**
**A:** Yes, HLD is outdated. B1/B2 design (no Python C-API in on_drop) is correct.
HLD update is tracked separately but not blocking for B2 implementation.

---

## 14. Next Steps

After this plan is approved:

1. Create test skeleton (test_py_timelog.c)
2. Create header (py_timelog.h)
3. Create implementation (py_timelog.c)
4. Create module (module.c)
5. Update CMakeLists.txt
6. Iteratively implement and test each phase
7. Run static analysis (clang-tidy, clang analyzer)
8. Run c17-reviewer agent for final review
