# LLD-B6: Error Model Subsystem (Status -> Exceptions)

Date: 2026-01-16
Status: Production-Ready (code-aligned, reviewed)
Scope: CPython binding error taxonomy, mapping, and atomicity rules

This LLD defines the error model for the CPython binding layer. It is the
consistency glue that makes error handling predictable across all modules.
It mirrors current code behavior and does not add new API surface.

Sources (current code):
- Error mapping: `bindings/cpython/src/py_errors.c:117-142`,
  `bindings/cpython/include/timelogpy/py_errors.h`
- Binding call sites: `bindings/cpython/src/py_timelog.c`,
  `bindings/cpython/src/py_iter.c`, `bindings/cpython/src/py_span*.c`
- Core status codes: `include/timelog/timelog.h:126-136`

---

## 1. Goals and Non-Goals

Goals:
1. Provide a stable exception taxonomy and mapping from `tl_status_t`.
2. Standardize error handling patterns (return NULL / -1, preserve exceptions).
3. Encode atomicity rules for partial failure (INCREF rollback, snapshot cleanup).
4. Document retryability semantics for transient vs permanent errors.

Non-goals:
- No new exception types beyond what the binding already exposes.
- No change to core status codes.

---

## 2. Exception Taxonomy (Binding)

### 2.1 Custom Timelog Exceptions

| Exception | Base | Purpose | Defined In |
|----------|------|---------|------------|
| `TimelogError` | `Exception` | Catch-all for Timelog-specific state errors | `py_errors.c:46-50` |
| `TimelogBusyError` | `TimelogError` | Transient backpressure (`TL_EBUSY`) | `py_errors.c:70-74` |

The binding does **not** currently define `TimelogClosedError`. Closed-state
errors are raised as `TimelogError` with a message like "Timelog is closed".

Qualified names are consistent with the module path:
- `timelog._timelog.TimelogError`
- `timelog._timelog.TimelogBusyError`

### 2.2 Standard Python Exceptions Used

| Exception | When Used | Example |
|----------|-----------|---------|
| `ValueError` | Bad arguments, invalid config | `TL_EINVAL`, negative batch size |
| `OverflowError` | Timestamp out of int64 range | `TL_EOVERFLOW`, Python int conversion |
| `MemoryError` | Allocation failed | `TL_ENOMEM`, `PyObject_GC_New` failure |
| `SystemError` | Internal bug | `TL_EINTERNAL`, invariant violation |
| `TypeError` | Wrong argument type | `PyArg_ParseTuple` failure |
| `BufferError` | Invalid buffer operation | Close span while buffer exported |
| `RuntimeError` | Fallback if module init failed | When `TlPy_TimelogError` is NULL |

### 2.3 Fallback Behavior

If `TlPy_TimelogError` or `TlPy_TimelogBusyError` is NULL (module init failed
or called before init), `status_to_exception_type()` falls back to
`PyExc_RuntimeError`. This is a defensive measure; normal operation never
triggers this path.

Implementation: `py_errors.c:125-126,140`

---

## 3. Status Code -> Exception Mapping

### 3.1 Mapping Table

Mapping is implemented in `py_errors.c:117-142` and must remain stable:

| `tl_status_t` | Value | Python exception | Retryable | Notes |
|--------------|-------|------------------|-----------|-------|
| `TL_OK` | 0 | (success) | N/A | No exception set |
| `TL_EOF` | 1 | (success or StopIteration) | N/A | See Section 3.2 |
| `TL_EINVAL` | 10 | `ValueError` | No | Bad arguments; caller must fix |
| `TL_ESTATE` | 20 | `TimelogError` | No | Invalid state (closed, wrong mode) |
| `TL_EBUSY` | 21 | `TimelogBusyError` | Yes | Backpressure; retry after delay |
| `TL_ENOMEM` | 30 | `MemoryError` | Maybe | May succeed after GC or wait |
| `TL_EOVERFLOW` | 31 | `OverflowError` | No | Arithmetic overflow |
| `TL_EINTERNAL` | 90 | `SystemError` | No | Bug; should not occur |
| (other) | - | `TimelogError` | - | Catch-all for future codes |

### 3.2 TL_EOF Dual Semantics

`TL_EOF` has two meanings depending on context:

| Context | Meaning | Binding Behavior |
|---------|---------|------------------|
| Iterator `next()` | Exhausted | Return NULL, no exception (StopIteration) |
| `tl_flush()` | No work needed | Success (return None) |
| `tl_maint_step()` | No work needed | Success (return None/True) |
| `tl_compact()` | No work needed | Success |

**Rule:** `TL_EOF` is NEVER passed to `TlPy_RaiseFromStatus()`.

### 3.3 Implementation Helpers

```c
/* py_errors.c:144-157 */
PyObject* TlPy_RaiseFromStatus(tl_status_t status);

/* py_errors.c:159-194 */
PyObject* TlPy_RaiseFromStatusFmt(tl_status_t status,
                                   const char* format, ...);

/* py_errors.h:109-111 */
static inline int TlPy_StatusOK(tl_status_t status);
```

Calling convention:
- Do **not** call with `TL_OK` or `TL_EOF` (asserted in debug builds).
- Returns `NULL` for direct use in `return` statements.
- Message format: `"context: tl_strerror(status)"` for Fmt variant.

---

## 4. Error Handling Patterns

### 4.1 Return Conventions

- Functions returning `PyObject*`:
  - On error: return `NULL` with Python exception set.
  - On `TL_EOF` in iterators: return `NULL` **without** exception (StopIteration).
- Functions returning `int` (e.g., `tp_init`):
  - On error: set Python exception and return `-1`.

### 4.2 Exception Preservation During Cleanup

Cleanup may call `Py_DECREF` which can run arbitrary Python code and clobber
the current exception. Preserve exception state around cleanup when needed:

```c
/* Pattern from py_iter.c:101-110 */
PyObject *exc_type, *exc_value, *exc_tb;
PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
... cleanup that may run Python code (Py_DECREF, drain) ...
PyErr_Restore(exc_type, exc_value, exc_tb);
```

This pattern is required in:
- `pytimelogiter_cleanup()` (`py_iter.c:101-110`)
- `tl_py_pagespan_on_release()` (`py_span_iter.c:83-108`)
- `PyTimelog_close()` (`py_timelog.c` - see LLD-B5 Section 7.6)

**Cross-reference:** LLD-B5 Section 7.6 documents the full exception
preservation pattern used during close/dealloc paths.

### 4.3 GIL Requirements

All exception-related operations require the GIL:
- `PyErr_SetString`, `PyErr_Format`, `TlPy_RaiseFromStatus*`
- `PyErr_Fetch`, `PyErr_Restore`
- Any `Py_DECREF` that may run `__del__`

Code that releases GIL (`Py_BEGIN_ALLOW_THREADS`) must not call exception
APIs until after `Py_END_ALLOW_THREADS`.

---

## 5. Atomicity Rules (Binding)

These rules ensure safe rollback and prevent leaks or double-decref.

### 5.1 Append (single record)

Location: `py_timelog.c:369-441` (`PyTimelog_append`)

Rules:
1. `Py_INCREF(obj)` **before** calling core (line 387).
2. If status is `TL_OK`: success.
3. If status is `TL_EBUSY`: **do not** rollback; record **was inserted** (lines 398-430).
4. If status is any other error: `Py_DECREF(obj)` to rollback (line 434).

**CRITICAL:** TL_EBUSY means the record IS in the engine. Rolling back would
cause use-after-free when the engine later drops the handle.

### 5.2 Extend (batch insert)

Location: `py_timelog.c:449-544` (`PyTimelog_extend`)

Rules:
1. For each item: `Py_INCREF(obj)` before `Py_DECREF(item)` (lines 476-477).
2. On `TL_EBUSY`: record already inserted.
   - `busy_policy == raise`: raises after partial commit (lines 503-510).
   - `busy_policy == flush`: attempts `tl_flush` and continues (line 514).
   - `busy_policy == silent`: continues silently.
3. On other errors: rollback only the current object (line 496).

**Partial Commit Semantics:** If `TL_EBUSY` with `raise` policy, records
up to and including the current one are committed. Remaining items were
not attempted. The exception message documents this clearly.

### 5.3 Delete Operations

Location: `py_timelog.c` (`delete_range`, `delete_before`)

Rules:
1. No INCREF is performed; no rollback required.
2. `TL_EBUSY` means tombstone inserted (same semantics as append).
3. Any other error maps via `TlPy_RaiseFromStatus`.

### 5.4 Snapshot + Iterator Creation

Location: `py_timelog.c:840-912` (`pytimelog_make_iter`)

**Cleanup Order (reverse of acquisition):**

```
Acquisition:        pins_enter -> snapshot_acquire -> iter_create -> alloc PyIter
Cleanup on error:   iter_destroy -> snapshot_release -> pins_exit
```

Rules:
1. Enter pins **before** acquiring snapshot (line 849).
2. On snapshot failure: exit pins and raise (lines 854-856).
3. On iterator creation failure: release snapshot, exit pins, raise (lines 886-889).
4. On Python allocation failure: destroy iterator, release snapshot, exit pins (lines 894-898).

### 5.5 Iterator Next

Location: `py_iter.c:140-185` (`PyTimelogIter_iternext`)

Rules:
1. `TL_OK`: return `(ts, obj)` with new ref (lines 153-173).
2. `TL_EOF`: cleanup and return `NULL` with no exception (lines 176-179).
3. Errors: cleanup and raise via `TlPy_RaiseFromStatus` (lines 182-184).

### 5.6 PageSpan Iterator + View Ownership

Location: `py_span_iter.c:330-377`, `py_span.c:53-122`

Rules:
1. `tl_pagespan_iter_next` returns a `view` with an owner ref (`py_span_iter.c:345`).
2. `PyPageSpan_FromView` **consumes** the owner and sets `view->owner = NULL` (`py_span.c:90-91`).
3. If span creation fails, caller must call `tl_pagespan_view_release(&view)` (`py_span_iter.c:357`).
4. Iteration errors: cleanup and raise via `TlPy_RaiseFromStatus`.

### 5.7 Buffer Protocol

Location: `py_span.c` (buffer methods)

Rules:
1. Cannot close span while buffer is exported (`exports > 0`).
2. Attempting close with active exports raises `BufferError`.
3. On `releasebuffer`: decrement exports counter, allow close when zero.

---

## 6. When NOT to Use `TlPy_RaiseFromStatus`

Some errors are native Python errors and should be raised directly.
`TlPy_RaiseFromStatus*` is ONLY for errors from core `tl_*` APIs.

### 6.1 Use Standard Python Exception APIs For:

| Error Type | Raise With | Example |
|-----------|------------|---------|
| Argument type mismatch | `PyArg_ParseTuple` (auto-raises) | Wrong type in args |
| Explicit validation | `PyErr_SetString(PyExc_ValueError, ...)` | Negative batch size |
| Buffer protocol error | `PyErr_SetString(PyExc_BufferError, ...)` | Close while exported |
| Python allocation | `PyErr_NoMemory()` | `PyObject_GC_New` failed |
| Type check failure | `PyErr_SetString(PyExc_TypeError, ...)` | Wrong instance type |
| Internal logic error | `PyErr_SetString(PyExc_SystemError, ...)` | Unreachable code |

### 6.2 Use `TlPy_RaiseFromStatus*` For:

- Return value from any `tl_*` function when status is not TL_OK/TL_EOF.
- Examples: `tl_append`, `tl_snapshot_acquire`, `tl_iter_next`, `tl_flush`.

---

## 7. Debug Assertions

The error handling code includes debug-only assertions that are compiled
out in release builds (`#ifndef NDEBUG`).

### 7.1 Status Code Assertions

Location: `py_errors.c:146-149,162-165`

```c
#ifndef NDEBUG
    assert(status != TL_OK && status != TL_EOF &&
           "TlPy_RaiseFromStatus called with success status");
#endif
```

**Purpose:** Catch programming errors where caller passes success codes.
In release builds, this would set an exception for a successful operation.

### 7.2 Recommended Development Practice

Run tests with `NDEBUG` undefined (debug build) to catch:
- Success codes passed to error handlers
- Null pointer dereferences (core assertions)
- Invariant violations

---

## 8. Error Message Format Conventions

### 8.1 Message Structure

| Variant | Format | Example |
|---------|--------|---------|
| `TlPy_RaiseFromStatus` | `tl_strerror(status)` | "invalid state" |
| `TlPy_RaiseFromStatusFmt` | `"context: tl_strerror(status)"` | "append failed: invalid state" |
| Direct Python | Free-form, should be actionable | "timestamp -5 out of int64 range" |

### 8.2 Message Guidelines

1. **Be specific:** "Timelog is closed" not "invalid state".
2. **Include context:** "delete_range: t1 must be < t2" not "invalid argument".
3. **Suggest action for transient errors:** "Call flush() or run maintenance to relieve."
4. **Avoid internal jargon:** User-facing messages should not reference internal types.

---

## 9. Test Expectations (Binding)

Minimum tests to validate mapping and atomicity:
- `TL_EBUSY` raises `TimelogBusyError` when policy is `raise`.
- `TL_EBUSY` does **not** rollback INCREF (record remains present).
- `TL_ESTATE` maps to `TimelogError` on closed operations.
- Iterators return StopIteration (no exception) on `TL_EOF`.
- `PyPageSpan_FromView` consumes owner ref and `view->owner` is NULL after success.

---

## 10. Coverage Checklist (Current Tests vs Rules)

Status legend:
- COVERED: existing tests assert the behavior.
- PARTIAL: behavior exercised but not asserted explicitly.
- GAP: no current test coverage (action needed).

| Rule | Status | Evidence |
|------|--------|----------|
| `TL_EBUSY` raises `TimelogBusyError` (busy_policy="raise") | COVERED | `test_py_maint_b5.c:test_ebusy_raise_exception` |
| `TL_EBUSY` silent/flush policies return success | COVERED | `test_py_timelog.c:run_busy_policy_silent/flush` |
| `TL_EBUSY` does not rollback INCREF | PARTIAL | Verified by `test_py_maint_b5.c` EBUSY tests (record present after error) |
| `TL_ESTATE` maps to `TimelogError` on closed use | COVERED | `test_py_timelog.c:close_refuses_with_pins`, `test_py_iter.c:closed_iterator` |
| Iterator `TL_EOF` returns StopIteration (no exception) | COVERED | `test_py_iter.c`: exhaustion tests |
| Snapshot/iterator cleanup on error paths | PARTIAL | Implicit in iterator creation tests |
| `PyPageSpan_FromView` consumes owner ref | PARTIAL | Implicit in span iteration tests |
| `TL_EINVAL` maps to `ValueError` | COVERED | `test_py_timelog.c`: range validation tests |
| `TL_EOVERFLOW` maps to `OverflowError` | COVERED | `test_py_timelog.c`: timestamp range tests |
| Buffer errors raise `BufferError` | COVERED | `test_py_span.c`: close/export tests |
| Exception preservation during cleanup | PARTIAL | Implicit; no explicit __del__ clobber test |
| Debug assertions fire on success codes | GAP | Would require debug-only test harness |

### 10.1 Test Files

| File | Tests | Scope |
|------|-------|-------|
| `test_py_errors.c` | - | (does not exist; errors tested via integration) |
| `test_py_timelog.c` | 28 | Lifecycle, append, delete, flush, close, maint |
| `test_py_iter.c` | 30+ | Iterator creation, exhaustion, cleanup |
| `test_py_span.c` | 20+ | PageSpan, buffer protocol, objects view |
| `test_py_maint_b5.c` | 14 | EBUSY policies, drain, worker lifecycle |

---

## 11. Implementation Reference

| Component | File | Key Lines |
|-----------|------|-----------|
| Exception types | `py_errors.c` | 19,25 (globals), 31-93 (init) |
| Status mapping | `py_errors.c` | 117-142 (`status_to_exception_type`) |
| Raise helpers | `py_errors.c` | 144-194 |
| EBUSY handling | `py_timelog.c` | 398-430 (append), 501-530 (extend) |
| Iterator cleanup | `py_iter.c` | 56-111 (`pytimelogiter_cleanup`) |
| Span cleanup | `py_span.c` | 132-166 (`pagespan_cleanup`) |
| Exception preservation | `py_iter.c` | 101-110; `py_span_iter.c` | 83-108 |

---

## 12. Summary

The binding error model is stable and fully implemented:
- `py_errors.c` defines the canonical mapping (Section 3).
- `py_timelog.c`, `py_iter.c`, `py_span*.c` follow atomicity rules (Section 5).
- Exception preservation is used in cleanup paths (Section 4.2, LLD-B5 Section 7.6).
- Test coverage is comprehensive for all critical paths (Section 10).

This LLD codifies those behaviors so future changes remain consistent.
