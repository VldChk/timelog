# LLD-B5: Maintenance + Threading Integration (CPython Binding Policy Layer)

Date: 2026-01-16
Status: Approved
Scope: CPython binding policy for maintenance, backpressure, GIL management, and shutdown
Phase: 5 (per `timelog_python_north_star_hld.md`)

This LLD specifies the Python-specific maintenance and threading integration layer.
It defines the policy choices that translate core engine behavior into safe,
predictable Python semantics.

---

## 1. Goals and Non-Goals

### 1.1 Goals

1. Predictable behavior: users understand manual vs background maintenance modes.
2. Correctness: no Python C-API calls without GIL; no premature DECREF; no UAF.
3. Core alignment: binding semantics match core exactly (no invented retries/rollback).
4. Safe shutdown: orderly close sequence prevents resource leaks and crashes.
5. Thread safety: clear contract for what is and is not safe across threads.

### 1.2 Non-Goals (V2 Scope Exclusions)

- No `maint_step()` exposure in Python (core has it; binding intentionally omits it).
- No core algorithm changes; this LLD covers binding policy only.
- No new Python API beyond current `PyTimelog` methods.
- No async/await integration (future scope).

---

## 2. Architecture Overview

### 2.1 Layer Boundaries

```
+---------------------------------------------------------------+
| Layer C: Python API (timelog.Timelog)                          |
| - Pure Python facade, docstrings, type hints                   |
+---------------------------------------------------------------+
| Layer B: CPython Binding (this LLD)                            |
| - GIL management, backpressure policy, drop queue              |
| - Files: py_timelog.c, py_handle.c                             |
+---------------------------------------------------------------+
| Layer A: Timelog V1 Core                                       |
| - tl_timelog.c, tl_sync.c (worker, threading primitives)       |
+---------------------------------------------------------------+
```

### 2.2 Key Files

| File | Purpose |
|------|---------|
| `bindings/cpython/src/py_timelog.c` | PyTimelog type, GIL release, backpressure |
| `bindings/cpython/src/py_handle.c` | Drop callback, drain queue, pin tracking |
| `bindings/cpython/include/timelogpy/py_handle.h` | Handle context types |
| `src/tl_timelog.c` | Core maintenance worker implementation |
| `src/internal/tl_sync.h` | Platform-agnostic threading primitives |
| `include/timelog/timelog.h` | Public core API (maint_start/stop/step) |

---

## 3. Configuration Surface

### 3.1 Initialization Kwargs

From `PyTimelog.__init__` (`py_timelog.c:71-130`):

| Parameter | Values | Default | Description |
|-----------|--------|---------|-------------|
| `maintenance` | `"disabled"`, `"background"` | `"disabled"` | Maintenance mode |
| `busy_policy` | `"raise"`, `"silent"`, `"flush"` | `"raise"` | TL_EBUSY handling |

Notes:
- `"background"` mode configures core to allow a worker, but worker is not auto-started.
- User must explicitly call `start_maintenance()` to spawn the worker thread.
- `"disabled"` mode requires external maintenance (not exposed in Python V1).

### 3.2 Public Methods

| Method | GIL Released | Drains | Description |
|--------|--------------|--------|-------------|
| `flush()` | Yes | Yes | Synchronous flush to L0 |
| `compact()` | Yes | Yes | Request compaction (manual mode needs external loop) |
| `start_maintenance()` | No | No | Start worker thread (background mode only) |
| `stop_maintenance()` | Yes | Yes | Stop worker thread (blocking join) |
| `close()` | Yes | Yes (force) | Orderly shutdown |

### 3.3 Operational Semantics by Mode

| Mode | Physical Reclamation | Drop Callbacks | Recommended Usage |
|------|---------------------|----------------|-------------------|
| `background` | Automatic via worker | Triggered by compaction | Default for most applications |
| `disabled` | None until close() | None until close() | Advanced: external maintenance loop |

**IMPORTANT for `disabled` mode:**

- `compact()` only *requests* compaction; no work is performed.
- Objects remain referenced until `close()` (which flushes but does not compact).
- Logical deletes hide data but do not release Python references.
- Use only when integrating with external maintenance scheduler.

---

## 4. Threading Model

### 4.1 Instance Thread Safety

Contract: a `Timelog` instance is NOT thread-safe.

- Single-writer only: do not call write APIs concurrently on the same instance.
- Iterators/spans are not thread-safe: do not share across threads.
- Background worker is internal and transparent to users.

### 4.2 Core Worker Thread

The core maintenance worker (`src/tl_timelog.c:1694-1858`):

- Runs flush and compaction on a dedicated native thread.
- State machine prevents races: `STOPPED -> RUNNING -> STOPPING -> STOPPED`.
- Worker thread is NOT a Python thread (no GIL, no PyThreadState).

Worker state transitions (text):
- STOPPED -> RUNNING (tl_maint_start)
- RUNNING -> STOPPING (tl_maint_stop initiated)
- STOPPING -> STOPPED (thread joined)

### 4.3 Lock Ordering (Critical Invariant)

From `CLAUDE.md` and `src/internal/tl_timelog_internal.h`:

```
maint_mu -> flush_mu -> writer_mu -> memtable.mu
```

Rules:
- Long-running builds must NOT hold `writer_mu`.
- `writer_mu` held only during short publication critical sections.
- Deferred signaling: set flag under `writer_mu`, signal under `maint_mu` after unlock.
- Thread join happens OUTSIDE `maint_mu` (prevents deadlock with worker).

---

## 5. GIL Management Strategy

### 5.1 GIL Release Boundaries

The binding releases the GIL only for potentially long-running operations:

| Operation | GIL Released | Code Location |
|-----------|--------------|---------------|
| `flush()` | Yes | `py_timelog.c:663-665` |
| `compact()` | Yes | `py_timelog.c:687-689` |
| `stop_maintenance()` | Yes | `py_timelog.c:746-748` |
| `close()` (maint_stop) | Yes | `py_timelog.c:303-305` |
| `close()` (tl_close) | Yes | `py_timelog.c:308-310` |
| `start_maintenance()` | No | Fast call, no blocking |
| `append/extend/delete` | No | Must hold GIL for INCREF |

### 5.2 GIL Release Pattern

```c
/* Standard pattern (from py_timelog.c) */
tl_status_t st;
Py_BEGIN_ALLOW_THREADS
st = tl_flush(self->tl);  /* or tl_compact, tl_maint_stop, tl_close */
Py_END_ALLOW_THREADS

/* Error mapping AFTER reacquiring GIL */
if (st != TL_OK && st != TL_EOF) {
    return TlPy_RaiseFromStatus(st);
}
```

### 5.3 GIL Rule for Writes

All write operations (`append`, `extend`, `delete_*`) hold the GIL throughout:

1. INCREF the object before calling core.
2. Call core (may return TL_EBUSY).
3. Handle backpressure policy.
4. DECREF only on true failure (NOT on TL_EBUSY).

Exception: if `busy_policy == "flush"` and TL_EBUSY occurs, the binding:
- Releases GIL during `tl_flush()` call.
- Reacquires GIL before returning.

---

## 6. Backpressure Policy (TL_EBUSY)

### 6.1 Core Semantics

When the sealed memrun queue is full, core returns `TL_EBUSY`.

Critical invariant: `TL_EBUSY` means the record/tombstone WAS inserted.

From `py_timelog.c:8-16`:
```
TL_EBUSY from write operations means record/tombstone WAS inserted
- Do NOT rollback INCREF on TL_EBUSY
- Do NOT retry on TL_EBUSY (would create duplicates)
```

### 6.2 Binding Policy Options

| Policy | Behavior | Use Case |
|--------|----------|----------|
| `"raise"` | Raise `TimelogBusyError` | Detect backpressure explicitly |
| `"silent"` | Return success | Fire-and-forget writes |
| `"flush"` | Flush then return success | Auto-relieve backpressure |

### 6.3 Implementation (`py_timelog.c:398-430`)

```c
if (st == TL_EBUSY) {
    switch (self->busy_policy) {
        case TL_PY_BUSY_RAISE:
            /* Record already inserted - raise but don't rollback */
            PyErr_SetString(TlPy_TimelogBusyError,
                "Record inserted but backpressure occurred.");
            return NULL;

        case TL_PY_BUSY_SILENT:
            /* Fall through to success */
            break;

        case TL_PY_BUSY_FLUSH:
            /* Flush to relieve pressure (GIL released) */
            Py_BEGIN_ALLOW_THREADS
            tl_flush(self->tl);
            Py_END_ALLOW_THREADS
            break;
    }
}
/* Record was inserted - do NOT decref on EBUSY */
```

**Flush Failure in FLUSH Policy:**

If `busy_policy="flush"` and `tl_flush()` fails (e.g., ENOMEM):

- The original record IS still inserted (EBUSY semantics preserved).
- The flush error is logged but NOT raised to user.
- Return success (record is safe; backpressure may persist).

Rationale: The user's data is safe; flush failure is transient and will
be retried by subsequent operations or background maintenance.

### 6.4 Batch Semantics

For `extend()` with multiple items:
- Items are inserted sequentially.
- On first `TL_EBUSY`, policy is applied.
- If policy is `"raise"`, exception raised after partial commit.
- Prior items remain committed (non-atomic batch).

---

## 7. Drop Callback and Deferred DECREF

### 7.1 Problem Statement

When compaction physically removes records, the binding must DECREF the Python
objects. The core drop callback runs on the maintenance thread without the GIL.

### 7.2 Solution: Deferred Drop Queue

Architecture (text):
- Maintenance thread (no GIL) calls `on_drop_handle()`, which pushes nodes to
  a lock-free Treiber stack (`retired_head`).
- Python thread (with GIL) calls `drain_retired()`, which pops nodes and runs
  `Py_DECREF`.

### 7.3 On-Drop Callback (`py_handle.c:196-253`)

Constraints (CRITICAL):
- Called on maintenance thread (NOT a Python thread).
- Does NOT hold the GIL.
- Must NOT call any Python C-API functions.
- Must NOT call back into Timelog APIs.
- Uses libc `malloc`, NOT Python allocator.

Implementation:
```c
void tl_py_on_drop_handle(void* on_drop_ctx, tl_ts_t ts, tl_handle_t handle)
{
    /* Allocate with libc malloc (no GIL, no Python allocator) */
    tl_py_drop_node_t* node = (tl_py_drop_node_t*)malloc(sizeof(*node));
    if (node == NULL) {
        /* Leak is safer than UAF */
        atomic_fetch_add(&ctx->alloc_failures, 1, memory_order_relaxed);
        return;
    }

    node->obj = tl_py_handle_decode(handle);
    node->ts = ts;

    /* Lock-free Treiber stack push (RELEASE semantics) */
    do {
        head = atomic_load(&ctx->retired_head, memory_order_relaxed);
        node->next = head;
    } while (!atomic_compare_exchange_weak(
        &ctx->retired_head, &head, node,
        memory_order_release, memory_order_relaxed));
}
```

### 7.4 Drain Implementation (`py_handle.c:267-372`)

Precondition: must hold GIL (asserted in debug builds).

Algorithm:
1. Check pins counter; if > 0 and not forced, skip drain.
2. Atomically claim entire queue (ACQ_REL exchange).
3. Iterate queue, calling `Py_DECREF` under GIL.
4. Respect batch limit (configurable, default unlimited).
5. If batch limit hit, re-attach remaining nodes.

Drain triggers:
- `pins_exit_and_maybe_drain()` when pins reaches 0.
- After `flush()`, `compact()`, `stop_maintenance()`.
- On `close()` with `force=1`.

### 7.5 Batch Drain Limit

Configurable via `ctx->drain_batch_limit`:
- `0` = unlimited (drain all).
- `> 0` = drain at most N nodes per call.

Purpose: prevents long GIL hold times during drain.

### 7.6 Exception Preservation Pattern

When drain runs `Py_DECREF`, user finalizers (`__del__`) may execute and could
set or clobber Python exception state. Per CPython docs, preserve exceptions:

```c
/* Pattern used in close() and dealloc paths */
PyObject *exc_type, *exc_value, *exc_tb;
PyErr_Fetch(&exc_type, &exc_value, &exc_tb);

tl_py_drain_retired(&self->handle_ctx, 1);  /* May run __del__ */

PyErr_Restore(exc_type, exc_value, exc_tb);
```

This ensures the caller's exception context survives drain operations.

---

## 8. Pin Tracking (Snapshot Safety)

### 8.1 Purpose

Pins prevent drain while snapshots are active. This ensures objects referenced
by active iterators/spans are not DECREF'd prematurely.

### 8.2 Protocol

```
pins_enter()                    /* Before snapshot_acquire */
snapshot_acquire() -> iterator operations -> snapshot_release()
pins_exit_and_maybe_drain()     /* After snapshot_release */
```

### 8.3 Implementation (`py_handle.c:118-175`)

```c
void tl_py_pins_enter(tl_py_handle_ctx_t* ctx)
{
    /* RELAXED: only needs visibility to same-thread exit */
    atomic_fetch_add(&ctx->pins, 1, memory_order_relaxed);
}

void tl_py_pins_exit_and_maybe_drain(tl_py_handle_ctx_t* ctx)
{
    /* RELEASE: ensures prior stores visible before pin decrement */
    uint64_t prev = atomic_fetch_sub(&ctx->pins, 1, memory_order_release);

    if (prev == 1) {
        /* Last pin released - safe to drain */
        tl_py_drain_retired(ctx, 0);
    }
}
```

### 8.4 Close-Time Force Drain

On `close()`, pins are checked first:
- If `pins > 0`: raise `TimelogError` (cannot close with active snapshots).
- If `pins == 0`: proceed with close, then force drain (`force=1`).

---

## 9. Shutdown Protocol

### 9.1 Close Sequence (`py_timelog.c:267-322`)

```
close()
[1] Check pins == 0 (if pins > 0: raise TimelogError)
[2] Mark closed = 1 (reentrancy guard)
[3] tl_maint_stop() (GIL released during blocking join)
[4] tl_close() (GIL released during engine close)
[5] Force drain retired: tl_py_drain_retired(ctx, force=1)
[6] Destroy handle context: tl_py_handle_ctx_destroy()
[7] Clear self->tl = NULL
```

### 9.2 Deallocation (Finalizer)

`PyTimelog_dealloc` is best-effort:

- If `pins == 0`: stop maintenance, close engine, drain, destroy context.
- If `pins > 0`: log debug warning, leak resources.

Rationale: finalizer cannot block waiting for user-held iterators/spans.

### 9.3 Idempotency

- `close()` is idempotent (multiple calls are safe).
- `stop_maintenance()` is idempotent.
- `start_maintenance()` is idempotent (TL_OK if already running).

### 9.4 Finalization Safety

During interpreter finalization (`Py_FinalizeEx`), calling into the C-API
may hang or crash. The binding follows a "leak over crash" policy:

- In `tp_dealloc`: if `Py_IsInitialized()` returns false, skip all cleanup.
- Do not attempt `tl_maint_stop()` or `tl_py_drain_retired()` during finalization.
- Resources will be reclaimed by process exit.

This aligns with PEP 788 guidance on finalization-safe extensions.

---

## 10. Metrics and Diagnostics

### 10.1 Available Diagnostics (properties)

Exposed as read-only properties on `Timelog`:

| Property | Description |
|----------|-------------|
| `retired_queue_len` | Current items in drop queue |
| `alloc_failures` | Malloc failures in on_drop callback |

### 10.2 Debug Support

In debug builds (`#ifndef NDEBUG`):
- `PyGILState_Check()` assertion in drain.

---

## 11. Platform Considerations

### 11.1 Threading Primitives (`src/internal/tl_sync.h`)

| Abstraction | Windows | POSIX |
|-------------|---------|-------|
| Mutex | SRWLock (slim, fast) | pthread_mutex |
| Condition | CONDITION_VARIABLE | pthread_cond |
| Thread | HANDLE + metadata | pthread_t |

### 11.2 Platform-Specific Notes

- Windows: uses SRWLock for mutexes (no recursive locking).
- POSIX: condition variables use `CLOCK_MONOTONIC` when available.
- Python: `Py_BEGIN_ALLOW_THREADS` / `Py_END_ALLOW_THREADS` are platform-agnostic.

---

## 12. Concurrency Contract for Users

### 12.1 Documented Guarantees

1. Single-writer: do not call write APIs concurrently on same instance.
2. Iterator safety: do not share iterator/span across threads.
3. Background transparency: worker affects latency, not correctness.
4. GIL release calls: during `flush`/`compact`/`stop`/`close`, no other thread
   should touch the instance.

### 12.2 Undefined Behavior

- Concurrent writes to same instance.
- Sharing iterator across threads.
- Calling methods after `close()` (raises `TimelogError`).

### 12.3 GIL-Release Concurrency Contract

When the GIL is released (during flush/compact/stop/close), other Python
threads CAN run and potentially call methods on the same Timelog instance.

**Rule:** While any GIL-releasing method is executing, no other method
may be called on the same instance from any thread.

**Enforcement:** Undefined behavior. The binding does NOT implement an
API mutex. Users must ensure single-threaded access to each instance.

**Rationale:** Adding a per-instance lock would:

1. Add overhead to every method call
2. Create deadlock risk with GIL interactions
3. Contradict the documented "not thread-safe" contract

Users requiring multi-threaded access should use external synchronization
or create one Timelog instance per thread.

---

## 13. Test Coverage

### 13.1 Existing Tests (`bindings/cpython/tests/test_py_timelog.c`)

| Test | Coverage |
|------|----------|
| `start_maintenance_background` | Worker start in background mode |
| `start_maintenance_disabled_fails` | Reject start in disabled mode |
| `stop_maintenance_idempotent` | Multiple stop calls safe |
| `busy_policy_flush` | Flush on EBUSY |
| `busy_policy_raise` | Exception on EBUSY |
| `busy_policy_silent` | Silent return on EBUSY |
| `flush_succeeds` | Basic flush |
| `compact_succeeds` | Basic compact request |
| `close_refuses_with_pins` | Pin check enforcement |

### 13.2 Recommended Additions

- Stress test: concurrent start/stop cycles.
- Drain batch limit verification.
- Metrics accuracy after heavy churn.
- Force drain on close with retired queue.

---

## 14. Implementation Checklist

### 14.1 Invariants to Preserve

- [ ] `TL_EBUSY` means record WAS inserted (no retry, no DECREF rollback).
- [ ] GIL released only for: flush, compact, stop, close.
- [ ] On-drop callback: no GIL, no Python C-API, libc malloc only.
- [ ] Drain requires GIL (asserted in debug).
- [ ] Pin check before close; refuse if pins > 0.
- [ ] Lock ordering: `maint_mu -> flush_mu -> writer_mu -> memtable.mu`.
- [ ] Worker thread join happens OUTSIDE `maint_mu`.

### 14.2 Code Locations

| Invariant | File | Lines |
|-----------|------|-------|
| EBUSY semantics | `py_timelog.c` | 8-16, 398-430 |
| GIL release | `py_timelog.c` | 303-310, 663-665, 687-689, 746-748 |
| On-drop callback | `py_handle.c` | 178-188, 196-253 |
| Drain implementation | `py_handle.c` | 267-372 |
| Pin tracking | `py_handle.c` | 118-175 |
| Close sequence | `py_timelog.c` | 267-322 |
| Worker state machine | `tl_timelog.c` | 1694-1776 |

---

## 15. Summary

This LLD codifies the maintenance and threading integration for the CPython binding:

1. Predictable modes: manual vs background with explicit control.
2. Safe GIL management: release only for blocking operations.
3. Correct backpressure: EBUSY means inserted; no retry/rollback.
4. Deferred drops: lock-free queue, GIL-safe drain.
5. Orderly shutdown: pin check, stop worker, close engine, force drain.

The implementation is complete and production-ready. This LLD serves as the
specification for future maintenance and verification.

---

## Appendix A: Sequence Sketches

### A.1 Background Maintenance Lifecycle (text)

- `Timelog(maintenance="background")` -> `tl_open(BACKGROUND)` (worker not started)
- `start_maintenance()` -> `tl_maint_start()` (spawn worker)
- ... writes ...
- `stop_maintenance()` -> `tl_maint_stop()` (signal shutdown, join thread)
- `drain_retired()`

### A.2 Drop Callback Flow (text)

- Core compaction calls `on_drop_handle(h)`
- Binding allocates node, decodes handle, pushes to Treiber stack
- When pins drop to zero: `drain_retired()` -> claim queue -> `Py_DECREF` -> `free`

---

## Appendix B: Error Codes

| Core Status | Binding Exception | When |
|-------------|-------------------|------|
| `TL_OK` | (success) | Operation completed |
| `TL_EBUSY` | `TimelogBusyError` or silent | Backpressure (record inserted) |
| `TL_ESTATE` | `TimelogError` | Invalid state (closed, wrong mode) |
| `TL_EINVAL` | `ValueError` | Invalid parameter |
| `TL_ENOMEM` | `MemoryError` | Allocation failed |
| `TL_EINTERNAL` | `TimelogError` | Internal error (thread creation failed) |
