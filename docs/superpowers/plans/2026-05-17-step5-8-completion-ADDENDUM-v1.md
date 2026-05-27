# Plan Addendum v1 — Hostile Review Corrections

> **Companion to** `2026-05-17-step5-8-completion.md`. Every original Task referenced here is **superseded** by the corresponding section below. Where the original task is correct as-is, this addendum does not mention it.

Three independent hostile reviews (CPython free-threading semantics; lock-ordering / deadlock; test rigor / CI) surfaced 7 critical-severity defects in the v1 plan. This addendum collects every fix as a concrete code change. Execution must follow this addendum where it conflicts with the v1 plan.

## Summary of critical defects

| # | Defect | Reviewer | Fix landing |
|---|---|---|---|
| A1 | `TL_PY_MUTEX_INIT(m) ((void)(m))` cannot be compared `!= 0` — does not compile | Free-threading | Task 5A.1 — rework macro |
| A2 | `_PyThreadState_UncheckedGet` is private API; `ts->interp` is opaque struct deref | Free-threading | Task 5A.7 — use `PyThreadState_GetUnchecked` (public 3.13+) + `PyThreadState_GetInterpreter` |
| A3 | `tl_py_drain_retired` calls `tl_py_live_note_drop` per node; after `live_lock`, this self-deadlocks PyMutex on `__del__` reentry via cyclic GC | All three | Task 5A.4 — restructure drain to collect node→obj pairs, drop L2, then iterate Py_DECREF + live_note_drop in a single batched re-acquire |
| A4 | `self->handle_ctx` and `self->engine_ctx` read outside L1 in `append`/`extend`/etc. races against close-writer | Lock-ordering | Task 5A.8 — also promote `handle_ctx` and `engine_ctx` to `_Atomic` pointers with acquire/release |
| A5 | `tl_py_handle_ctx_traverse` under L2 may ABBA with visit callbacks acquiring per-object internal mutexes | Free-threading + lock-ordering | Task 5A.6 — collect-then-visit: snapshot live-entry pointers under L2 into a local array, release L2, then visit |
| A6 | Critical sections do NOT pin the object via refcount; pure C-internal callers can hit UAF | Lock-ordering | Compat macro doc + audit: every internal CS entry path must hold a Python strong ref. Document in `py_compat.h` |
| A7 | Stress tests use `pytestmark = pytest.mark.skipif(...)` — invisible to `-m freethreading` CI selector | Test rigor | Task 5B.1 — `pytestmark = [pytest.mark.freethreading, pytest.mark.skipif(...)]` |
| A8 | No TSan-on-3.14t CI job; current TSan leg runs 3.13 regular | Test rigor | New task: 8.5 — concrete YAML for `thread-sanitizer-freethreaded` in `sanitizers.yml` |
| A9 | Iteration counts (10-50) far too low for race surfacing | Test rigor | All Phase 5B/5C tests — use `compat_runtime.short_stress` knob with long/short defaults of 5000 / 200 |
| A10 | §7.5 concurrent read stress and §7.9 reopen test never added by plan | Test rigor | New Tasks 5C.4 (§7.5) and 5C.5 (§7.9) |
| A11 | cp314t wheel built but never proven to import | Test rigor | Task 8.2 — concrete `python3.14t -c "import timelog"` smoke after install |
| A12 | freethreading leg has `stress-tests: "0"`; `LEG_CONFIG` does not include the new file | Test rigor | Task 5C.3 — flip to `"1"`; add `python/tests/test_freethreaded_stress.py` to LEG_CONFIG paths |
| A13 | Atomic store of `closed=1` + plain store `tl=NULL` not ordered; readers can see stale state | Free-threading | Task 5A.8 — make `self->tl` `_Atomic(tl_timelog_t*)` with explicit ordering |
| A14 | `objectsviewiter_next` reads `span->h[my_idx]` and `span->len` outside the span's CS | Lock-ordering | Task 5B.4 — use `TL_PY_OBJ_LOCK2(self, span)` or strong-ref the owner directly |
| A15 | `iternext` engine call outside L4 means cleanup can free iter mid-call regardless of CS | Lock-ordering | Task 5B.2 — accept the spec contract (same-iter concurrent close is undefined); stress test asserts "no crash" not "no errors" |
| A16 | `PyMem_Malloc` inside L2 risks allocator-lock ordering issue | Free-threading | Task 5A.5 — use libc `malloc/free` for the snapshot array |
| A17 | "GIL-coincidence" tests have no regression-detection power | Test rigor | Tests use pthread-based contention + invariant assertions (live_len, refcount checks) that fail deterministically on missed lock |

## Revised Task 5A.1 — locking compat macros (replaces v1 Task 5A.1)

**Files:** Modify `bindings/cpython/include/timelogpy/py_compat.h`

- [ ] **Step 1: Read the current py_compat.h** (same as v1)

- [ ] **Step 2: Append revised compat macros**

The corrections from A1, A6, and partial A2:

```c
/*===========================================================================
 * Mutex compat — PyMutex (3.13+) vs PyThread_type_lock fallback (3.12)
 *
 * Both branches expose:
 *   tl_py_mutex_t           opaque storage type
 *   tl_py_mutex_init(m)     returns 0 on success, -1 on failure
 *   tl_py_mutex_deinit(m)   releases resources (NULL-safe)
 *   TL_PY_MUTEX_LOCK(m)     blocking acquire
 *   TL_PY_MUTEX_UNLOCK(m)   release
 *
 * Memory model:
 *   PyMutex acquire = full memory barrier; release pairs with acquire on
 *   any other thread's acquire. Same for the PyThread_type_lock fallback.
 *
 * Failure model:
 *   PyMutex is statically zero-initializable so init never fails on 3.13+.
 *   The fallback allocates a PyThread_type_lock and can fail; callers MUST
 *   check the int return.
 *===========================================================================*/

#include <pythread.h>

#if PY_VERSION_HEX >= 0x030D0000

typedef PyMutex tl_py_mutex_t;

static inline int tl_py_mutex_init(tl_py_mutex_t* m) {
    /* PyMutex is statically zero-initializable. Be explicit. */
    PyMutex zero = {0};
    *m = zero;
    return 0;
}
static inline void tl_py_mutex_deinit(tl_py_mutex_t* m) {
    (void)m;  /* PyMutex needs no explicit teardown */
}
#define TL_PY_MUTEX_LOCK(m)   PyMutex_Lock(m)
#define TL_PY_MUTEX_UNLOCK(m) PyMutex_Unlock(m)

#else

typedef PyThread_type_lock tl_py_mutex_t;

static inline int tl_py_mutex_init(tl_py_mutex_t* m) {
    *m = PyThread_allocate_lock();
    return *m == NULL ? -1 : 0;
}
static inline void tl_py_mutex_deinit(tl_py_mutex_t* m) {
    if (*m != NULL) {
        PyThread_free_lock(*m);
        *m = NULL;
    }
}
#define TL_PY_MUTEX_LOCK(m)   ((void)PyThread_acquire_lock(*(m), WAIT_LOCK))
#define TL_PY_MUTEX_UNLOCK(m) PyThread_release_lock(*(m))

#endif

/*===========================================================================
 * Critical-section compat — Py_BEGIN_CRITICAL_SECTION (3.13+)
 *
 * IMPORTANT INVARIANT (PEP 703 contract):
 *   Critical sections do NOT pin their target via refcount. The caller MUST
 *   already hold a strong Python reference to the target object for the full
 *   duration of TL_PY_OBJ_LOCK ... TL_PY_OBJ_UNLOCK. For methods invoked via
 *   Python's bound-method dispatch this is automatic (the dispatch holds an
 *   implicit ref on `self`). For C-internal callers (factories, callbacks),
 *   an explicit Py_INCREF before TL_PY_OBJ_LOCK is REQUIRED.
 *
 * On 3.12 the macros are no-ops because the GIL serializes object access.
 * Subinterpreter isolation on 3.12 (Layer A) keeps each PyTimelog object in
 * exactly one interpreter, so cross-interpreter access cannot happen even
 * without these macros.
 *===========================================================================*/

#if PY_VERSION_HEX >= 0x030D0000
#define TL_PY_OBJ_LOCK(obj)   Py_BEGIN_CRITICAL_SECTION((PyObject*)(obj))
#define TL_PY_OBJ_UNLOCK()    Py_END_CRITICAL_SECTION()
#define TL_PY_OBJ_LOCK2(a, b) Py_BEGIN_CRITICAL_SECTION2((PyObject*)(a), (PyObject*)(b))
#define TL_PY_OBJ_UNLOCK2()   Py_END_CRITICAL_SECTION2()
#else
/* GIL-serialized fallback. (void) casts kept to suppress unused-arg warnings. */
#define TL_PY_OBJ_LOCK(obj)   do { (void)(obj);
#define TL_PY_OBJ_UNLOCK()    } while (0)
#define TL_PY_OBJ_LOCK2(a, b) do { (void)(a); (void)(b);
#define TL_PY_OBJ_UNLOCK2()   } while (0)
#endif
```

- [ ] **Step 3: Build to confirm syntax**

```bash
cmake --build build-step2 -j$(nproc) 2>&1 | tail -10
```

Expected: clean (no new errors).

- [ ] **Step 4: Commit**

```bash
git add bindings/cpython/include/timelogpy/py_compat.h
git commit -m "feat(layer-b): PyMutex + critical-section compat macros with documented invariants"
```

## Revised Task 5A.3 — handle_ctx init/destroy (replaces v1 Task 5A.3)

The init code uses the int-returning `tl_py_mutex_init` (fixed in revised 5A.1):

```c
tl_status_t tl_py_handle_ctx_init(tl_py_handle_ctx_t* ctx, uint32_t drain_batch_limit)
{
    /* ... existing atomic_init calls ... */

    if (tl_py_mutex_init(&ctx->live_lock) != 0) {
        return TL_ENOMEM;
    }

    /* ... existing tail ... */
    return TL_OK;
}
```

Destroy uses the NULL-safe deinit:

```c
void tl_py_handle_ctx_destroy(tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL) return;
    tl_py_mutex_deinit(&ctx->live_lock);
    /* ... existing free of live_entries ... */
}
```

The order matters: `live_lock` is deinit'd before `live_entries` is freed, because no thread should be holding it at this point (refcount has dropped to zero — the invariant from H6 of the lock-ordering review). Document the invariant inline.

## Revised Task 5A.4 — live_note_insert + drain refactor (replaces v1 Task 5A.4)

The key correction (A3): `tl_py_drain_retired` must NOT call `tl_py_live_note_drop` per-node while reacquiring `live_lock` each time. Instead, batch.

### Step 1: Wrap insert/drop with live_lock (unchanged from v1, with assertion fix)

```c
tl_status_t tl_py_live_note_insert(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
    if (ctx == NULL || obj == NULL) return TL_EINVAL;
    /* Spec §5.5: must be on an attached thread state, but we no longer
     * insist GIL is held — live_lock provides the actual ordering. */
    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    tl_status_t st = tl_py_live_ensure(ctx, 1);
    if (st != TL_OK) {
        ctx->live_tracking_failed = 1;
        TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
        return st;
    }
    /* ... existing insert body verbatim, but ALL inside the lock ... */
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
    return TL_OK;
}

void tl_py_live_note_drop(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
    if (ctx == NULL || obj == NULL || ctx->live_cap == 0) return;
    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    /* ... existing drop body verbatim, but inside the lock ... */
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
}
```

### Step 2: Restructure `tl_py_drain_retired` to batch live_note_drops

```c
size_t tl_py_drain_retired(tl_py_handle_ctx_t* ctx, int force)
{
    if (ctx == NULL) return 0;
    if (atomic_flag_test_and_set_explicit(&ctx->drain_guard, memory_order_acquire))
        return 0;

    size_t total = 0;

    /* Phase 1: claim the retired list atomically (existing logic). */
    uint64_t pins = atomic_load_explicit(&ctx->pins, memory_order_acquire);
    if (pins != 0 && !force) goto out;

    tl_py_drop_node_t* list = atomic_exchange_explicit(
        &ctx->retired_head, NULL, memory_order_acq_rel);
    if (list == NULL) goto out;

    /* Phase 2: build a flat array of (obj, node) pairs without touching
     *          live_lock or Py_DECREF. Free node memory only AFTER we
     *          have batched live_note_drop and DECREF'd outside locks. */
    /* Snapshot length first. */
    size_t n = 0;
    for (tl_py_drop_node_t* p = list; p != NULL; p = p->next) n++;

    PyObject** batch = NULL;
    if (n > 0) {
        batch = (PyObject**)malloc(n * sizeof(PyObject*));
        if (batch == NULL) {
            /* OOM fallback: walk one at a time, decref under no lock,
             * call live_note_drop with its own lock. Each iteration is
             * effectively a one-element collect-unlock-execute. This
             * preserves correctness at the cost of throughput. */
            tl_py_drop_node_t* p = list;
            while (p != NULL) {
                tl_py_drop_node_t* nxt = p->next;
                PyObject* obj = p->obj;
                free(p);
                tl_py_live_note_drop(ctx, obj);
                Py_DECREF(obj);
                total++;
                p = nxt;
            }
            goto record;
        }
    }

    /* Build array + free nodes (no Py_DECREF, no live_lock). */
    size_t idx = 0;
    while (list != NULL) {
        tl_py_drop_node_t* nxt = list->next;
        batch[idx++] = list->obj;
        free(list);
        list = nxt;
    }

    /* Phase 3: take live_lock ONCE, drop each in the table. */
    if (idx > 0) {
        TL_PY_MUTEX_LOCK(&ctx->live_lock);
        for (size_t i = 0; i < idx; i++) {
            /* inline the drop body (we already hold the lock) */
            tl_py_live_drop_locked(ctx, batch[i]);  /* helper that skips the lock */
        }
        TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
    }

    /* Phase 4: DECREF outside all locks. __del__ reentry is safe here
     *          because no internal lock is held. */
    for (size_t i = 0; i < idx; i++) {
        Py_DECREF(batch[i]);
    }
    free(batch);
    total = idx;

record:
    atomic_fetch_add_explicit(&ctx->drained_count, total, memory_order_relaxed);

out:
    atomic_flag_clear_explicit(&ctx->drain_guard, memory_order_release);
    return total;
}
```

Extract a static helper `tl_py_live_drop_locked(ctx, obj)` that contains the existing drop body sans lock — it's called from both `tl_py_live_note_drop` (which acquires the lock) and the new batched drain (which holds it across the loop).

### Step 3: Concurrent stress test (unchanged from v1 but stronger invariant)

The test stays as v1 wrote it but the invariant `ASSERT_EQ(ctx->live_len, 0)` is now the actual proof that no insert was lost.

### Step 4: Commit

```bash
git add bindings/cpython/src/py_handle.c bindings/cpython/tests/test_py_handle.c
git commit -m "feat(layer-b): batched drain with collect/unlock/execute"
```

## Revised Task 5A.5 — live_release_all (correction A16)

Use libc `malloc/free` (not `PyMem_*`) for the snapshot array, matching the existing `free(ctx->live_entries)` pattern in the same file. Rationale: `PyMem_Malloc` can take an internal allocator lock; combined with `live_lock`-held during the malloc call, this risks an unaudited lock-ordering chain. libc malloc never reaches back into the binding.

The body of the refactor stays as v1 wrote it; only `PyMem_Malloc → malloc` and `PyMem_Free → free`. The OOM fallback path documented as "Acceptable because allocation already failed" is **REPLACED** with: leak deliberately + log to stderr in debug builds (matching the spec's hard invariant that no Py_DECREF happens under any internal lock — even the fallback path).

```c
void tl_py_live_release_all(tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL) return;

    PyObject** refs = NULL;
    size_t total = 0;

    /* Phase 1: collect under live_lock. */
    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    if (ctx->live_entries == NULL) {
        TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
        return;
    }
    size_t cap_needed = ctx->live_len;
    if (cap_needed > 0) {
        refs = (PyObject**)malloc(cap_needed * sizeof(PyObject*));
        if (refs == NULL) {
            /* Spec hard invariant: NO Py_DECREF under live_lock. Leak the
             * entries (they're not freed; the ctx is being destroyed). The
             * payload PyObjects will be unreferenced from this side but
             * remain in their interpreter's GC until interpreter teardown. */
            ctx->live_tracking_failed = 1;
            /* Walk just to zero the entries so destroy() doesn't double-leak. */
            for (size_t i = 0; i < ctx->live_cap; i++) {
                tl_py_live_entry_t* e = &ctx->live_entries[i];
                e->obj = NULL; e->count = 0; e->state = TL_PY_LIVE_EMPTY;
            }
            free(ctx->live_entries);
            ctx->live_entries = NULL;
            ctx->live_cap = 0;
            ctx->live_len = 0;
            ctx->live_tombstones = 0;
            TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
#ifndef NDEBUG
            fprintf(stderr,
                "tl_py_live_release_all: OOM during snapshot, leaked refs\n");
#endif
            return;
        }
    }
    for (size_t i = 0; i < ctx->live_cap; i++) {
        tl_py_live_entry_t* e = &ctx->live_entries[i];
        if (e->state == TL_PY_LIVE_FULL) {
            for (uint64_t c = e->count; c > 0; c--) {
                refs[total++] = e->obj;
            }
            e->obj = NULL; e->count = 0; e->state = TL_PY_LIVE_EMPTY;
        }
    }
    free(ctx->live_entries);
    ctx->live_entries = NULL;
    ctx->live_cap = 0;
    ctx->live_len = 0;
    ctx->live_tombstones = 0;
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);

    /* Phase 2: execute outside all locks. */
    for (size_t i = 0; i < total; i++) {
        Py_DECREF(refs[i]);
    }
    free(refs);
}
```

## Revised Task 5A.6 — collect-then-visit in traverse (correction A5)

```c
int tl_py_handle_ctx_traverse(tl_py_handle_ctx_t* ctx, visitproc visit, void* arg)
{
    if (ctx == NULL || visit == NULL) return 0;

    PyObject** snap = NULL;
    size_t snap_n = 0;

    /* Phase 1: snapshot live-entry pointers under live_lock. */
    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    if (ctx->live_entries != NULL && ctx->live_len > 0) {
        snap = (PyObject**)malloc(ctx->live_len * sizeof(PyObject*));
        if (snap == NULL) {
            /* OOM fallback: visit under lock, accepting the small risk of
             * visit-callback reentry. Real fix requires the caller to
             * pre-allocate, but tp_traverse signature doesn't allow that. */
            for (size_t i = 0; i < ctx->live_cap; i++) {
                tl_py_live_entry_t* e = &ctx->live_entries[i];
                if (e->state == TL_PY_LIVE_FULL && e->obj != NULL) {
                    int st = visit(e->obj, arg);
                    if (st != 0) {
                        TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
                        return st;
                    }
                }
            }
            TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
            goto retired;
        }
        for (size_t i = 0; i < ctx->live_cap; i++) {
            tl_py_live_entry_t* e = &ctx->live_entries[i];
            if (e->state == TL_PY_LIVE_FULL && e->obj != NULL) {
                snap[snap_n++] = e->obj;
            }
        }
    }
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);

    /* Phase 2: visit outside live_lock. */
    for (size_t i = 0; i < snap_n; i++) {
        int st = visit(snap[i], arg);
        if (st != 0) {
            free(snap);
            return st;
        }
    }
    free(snap);

retired:
    /* Phase 3: traverse retired stack (lock-free, atomic loads only). */
    tl_py_drop_node_t* retired = atomic_load_explicit(
        &ctx->retired_head, memory_order_acquire);
    while (retired != NULL) {
        if (retired->obj != NULL) {
            int st = visit(retired->obj, arg);
            if (st != 0) return st;
        }
        retired = retired->next;
    }
    return 0;
}
```

Memory ordering note: the retired-stack walk uses `memory_order_acquire` on `retired_head` and reads `->next` without atomic. The producer (`tl_py_on_drop_handle`) uses CAS with `memory_order_release`. The release-acquire pair guarantees that nodes published before the load are visible. **However**, between the load and the walk, another thread can call `tl_py_drain_retired` which `atomic_exchange`'s the head to NULL and `free()`s the nodes. Walking freed nodes is UAF.

This is a pre-existing free-threading hazard the v1 plan did not address. The fix: GC's `tp_traverse` is documented to require exclusive access (CPython's free-threaded GC stops the world). Verify against CPython 3.14 sources during execution; if the documentation doesn't guarantee it, snapshot the retired list under a separate atomic exchange (claim-then-restore pattern).

## Revised Task 5A.7 — public attached-thread-state API (correction A2)

```c
static int tl_py_attached_to_interp(const tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL || !Py_IsInitialized()) return 0;
#if PY_VERSION_HEX >= 0x030D0000
    /* Public API since 3.13 — does not assume GIL is held. */
    PyThreadState* ts = PyThreadState_GetUnchecked();
    if (ts == NULL) return 0;
    return PyThreadState_GetInterpreter(ts) == ctx->interp;
#else
    /* 3.12: PyGILState_Check is acceptable (no free-threaded build exists).
     * Interpreter equality via PyInterpreterState_Get(). */
    if (!PyGILState_Check()) return 0;
    return PyInterpreterState_Get() == ctx->interp;
#endif
}
```

The `interp` capture at ctx init can stay as `PyInterpreterState_Get()` (called from a known-attached path).

## Revised Task 5A.8 — atomic `closed` + `tl` + `engine_ctx` + `handle_ctx` (correction A4 + A13)

The v1 plan only promoted `closed`. The lock-ordering review identified that `tl`, `engine_ctx`, and `handle_ctx` are also read outside L1 in hot paths (`append`, `extend`, `delete_range`). Promote all four to atomic pointers / values.

Struct change:

```c
typedef struct {
    PyObject_HEAD

    /* All four are atomic mirrors. Writes happen under core_lock with
     * memory_order_release; reads from anywhere may use memory_order_acquire. */
    _Atomic(uint8_t)                closed;
    _Atomic(tl_timelog_t*)          tl;
    _Atomic(tl_py_engine_ctx_t*)    engine_ctx;
    _Atomic(tl_py_handle_ctx_t*)    handle_ctx;

    /* ... rest unchanged ... */
} PyTimelog;
```

Reads at call sites:

```c
tl_timelog_t* tl = atomic_load_explicit(&self->tl, memory_order_acquire);
tl_py_handle_ctx_t* hctx = atomic_load_explicit(&self->handle_ctx, memory_order_acquire);
if (tl == NULL || hctx == NULL) {
    /* closed */
    ...
}
```

Writes under core_lock:

```c
TL_PY_LOCK(self);
atomic_store_explicit(&self->closed, 1, memory_order_release);
atomic_store_explicit(&self->tl, NULL, memory_order_release);
...
TL_PY_UNLOCK(self);
```

`CHECK_CLOSED` and friends already snapshot once; just change to atomic_load.

`PyTimelog_get_closed` (M5 from lock-ordering): change to `atomic_load_explicit(&self->closed, memory_order_acquire)`.

The `tl_py_handle_ctx_incref` invariant becomes: callers MUST `incref` the ctx they captured atomically before releasing the lock that snapshotted it, OR document that the capture is borrowed and only valid while no concurrent close has run. The simplest contract: every method that reads `self->handle_ctx` atomically and then calls into the ctx without taking L1 first **must** also `tl_py_handle_ctx_incref` before use and decref after.

This raises the cost of fast-path `append`/`extend` — two atomic ops per call. Acceptable: this is the price of free-threaded safety on these paths.

## Revised Task 5B.1 — PageSpan critical sections (correction A6 + A7)

Documentation correction (A6): add a comment above each critical-section site:

```c
/* CS contract: caller holds a strong Python ref to `self` (method dispatch
 * holds one implicitly for Python-callable methods). Internal C callers
 * must Py_INCREF before TL_PY_OBJ_LOCK. */
TL_PY_OBJ_LOCK(self);
```

Marker fix (A7): in `python/tests/test_freethreaded_stress.py`, the file-scope marker becomes:

```python
import pytest

pytestmark = [
    pytest.mark.freethreading,
    pytest.mark.skipif(
        not _is_free_threaded(),
        reason="Free-threaded stress requires Py_GIL_DISABLED=1 build",
    ),
]
```

Iteration count via short-stress (A9 + A17): tests use the conftest fixture:

```python
def test_close_overlapped_with_buffer_export_and_property_reads(self, compat_runtime):
    iters = 200 if compat_runtime.short_stress else 5_000
    ...
```

## Revised Task 5B.2 — iter close-vs-iternext stress (correction A15)

The spec accepts that same-iter concurrent close is undefined for the user contract, but binding must not crash. Reformulate the test:

```python
def test_iter_exhaustion_overlapped_with_close_no_crash(self, compat_runtime):
    """Concurrent exhaust + close on same iter: must not crash, may raise."""
    from timelog import Timelog
    iters = 50 if compat_runtime.short_stress else 1_000
    log = Timelog(maintenance="disabled")
    try:
        log.extend([(i, str(i)) for i in range(256)])
        log.flush()
        crashes: list[BaseException] = []
        for _ in range(iters):
            it = log.all()
            def exhaust():
                try:
                    for _ in it: pass
                except (RuntimeError, ValueError):
                    pass  # iterator closed mid-iteration — expected
                except BaseException as e:
                    crashes.append(e)
            def closer():
                try:
                    it.close()
                except (RuntimeError, ValueError):
                    pass
                except BaseException as e:
                    crashes.append(e)
            t1 = threading.Thread(target=exhaust)
            t2 = threading.Thread(target=closer)
            t1.start(); t2.start()
            t1.join(); t2.join()
        assert not crashes, f"unexpected crashes: {crashes!r}"
    finally:
        log.close()
```

Assertions are about no-crash + only expected exceptions. Same pattern for Task 5B.3.

## Revised Task 5B.4 — objectsviewiter (correction A14)

The iter must take the span's CS, not its own, when reading the underlying buffer:

```c
static PyObject* objectsviewiter_next(PyObject* self_obj)
{
    PyPageSpanObjectsViewIter* self = (PyPageSpanObjectsViewIter*)self_obj;
    PyPageSpanObjectsView* view;
    PyPageSpan* span;
    Py_ssize_t my_idx;
    tl_handle_t h;
    int eof = 0;

    /* CS contract: bound-method dispatch holds a strong ref on self. */

    /* Snapshot iter index + locate span under self's CS. */
    TL_PY_OBJ_LOCK(self);
    if (self->view == NULL) {
        TL_PY_OBJ_UNLOCK();
        return NULL;
    }
    view = self->view;
    span = view->span;
    Py_INCREF(span);  /* pin for the span-CS read below */
    my_idx = self->index;
    TL_PY_OBJ_UNLOCK();

    /* Read span buffer under the SPAN's CS, so close() cannot null `h`
     * out from under us. */
    TL_PY_OBJ_LOCK(span);
    if (span->closed || my_idx >= span->len) {
        eof = 1;
    } else {
        h = span->h[my_idx];
    }
    TL_PY_OBJ_UNLOCK();

    if (eof) {
        Py_DECREF(span);
        return NULL;
    }

    /* Advance our own cursor under self's CS. */
    TL_PY_OBJ_LOCK(self);
    /* Re-validate: another thread may have closed self between releases */
    if (self->view == NULL) {
        TL_PY_OBJ_UNLOCK();
        Py_DECREF(span);
        return NULL;
    }
    self->index++;
    TL_PY_OBJ_UNLOCK();

    Py_DECREF(span);

    PyObject* obj = tl_py_handle_decode(h);
    Py_INCREF(obj);
    return obj;
}
```

The double-lock with explicit Py_INCREF/DECREF on `span` ensures the span outlives our read of `h[my_idx]`.

## New Task 5C.3 — corrected LEG_CONFIG + stress + strict markers

In `demo/ci/run_compat_baseline.py`:

```python
LEG_CONFIG = {
    "subinterpreters": {
        "marker": "subinterpreters",
        "paths": ["python/tests/test_subinterpreters.py"],
    },
    "freethreading": {
        "marker": "freethreading",
        "paths": [
            "python/tests/test_free_threading.py",
            "python/tests/test_freethreaded_stress.py",   # NEW
        ],
    },
    "stress": {
        "marker": "stress",
        "paths": ["python/tests/test_compat_stress.py"],
    },
}
```

Pytest invocation adds `--strict-markers`:

```python
args = [
    "-q", "-rA", "--strict-markers",
    "-m", config["marker"],
    *config["paths"],
]
```

In `compatibility-baseline-pr.yml` and `compatibility-baseline-main.yml`, flip the freethreading leg's stress switch:

```yaml
- legs: freethreading
  python-version: "3.14"
  python-tag: "3.14t"
  short-stress: "0"      # full-size run
  stress-tests: "1"      # enable stress
```

Add a setup-python sanity check immediately after the setup step:

```yaml
- name: Verify free-threaded Python
  if: matrix.python-tag == '3.14t'
  run: |
    python -c "import sysconfig; assert sysconfig.get_config_var('Py_GIL_DISABLED') == 1, 'expected Py_GIL_DISABLED build'"
```

## New Task 5C.4 — §7.5 concurrent read stress

Add to `test_freethreaded_stress.py`:

```python
class TestConcurrentReadStress:
    """§7.5 — N readers + 1 writer (externally serialized)."""

    def test_n_readers_one_writer_no_corruption(self, compat_runtime):
        from timelog import Timelog
        n_readers = 4
        iters = 100 if compat_runtime.short_stress else 2_000
        log = Timelog(maintenance="background", maintenance_wakeup_ms=1)
        errors: list[BaseException] = []
        stop = threading.Event()

        def writer():
            try:
                i = 0
                while not stop.is_set():
                    log.append(i, str(i))
                    i += 1
                    if i % 256 == 0:
                        log.flush()
            except BaseException as e:
                errors.append(e)

        def reader(seed):
            import random
            rng = random.Random(seed)
            try:
                for _ in range(iters):
                    op = rng.choice(["all", "views", "page_spans", "slice"])
                    if op == "all":
                        it = log.all()
                        consumed = sum(1 for _ in it)
                        assert consumed >= 0
                    elif op == "views":
                        for span in log.views(0, 10_000):
                            _ = span.first_ts
                            span.close()
                    elif op == "page_spans":
                        for span in log.page_spans(0, 10_000):
                            _ = span.last_ts
                            span.close()
                    elif op == "slice":
                        _ = log[0:64]
            except BaseException as e:
                errors.append(e)

        try:
            w = threading.Thread(target=writer)
            rs = [threading.Thread(target=reader, args=(i,)) for i in range(n_readers)]
            w.start()
            for r in rs:
                r.start()
            for r in rs:
                r.join()
            stop.set()
            w.join()
            assert not errors, f"errors: {errors!r}"
        finally:
            log.close()
```

## New Task 5C.5 — §7.9 finalization and reopen

`reopen` exists at `python/timelog/__init__.py:200-219`. Add:

```python
class TestFinalizationAndReopen:
    """§7.9 — close/reopen/finalize semantics."""

    def test_explicit_close_then_reopen_resumes_operation(self):
        from timelog import Timelog
        log = Timelog(maintenance="disabled")
        log.extend([(i, i) for i in range(16)])
        log.flush()
        log.close()
        log.reopen()
        log.extend([(i + 16, i + 16) for i in range(16)])
        log.flush()
        result = list(log.all())
        assert len(result) == 32
        log.close()

    def test_gc_finalization_of_unclosed_instance_is_safe(self):
        from timelog import Timelog
        log = Timelog(maintenance="disabled")
        log.extend([(i, str(i)) for i in range(8)])
        log_ref = weakref.ref(log)
        del log
        gc.collect()
        gc.collect()
        assert log_ref() is None

    def test_interpreter_shutdown_smoke_in_subprocess(self):
        import subprocess, sys
        code = (
            "import timelog; "
            "t = timelog.Timelog(maintenance='background', maintenance_wakeup_ms=1); "
            "t.extend([(i, str(i)) for i in range(1024)]); "
            "t.flush()"
        )
        r = subprocess.run(
            [sys.executable, "-c", code],
            timeout=30, capture_output=True, text=True,
        )
        assert r.returncode == 0, f"shutdown failed: {r.stderr}"
```

## New Task 8.5 — TSan-on-3.14t CI job

In `.github/workflows/sanitizers.yml`, add:

```yaml
  thread-sanitizer-freethreaded:
    name: TSan (Free-threaded 3.14t)
    runs-on: ubuntu-latest
    timeout-minutes: 60
    env:
      TSAN_OPTIONS: "halt_on_error=0:second_deadlock_stack=1:suppressions=${{ github.workspace }}/.tsan-suppressions"
    steps:
      - uses: actions/checkout@<pinned>
      - uses: actions/setup-python@<pinned>
        with:
          python-version: "3.14t"
          allow-prereleases: true
      - name: Verify free-threaded
        run: python -c "import sysconfig; assert sysconfig.get_config_var('Py_GIL_DISABLED') == 1"
      - name: Configure
        run: |
          cmake -B build-tsan-ft \
            -DCMAKE_BUILD_TYPE=RelWithDebInfo \
            -DTIMELOG_SANITIZER=thread \
            -DTIMELOG_BUILD_PYTHON=ON \
            -DPython_EXECUTABLE=$(which python)
      - name: Build
        run: cmake --build build-tsan-ft -j$(nproc)
      - name: Free-threaded + stress legs under TSan
        run: |
          PYTHONPATH=$PWD/python python demo/ci/run_compat_baseline.py \
            --legs freethreading,stress
```

Create `.tsan-suppressions` with a starter set of CPython-internal frames to silence (extend during validation).

This job is **required-pass** (no `continue-on-error`).

## Revised Task 8.2 — cp314t wheel + smoke import

```yaml
- name: Build cp314t wheel
  if: matrix.python-tag == 'cp314t'
  env:
    CIBW_BUILD: "cp314t-manylinux_x86_64"
    CIBW_TEST_COMMAND: "python -c 'import timelog; t = timelog.Timelog(); t.append(1, \"x\"); t.flush(); t.close()'"
  run: pipx run cibuildwheel --output-dir wheelhouse
```

The `CIBW_TEST_COMMAND` runs against the built wheel after install — proves the wheel imports and basic ops work on cp314t.

---

## Execution order with this addendum

The original v1 plan's phase structure stands. Within each phase, the addendum's task revisions override v1's task content. Execution proceeds:

1. **Phase 5A**: revised tasks 5A.1 → 5A.8 (locking infra + atomics)
2. **Phase 5B**: revised tasks 5B.1 → 5B.4 (critical sections)
3. **Phase 5C**: revised + new tasks 5C.1 → 5C.5 (stress suite)
4. **Phase 6**: tasks 6.1 → 6.2 (Py_mod_gil, gated on Phase 7 TSan green)
5. **Phase 7**: TSan sweep (the gate)
6. **Phase 8**: revised tasks 8.1 → 8.5 (packaging, docs, acceptance)

Phase 6.2 must NOT land until Phase 8.5's TSan job is green. This addendum's TSan job replaces the v1 plan's "manual local TSan sweep" as the actual gate.
