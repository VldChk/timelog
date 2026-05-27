# Steps 5/6/8 Completion — Layer B Free-Threaded Readiness

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Drive Timelog from "Layer A complete" to "free-threaded CPython 3.14t safe, declared via `Py_mod_gil = Py_MOD_GIL_NOT_USED`," and publish supporting tests, docs, and wheel builds. After this plan lands, the LLD §10 acceptance checklist is fully ticked.

**Architecture:** Layer B introduces explicit synchronization where the GIL previously serialized access. Two new primitives are added: (L2) a `PyMutex` on the handle context's live-table; (L4) `Py_BEGIN_CRITICAL_SECTION` around mutable extension-object fields. The "collect under lock → release lock → execute Python-capable work" rule becomes mandatory at every site where Python-visible refs are dropped. Once those primitives are sound and the spec's stress tests pass on free-threaded CPython 3.14t, `Py_mod_gil = Py_MOD_GIL_NOT_USED` is enabled — the final public Layer B claim. Step 8 follows with packaging and docs cleanup.

**Tech Stack:** C17 binding; CPython 3.12-3.14 (regular) + 3.14t (free-threaded); `PyMutex` (3.13+) with `PyThread_type_lock` fallback for 3.12; `Py_BEGIN_CRITICAL_SECTION` (3.13+) with no-op fallback for 3.12; `cibuildwheel` for `cp314t` artifacts; TSan in CI on 3.14t.

---

## File Structure

### New files
- `bindings/cpython/tests/test_py_layer_b_sync.c` — C-level unit tests for `live_lock`, atomic `closed`, critical sections
- `python/tests/test_freethreaded_stress.py` — §7.6/§7.7/§7.8 stress suites (gated on `Py_GIL_DISABLED`)

### Modified files
- `bindings/cpython/include/timelogpy/py_compat.h` — Add locking compat macros
- `bindings/cpython/include/timelogpy/py_handle.h` — Add `live_lock` field; update doc comments
- `bindings/cpython/src/py_handle.c` — Use `live_lock`; collect/unlock/execute refactor; replace `PyGILState_Check` correctness uses
- `bindings/cpython/include/timelogpy/py_timelog.h` — Promote `closed` to atomic; update `CHECK_CLOSED` macros; doc cleanup
- `bindings/cpython/src/py_timelog.c` — Atomic `closed` reads/writes
- `bindings/cpython/src/py_iter.c` — Critical sections on mutable fields
- `bindings/cpython/src/py_span.c` — Critical sections; `exports` cleanup
- `bindings/cpython/src/py_span_iter.c` — Critical sections
- `bindings/cpython/src/py_span_objects.c` — Critical sections on `index` cursor
- `bindings/cpython/src/module.c` — Add `Py_mod_gil = Py_MOD_GIL_NOT_USED` slot (last gate)
- `python/tests/test_free_threading.py` — Remove xfail wrapper once Py_mod_gil lands
- `pyproject.toml` — Add `cp314t-*` to cibuildwheel build set
- `.github/workflows/packaging-pr.yml` — Add `cp314t` wheel matrix leg
- `.github/workflows/release-pypi.yml` — Same
- `.github/workflows/sanitizers.yml` — Add TSan + free-threaded leg running the new stress tests
- `demo/ci/check_layer_a_static.py` — Extend regex set to keep blanket "GIL required" wording out of new code
- Docs sweep: `python/timelog/__init__.py`, `bindings/cpython/include/timelogpy/py_timelog.h`, `bindings/cpython/include/timelogpy/py_handle.h`, `docs/python-api.md`, `docs/internals/components/python-binding-architecture.md`, `docs/timelog_lld_gil_free_subinterpreters.md` (rollout-status only)

### Touched-but-not-broken (verification only)
- `core/src/query/tl_pagespan_iter.c` — Already atomic; verify the cross-thread stress test exercises this path

---

## Compatibility Decision: 3.12 Floor

`PyMutex` and `Py_BEGIN_CRITICAL_SECTION` exist from CPython 3.13. The project floor is 3.12 per `pyproject.toml`. Strategy:

- On 3.13+: use real `PyMutex` and real critical sections.
- On 3.12: `PyMutex` falls back to `PyThread_type_lock` (always available); critical sections are no-ops because the GIL provides the equivalent serialization. Free-threaded support is only claimed for 3.14+, where the real primitives are always present.

This is implemented in `py_compat.h` as `TL_PY_MUTEX_*` and `TL_PY_CRITICAL_SECTION_*` macros (Phase 5A.1).

---

# Phase 5A — Locking infrastructure

### Task 5A.1: Add locking compat macros to py_compat.h

**Files:**
- Modify: `bindings/cpython/include/timelogpy/py_compat.h`

- [ ] **Step 1: Read the current py_compat.h**

```bash
cat bindings/cpython/include/timelogpy/py_compat.h
```

Expected: file with a `PY_VERSION_HEX < 0x030D0000` guard around an existing compat shim (likely `Py_IsFinalizing`).

- [ ] **Step 2: Append the new compat macros to py_compat.h**

Add after the existing guards, before the closing `#endif`:

```c
/*===========================================================================
 * Mutex compat — PyMutex (3.13+) vs PyThread_type_lock fallback (3.12)
 *
 * TL_PY_MUTEX_T:      opaque storage type
 * TL_PY_MUTEX_INIT:   initialize a TL_PY_MUTEX_T*
 * TL_PY_MUTEX_DEINIT: destroy a TL_PY_MUTEX_T*
 * TL_PY_MUTEX_LOCK:   acquire
 * TL_PY_MUTEX_UNLOCK: release
 *
 * Notes:
 * - PyMutex is statically zero-initializable; the fallback is heap-allocated.
 * - The fallback's INIT can fail (returns nonzero); callers MUST check.
 * - Holds no thread state. Safe to acquire from any C thread, including the
 *   maintenance worker (the worker does not use these locks today, but this
 *   keeps the type usable below the Python boundary).
 *===========================================================================*/

#if PY_VERSION_HEX >= 0x030D0000
typedef PyMutex tl_py_mutex_t;
#define TL_PY_MUTEX_INIT(m)   ((void)(m))           /* PyMutex is zero-init */
#define TL_PY_MUTEX_DEINIT(m) ((void)(m))           /* PyMutex needs no deinit */
#define TL_PY_MUTEX_LOCK(m)   PyMutex_Lock(m)
#define TL_PY_MUTEX_UNLOCK(m) PyMutex_Unlock(m)
#define TL_PY_MUTEX_OK 0
#else
typedef PyThread_type_lock tl_py_mutex_t;
/* Returns 0 on success, -1 on alloc failure. */
static inline int tl_py_mutex_init(tl_py_mutex_t* m) {
    *m = PyThread_allocate_lock();
    return *m == NULL ? -1 : 0;
}
static inline void tl_py_mutex_deinit(tl_py_mutex_t* m) {
    if (*m) { PyThread_free_lock(*m); *m = NULL; }
}
#define TL_PY_MUTEX_INIT(m)   tl_py_mutex_init(m)
#define TL_PY_MUTEX_DEINIT(m) tl_py_mutex_deinit(m)
#define TL_PY_MUTEX_LOCK(m)   PyThread_acquire_lock(*(m), WAIT_LOCK)
#define TL_PY_MUTEX_UNLOCK(m) PyThread_release_lock(*(m))
#define TL_PY_MUTEX_OK 0
#endif

/*===========================================================================
 * Critical-section compat — Py_BEGIN_CRITICAL_SECTION (3.13+)
 *
 * Use these around mutable extension-object field accesses that the GIL used
 * to serialize. On 3.12 (no free-threaded build exists), these are no-ops.
 *===========================================================================*/

#if PY_VERSION_HEX >= 0x030D0000
#define TL_PY_OBJ_LOCK(obj)   Py_BEGIN_CRITICAL_SECTION((PyObject*)(obj))
#define TL_PY_OBJ_UNLOCK()    Py_END_CRITICAL_SECTION()
#define TL_PY_OBJ_LOCK2(a, b) Py_BEGIN_CRITICAL_SECTION2((PyObject*)(a), (PyObject*)(b))
#define TL_PY_OBJ_UNLOCK2()   Py_END_CRITICAL_SECTION2()
#else
#define TL_PY_OBJ_LOCK(obj)   do { (void)(obj);
#define TL_PY_OBJ_UNLOCK()    } while (0)
#define TL_PY_OBJ_LOCK2(a, b) do { (void)(a); (void)(b);
#define TL_PY_OBJ_UNLOCK2()   } while (0)
#endif
```

- [ ] **Step 3: Verify the file still compiles standalone**

Run:
```bash
cmake --build build-step2 -j$(nproc) 2>&1 | tail -20
```

Expected: clean build (no new errors).

- [ ] **Step 4: Commit**

```bash
git add bindings/cpython/include/timelogpy/py_compat.h
git commit -m "feat(layer-b): add PyMutex and critical-section compat macros"
```

---

### Task 5A.2: Add `live_lock` field to handle_ctx

**Files:**
- Modify: `bindings/cpython/include/timelogpy/py_handle.h`

- [ ] **Step 1: Add `live_lock` field to `tl_py_handle_ctx_t`**

In `py_handle.h`, find the struct declaration (currently `struct tl_py_handle_ctx { ... }`). Add immediately after `uint8_t live_tracking_failed;`:

```c
    /**
     * Lock protecting the live-handle table (entries, cap, len, tombstones,
     * tracking_failed). Mandatory under free-threaded builds; harmless under
     * regular builds (under GIL it acts as a no-op recursive guard, but is
     * still required for correctness under per-instance overlap).
     *
     * Acquired ONLY around bounded sections that mutate or scan the live
     * table. Never held across Py_DECREF, warnings, weakref callbacks, or
     * any code that may execute Python (collect/unlock/execute rule —
     * spec §5.4).
     */
    tl_py_mutex_t live_lock;
```

Add `#include "timelogpy/py_compat.h"` at the top of `py_handle.h` if not already present.

- [ ] **Step 2: Update the existing GIL comments to point to live_lock**

Replace the comment in `py_handle.h` (currently around line 165):

```c
    /**
     * Live handle tracking (multiset by pointer identity).
     * Used to DECREF all remaining objects on close().
     *
     * NOTE: Accessed only with GIL held (append/extend/drain/close).
     */
```

with:

```c
    /**
     * Live handle tracking (multiset by pointer identity).
     * Used to DECREF all remaining objects on close().
     *
     * Mutation and scan are protected by `live_lock`. Per the collect/
     * unlock/execute rule, callers must drop the lock before any Python
     * decref happens.
     */
```

- [ ] **Step 3: Verify header still parses (no compile yet)**

```bash
gcc -fsyntax-only -I bindings/cpython/include -I core/include -I /usr/include/python3.13 \
    bindings/cpython/include/timelogpy/py_handle.h 2>&1 | head -5
```

Expected: no errors (warnings about Python version OK).

- [ ] **Step 4: Commit**

```bash
git add bindings/cpython/include/timelogpy/py_handle.h
git commit -m "feat(layer-b): declare live_lock on handle context"
```

---

### Task 5A.3: Initialize/destroy live_lock + guard insertions

**Files:**
- Modify: `bindings/cpython/src/py_handle.c`

- [ ] **Step 1: Write the failing test first**

Add to `bindings/cpython/tests/test_py_handle.c` (after the existing `ctx_new_refcount_incref_decref` test):

```c
TEST(live_lock_lifecycle_init_and_destroy)
{
    /* Heap-allocated ctx must construct, hold a live_lock, destroy cleanly. */
    tl_py_handle_ctx_t* ctx = tl_py_handle_ctx_new(0);
    ASSERT_NOT_NULL(ctx);
    ASSERT_EQ(atomic_load_explicit(&ctx->refcnt, memory_order_acquire), 1);

    /* Lock + unlock a few times — exercise the path; cannot directly read
     * the mutex state portably, so the assertion is "no crash, no deadlock." */
    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);

    tl_py_handle_ctx_decref(ctx);
}
```

Wire it into the test runner array.

- [ ] **Step 2: Run the new test — expect a LINK FAILURE (no init code yet)**

```bash
cmake --build build-step2 -j$(nproc) --target test_py_handle 2>&1 | tail -10
```

Expected: undefined reference OR test fails because `live_lock` field exists but is uninitialized (on the fallback path this means NULL lock pointer).

- [ ] **Step 3: Initialize live_lock in `tl_py_handle_ctx_init`**

In `py_handle.c`, find `tl_py_handle_ctx_init` and add:

```c
    if (TL_PY_MUTEX_INIT(&ctx->live_lock) != 0) {
        return TL_ENOMEM;
    }
```

Place it after the existing atomic inits, before returning `TL_OK`.

- [ ] **Step 4: Deinitialize live_lock in `tl_py_handle_ctx_destroy`**

Add to the start of `tl_py_handle_ctx_destroy` (after the NULL check, before the existing free of `live_entries`):

```c
    TL_PY_MUTEX_DEINIT(&ctx->live_lock);
```

- [ ] **Step 5: Re-run the test — expect PASS**

```bash
ctest --test-dir build-step2 -R py_handle_tests --output-on-failure 2>&1 | tail -20
```

Expected: PASSED.

- [ ] **Step 6: Commit**

```bash
git add bindings/cpython/src/py_handle.c bindings/cpython/tests/test_py_handle.c
git commit -m "feat(layer-b): initialize and tear down live_lock"
```

---

### Task 5A.4: Wrap live_note_insert / live_note_drop with live_lock

**Files:**
- Modify: `bindings/cpython/src/py_handle.c`

- [ ] **Step 1: Write the failing test (concurrent insertions must not corrupt)**

Add to `test_py_handle.c`:

```c
#include <pthread.h>

typedef struct {
    tl_py_handle_ctx_t* ctx;
    PyObject** objects;
    size_t count;
    int repeats;
} live_stress_arg_t;

static void* live_insert_thread(void* arg)
{
    live_stress_arg_t* a = (live_stress_arg_t*)arg;
    PyGILState_STATE g = PyGILState_Ensure();
    for (int r = 0; r < a->repeats; r++) {
        for (size_t i = 0; i < a->count; i++) {
            (void)tl_py_live_note_insert(a->ctx, a->objects[i]);
        }
        for (size_t i = 0; i < a->count; i++) {
            tl_py_live_note_drop(a->ctx, a->objects[i]);
        }
    }
    PyGILState_Release(g);
    return NULL;
}

TEST(live_table_concurrent_insert_drop_no_corruption)
{
    tl_py_handle_ctx_t* ctx = tl_py_handle_ctx_new(0);
    ASSERT_NOT_NULL(ctx);

    /* Borrow stable singletons - no DECREF responsibility. */
    PyObject* objs[8] = {
        Py_True, Py_False, Py_None, Py_Ellipsis,
        Py_True, Py_False, Py_None, Py_Ellipsis
    };

    live_stress_arg_t arg = { ctx, objs, 8, 200 };

    enum { N_THREADS = 4 };
    pthread_t threads[N_THREADS];
    Py_BEGIN_ALLOW_THREADS
    for (int t = 0; t < N_THREADS; t++) {
        pthread_create(&threads[t], NULL, live_insert_thread, &arg);
    }
    for (int t = 0; t < N_THREADS; t++) {
        pthread_join(threads[t], NULL);
    }
    Py_END_ALLOW_THREADS

    /* After symmetric insert/drop, live_len must return to 0 */
    ASSERT_EQ(ctx->live_len, 0);

    tl_py_handle_ctx_decref(ctx);
}
```

- [ ] **Step 2: Run — expect FAILURE (live_len != 0, race in unprotected hash table)**

```bash
ctest --test-dir build-step2 -R py_handle_tests --output-on-failure 2>&1 | tail -20
```

Expected: ASSERT_EQ fails, live_len positive (race lost entries).

NOTE: On a regular (GIL) build this may pass by coincidence because the GIL serializes. The real test is under free-threaded 3.14t — but the locking change must land first. We accept a passing-by-coincidence result here and rely on §7.6/§7.7 stress (Phase 5E) for the genuine race exposure.

- [ ] **Step 3: Wrap insert + drop with live_lock**

In `tl_py_live_note_insert` (currently at `py_handle.c:517`), restructure:

```c
tl_status_t tl_py_live_note_insert(tl_py_handle_ctx_t* ctx, PyObject* obj)
{
    if (ctx == NULL || obj == NULL) {
        return TL_EINVAL;
    }

    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    tl_status_t st = tl_py_live_ensure(ctx, 1);
    if (st != TL_OK) {
        ctx->live_tracking_failed = 1;
        TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
        return st;
    }
    /* ... existing insert body ... */
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
    return TL_OK;
}
```

Replace the `assert(PyGILState_Check() && ...)` with `assert(Py_IsInitialized() && "live_note_insert needs interpreter")` (the live_lock now provides the actual ordering).

Same restructure for `tl_py_live_note_drop` at `py_handle.c:563`.

- [ ] **Step 4: Re-run — expect PASS**

```bash
ctest --test-dir build-step2 -R py_handle_tests --output-on-failure 2>&1 | tail -20
```

Expected: PASSED.

- [ ] **Step 5: Commit**

```bash
git add bindings/cpython/src/py_handle.c bindings/cpython/tests/test_py_handle.c
git commit -m "feat(layer-b): protect live-table mutations with live_lock"
```

---

### Task 5A.5: Refactor `tl_py_live_release_all` to collect/unlock/execute

**Files:**
- Modify: `bindings/cpython/src/py_handle.c`

This is the spec's headline pattern (§5.4 line 387-406). The current `tl_py_live_release_all` calls `Py_DECREF` inside the scan loop. Once `live_lock` exists, that's a recipe for deadlock if any `__del__` re-enters timelog. Refactor to: take lock → snapshot strong refs into a local array → free `live_entries` → unlock → DECREF refs → free array.

- [ ] **Step 1: Write the failing test — payload `__del__` that re-enters timelog must not deadlock**

Add to `test_py_handle.c`:

```c
static PyObject* test_payload_class = NULL;
static int test_payload_del_calls = 0;

/* A class whose __del__ acquires the live_lock indirectly by calling a
 * timelog method that touches live tracking. We synthesize this by having
 * __del__ call back into a test hook function exposed by the module. */

TEST(live_release_all_no_deadlock_with_reentrant_del)
{
    tl_py_handle_ctx_t* ctx = tl_py_handle_ctx_new(0);
    ASSERT_NOT_NULL(ctx);

    /* Build a Python class with __del__ that performs a benign lookup
     * which would deadlock if live_release_all held the lock during DECREF. */
    PyObject* main = PyImport_AddModule("__main__");
    int rc = PyRun_SimpleString(
        "class _ReentDel:\n"
        "    def __del__(self):\n"
        "        # Any benign Python work here proves we are not in a deadlock.\n"
        "        list(range(2))\n"
    );
    ASSERT_EQ(rc, 0);
    PyObject* cls = PyObject_GetAttrString(main, "_ReentDel");
    ASSERT_NOT_NULL(cls);

    /* Insert several instances into the live table. */
    for (int i = 0; i < 16; i++) {
        PyObject* o = PyObject_CallNoArgs(cls);
        ASSERT_NOT_NULL(o);
        ASSERT_EQ(tl_py_live_note_insert(ctx, o), TL_OK);
    }

    /* release_all: must drop the lock before DECREF triggers __del__ */
    tl_py_live_release_all(ctx);

    /* If we reach here without deadlock, the contract holds. */
    Py_DECREF(cls);
    tl_py_handle_ctx_decref(ctx);
}
```

- [ ] **Step 2: Run — likely PASSES today (Python runs __del__ on the next opportunity, not synchronously while we hold the lock today because no lock exists). After Task 5A.4 lands, this test asserts the no-deadlock property.**

```bash
ctest --test-dir build-step2 -R py_handle_tests --output-on-failure 2>&1 | tail -20
```

Expected: PASSES today (no live_lock held during DECREF yet). After refactor: still PASSES.

To make the test genuinely fail without the refactor, we'd need to artificially acquire `live_lock` from `__del__`. Skip — the spec's stress tests in Phase 5E will produce real failures.

- [ ] **Step 3: Refactor `tl_py_live_release_all` to collect/unlock/execute**

In `py_handle.c` (currently around `:598`), replace the body:

```c
void tl_py_live_release_all(tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL) return;

    /* Phase 1: collect strong refs into a local array under the lock. */
    PyObject** refs = NULL;
    size_t refs_count = 0;
    size_t refs_cap = 0;

    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    if (ctx->live_entries == NULL) {
        TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
        return;
    }
    /* Estimate refs_cap as sum of counts; pessimistically use live_len. */
    refs_cap = ctx->live_len;
    refs = refs_cap > 0 ? PyMem_Malloc(refs_cap * sizeof(PyObject*)) : NULL;
    if (refs == NULL && refs_cap > 0) {
        /* Allocation failed — fall back to inline DECREF under lock. This is
         * the rare "best effort to avoid leak" path. We still respect the
         * collect-first principle by snapshotting then releasing inline. */
        ctx->live_tracking_failed = 1;
    }

    size_t total = 0;
    for (size_t i = 0; i < ctx->live_cap; i++) {
        tl_py_live_entry_t* e = &ctx->live_entries[i];
        if (e->state == TL_PY_LIVE_FULL) {
            for (uint64_t c = e->count; c > 0; c--) {
                if (refs != NULL && total < refs_cap) {
                    refs[total++] = e->obj;
                } else {
                    /* Fallback: decref under lock. Acceptable because
                     * allocation already failed; data integrity prevails. */
                    Py_DECREF(e->obj);
                }
            }
            e->obj = NULL;
            e->count = 0;
            e->state = TL_PY_LIVE_EMPTY;
        }
    }

    /* Free the live table itself under the lock (other paths must not
     * concurrently insert; this is enforced by close ordering). */
    PyMem_Free(ctx->live_entries);
    ctx->live_entries = NULL;
    ctx->live_cap = 0;
    ctx->live_len = 0;
    ctx->live_tombstones = 0;

    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);

    /* Phase 2: execute Py_DECREF outside the lock. */
    if (refs != NULL) {
        for (size_t i = 0; i < total; i++) {
            Py_DECREF(refs[i]);
        }
        PyMem_Free(refs);
    }
}
```

Replace the `PyMem_Malloc` with whichever allocator the rest of `py_handle.c` uses (verify by grep — likely `PyMem_Malloc`).

- [ ] **Step 4: Re-run all py_handle tests**

```bash
ctest --test-dir build-step2 -R py_handle_tests --output-on-failure 2>&1 | tail -30
```

Expected: all PASS.

- [ ] **Step 5: Commit**

```bash
git add bindings/cpython/src/py_handle.c bindings/cpython/tests/test_py_handle.c
git commit -m "feat(layer-b): collect/unlock/execute pattern in live_release_all"
```

---

### Task 5A.6: Update `tl_py_handle_ctx_traverse` to acquire live_lock

**Files:**
- Modify: `bindings/cpython/src/py_handle.c`

- [ ] **Step 1: Wrap the live-table traversal portion with live_lock**

In `tl_py_handle_ctx_traverse` (currently `py_handle.c:636`), wrap the `for (i = 0; i < ctx->live_cap; i++)` loop:

```c
    TL_PY_MUTEX_LOCK(&ctx->live_lock);
    if (ctx->live_entries != NULL) {
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
    }
    TL_PY_MUTEX_UNLOCK(&ctx->live_lock);
```

Note: `visit` callbacks in CPython's GC contract may not re-enter Python; they only call `Py_VISIT` (a macro that bumps refcounts). So holding `live_lock` across visit is safe.

The retired-stack traversal that follows does NOT need `live_lock` — it uses atomic loads only.

- [ ] **Step 2: Run all py_handle tests + run a quick GC-cycle test from Python**

```bash
ctest --test-dir build-step2 -R py_handle_tests --output-on-failure 2>&1 | tail -10
PYTHONPATH=$PWD/python python -m pytest python/tests/test_facade.py -q -k 'gc or cycle' 2>&1 | tail -10
```

Expected: all PASS.

- [ ] **Step 3: Commit**

```bash
git add bindings/cpython/src/py_handle.c
git commit -m "feat(layer-b): traverse live table under live_lock"
```

---

### Task 5A.7: Replace correctness `PyGILState_Check()` with attached-thread-state probe

**Files:**
- Modify: `bindings/cpython/src/py_handle.c`

- [ ] **Step 1: Replace `tl_py_handle_ctx_current_interp_owns` to drop PyGILState_Check**

At `py_handle.c:45`, current:

```c
static int tl_py_handle_ctx_current_interp_owns(const tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL || !Py_IsInitialized() || !PyGILState_Check()) return 0;
    PyInterpreterState* current = PyInterpreterState_Get();
    return current != NULL && current == ctx->interp;
}
```

New version (uses `_PyThreadState_UncheckedGet` to detect attached thread state without GIL semantics):

```c
static int tl_py_attached_to_interp(const tl_py_handle_ctx_t* ctx)
{
    if (ctx == NULL || !Py_IsInitialized()) return 0;
    /* An attached thread state is the precondition for Python C-API access
     * under free-threaded CPython; GIL acquisition is separate. */
    PyThreadState* ts = _PyThreadState_UncheckedGet();
    if (ts == NULL) return 0;
    return ts->interp == ctx->interp;
}
```

(The interpreter capture at init can stay the same — when init runs from a known-attached thread, `PyInterpreterState_Get()` works.)

Rename all call sites: `tl_py_handle_ctx_current_interp_owns` → `tl_py_attached_to_interp`.

- [ ] **Step 2: Keep the diagnostic `PyGILState_Check` at line 262 unchanged** (it's used to format a warning reason string; correctness is gated by `tl_py_attached_to_interp` already)

- [ ] **Step 3: Build + run all C tests**

```bash
cmake --build build-step2 -j$(nproc) 2>&1 | tail -5
ctest --test-dir build-step2 --output-on-failure 2>&1 | tail -20
```

Expected: all PASS.

- [ ] **Step 4: Commit**

```bash
git add bindings/cpython/src/py_handle.c
git commit -m "feat(layer-b): replace PyGILState_Check with attached-thread-state probe"
```

---

### Task 5A.8: Atomic `closed` mirror in PyTimelog

**Files:**
- Modify: `bindings/cpython/include/timelogpy/py_timelog.h`
- Modify: `bindings/cpython/src/py_timelog.c`

Spec §5.4 invariant L1 (line 449-450): "any fast-path unlocked `closed` checks must be audited and removed or atomically synchronized." Today `closed` is a plain `int` read unlocked in `CHECK_CLOSED`. Promote to `_Atomic(uint8_t)` (or `tl_atomic_u8`) — same one-byte read on x86/ARM but with the memory-model guarantee.

- [ ] **Step 1: Add atomic header include + change field declaration in py_timelog.h**

In `py_timelog.h`, find the PyTimelog struct. Add `#include <stdatomic.h>` near the top includes. Change:

```c
    /**
     * Lifecycle state.
     * 0 = open, 1 = closed.
     * Set early in close() to prevent reentrancy.
     */
    int closed;
```

to:

```c
    /**
     * Lifecycle state (atomic mirror so fast-path checks are race-free).
     * 0 = open, 1 = closed.
     * Writers must hold `core_lock` and use atomic_store(release);
     * readers may use atomic_load(acquire) without the lock.
     */
    _Atomic(uint8_t) closed;
```

- [ ] **Step 2: Update CHECK_CLOSED macros to atomic_load**

In the same header, change:

```c
#define CHECK_CLOSED(self) \
    do { \
        if ((self)->closed || (self)->tl == NULL) { ... } \
    } while (0)
```

to:

```c
#define CHECK_CLOSED(self) \
    do { \
        if (atomic_load_explicit(&(self)->closed, memory_order_acquire) || \
            (self)->tl == NULL) { ... } \
    } while (0)
```

Same for `CHECK_CLOSED_INT`.

(Note `self->tl` remains a non-atomic pointer read — but it's only written under `core_lock` and the atomic load of `closed` orders the engine-detach. The first hard test of `tl` happens under lock anyway in the locked methods.)

- [ ] **Step 3: Update writes in py_timelog.c**

Grep for `self->closed = 0` and `self->closed = 1` in `py_timelog.c`. Replace each with:

```c
atomic_store_explicit(&self->closed, 1, memory_order_release);
```

Sites to update (verify by `grep -n 'self->closed = ' bindings/cpython/src/py_timelog.c`):
- `PyTimelog_init`: `self->closed = 0;` (initial state) → `atomic_init(&self->closed, 0);`
- `pytimelog_close_no_raise`: `self->closed = 1;` → `atomic_store_explicit(..., 1, memory_order_release);`
- Any other set-on-error paths (search the file).

For initial init in `PyTimelog_new` / `tp_init` (depending on type construction): use `atomic_init`.

- [ ] **Step 4: Build + run all C tests + Python tests**

```bash
cmake --build build-step2 -j$(nproc) 2>&1 | tail -5
ctest --test-dir build-step2 --output-on-failure 2>&1 | tail -10
PYTHONPATH=$PWD/python python -m pytest python/tests -q 2>&1 | tail -10
```

Expected: all PASS, 97 passed / 9 skipped (same as baseline).

- [ ] **Step 5: Commit**

```bash
git add bindings/cpython/include/timelogpy/py_timelog.h bindings/cpython/src/py_timelog.c
git commit -m "feat(layer-b): atomic closed mirror in PyTimelog"
```

---

# Phase 5B — Object critical sections

Each task wraps mutable extension-object fields with `TL_PY_OBJ_LOCK(self) / TL_PY_OBJ_UNLOCK()`. The critical section is **leaf scope only** — no engine calls, no Py_DECREF, no allocations. Snapshot the field into a local under the section, drop the lock, then act.

### Task 5B.1: PyPageSpan critical sections (close, exports, getters)

**Files:**
- Modify: `bindings/cpython/src/py_span.c`

- [ ] **Step 1: Write the failing test (overlap close + buffer release)**

Add to `python/tests/test_freethreaded_stress.py` (create the file with the boilerplate below):

```python
"""§7.7 mutable object-state overlap stress — free-threaded only.

These tests gate on Py_GIL_DISABLED == 1 because they require true
parallelism to expose torn-state bugs. On regular GIL builds they are
skipped (the GIL covers up the races we want to surface).
"""

from __future__ import annotations

import gc
import os
import sysconfig
import threading
import unittest
import weakref

import pytest


def _is_free_threaded() -> bool:
    return sysconfig.get_config_var("Py_GIL_DISABLED") == 1


pytestmark = pytest.mark.skipif(
    not _is_free_threaded(),
    reason="Free-threaded stress requires Py_GIL_DISABLED=1 build",
)


class TestPageSpanCloseOverlap:
    def test_close_overlapped_with_buffer_export_and_property_reads(self):
        from timelog import Timelog

        log = Timelog(maintenance="disabled")
        try:
            log.extend([(i, i) for i in range(64)])
            log.flush()

            spans = list(log.views(0, 64))
            errors: list[BaseException] = []

            def reader(span):
                try:
                    for _ in range(50):
                        try:
                            mv = memoryview(span)
                            _ = mv[0]
                            mv.release()
                            _ = span.first_ts
                        except (ValueError, BufferError):
                            return
                except BaseException as e:
                    errors.append(e)

            def closer(span):
                try:
                    for _ in range(50):
                        try:
                            span.close()
                        except Exception:
                            pass
                except BaseException as e:
                    errors.append(e)

            threads: list[threading.Thread] = []
            for span in spans:
                threads.append(threading.Thread(target=reader, args=(span,)))
                threads.append(threading.Thread(target=closer, args=(span,)))
            for t in threads:
                t.start()
            for t in threads:
                t.join()

            assert not errors, f"hostile overlap surfaced: {errors!r}"
        finally:
            log.close()
```

- [ ] **Step 2: Run — expect SKIP locally (regular GIL build) or RACE under TSan on 3.14t**

```bash
PYTHONPATH=$PWD/python python -m pytest python/tests/test_freethreaded_stress.py -v 2>&1 | tail -10
```

Expected on local 3.13: `1 skipped` (not free-threaded). On 3.14t: race conditions exposed without critical sections (test fails).

- [ ] **Step 3: Wrap PyPageSpan_close + getbuffer/releasebuffer + getters with TL_PY_OBJ_LOCK**

Add `#include "timelogpy/py_compat.h"` to `py_span.c` if not present.

For `pagespan_close` (`py_span.c` around close path):

```c
static PyObject* PyPageSpan_close(PyPageSpan* self, PyObject* Py_UNUSED(args))
{
    int already_closed = 0;
    int exports_outstanding = 0;
    tl_pagespan_owner_t* owner_to_release = NULL;
    PyObject* timelog_to_release = NULL;

    TL_PY_OBJ_LOCK(self);
    if (self->closed) {
        already_closed = 1;
    } else if (self->exports != 0) {
        exports_outstanding = 1;
    } else {
        self->closed = 1;
        owner_to_release = self->owner;
        timelog_to_release = self->timelog;
        self->owner = NULL;
        self->timelog = NULL;
        self->ts = NULL;
        self->h = NULL;
        self->len = 0;
    }
    TL_PY_OBJ_UNLOCK();

    if (exports_outstanding) {
        PyErr_SetString(PyExc_BufferError,
            "Cannot close PageSpan while buffer exports are outstanding");
        return NULL;
    }
    if (already_closed) {
        Py_RETURN_NONE;
    }

    /* Phase 2: execute decrefs/owner release outside the critical section */
    if (owner_to_release) tl_pagespan_owner_decref(owner_to_release);
    Py_XDECREF(timelog_to_release);
    Py_RETURN_NONE;
}
```

For `pagespan_getbuffer` (currently raises BufferError if closed; this needs to be atomic with close):

```c
static int pagespan_getbuffer(PyObject* exporter, Py_buffer* view, int flags)
{
    PyPageSpan* self = (PyPageSpan*)exporter;
    int ok = 0;

    TL_PY_OBJ_LOCK(self);
    if (!self->closed && self->ts != NULL) {
        /* fill view fields */
        view->buf = self->ts;
        view->len = self->len * sizeof(int64_t);
        /* ... existing fill logic ... */
        self->exports++;
        ok = 1;
    }
    TL_PY_OBJ_UNLOCK();

    if (!ok) {
        PyErr_SetString(PyExc_BufferError, "PageSpan is closed");
        return -1;
    }
    /* obj is the exporter; INCREF outside the lock per CPython buffer contract */
    Py_INCREF(exporter);
    view->obj = exporter;
    return 0;
}
```

For `pagespan_releasebuffer`:

```c
static void pagespan_releasebuffer(PyObject* exporter, Py_buffer* view)
{
    PyPageSpan* self = (PyPageSpan*)exporter;
    TL_PY_OBJ_LOCK(self);
    if (self->exports > 0) self->exports--;
    TL_PY_OBJ_UNLOCK();
}
```

For getters (`closed`, `first_ts`, `last_ts`, `timestamps`, etc.) — wrap the read with TL_PY_OBJ_LOCK around the field access, then build the Python object outside the lock:

```c
static PyObject* pagespan_get_closed(PyPageSpan* self, void* closure)
{
    int c;
    TL_PY_OBJ_LOCK(self);
    c = self->closed;
    TL_PY_OBJ_UNLOCK();
    return PyBool_FromLong(c);
}
```

- [ ] **Step 4: Re-run all py_span tests**

```bash
ctest --test-dir build-step2 -R py_span_tests --output-on-failure 2>&1 | tail -10
PYTHONPATH=$PWD/python python -m pytest python/tests/test_facade.py -q 2>&1 | tail -5
```

Expected: all PASS.

- [ ] **Step 5: Commit**

```bash
git add bindings/cpython/src/py_span.c python/tests/test_freethreaded_stress.py
git commit -m "feat(layer-b): critical sections on PageSpan close/exports/getters"
```

---

### Task 5B.2: PyTimelogIter critical sections

**Files:**
- Modify: `bindings/cpython/src/py_iter.c`

Wrap every method that reads or writes `closed`, `iter`, `pinned_snapshot`, `owner`, `remaining_count`, `remaining_valid`.

- [ ] **Step 1: Write failing test (iter exhaustion + close overlap)**

Append to `test_freethreaded_stress.py`:

```python
class TestTimelogIterCloseOverlap:
    def test_iter_exhaustion_overlapped_with_close(self):
        from timelog import Timelog
        log = Timelog(maintenance="disabled")
        try:
            log.extend([(i, str(i)) for i in range(256)])
            log.flush()

            errors: list[BaseException] = []
            for _ in range(20):
                it = log.all()

                def exhaust():
                    try:
                        for _ in it:
                            pass
                    except BaseException as e:
                        errors.append(e)

                def closer():
                    try:
                        it.close()
                    except BaseException as e:
                        errors.append(e)

                t1 = threading.Thread(target=exhaust)
                t2 = threading.Thread(target=closer)
                t1.start()
                t2.start()
                t1.join()
                t2.join()

            assert not errors, f"unexpected errors: {errors!r}"
        finally:
            log.close()
```

- [ ] **Step 2: Run — SKIP locally**

```bash
PYTHONPATH=$PWD/python python -m pytest python/tests/test_freethreaded_stress.py -v 2>&1 | tail -5
```

- [ ] **Step 3: Wrap mutating PyTimelogIter methods with TL_PY_OBJ_LOCK**

Sites in `py_iter.c`:
- `PyTimelogIter_close` — snapshot fields, set closed=1, NULL pointers; release outside lock
- `PyTimelogIter_iternext` — read `closed` and snapshot `iter` pointer under lock; if open, drop lock then call engine; on EOF re-acquire to flip closed
- `PyTimelogIter_next_batch` — same pattern
- `PyTimelogIter_len` — read under lock, build Long outside
- `pytimelogiter_cleanup` — collect, set fields NULL under lock, release outside

Follow the same collect/unlock/execute shape as Task 5B.1.

- [ ] **Step 4: Re-run all iter tests + Python tests**

```bash
ctest --test-dir build-step2 -R py_iter_tests --output-on-failure 2>&1 | tail -10
PYTHONPATH=$PWD/python python -m pytest python/tests/test_facade.py -q 2>&1 | tail -5
```

Expected: all PASS.

- [ ] **Step 5: Commit**

```bash
git add bindings/cpython/src/py_iter.c python/tests/test_freethreaded_stress.py
git commit -m "feat(layer-b): critical sections on PyTimelogIter mutable fields"
```

---

### Task 5B.3: PyPageSpanIter critical sections

**Files:**
- Modify: `bindings/cpython/src/py_span_iter.c`

Same pattern as Task 5B.2 but for `closed`, `iter`, `timelog` on PageSpanIter.

- [ ] **Step 1: Failing test (already part of Task 5B.2's harness; just ensure span_iter is exercised)**

Append to `test_freethreaded_stress.py`:

```python
class TestPageSpanIterOverlap:
    def test_views_iter_exhaustion_overlapped_with_close(self):
        from timelog import Timelog
        log = Timelog(maintenance="disabled")
        try:
            log.extend([(i, i) for i in range(512)])
            log.flush()

            errors: list[BaseException] = []
            for _ in range(10):
                span_iter = log.views(0, 512)

                def exhaust():
                    try:
                        for span in span_iter:
                            try:
                                _ = span.first_ts
                            finally:
                                span.close()
                    except BaseException as e:
                        errors.append(e)

                def closer():
                    try:
                        span_iter.close()
                    except BaseException as e:
                        errors.append(e)

                t1 = threading.Thread(target=exhaust)
                t2 = threading.Thread(target=closer)
                t1.start(); t2.start()
                t1.join(); t2.join()

            assert not errors, f"unexpected errors: {errors!r}"
        finally:
            log.close()
```

- [ ] **Step 2: Wrap PyPageSpanIter methods with TL_PY_OBJ_LOCK**

Same shape as 5B.2.

- [ ] **Step 3: Build + tests pass**

```bash
ctest --test-dir build-step2 -R py_span_iter_tests --output-on-failure 2>&1 | tail -10
```

- [ ] **Step 4: Commit**

```bash
git add bindings/cpython/src/py_span_iter.c python/tests/test_freethreaded_stress.py
git commit -m "feat(layer-b): critical sections on PyPageSpanIter mutable fields"
```

---

### Task 5B.4: PyPageSpanObjectsViewIter critical section on `index`

**Files:**
- Modify: `bindings/cpython/src/py_span_objects.c`

The internal iterator has a mutable `index` cursor that races on concurrent `__next__` calls.

- [ ] **Step 1: Wrap `objectsviewiter_next` with TL_PY_OBJ_LOCK**

Snapshot `index` under the lock, fetch the corresponding handle pointer (the underlying span data is immutable while the view is alive), then build the Python object outside the lock:

```c
static PyObject* objectsviewiter_next(PyObject* self_obj)
{
    PyPageSpanObjectsViewIter* self = (PyPageSpanObjectsViewIter*)self_obj;
    PyPageSpanObjectsView* view;
    Py_ssize_t my_idx;
    PyPageSpan* span;
    tl_handle_t h;
    int eof = 0;

    TL_PY_OBJ_LOCK(self);
    if (self->view == NULL) {
        TL_PY_OBJ_UNLOCK();
        return NULL;
    }
    view = self->view;
    span = view->span;
    if (self->index >= span->len) {
        eof = 1;
    } else {
        my_idx = self->index;
        self->index++;
        h = span->h[my_idx];
    }
    TL_PY_OBJ_UNLOCK();

    if (eof) return NULL;

    PyObject* obj = tl_py_handle_decode(h);
    Py_INCREF(obj);
    return obj;
}
```

- [ ] **Step 2: Wrap `objectsviewiter_clear` to defer DECREF outside lock**

Same collect/unlock/execute pattern.

- [ ] **Step 3: Build + tests pass**

```bash
ctest --test-dir build-step2 --output-on-failure 2>&1 | tail -10
```

- [ ] **Step 4: Commit**

```bash
git add bindings/cpython/src/py_span_objects.c
git commit -m "feat(layer-b): critical section on PageSpanObjectsViewIter cursor"
```

---

# Phase 5C — Stress test suite (§7.6, §7.7, §7.8)

### Task 5C.1: §7.6 PageSpan owner cross-thread release stress

**Files:**
- Modify: `python/tests/test_freethreaded_stress.py`

- [ ] **Step 1: Add the cross-thread release stress test**

Append:

```python
class TestPageSpanCrossThreadRelease:
    """§7.6 — independent spans released from different threads, randomly."""

    def test_independent_spans_released_concurrently(self):
        import random
        from timelog import Timelog

        log = Timelog(maintenance="disabled")
        try:
            log.extend([(i, i) for i in range(2048)])
            log.flush()

            errors: list[BaseException] = []
            spans = list(log.views(0, 2048))
            assert len(spans) >= 4, "need multiple spans to test cross-thread release"

            def releaser(my_span, seed):
                rng = random.Random(seed)
                try:
                    # Random delays + buffer access before release
                    for _ in range(rng.randint(0, 10)):
                        try:
                            mv = memoryview(my_span)
                            _ = mv[rng.randint(0, max(0, len(mv) - 1))]
                            mv.release()
                        except (ValueError, BufferError):
                            return
                    my_span.close()
                except BaseException as e:
                    errors.append(e)

            threads = [
                threading.Thread(target=releaser, args=(s, i))
                for i, s in enumerate(spans)
            ]
            for t in threads:
                t.start()
            for t in threads:
                t.join()

            assert not errors, f"cross-thread release surfaced: {errors!r}"
        finally:
            log.close()
```

- [ ] **Step 2: Verify the test exists and is collected**

```bash
PYTHONPATH=$PWD/python python -m pytest python/tests/test_freethreaded_stress.py --collect-only -q 2>&1 | tail -10
```

- [ ] **Step 3: Commit**

```bash
git add python/tests/test_freethreaded_stress.py
git commit -m "test(layer-b): §7.6 PageSpan cross-thread release stress"
```

---

### Task 5C.2: §7.8 drop/drain stress with __del__ side effects

**Files:**
- Modify: `python/tests/test_freethreaded_stress.py`

- [ ] **Step 1: Add the drop/drain stress test**

Append:

```python
class TestDropDrainStress:
    """§7.8 — payloads with __del__ side effects under flush/compact cycles."""

    def test_payloads_with_reentrant_del_no_deadlock(self):
        from timelog import Timelog
        import warnings

        class ReentrantPayload:
            __slots__ = ("val",)

            def __init__(self, val):
                self.val = val

            def __del__(self):
                # Benign re-entry into timelog APIs from finalizer
                try:
                    warnings.warn(f"finalizing {self.val}", stacklevel=1)
                except Exception:
                    pass

        log = Timelog(maintenance="background", maintenance_wakeup_ms=1)
        errors: list[BaseException] = []

        def producer(start, count):
            try:
                for i in range(start, start + count):
                    log.append(i, ReentrantPayload(i))
            except BaseException as e:
                errors.append(e)

        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                threads = [
                    threading.Thread(target=producer, args=(i * 1000, 1000))
                    for i in range(4)
                ]
                for t in threads:
                    t.start()
                # Concurrent flush + compact while producers run
                for _ in range(5):
                    try:
                        log.flush()
                        log.compact()
                    except Exception:
                        pass
                for t in threads:
                    t.join()
                log.flush()
                log.compact()

            assert not errors, f"producer errors: {errors!r}"
        finally:
            log.close()
            gc.collect()
```

- [ ] **Step 2: Commit**

```bash
git add python/tests/test_freethreaded_stress.py
git commit -m "test(layer-b): §7.8 drop/drain stress with reentrant __del__"
```

---

### Task 5C.3: Wire stress tests into the free-threaded CI job

**Files:**
- Modify: `.github/workflows/compatibility-baseline-pr.yml`
- Modify: `.github/workflows/compatibility-baseline-main.yml`
- Modify: `docs/CI_TESTS.md`

- [ ] **Step 1: Ensure the free-threaded leg invokes the stress test file**

In `compatibility-baseline-pr.yml`, find the `freethreading-3.14t-ubuntu` matrix entry. Confirm it runs `run_compat_baseline.py --legs freethreading`. Update `run_compat_baseline.py` to include `python/tests/test_freethreaded_stress.py` in the freethreading leg's pytest invocation if not already covered.

- [ ] **Step 2: Update `_classify_leg` if 0-test edge cases need new handling**

Verify the leg can no longer silently pass with zero tests (already covered in Step 4 fix). Spot-check.

- [ ] **Step 3: Commit**

```bash
git add .github/workflows/compatibility-baseline-pr.yml \
        .github/workflows/compatibility-baseline-main.yml \
        demo/ci/run_compat_baseline.py \
        docs/CI_TESTS.md
git commit -m "ci(layer-b): wire free-threaded stress suite into compat baseline"
```

---

# Phase 6 — Declare no-GIL support

### Task 6.1: Local 3.14t validation before flipping Py_mod_gil

- [ ] **Step 1: Build _timelog against 3.14t locally**

```bash
cmake -B build-py314t -DPython_EXECUTABLE=$(which python3.14t)
cmake --build build-py314t -j$(nproc) 2>&1 | tail -10
```

Expected: clean build. If 3.14t isn't installed locally, install via `uv python install 3.14t` or pyenv equivalent.

- [ ] **Step 2: Run the entire test suite under 3.14t**

```bash
PYTHONPATH=$PWD/python python3.14t -m pytest python/tests -q 2>&1 | tail -20
```

Expected: free-threaded tests run (not skip). All other tests pass. test_free_threading.py still xfails (until Task 6.2).

- [ ] **Step 3: Run with TSan under 3.14t**

```bash
cmake -B build-tsan-py314t \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DCMAKE_C_FLAGS="-fsanitize=thread -g -O1" \
  -DPython_EXECUTABLE=$(which python3.14t)
cmake --build build-tsan-py314t -j$(nproc)
TSAN_OPTIONS="halt_on_error=1:report_signal_unsafe=0" \
  PYTHONPATH=$PWD/python python3.14t -m pytest \
  python/tests/test_freethreaded_stress.py -q 2>&1 | tail -20
```

Expected: no TSan reports. If any, return to Phases 5A/5B and fix.

- [ ] **Step 4: NO COMMIT yet — this is validation only. Proceed only if Step 3 is clean.**

---

### Task 6.2: Flip `Py_mod_gil = Py_MOD_GIL_NOT_USED`

**Files:**
- Modify: `bindings/cpython/src/module.c`
- Modify: `python/tests/test_free_threading.py`

- [ ] **Step 1: Add `Py_mod_gil` slot to `timelog_slots[]`**

In `module.c`, find `timelog_slots[]`. Add (immediately after `Py_mod_multiple_interpreters`):

```c
#if PY_VERSION_HEX >= 0x030D0000
    {Py_mod_gil, Py_MOD_GIL_NOT_USED},
#endif
```

- [ ] **Step 2: Remove the xfail wrapper from test_free_threading.py**

Find `_LAYER_B_XFAIL_REASON` and the try/except that wraps the assertion. Replace with a hard assertion:

```python
def test_import_does_not_enable_gil_on_free_threaded_build():
    if sysconfig.get_config_var("Py_GIL_DISABLED") != 1:
        pytest.skip("requires free-threaded build")
    before = sys._is_gil_enabled()
    assert before is False
    import timelog  # noqa: F401
    after = sys._is_gil_enabled()
    assert after is False, "Importing timelog must not re-enable the GIL"
```

- [ ] **Step 3: Build + run on 3.14t**

```bash
cmake --build build-py314t -j$(nproc) 2>&1 | tail -5
PYTHONPATH=$PWD/python python3.14t -m pytest python/tests/test_free_threading.py -v 2>&1 | tail -10
```

Expected: test PASSES (GIL stays disabled after import).

- [ ] **Step 4: Run full suite on 3.14t**

```bash
PYTHONPATH=$PWD/python python3.14t -m pytest python/tests -q 2>&1 | tail -20
```

Expected: all PASS.

- [ ] **Step 5: Commit**

```bash
git add bindings/cpython/src/module.c python/tests/test_free_threading.py
git commit -m "feat(layer-b): declare Py_mod_gil = Py_MOD_GIL_NOT_USED on 3.13+"
```

---

# Phase 7 — Stress validation lab

### Task 7.1: TSan sweep across full test surface on 3.14t

- [ ] **Step 1: Run the entire test suite under TSan + 3.14t**

```bash
TSAN_OPTIONS="halt_on_error=0:report_signal_unsafe=0:second_deadlock_stack=1" \
  PYTHONPATH=$PWD/python python3.14t -m pytest python/tests -q 2>&1 | tee /tmp/tsan-run.log | tail -30
grep -E "^(WARNING|ERROR): ThreadSanitizer" /tmp/tsan-run.log | wc -l
```

Expected: zero TSan reports.

- [ ] **Step 2: If any reports — file as findings, fix, re-run.**

This is iterative. Each report should be addressed by either:
- Adding a missing critical section
- Promoting a field to atomic
- Refactoring the offending site to follow collect/unlock/execute

- [ ] **Step 3: NO COMMIT for the sweep itself; commits arrive with each fix.**

---

# Phase 8 — Packaging, docs, acceptance

### Task 8.1: pyproject.toml — add cp314t to cibuildwheel build set

**Files:**
- Modify: `pyproject.toml`

- [ ] **Step 1: Find and update the cibuildwheel `build` line**

In `pyproject.toml`, find:

```toml
build = "cp312-* cp313-* cp314-*"
```

Replace with:

```toml
build = "cp312-* cp313-* cp314-* cp314t-*"
```

(Leave `cp313t` out — spec §6.10 says "explicitly tested only.")

- [ ] **Step 2: Confirm the package still builds (regular)**

```bash
pip install -e . 2>&1 | tail -5
```

- [ ] **Step 3: Commit**

```bash
git add pyproject.toml
git commit -m "build(layer-b): add cp314t to cibuildwheel matrix"
```

---

### Task 8.2: Packaging CI matrix — add cp314t leg

**Files:**
- Modify: `.github/workflows/packaging-pr.yml`
- Modify: `.github/workflows/release-pypi.yml`

- [ ] **Step 1: Add a `cp314t` matrix entry to each workflow**

For `packaging-pr.yml`, add:

```yaml
- python: "3.14t"
  python-abi: "cp314t"
```

…to the existing matrix. Make the job non-required initially (continue-on-error: false but track failure separately).

For `release-pypi.yml`, same.

- [ ] **Step 2: Update `CIBW_BUILD` env if needed to include `cp314t-*` filter**

- [ ] **Step 3: Commit**

```bash
git add .github/workflows/packaging-pr.yml .github/workflows/release-pypi.yml
git commit -m "ci(layer-b): add cp314t wheel build leg"
```

---

### Task 8.3: Docs sweep — remove blanket "GIL required" claims

**Files:**
- Modify: `python/timelog/__init__.py`
- Modify: `bindings/cpython/include/timelogpy/py_timelog.h`
- Modify: `bindings/cpython/include/timelogpy/py_handle.h`
- Modify: `docs/python-api.md`
- Modify: `docs/internals/components/python-binding-architecture.md`

- [ ] **Step 1: Run the static check to surface all current violations**

```bash
python demo/ci/check_layer_a_static.py 2>&1 | tail -20
```

(After Task 6.2, this may now flag the previously-allowed "Free-threaded… unsupported until Layer B" sentinel. Update the sentinel wording.)

- [ ] **Step 2: Rewrite each flagged comment / docstring**

For each file, replace blanket GIL-required claims with the new contract:

- `python/timelog/__init__.py:80-81`: replace with "Supported on regular CPython 3.12+, isolated subinterpreters (3.12+), and free-threaded CPython 3.14t+."
- `py_timelog.h:13`: rewrite the thread-safety note to describe the per-instance lock + critical-section model
- `py_handle.h`: rewrite the 6 "GIL held" comments to "owning interpreter attached" or "live_lock held" depending on the actual contract
- `docs/python-api.md:14-15`: update the support claim
- `docs/internals/components/python-binding-architecture.md:22-23`: update to describe the new synchronization model

- [ ] **Step 3: Re-run static check — expect zero violations**

```bash
python demo/ci/check_layer_a_static.py 2>&1
```

Expected: "Layer A static regression check passed."

- [ ] **Step 4: Commit**

```bash
git add python/timelog/__init__.py \
        bindings/cpython/include/timelogpy/py_timelog.h \
        bindings/cpython/include/timelogpy/py_handle.h \
        docs/python-api.md \
        docs/internals/components/python-binding-architecture.md
git commit -m "docs(layer-b): replace GIL-required claims with attached-thread-state model"
```

---

### Task 8.4: Final acceptance checklist verification

- [ ] **Step 1: Walk LLD §10 — check each item against code with file:line evidence**

Produce `docs/superpowers/plans/2026-05-17-step5-8-completion-ACCEPTANCE.md` with a table:

| # | Item | Status | Evidence |
|---|---|---|---|
| 1 | `m_size != -1` | ✅ | `module.c:444` `sizeof(tl_py_module_state_t)` |
| 2 | multi-phase init | ✅ | `module.c:455` `Py_mod_exec` slot |
| 3 | idempotent exec + unwind | ✅ | `test_py_module_exec.c:765` retry_after_each_failpoint |
| 4 | no process-global Python objects | ✅ | static check passes |
| 5 | per-module exceptions | ✅ | `py_errors.c` |
| 6 | all heap types | ✅ | `PyType_FromModuleAndSpec` in all 6 type files |
| 7 | no static binding `PyTypeObject` | ✅ | `check_layer_a_static.py` passes |
| 8 | atomic `tl_pagespan_owner.refcnt` | ✅ | `core/src/query/tl_pagespan_iter.c:43` |
| 9 | no GIL-as-lock | ✅ | TSan + stress |
| 10 | no decref/warning under any internal lock | ✅ | Phase 5A.5 refactor + audit |
| 11 | live tracking + object state synchronized | ✅ | `live_lock` + critical sections |
| 12 | maintenance thread no Python C-API | ✅ | grep `core/src/maint/` |
| 13 | `Py_MOD_PER_INTERPRETER_GIL_SUPPORTED` | ✅ | `module.c:457` |
| 14 | `Py_MOD_GIL_NOT_USED` | ✅ | Task 6.2 |
| 15 | free-threaded import doesn't enable GIL | ✅ | `test_free_threading.py` passes |
| 16 | subinterpreter tests pass | ✅ | `test_subinterpreters.py` |
| 17 | concurrent stress + cross-thread tests pass | ✅ | `test_freethreaded_stress.py` |
| 18 | docs no GIL-required claims | ✅ | Task 8.3 |
| 19 | dual wheel families | ✅ | Task 8.1 + 8.2 |

- [ ] **Step 2: Commit the acceptance evidence**

```bash
git add docs/superpowers/plans/2026-05-17-step5-8-completion-ACCEPTANCE.md
git commit -m "docs(layer-b): record acceptance checklist evidence"
```

---

## Self-review notes

This plan should be self-contained. Every step has either exact code or an exact command. The TDD cycle is preserved at the file/function granularity (write failing test → run → minimal impl → run → commit) where the test can be authored in isolation. For tests that only fail under true parallel execution (CV-2 critical sections), the plan acknowledges this and relies on the Phase 5C stress suite under TSan + 3.14t in Phase 7 as the genuine race-exposure gate — not on the per-task tests which would pass by GIL-coincidence on regular builds.

The plan deliberately delays `Py_mod_gil = Py_MOD_GIL_NOT_USED` (Task 6.2) until after Phases 5A-5C and Phase 6.1 local validation, per spec §11 Step 6's "enable only after the free-threaded checkpoint is satisfied" rule. If any TSan finding remains open at Phase 7, do NOT proceed to Task 6.2 — fix the root cause first.

After this plan completes, the LLD §10 acceptance checklist is fully checked. Phase 8 closes documentation, packaging, and release readiness. The branch is then ready for merge.
