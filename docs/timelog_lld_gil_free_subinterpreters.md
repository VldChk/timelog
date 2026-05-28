# Timelog LLD: GIL-free support and independent subinterpreters

Date: 2026-04-12
Primary design target: CPython 3.14+
Secondary compatibility targets:
- regular GIL-enabled CPython 3.12-3.14 when validated
- isolated subinterpreters with per-interpreter GIL
- free-threaded / no-GIL CPython build

## 1. Goal

Upgrade the `timelog` CPython binding so that:

1. it is **safe to import and use from multiple isolated subinterpreters** without sharing Python module state;
2. it is **safe to import into a free-threaded CPython build without re-enabling the GIL**;
3. it preserves the current storage-engine semantics:
   - single-writer API contract remains in force;
   - snapshot iterators remain concurrent-read safe;
   - background maintenance thread must never execute Python C-API work directly;
4. it continues to support the existing high-level Python API with minimal user-visible breakage.

This LLD is intentionally split into two compatibility layers:

- **Layer A: interpreter isolation** — multi-phase init, per-module state, heap types, no process-global Python objects.
- **Layer B: free-threaded safety** — explicit synchronization for all shared extension state that currently relies on the GIL.

These two layers should be implemented in sequence. Layer A is necessary for subinterpreters. Layer B is necessary before declaring `Py_mod_gil = Py_MOD_GIL_NOT_USED`.

## 2. Non-goals

The following are **not** part of this migration:

- changing the underlying C storage engine concurrency model from single-writer to multi-writer;
- making arbitrary object payloads cross-interpreter transferable;
- preserving exact identity equality of module classes/exceptions across separate module objects/interpreters;
- stable ABI / limited C API compatibility for free-threaded wheels.

## 3. Current-state blockers in the repository

The current codebase has four hard blockers:

### B1. Single-phase module init and no module state

`module.c` currently builds the module with `PyModule_Create()` and `m_size = -1`.

Impact:
- no per-module state;
- legacy single-phase behavior;
- incompatible with robust subinterpreter isolation;
- cannot express free-threading opt-in using the multi-phase slot path.

### B2. Process-global Python exception objects

`py_errors.c` stores `TlPy_TimelogError` and `TlPy_TimelogBusyError` in process-global `PyObject *` variables.

Impact:
- exception objects are shared across interpreters;
- violation of module isolation;
- wrong lifetime model under repeated imports / reinitialization.

### B3. Static global type objects

`py_timelog.c` and the iterator/span files define extension types as static `PyTypeObject` instances, readied with `PyType_Ready()` and exported from module init.

Impact:
- process-global types;
- methods cannot directly and safely recover per-module state;
- global error/type linkage leaks across interpreters.

### B4. Pre-Layer-B synchronization invariants

`py_handle.c` now ties retired-object draining and live-tracking operations to the owning interpreter, and the core PageSpan owner refcount is atomic. The binding also releases the GIL around engine operations and uses per-instance `core_lock`, but not all mutable extension state is protected by the object-level synchronization needed for a free-threaded/no-GIL build.

Impact:
- free-threaded build correctness is not established;
- some shared extension state is only accidentally safe today because the GIL serializes access;
- `views()` / `PageSpan` lifetime no longer depends on interpreter-lock serialization of owner refs, but PageSpan object fields still need object-level critical sections for no-GIL support;
- thread-state and interpreter ownership checks remain required anywhere Python references are drained or released.

### B5. Public facade and docs must stay phase-accurate

The binding headers and Python facade must distinguish regular CPython and
per-interpreter-GIL support from the still-unsupported free-threaded/no-GIL
target.

Impact:
- release notes, docs, and runtime claims can drift from the actual implementation state;
- support declarations must move in lockstep across the C layer, Python facade, packaging, and CI.

## 4. Target behavior and guarantees

### 4.1 Compatibility matrix

| Python mode | Import allowed | API usable | Support tier | Parallelism model | Notes |
|---|---:|---:|---|---|---|
| CPython 3.12-3.14, normal build | yes | yes | validated compatibility | current single-writer + concurrent reads | keep supporting when CI-covered |
| CPython 3.14+, isolated subinterpreters | yes | yes | primary target after Layer A | one module object per interpreter | do not declare support until heap types land and no global Python objects remain |
| CPython 3.14+, free-threaded build | yes | yes | official target after Layer B | true thread parallelism within interpreter, but still single-writer API | import must not enable the GIL |
| CPython 3.13t, free-threaded build | optional | optional | experimental only | same as above | build/publish only if explicitly tested |

### 4.2 Required guarantees

1. **Per-interpreter module objects**
   - importing `timelog._timelog` in two interpreters must create independent module objects;
   - each module object owns its exceptions, heap types, and C module state.

2. **No process-global Python objects**
   - no exception, type, capsule, cached Python object, or Python callback is stored in a global `static` variable.

3. **Attached-thread-state discipline**
   - any thread executing Python C-API work must have an attached thread state;
   - this requirement holds even in free-threaded builds.

4. **Background maintenance isolation**
   - the storage-engine maintenance thread must never perform `Py_DECREF`, `PyObject_*`, `PyErr_*`, or other Python C-API calls directly;
   - dropped handles continue to be enqueued and drained by Python-attached threads only.

5. **Single-writer contract preserved**
   - the library continues to require external serialization of write and lifecycle methods;
   - this contract is documented and enforced where practical.

6. **Free-threaded import does not flip the GIL on**
   - on a free-threaded 3.14 interpreter with the GIL disabled, importing `timelog` must not re-enable the GIL.

## 5. Architecture after migration

## 5.1 Module initialization architecture

The extension moves from legacy single-phase init to **multi-phase init**.

### New module definition

```c
typedef struct {
    int initialized;

    /* exceptions */
    PyObject *exc_timelog_error;
    PyObject *exc_timelog_busy_error;

    /* heap types */
    PyObject *type_timelog;
    PyObject *type_timelog_iter;
    PyObject *type_pagespan;
    PyObject *type_pagespan_iter;
    PyObject *type_pagespan_objects_view;
    PyObject *type_pagespan_objects_view_iter;
} timelog_module_state;
```

```c
static struct PyModuleDef_Slot timelog_slots[] = {
    {Py_mod_exec, timelog_exec},
#if PY_VERSION_HEX >= 0x030C0000
    {Py_mod_multiple_interpreters, Py_MOD_PER_INTERPRETER_GIL_SUPPORTED},
#endif
#if defined(TIMELOG_ENABLE_FREE_THREADED_SUPPORT) && PY_VERSION_HEX >= 0x030D0000
    {Py_mod_gil, Py_MOD_GIL_NOT_USED},
#endif
    {0, NULL},
};

static struct PyModuleDef timelog_module = {
    PyModuleDef_HEAD_INIT,
    "timelog._timelog",
    module_doc,
    sizeof(timelog_module_state),
    NULL,
    timelog_slots,
    timelog_traverse,
    timelog_clear,
    timelog_free,
};
```

### Initialization flow

1. import machinery allocates module object + zeroed module state;
2. `timelog_exec(module)` does:
   - classify state as empty, complete, or invalid;
   - if state is complete, transactionally re-export the existing module-owned exceptions and public types, then return success;
   - exceptions;
   - heap types via `PyType_FromModuleAndSpec()`;
   - transactional module exports;
3. if initialization fails partway through, unwind partial state explicitly, leave `initialized = 0`, and return failure;
4. set `initialized = 1` only after the module object is fully ready;
5. module methods and type methods recover state from the module/type, never from globals.

### Why this shape

- per-module state provides one state block per module object;
- new module objects in new interpreters get fresh state;
- same-module `Py_mod_exec` is explicitly idempotent instead of vaguely "rerunnable";
- the module slots carry subinterpreter / free-threaded declarations.

Important staging rule:
- after Layer A/Step 4, advertise `Py_MOD_PER_INTERPRETER_GIL_SUPPORTED` on CPython 3.12+;
- do not advertise `Py_MOD_GIL_NOT_USED` until Layer B locking and lifetime work is complete.

Here `TIMELOG_ENABLE_*` is pseudocode for rollout gates, not a permanent public macro surface. The real implementation can spell those gates differently, but the declarations themselves must remain phase-gated.

## 5.2 Type architecture

All reachable binding types are converted from static types to **heap types** created per-module.

Completing this conversion is part of Layer A, not a later optional polish pass. Until every reachable type is a module-owned heap type wired to module state, interpreter isolation is not complete.

### Types affected

- `Timelog`
- `TimelogIter`
- `PageSpan`
- `PageSpanIter`
- `PageSpanObjectsView`
- `PageSpanObjectsViewIter`

### Construction pattern

Each type gets:

- a `PyType_Spec`;
- a `PyType_Slot[]` table;
- creation in `timelog_exec()` through `PyType_FromModuleAndSpec()`;
- storage both in module state and module `__dict__`.

Global `Py*_Check` macros and direct `PyObject_GC_New(..., &StaticType)` allocation paths are replaced by module-state-aware helpers. Production code must stop depending on process-global `PyTypeObject` symbols for type checks, allocation, or method dispatch.

### Required flags

For types that were intentionally non-instantiable from Python:
- add `Py_TPFLAGS_DISALLOW_INSTANTIATION`.

For GC-tracked heap instances:
- add `Py_TPFLAGS_HAVE_GC`;
- implement `tp_traverse` and `tp_clear` correctly;
- visit `Py_TYPE(self)` in `tp_traverse` where required.

### Accessing module state from methods

#### Regular methods

Methods that can use the defining class should switch to `METH_METHOD | METH_FASTCALL | METH_KEYWORDS` where practical and recover state with:

```c
timelog_module_state *st = PyType_GetModuleState(defining_class);
```

#### Slot methods / getters / setters

For slots like `tp_dealloc`, `tp_iter`, `tp_iternext`, or getters/setters, recover the module object using:

```c
PyObject *module = PyType_GetModuleByDef(Py_TYPE(self), &timelog_module);
timelog_module_state *st = PyModule_GetState(module);
```

#### Type-check / allocation helpers

For C paths that historically used static type globals:

```c
PyObject_TypeCheck(op, &SomeTimelogType)
PyObject_GC_New(SomeObject, &SomeTimelogType)
```

replace them with helpers that recover the module-local heap type first and then:

- use `PyObject_TypeCheck(op, (PyTypeObject *)type_obj)` with the module-owned type;
- allocate via the recovered heap type rather than a global `PyTypeObject`.

### Error routing rule

No code path may reference a global exception singleton. All raising helpers accept or recover module state.

## 5.3 Error subsystem architecture

`py_errors.c` is rewritten so that exceptions are module-owned.

### New API

```c
int TlPy_InitErrors(PyObject *module, timelog_module_state *st);
void TlPy_ClearErrors(timelog_module_state *st);
int TlPy_StateHasCompleteErrors(const timelog_module_state *st);
PyObject *TlPy_RaiseFromState(timelog_module_state *st,
                              tl_status_t status);
PyObject *TlPy_RaiseFromStateFmt(timelog_module_state *st,
                                 tl_status_t status,
                                 const char *fmt, ...);
PyObject *TlPy_RaiseFromObject(PyObject *obj,
                               tl_status_t status);
PyObject *TlPy_RaiseFromObjectFmt(PyObject *obj,
                                  tl_status_t status,
                                  const char *fmt, ...);
```

### Mapping table

| Engine status | Python exception |
|---|---|
| `TL_EINVAL` | `ValueError` |
| `TL_ENOMEM` | `MemoryError` |
| `TL_EOVERFLOW` | `OverflowError` |
| `TL_EBUSY` | module-local `TimelogBusyError` |
| `TL_ESTATE`, default | module-local `TimelogError` |
| `TL_EINTERNAL` | `SystemError` |

### Design note

Custom exception identity is module-local. That is correct under isolation and must be accepted.
After Step 4, live objects recover their originating module state through heap type APIs, so manual reload/reimport creates a new module identity without corrupting existing objects.

## 5.4 Internal synchronization model

The current implementation already has a **per-instance core lock** guarding engine access and releases the GIL around blocking engine work. The migrated design keeps that lock but stops treating the GIL as a correctness primitive.

### Lock inventory after migration

#### L1. `PyTimelog.core_lock`

Purpose:
- serialize mutable access to one `Timelog` instance across lifecycle and engine entrypoints.

Protects:
- `self->tl`
- `self->closed`
- lifecycle transitions (`open -> running -> closing -> closed`)
- engine calls that should not overlap on one instance

#### L2. `handle_ctx.live_lock` (new)

Purpose:
- protect the live-handle multiset / hash table, which currently assumes GIL serialization.

Protects:
- `live_entries`
- `live_cap`
- `live_len`
- `live_tombstones`
- `live_tracking_failed`
- live-table scans used by traversal / cleanup paths

Implementation:
- `PyMutex` or `PyThread_type_lock`
- prefer `PyMutex` if already available in minimum supported CPython without portability pain

#### L3. `handle_ctx.retired_head` + atomic counters (existing)

Purpose:
- lock-free retired object queue from maintenance thread to Python-attached drainer.

Keep:
- Treiber stack structure;
- atomic pin counters;
- atomic retired/drained metrics.

Change:
- debug assertions must stop checking “GIL held” and instead validate “attached thread state present” where relevant.

#### L4. Critical sections for Python-visible mutable object fields

Use `Py_BEGIN_CRITICAL_SECTION` / `Py_END_CRITICAL_SECTION` only where Python object internals or extension object fields may be concurrently accessed from multiple threads.

Use cases:
- reading/writing internal Python-owned state that would previously have been implicitly protected by the GIL;
- protecting dict iteration with `PyDict_Next` if the dict might be concurrently modified.

Do **not** use critical sections as a replacement for the storage engine’s own locks. They are for Python-object-level protection and deadlock-aware interaction with CPython’s locking rules. Keep them as leaf scopes around object-local field access, not around engine calls or arbitrary cleanup.

#### L5. Core `tl_pagespan_owner.refcnt` (new core requirement)

Purpose:
- allow `PageSpan` owners to survive incref/decref from distinct Python threads in free-threaded builds.

Protects:
- lifetime of the snapshot-owning pagespan owner returned by `views()` / `page_spans()`.

Implementation:
- change `tl_pagespan_owner.refcnt` from plain `uint32_t` to an atomic refcount in core;
- keep owner destruction one-shot and preserve the existing release-hook ordering;
- do not rely on binding-side locks or the GIL to serialize owner lifetime.

Rationale:
- `PageSpan` objects can outlive their iterator and be released independently on different threads;
- therefore `views()` cannot be considered free-threaded-safe unless this core refcount contract is fixed.

### Hard invariant: no Python-executing work under internal locks

Before any operation that may execute Python or trigger user callbacks/finalizers, release:

- `core_lock`
- `live_lock`
- any active Python object critical section

This rule applies to paths involving:

- `Py_DECREF`, `Py_XDECREF`, `Py_CLEAR`
- weakref callbacks or `__del__`
- warning emission or other helper paths that can re-enter Python

Required pattern:

1. collect/remove references under the relevant lock(s);
2. release internal lock(s);
3. perform decref / warning / callback-capable work;
4. reacquire only if a later non-Python section still needs locking.

### Lock ordering

To avoid ABBA deadlocks, the binding uses this order:

1. attach thread state if needed
2. acquire `core_lock` when entering instance lifecycle or engine state
3. acquire `live_lock` only inside small bounded sections
4. enter Python object critical sections only for short object-local field access
5. release `core_lock`, `live_lock`, and critical sections before any Python-executing work
6. never hold `core_lock` while entering potentially blocking Python operations unrelated to the instance

Existing code already releases `core_lock` before reacquiring Python execution after `Py_BEGIN_ALLOW_THREADS` sections. Keep that rule.

### Synchronization matrix

| Object / state | Protection | Notes |
|---|---|---|
| `PyTimelog.tl`, lifecycle state, `closed` | `core_lock` | No unlocked production reads unless a dedicated atomic mirror is introduced and documented. |
| `tl_py_handle_ctx.live_*` | `live_lock` | Mutate and scan under lock; move references out before decref. |
| `tl_py_handle_ctx.retired_head`, `pins`, retired/drained metrics | atomics | Maintenance-thread safe; no Python C API allowed. |
| `tl_pagespan_owner.refcnt` | atomic refcount in core | Required for free-threaded `views()` / `PageSpan` lifetime. |
| `PyTimelogIter.closed`, `iter`, `pinned_snapshot`, `owner`, `remaining_count`, `remaining_valid` | object critical section | Same iterator instance remains semantically non-thread-safe; this protection prevents races/UAF during accidental overlap. |
| `PyPageSpan.closed`, `exports` | object critical section | `close()`, buffer acquire/release, and property access can overlap in free-threaded builds. |
| `PyPageSpan.ts`, `h`, `len`, `first_ts`, `last_ts` | immutable after construction; invalidated only under PageSpan critical section | Readers must observe either open+valid or closed+invalid state. |
| `PyPageSpanIter.closed`, `iter`, `timelog` | object critical section | Same iterator instance remains semantically non-thread-safe. |
| `PyPageSpanObjectsView.span` and `PyPageSpanObjectsViewIter.view` | immutable strong references | Mutable cursor state, if any, is object-local and protected by the iterator object's critical section. |

### State machine for `Timelog`

```text
UNINITIALIZED
  -> INITIALIZED
  -> RUNNING
  -> CLOSING
  -> CLOSED
  -> REOPENING (optional path)
  -> RUNNING
```

Rules:
- transitions are only made under `core_lock`;
- `closed` is protected by `core_lock` unless the implementation deliberately introduces a documented atomic mirror;
- any fast-path unlocked `closed` checks must be audited and removed or atomically synchronized.

## 5.5 Thread-state discipline

The binding must stop equating “safe to use Python C API” with “holding the GIL”. Under free-threaded CPython, Python C API access still requires an **attached thread state** even when the GIL is disabled.

### Rules

1. Python-created threads entering binding methods already have an attached thread state.
2. Threads created outside Python must attach a thread state before calling Python C API.
3. The maintenance thread remains **non-Python** and must not attach solely to do reference-counting work; instead it continues to enqueue drops.
4. `Py_BEGIN_ALLOW_THREADS` / `Py_END_ALLOW_THREADS` remain valid around blocking engine calls, because they detach/reattach thread state appropriately.

### `PyGILState_*` restriction

Do not build new correctness logic around `PyGILState_Ensure()` for background or cross-interpreter work. Under subinterpreters, `PyGILState_*` is delicate and can attach to the wrong interpreter if misused.

## 5.6 Handle lifetime architecture

This is the most sensitive part of the migration.

### Current invariant worth preserving

- `on_drop_handle()` runs on maintenance thread and must never call Python C API.
- decref/finalizer execution happens only in a Python-attached drain path.
- pin counting prevents draining while snapshots/iterators may still expose objects.

### Required redesign

#### Drain precondition

Change debug contract from:
- “GIL held”

to:
- “thread has attached thread state and is allowed to execute Python C API”.

#### Live tracking

Move live tracking off implicit GIL protection to explicit `live_lock`.

Required pattern:
- mutate or scan the live table under `live_lock`;
- if cleanup needs `Py_DECREF`, first detach the to-be-released references from the table under lock;
- then drop `live_lock` and perform decrefs outside all internal locks.

#### Finalizer safety

`Py_DECREF` may run arbitrary Python (`__del__`, weakref callbacks, destructors). Therefore:
- drain only from attached Python threads;
- never drain from maintenance thread;
- preserve existing reentrancy guard;
- never hold `core_lock`, `live_lock`, or object critical sections across decref-capable cleanup;
- preserve force-drain path during close, but only when not in interpreter finalization.

#### Finalization behavior

During interpreter finalization:
- skip Python-aware cleanup paths that may attach or execute arbitrary Python;
- keep C-only engine shutdown best effort;
- leak-avoidance is secondary to shutdown safety.

## 5.7 Python facade behavior

The pure Python `timelog` package is a contract surface and must be updated.

### Changes

1. Remove stale blanket statements that present the extension as tied only to the process-wide CPython lock or permanently unable to support free-threaded builds.
   - this includes binding headers, facade docstrings, top-level docs, and any runtime warnings that still make CPython-GIL-required claims.
   - blanket GIL-required language is stale once subinterpreter isolation and free-threaded support work begins landing.
2. Replace them with phase-accurate concurrency guarantees:
   - single-writer remains required;
   - concurrent snapshot iteration is supported;
   - subinterpreter import is supported only after Layer A exit criteria are met;
   - free-threaded import is officially supported only after Layer B exit criteria are met on designated versions/builds;
   - module/type/exception isolation is a prerequisite for claiming subinterpreter support.
3. Add small runtime helpers:
   - `_supports_free_threading()` based on `sysconfig.get_config_var("Py_GIL_DISABLED")`
   - `_gil_enabled()` using `sys._is_gil_enabled()` when present
4. Provide targeted warnings only during transition phases if a feature flag says free-threaded support is provisional.

### Non-goal

The Python facade should **not** attempt to emulate cross-interpreter object passing. That belongs to interpreter-level orchestration and user code.

## 5.8 Build and packaging architecture

### Wheel matrix

Build distinct wheels with explicit support tiers:
- regular ABI: `cp312`, `cp313`, `cp314` when validated by CI
- official free-threaded ABI: `cp314t`
- optional experimental free-threaded ABI: `cp313t` only if explicitly tested and documented as experimental

### Important packaging constraints

- free-threaded builds currently require separate wheels;
- the free-threaded build does not support the limited C API / stable ABI;
- Windows builds need `Py_GIL_DISABLED=1` defined explicitly when building extension sources.

### Suggested build policy

- regular wheels: continue as today, but only claim support for versions still covered by CI
- free-threaded wheels:
  - opt out of `py_limited_api`
  - tag and test separately
  - publish official support only after the free-threaded test suite passes
  - do not publish `cp313t` as if it were first-class support unless it has dedicated coverage

## 6. File-by-file implementation plan

## 6.1 `bindings/cpython/src/module.c`

### Change set

- replace `PyModule_Create()` path with multi-phase init;
- define `timelog_module_state`;
- add `state->initialized` and make `timelog_exec()` explicitly idempotent on the same module object;
- add module slots:
  - `Py_mod_exec`
  - `Py_mod_multiple_interpreters = Py_MOD_PER_INTERPRETER_GIL_SUPPORTED` **only after Layer A is complete**
  - `Py_mod_gil = Py_MOD_GIL_NOT_USED` **only after Layer B is complete**
- implement `m_traverse`, `m_clear`, `m_free`;
- create/export heap types inside `timelog_exec()`;
- initialize exceptions via module-state-aware initializer;
- ensure partial-init failure unwinds state cleanly and leaves `initialized = 0`.

### Acceptance criteria

- multiple imports in separate subinterpreters succeed;
- same-module `timelog_exec()` is idempotent;
- no process-global Python objects remain reachable from module init code.

## 6.2 `bindings/cpython/src/py_errors.c` / `.h`

### Change set

- delete process-global exception pointers;
- define module-state-aware init/clear/raise helpers;
- update all call sites to pass or recover module state;
- keep fallback to built-in exceptions where appropriate.

### Acceptance criteria

- exception types are distinct per module object;
- `TimelogBusyError` still subclasses `TimelogError`;
- all error paths work in subinterpreters.

## 6.3 `bindings/cpython/src/py_timelog.c` / `.h`

### Change set

- convert the `Timelog` binding type from static `PyTypeObject` storage to `PyType_Spec`;
- use heap type flags and GC hooks where needed;
- route all module-state access through `PyType_GetModuleState()` or `PyType_GetModuleByDef()`;
- replace global-type check / allocation helpers with module-local heap-type lookup;
- audit all reads/writes of `self->closed`, `self->tl`, `self->core_lock`;
- keep `core_lock` as the authoritative per-instance serialization primitive;
- update close/finalizer/reopen paths for interpreter-finalization safety.

### Acceptance criteria

- `Timelog` can be imported in more than one interpreter in the same process;
- no static type objects remain for reachable binding classes;
- all methods compile and function with the heap-type access pattern.

## 6.4 `bindings/cpython/src/py_iter.c`

### Change set

- convert the `TimelogIter` binding type to a heap type;
- ensure iterator holds strong references required for snapshot/module/type lifetime;
- route errors through module state;
- protect iterator-local mutable fields according to the synchronization matrix;
- audit dealloc and traversal for heap-type GC protocol.

### Acceptance criteria

- iterator creation/use/deallocation succeeds across interpreters;
- no Python object lifetime depends on process-global type storage.

## 6.5 `bindings/cpython/src/py_span.c`, `py_span_iter.c`, `py_span_objects.c`

### Change set

- convert all span-related types to heap types;
- ensure views/iterators preserve module/type/snapshot lifetime correctly;
- use `PyType_GetModuleByDef()` for slot methods when needed;
- protect `closed`, `exports`, and iterator-local mutable state according to the synchronization matrix;
- audit any borrowed-reference and direct-field usage for free-threaded safety.

### Acceptance criteria

- `views()` API behaves the same in regular and free-threaded builds;
- concurrent read-only iteration remains safe.

## 6.6 `core/src/query/tl_pagespan_iter.c` / `.h`

### Change set

- replace plain `tl_pagespan_owner.refcnt` with an atomic refcount in core;
- define the memory-ordering contract for owner incref/decref and one-shot destroy;
- preserve the current release-hook ordering and "free owner before hook" invariant;
- update comments to remove any statement that the GIL provides required serialization.

### Acceptance criteria

- spans remain valid after iterator close exactly as today;
- independent `PageSpan` objects can be released from different Python threads in free-threaded builds without corruption;
- `views()` no longer depends on a GIL-era core refcount contract.

## 6.7 `bindings/cpython/src/py_handle.c` / `.h`

### Change set

- replace old lock-presence assertions with attached-thread-state checks or documented preconditions;
- introduce `live_lock` for live-entry hash table;
- audit retired/drain queue memory ordering but keep lock-free queue design;
- ensure drain paths only execute under attached Python threads;
- restructure live-table cleanup so references are detached under `live_lock` and decref'd only after all internal locks are released;
- make traversal / clear paths obey the same synchronization rules instead of iterating mutable state under implicit GIL assumptions;
- update comments and invariants to stop relying on the GIL as a lock;
- audit any use of `PyGILState_Check()` and keep it for diagnostics only if still meaningful.

### Acceptance criteria

- stress tests show no race or corruption in live-entry accounting;
- object drops do not call Python APIs from maintenance thread;
- close/finalizer paths do not deadlock under free-threaded execution.

## 6.8 `bindings/cpython/include/timelogpy/*.h`

### Change set

- add module-state struct definitions and access helpers;
- expose heap-type creation helpers instead of static `PyTypeObject` symbols where possible;
- update public comments to the new attached-thread-state and locking contract.

## 6.9 `python/timelog/__init__.py` and `_api.py`

### Change set

- update top-level docstrings and warnings;
- add feature-detection helpers and test support utilities;
- remove user-visible CPython-GIL-required claims;
- preserve user API surface.

### Acceptance criteria

- docs match actual runtime support;
- slice and convenience helpers remain behaviorally unchanged.

## 6.10 `pyproject.toml` and CI workflows

### Change set

- add official free-threaded build targets (`cp314t`) and optional experimental targets (`cp313t`) only when explicitly tested;
- disable limited API for free-threaded wheels if ever enabled later;
- add test jobs for:
  - regular 3.14
  - free-threaded 3.14
  - subinterpreter suite on 3.14
- on Windows, define `Py_GIL_DISABLED=1` for free-threaded builds.

### Acceptance criteria

- wheels are produced for both ABI families;
- free-threaded import test proves the GIL stays disabled;
- subinterpreter test suite passes.

## 7. Testing strategy

## 7.1 Unit tests

### T1. Subinterpreter import smoke test

Goal:
- import `timelog` inside an isolated interpreter and perform `open -> append -> iterate -> close`.

Mechanism:
- use `concurrent.interpreters` on Python 3.14.

Expected:
- import succeeds;
- no `ImportError` related to extension compatibility;
- methods behave normally.

This test becomes a required pass gate only after Phase C, when true Layer A isolation is complete.

## 7.2 Multi-interpreter independence test

Goal:
- prove module-local exceptions/types are not process-global.

Test:
- import in interpreter A and B;
- raise `TimelogError` in each;
- verify identities are distinct per interpreter while semantics remain correct.

## 7.3 Multi-phase exec idempotence and unwind test

Goal:
- make `timelog_exec()` behavior concrete instead of relying on a vague “rerunnable” promise.

Test:
- add a binding-level C unit test or dedicated internal test helper that constructs a module object and invokes `timelog_exec()` twice on the same module object;
- verify the second call is a no-op success and does not duplicate exceptions, heap types, or module exports;
- add failure injection at one or more intermediate init points (for example after exception creation and after first heap type creation);
- verify partial failure unwinds correctly, leaves `initialized = 0`, and allows a subsequent clean exec attempt on the same module object once failure injection is removed.

Expected:
- same-module `timelog_exec()` is idempotent;
- no partially initialized module state leaks across failure/retry;
- no duplicate heap types or exceptions are created.

## 7.4 Free-threaded import test

Goal:
- prove import does not enable the GIL.

Test:
- only run when `sysconfig.get_config_var("Py_GIL_DISABLED") == 1`;
- assert `not sys._is_gil_enabled()` before import;
- import `timelog`;
- assert `not sys._is_gil_enabled()` after import.

## 7.5 Concurrent read stress

Goal:
- prove snapshot iterators and span views remain safe under actual thread parallelism.

Test:
- one writer thread externally serialized;
- N reader threads repeatedly acquire snapshots/iterators/views;
- validate no crashes, refcount corruption, or stale-pointer behavior.

## 7.6 PageSpan owner cross-thread release stress

Goal:
- prove the core `tl_pagespan_owner` lifetime contract no longer relies on GIL-era caller serialization.

Test:
- create many `PageSpan` objects from `views()` / `page_spans()` and hand independent span objects to different Python threads in a free-threaded build;
- randomly drop spans, close iterators, and release sibling objects in overlapping orders;
- run the test under sanitizer-enabled native jobs where practical.

Expected:
- no use-after-free, double free, or refcount corruption;
- spans remain valid for exactly the lifetime contract documented by the API, regardless of which thread releases them.

## 7.7 Mutable object-state overlap stress

Goal:
- validate the synchronization matrix for object-local mutable fields.

Test:
- overlap `PageSpan.close()`, buffer export acquire/release, metadata/property access, and iterator teardown on hostile test threads;
- overlap iterator exhaustion, `close()`, and deallocation on the same iterator object;
- treat same-object concurrent use as a memory-safety test, not as a promise of useful shared semantics.

Expected:
- no crashes or data races in object-local mutable fields;
- readers observe either the pre-close or post-close state, never torn state.

## 7.8 Drop/drain stress

Goal:
- exercise retired queue and live tracking.

Test:
- create many short-lived objects with `__del__` side effects;
- include finalizers that log, warn, or re-enter harmless `timelog` APIs so decref-under-lock bugs surface;
- force flush/compact/close cycles;
- verify all decref-sensitive paths run on Python threads only.

## 7.9 Finalization and reopen tests

Goal:
- verify close/finalizer/reopen behavior remains deterministic enough.

Test:
- explicit `close()` after `flush()`;
- `reopen()` on closed instance;
- GC finalization with unclosed instance;
- interpreter shutdown smoke test in subprocess.

## 7.10 ABI/build tests

Goal:
- verify both regular and free-threaded wheel families build and import.

## 8. Rollout plan

## Phase A — test scaffolding

Deliverables:
- new pytest markers: `subinterpreters`, `freethreading`, `stress`
- failing tests that demonstrate current incompatibility
- failure-injection hooks or equivalent binding-level tests for module-init unwind where needed

Exit criteria:
- baseline failures are reproducible in CI or local dedicated jobs.

## Phase B — multi-phase init scaffold and module-state migration

Phase B spans multiple implementation steps.
Step 2 lands only the multi-phase scaffold and same-module exec control point.
Module-local exceptions and removal of process-global exception objects are completed later in this phase, not at the Step 2 checkpoint.

Deliverables:
- multi-phase init
- per-module state
- module-local exceptions
- `state->initialized`
- same-module `timelog_exec()` idempotence and partial-init unwind
- explicit refusal to declare per-interpreter support until true Layer A isolation lands

Exit criteria:
- regular-build import/use remains green;
- process-global exception objects are gone;
- same-module exec/unwind tests pass;
- module-state migration has started, but full interpreter isolation is not yet claimed.

## Phase C — true Layer A interpreter isolation

Deliverables:
- all reachable static binding types converted to heap types
- module-state access re-plumbed
- type-check / allocation helpers re-plumbed away from process-global `PyTypeObject` symbols
- no process-global Python objects remain
- `Py_mod_multiple_interpreters = Py_MOD_PER_INTERPRETER_GIL_SUPPORTED`
- user-facing docs updated to claim subinterpreter support without implying free-threaded support is already complete

Exit criteria:
- all existing tests pass under regular 3.14 and subinterpreters;
- multi-interpreter identity/isolation tests pass;
- no reachable production static binding `PyTypeObject` remains;
- no process-global Python object state remains.

## Phase D — free-threaded correctness / true Layer B

Deliverables:
- atomic `tl_pagespan_owner.refcnt` in core
- explicit locks for live tracking and any remaining shared state
- critical sections where appropriate
- synchronization matrix implemented for object-local mutable fields
- hard invariant enforced: no decref / warning / callback-capable work under internal locks
- attached-thread-state discipline fully documented and enforced
- `Py_mod_gil = Py_MOD_GIL_NOT_USED`
- user-facing docs updated to advertise official free-threaded support on designated versions/builds

Exit criteria:
- free-threaded import test passes without GIL flip;
- concurrent stress suite passes on `cp314t`;
- PageSpan owner cross-thread release stress passes;
- decref/finalizer stress passes without deadlock or corruption.

## Phase E — packaging and release

Deliverables:
- CI matrix for `cp314` and `cp314t`
- release notes documenting concurrency guarantees and residual limits

Exit criteria:
- publish both wheel families;
- user docs updated.

## 9. Risks and mitigations

### R1. Heap type conversion subtly changes behavior

Risk:
- direct conversion from static types to heap types is not perfectly lossless.

Mitigation:
- preserve instantiation flags explicitly;
- regression-test pickling/representation/slot behavior if user-visible.

### R2. Hidden GIL assumptions remain in extension code

Risk:
- a path still mutates shared state without explicit locking.

Mitigation:
- grep/audit for:
  - global `static PyObject *`
  - global `static PyTypeObject`
  - `PyGILState_Check()` assertions
  - comments or contracts that say “caller serialization required” or “the GIL provides this serialization”
  - borrowed-reference APIs on mutable containers
  - direct struct-field access to mutable Python objects
- run TSAN/ASAN-style native stress where practical.

### R3. Per-interpreter support declared too early

Risk:
- setting `Py_mod_multiple_interpreters = Py_MOD_PER_INTERPRETER_GIL_SUPPORTED` before heap types and module-local type/exception state are complete creates a false isolation claim.

Mitigation:
- treat Phase C as the first real Layer A checkpoint;
- keep the slot disabled until heap types land and no process-global Python objects remain;
- require multi-interpreter identity/isolation tests before enabling the declaration.

### R4. Python-executing cleanup occurs under internal locks

Risk:
- `Py_DECREF`, `Py_CLEAR`, warning emission, or callback-capable cleanup under `core_lock`, `live_lock`, or object critical sections can deadlock or re-enter corrupted state.

Mitigation:
- enforce the collect/unlock/execute pattern as a hard invariant;
- add `__del__`/warning/reentrancy stress tests;
- audit every cleanup path that can reach decref-capable work.

### R5. Background thread and subinterpreter attachment bugs

Risk:
- accidental use of `PyGILState_Ensure()` in the wrong interpreter context.

Mitigation:
- keep maintenance thread fully Python-blind;
- never use Python callbacks from it;
- drain on API-entry/exit paths only.

### R6. Free-threaded import declared too early

Risk:
- declaring `Py_MOD_GIL_NOT_USED` before internal locking is complete causes hard-to-debug corruption.

Mitigation:
- stage the work;
- do not set the slot until Phase D exit criteria are met.

## 10. Acceptance checklist

The task is complete only when all are true:

- [ ] no `m_size = -1` in the extension module definition
- [ ] module uses multi-phase initialization
- [ ] same-module `timelog_exec()` is idempotent and partial-init failure unwinds to `initialized = 0`
- [ ] no process-global Python objects remain
- [ ] all exceptions are per-module, not global
- [ ] all reachable extension types are heap types
- [ ] no reachable production static binding `PyTypeObject` remains
- [ ] core `tl_pagespan_owner.refcnt` is atomic and no `views()` lifetime path relies on GIL-era serialization
- [ ] no correctness-critical path relies on the GIL as a lock
- [ ] no decref / warning / callback-capable work occurs under `core_lock`, `live_lock`, or object critical sections
- [ ] live tracking and object-local mutable state are explicitly synchronized according to the synchronization matrix
- [ ] maintenance thread never calls Python C API
- [ ] `Py_mod_multiple_interpreters = Py_MOD_PER_INTERPRETER_GIL_SUPPORTED`
- [ ] `Py_mod_gil = Py_MOD_GIL_NOT_USED`
- [ ] free-threaded import does not enable the GIL
- [ ] subinterpreter smoke and independence tests pass
- [ ] concurrent stress tests and PageSpan cross-thread release tests pass on free-threaded 3.14
- [ ] public docs and Python facade no longer make blanket CPython-GIL-required support claims
- [ ] dual wheel families build in CI

## 11. High-level implementation plan

This section expands the implementation order into a practical branch plan. It is intentionally high level: the goal is to preserve sequencing, checkpoints, and scope boundaries without turning the LLD into a line-by-line coding script.

### Step 1. Establish the validation baseline

Focus:
- land the tests and stress harnesses that prove today’s limitations and will later prove the migration is correct;
- include subinterpreter smoke coverage and hostile lifetime/concurrency stress early;
- reserve the home for same-module `timelog_exec()` idempotence coverage, but defer the real T3 test to Step 2 because the current single-phase init path has no legitimate same-module exec surface to exercise without fake hooks.

Why first:
- the rest of the migration changes initialization, type identity, and object lifetime rules at the same time;
- having validation in place early reduces the chance of “it imports, so it must be correct” false confidence.

Checkpoint:
- the team can reproduce baseline failures or gaps locally and in CI;
- the target pass conditions for later phases are visible before implementation starts.

### Step 2. Land the multi-phase initialization scaffold

Focus:
- move the module onto multi-phase initialization;
- introduce module state and `state->initialized`;
- make same-module `timelog_exec()` explicitly idempotent with clean partial-init unwind.

Why this comes next:
- almost every later change depends on having a stable per-module state home;
- it creates the control point needed for subinterpreter-safe exceptions and heap types.

Checkpoint:
- regular imports still behave as today;
- initialization is no longer structurally tied to legacy single-phase assumptions;
- the scaffold is landed, but interpreter isolation is still incomplete until later steps remove process-global Python objects and static types.

### Step 3. Migrate process-global Python objects into module-local state

Focus:
- remove process-global exception objects first;
- then finish moving exported Python-facing state behind module accessors instead of globals.

Why this is its own step:
- it shrinks the global-state surface before type conversion starts;
- it makes later isolation bugs easier to reason about because exceptions and module exports already follow the new ownership model.

Checkpoint:
- exception identity is module-local;
- initialization and error paths no longer depend on process-global Python object storage.
- any temporary reload caveat ends once Step 4 replaces cached context with heap-type module-state recovery.

### Step 4. Complete Layer A interpreter isolation

Focus:
- migrate every reachable binding type to a per-module heap type, including the internal objects-view iterator;
- update method access, slot access, type checks, and allocation helpers to recover state through module/type APIs rather than static `PyTypeObject` symbols.
- remove the temporary `sys.modules` binding scaffold and cached exception context.
- enable `Py_mod_multiple_interpreters = Py_MOD_PER_INTERPRETER_GIL_SUPPORTED` after the heap-type and module-state checks pass.
- leave `Py_mod_gil` unset until Layer B.
- update user-facing messaging to say subinterpreter support is available, without yet claiming free-threaded support.

Why this is the Layer A turning point:
- interpreter isolation is not real until all reachable binding types stop being process-shared;
- this is the step that turns “module state exists” into “module identity is actually isolated.”

Checkpoint:
- no reachable production static binding `PyTypeObject` remains;
- module-local types, methods, and exceptions all work across multiple interpreters.
- subinterpreter smoke and independence tests pass;
- the public contract matches the implementation state.

### Step 5. Make lifetime and shared-state mechanics free-thread-safe

Focus:
- land the core `tl_pagespan_owner` atomic refcount change;
- add binding-side synchronization for live tracking and object-local mutable state;
- enforce the collect/unlock/execute rule for decref-capable cleanup.

Why this is grouped together:
- these pieces jointly remove the strongest remaining GIL-era correctness assumptions;
- splitting them too finely would make it harder to reason about lifetime ownership across core and binding boundaries.

Checkpoint:
- `views()` / `PageSpan` lifetime no longer depends on caller serialization by the GIL;
- cleanup, finalizers, and mutable object state are governed by explicit synchronization rules.

### Step 6. Finish free-threaded readiness and only then declare no-GIL support

Focus:
- complete attached-thread-state and finalization audits;
- run the deadlock, stress, and free-threaded import validations;
- enable `Py_mod_gil = Py_MOD_GIL_NOT_USED` only after the free-threaded checkpoint is satisfied.

Why this is late in the plan:
- `Py_mod_gil` is the strongest public claim in the migration;
- enabling it too early would hide design debt behind a compatibility declaration.

Checkpoint:
- import no longer flips the GIL on in free-threaded builds;
- concurrency and lifetime stress pass without deadlocks or corruption.

### Step 8. Close the loop with docs, packaging, and release readiness

Focus:
- sync the Python facade and public docs with the support level reached;
- expand CI and wheel production to the supported ABI set;
- publish official `cp314t` support only when the earlier checkpoints are green.

Why this is last:
- packaging and user messaging should reflect the proven state of the implementation, not the intended destination;
- this step turns the internal migration into a supportable release story.

Checkpoint:
- docs, CI, wheel matrix, and release notes all describe the same support contract.

This order keeps the plan anchored around two real checkpoints:
- Layer A completion, where interpreter isolation becomes true rather than aspirational;
- Layer B completion, where free-threaded support becomes a supported public claim rather than an internal work-in-progress.
