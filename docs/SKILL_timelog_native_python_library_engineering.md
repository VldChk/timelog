---
name: timelog-native-python-library-engineering
description: |
  End-to-end engineering discipline for Timelog as a native C engine with a CPython extension
  and a Python-facing API. Use when building any part of the stack: the C core (pages/segments,
  snapshots, compaction), the CPython binding layer (handles, refcounts, GIL, buffer protocol),
  or the packaging/CI pipeline (wheels, manylinux, macOS, Windows).

  This skill is written for Timelog’s “Python object mode”: values are opaque uint64 handles that
  encode PyObject* pointers; Timelog owns one strong reference per inserted record until physical
  reclamation (compaction/close).
---

# Timelog native + Python library engineering

This document is the “do not skip” competency map for building Timelog into a production-quality
Python library without regressing performance or correctness.

A Timelog library is not just “C code + bindings”. It is a three-layer system with different failure modes:

Layer A — the C engine:
immutable page/segment layouts, snapshots, tombstones, atomic publication, background maintenance.

Layer B — the CPython runtime adapter:
turns `(ts:int64, handle:uint64)` into `(ts:int, obj:PyObject*)`, makes lifetimes correct, and ensures
the engine never calls Python except via the drop bridge.

Layer C — the Python product layer:
a small ergonomic API (slicing, iterators, exceptions, type hints) that does not know about manifests,
segments, or tombstone mechanics.

The project is at high risk if any one of these three layers is engineered “by vibes”.

---

## 1) Timelog semantics are the foundation

Before performance or bindings, an engineer must internalize Timelog’s semantic contract:

Timelog is a time-sorted multimap of records `(ts:int64, handle:uint64)` with:

- half-open time ranges: `[t1, t2)` is the only range semantics
- duplicates allowed and preserved
- output order non-decreasing by timestamp; tie order is unspecified in V1
- deletes are tombstones (logical) with deferred physical reclamation
- snapshot reads: iterators run against a stable snapshot (manifest + memtable view)

If you cannot restate these semantics precisely, you will write a “fast” bug.

---

## 2) C core competence that still matters (Layer A)

Timelog’s engine is already performance-oriented; the goal is to keep it correct, stable, and
extensible while Layer B/C are added.

### C correctness in performance builds

You must be fluent in undefined behavior (UB) sources that cause miscompilations at `-O2/-O3`:

out-of-bounds access, signed overflow, uninitialized reads, invalid shifts, alignment violations,
strict aliasing violations, and data races.

If you cannot argue “defined by the C standard”, the code is not shippable.

### Data-oriented memory layout

A Timelog-class engine wins because it is cache-friendly:

timestamps are hot keys, payload handles are cold-ish.

Competence requirements:

- SoA layouts for hot scans: contiguous `ts[]` + parallel `handles[]`
- catalogs/fence pointers for pruning: skip whole pages/segments quickly
- avoid pointer-chasing inside hot loops
- avoid per-row allocation and per-row virtual dispatch

### Atomic publication + reclamation

Atomic swap is easy. Safe freeing is hard.

Minimum competence:

- C11 atomics and acquire/release ordering
- build-then-publish workflows (construct immutable structures off-lock)
- snapshot-safe reclamation (refcounts or epochs) with tests

### Algorithms that dominate costs

The core hot-path algorithms are not optional knowledge:

- correct `lower_bound` for int64 arrays and half-open mapping
- interval sets: sorted, non-overlapping, coalesced; strict `[t1, t2)` reasoning
- k-way merge over sorted sources using a min-heap (bounded merge width matters)

---

## 3) CPython binding competence (Layer B) — the new “hard part”

Python bindings are not glue. They are a runtime contract with strict rules:

only the thread holding the GIL may touch Python objects, reference counting must be balanced, and
background threads must not call Python APIs without attaching to the interpreter.

This section is the new competency delta compared to “C engine only”.

### 3.1 Reference model: owned vs borrowed references

You must be able to reason about CPython reference ownership without guessing.

The binding layer must be explicit for every PyObject value it touches:

- is this a borrowed reference or an owned one?
- if owned, who decrefs it and when?
- can it escape to user code, and if so, is it incref’d before escape?

If you do not understand “steals a reference” APIs (e.g., tuple/set item setters),
you will leak or double-free.

### 3.2 Handle encoding/decoding discipline

In Python-object mode, `tl_handle_t` stores a `PyObject*` as an integer.

Competence requirements:

- correct cast sequence via `uintptr_t`:
  `handle = (uint64_t)(uintptr_t)obj`
  `obj = (PyObject*)(uintptr_t)handle`
- compile-time assertion: `sizeof(void*) <= sizeof(uint64_t)`
- no pointer tagging or bit tricks unless you can prove alignment guarantees and portability

### 3.3 The Timelog ownership model for PyObjects

This is where bindings differ from typical “store a pointer” wrappers.

Timelog must own a strong reference per inserted record until the record is physically reclaimed.

Contract:

- append(ts, obj):
  binding does `Py_INCREF(obj)` and stores encoded pointer as handle
- delete/tombstone:
  no decref (logical deletion only)
- physical drop (compaction or close):
  binding’s on-drop callback does `Py_DECREF(obj)` exactly once per physically removed record
- iterator yield:
  binding does an additional `Py_INCREF(obj)` before returning it to user code

An engineer must be able to audit this as an invariant:
“Every successful append adds exactly one engine-owned INCREF; every physical record retirement
eventually triggers exactly one DECREF.”

### 3.4 GIL discipline and thread attachment

Rules you must treat as axioms:

- any `Py_INCREF`, `Py_DECREF`, or `PyObject*` manipulation requires the GIL
- calls from Python into the extension arrive with the GIL held
- callbacks from engine maintenance threads may arrive without the GIL
- `PyGILState_Ensure()` / `PyGILState_Release()` is the correct attach/detach idiom for foreign threads
- acquiring the GIL while holding engine locks is a deadlock risk if user finalizers re-enter the engine

Timelog-specific binding skill is designing lock/GIL order so deadlock is structurally impossible.

Practical implications for Timelog:

- drop callbacks must run without engine locks held (engine must guarantee this)
- drop callbacks must be minimal: “ensure GIL → DECREF → release GIL”
- drop callbacks must never call back into Timelog APIs (no re-entrancy)

### 3.5 Finalization hazards

CPython runtime finalization is hostile to background threads calling into the C API.
If a background thread calls into the C API while the interpreter is finalizing, it may hang or worse.

Operational skill requirements:

- Timelog must stop maintenance threads deterministically on `close()` and module teardown
- `__del__` / dealloc paths must not attempt complex work; they should aim to:
  “stop worker → close engine → release resources”
- you must assume `Py_DECREF()` can execute arbitrary user code (`__del__`)
  and therefore you must not hold engine locks while decrementing

### 3.6 Garbage collector and cycles

Holding PyObject references in C creates GC visibility issues.

If a user stores objects that reference the Timelog (directly or indirectly), cycles may form:
`timelog -> obj -> timelog`.

If the Timelog container is not GC-tracked with a full `tp_traverse`, those cycles may not be collectible.

Competence requirements:

- understand the tradeoff:
  implementing `tp_traverse` may require traversing potentially millions of stored objects
  (expensive, may defeat the purpose)
- choose and document a policy:
  V1 can document that cycles are the user’s responsibility (remove objects / close timelog)
  and provide deterministic `close()`/context-manager behavior

### 3.7 Buffer protocol and zero-copy memory views

“Zero-copy” in Timelog has a precise meaning:

- timestamps are stored contiguously per page; the binding can expose them via a read-only buffer
- arbitrary ranges are not contiguous and should not pretend to be a single memoryview

Competence requirements:

- understand the buffer protocol (`PyBufferProcs`) and lifetime rules:
  exported memory must remain valid until the consumer releases the view
- design a pinning mechanism:
  a PageSpan/memoryview must pin the snapshot/page that owns the memory
- avoid exposing writable buffers unless the underlying memory is truly mutable and safe

If you cannot reason about buffer lifetime, do not implement memoryview exposure.

### 3.8 Python-call overhead and batching

A high-performance binding minimizes Python ↔ C transitions.

Competence requirements:

- provide iterator batching primitives (`next_batch(n)`) to amortize per-call overhead
- avoid allocating Python objects per element when a contiguous view is possible
- release the GIL around long pure-C work where safe (flush/compaction), but never while touching PyObjects

---

## 4) Packaging and distribution competence (build is part of the product)

A Timelog Python library must install cleanly across platforms, not just on the dev machine.

Competence requirements:

- PEP 517/518 build system basics (`pyproject.toml`, isolated builds)
- choosing and operating a native build backend (e.g., scikit-build-core or meson-python)
- building wheels across:
  Linux manylinux/musllinux, macOS (x86_64/arm64), Windows
- using automation (e.g., cibuildwheel) and auditing tools (auditwheel/delocate)

You must understand the ABI decision:

- “full CPython API per version” wheels are simplest and fastest to develop
- “Stable ABI” (Limited API / Py_LIMITED_API) reduces wheel matrix but constrains APIs

Timelog likely starts with per-version wheels for correctness and evolves only if the constraints
are worth it.

---

## 5) Verification competence (Layer A + B + C)

Timelog’s hardest bugs are cross-layer:

“engine lifetime + snapshot lifetime + Python refcounts + background threads”.

Competence requirements:

- C-level sanitizers in CI (ASan/UBSan; TSan when maintenance thread is enabled)
- Python-level tests that validate:
  append/range iteration/delete semantics
  snapshot isolation behavior visible from Python
  refcount correctness (no leaks, no double-decref)
  memoryview lifetime rules (views do not outlive pinned memory)
  close/shutdown ordering with iterators alive

The core idea: correctness is not “works on my laptop”.
It is “survives stress and adversarial interleavings”.

---

## 6) Implementation protocol (how to land safe patches)

For any non-trivial change in core or binding:

1) Spec pass:
write down semantics, invariants, boundary cases, and the rollback rules on error.

2) Inventory pass:
do not invent new helpers that already exist; do not reference APIs that do not exist.

3) Design pass:
state complexity and allocations; state locking implications; state ownership rules.

4) Implementation pass:
single cleanup path; minimal critical sections; avoid UB; do not DECREF under engine locks.

5) Verification pass:
add tests; run sanitizers; reproduce benchmarks.

---

## 7) Shipping checklist (native + Python)

Semantics and invariants:

- [ ] half-open range semantics everywhere
- [ ] no timestamp sentinels (TL_TS_MAX is valid data)
- [ ] duplicates preserved; tie order explicitly unspecified
- [ ] deletes are tombstones; physical drop is deferred

C engine safety:

- [ ] ASan/UBSan clean
- [ ] no data races (TSan where applicable)
- [ ] atomic publication has acquire/release correctness
- [ ] reclamation is proven by tests

CPython binding safety:

- [ ] all Python C-API usage under the GIL
- [ ] append failure rolls back INCREF
- [ ] iterator yields INCREF’d objects (user owns safe ref)
- [ ] drop callback acquires GIL and never calls back into Timelog
- [ ] no DECREF while holding engine locks
- [ ] maintenance thread stops before close and before interpreter finalization

Zero-copy / buffer protocol:

- [ ] memoryviews expose only truly contiguous data (page spans)
- [ ] exported buffers are pinned by snapshot/page lifetime
- [ ] releasebuffer properly unpins resources

Packaging:

- [ ] wheels build on Linux/macOS/Windows
- [ ] wheels tested in wheel-installed environment (not editable-only)
- [ ] symbols/visibility and runtime dependencies are sane

---

## 8) High-ROI references (keep close)

C and systems:
- Effective C
- Modern C
- Write Great Code (Vol 1–2)
- Systems Performance

CPython / bindings / packaging:
- Python C-API docs: “Initialization, Finalization, and Threads”
- Python C-API docs: “Buffer Protocol”
- PEP 517 (build backend interface)
- manylinux + auditwheel documentation
- scikit-build-core or meson-python build backend docs
- cibuildwheel documentation
