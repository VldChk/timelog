LLD-B1: Python Handle & Lifetime Subsystem - Engineering Plan

 Status: Phase 3 Complete - Ready for Final Approval
 Last Updated: 2026-01-11

 ---
 Goal

 Implement the Python object handle and lifetime management subsystem (LLD-B1) that enables Timelog to store CPython objects as tl_handle_t values while maintaining correct reference      
 counting, snapshot safety, and thread/GIL compliance.

 ---
 Phases

 - Phase 1: Codebase exploration and analysis
 - Phase 2: Detailed implementation design
 - Phase 3: Code review and plan verification
 - Phase 4: Final plan approval

 ---
 Key Findings from Exploration

 1. Core Engine Drop Callback Mechanism

 Location: src/maint/tl_compaction.c:1233-1260

 The drop callback (on_drop_handle) is invoked ONLY after successful manifest publication:

 if (publish_st == TL_OK) {
     if (ctx.on_drop_handle != NULL) {
         for (size_t i = 0; i < ctx.dropped_len; i++) {
             ctx.on_drop_handle(ctx.on_drop_ctx,
                                ctx.dropped_records[i].ts,
                                ctx.dropped_records[i].handle);
         }
     }
 }

 Critical Insight: Records are COLLECTED during merge but callbacks are DEFERRED until after publish succeeds. This aligns perfectly with LLD-B1's "retire → quiesce → release" model.      

 2. Snapshot Pinning Mechanism

 Location: src/query/tl_snapshot.c:67-176

 Snapshots use seqlock + writer_mu for consistent capture:
 - Manifest is pinned via tl_manifest_acquire() (refcount increment)
 - Memview is captured as a refcounted shared structure
 - Snapshot lifetime guarantees handle visibility

 Key Pattern for Python Binding:
 - Increment pins counter BEFORE tl_snapshot_acquire()
 - Decrement pins counter AFTER tl_snapshot_release()
 - Only drain retired objects when pins == 0

 3. Handle Immutability in Iterator Pipeline

 Location: src/tl_timelog.c:1278-1309

 Handles are returned as tl_record_t.handle (immutable uint64):
 *out = it->point_result.records[it->point_idx];  // Direct copy

 The iterator never modifies handles - they're read-only from segment/memrun storage.

 4. Lock Ordering Constraints

 From: src/internal/tl_locks.h:6-15

 maint_mu → flush_mu → writer_mu → memtable_mu

 Implication for Python Binding:
 - Drop callback runs WITHOUT engine locks held (after publication)
 - Safe to acquire GIL in callback without deadlock risk
 - However, must not call back into Timelog APIs

 5. Maintenance Worker Thread

 Location: src/tl_timelog.c:1538-1691

 Background worker runs compaction which triggers drop callbacks. The callback may be invoked on a non-Python thread, requiring PyGILState_Ensure()/Release().

 ---
 Proposed Directory Structure

 timelog/
   core/                        # Existing C engine (moved)
     include/timelog/
       timelog.h                # Public C API
       tl_export.h
     src/
       storage/
       delta/
       query/
       maint/
       internal/
     tests/
     CMakeLists.txt             # Builds libtimelog_core

   bindings/
     cpython/
       include/timelogpy/
         py_handle.h            # LLD-B1: Handle encoding + lifetime
         py_errors.h            # Status → exception mapping
       src/
         module.c               # PyInit__timelog
         py_handle.c            # LLD-B1 implementation
         py_errors.c            # Error translation
       CMakeLists.txt           # Builds _timelog extension

   python/
     src/timelog/
       __init__.py
       _errors.py
     tests/
       test_refcounts.py

 ---
 LLD-B1 Implementation Components

 Component 1: Handle Encoding/Decoding

 File: bindings/cpython/include/timelogpy/py_handle.h

 // Compile-time safety
 _Static_assert(sizeof(void*) <= sizeof(tl_handle_t),
                "Pointer size exceeds tl_handle_t width");

 static inline tl_handle_t tl_py_handle_encode(PyObject* obj) {
     return (tl_handle_t)(uintptr_t)obj;
 }

 static inline PyObject* tl_py_handle_decode(tl_handle_t h) {
     return (PyObject*)(uintptr_t)h;
 }

 Component 2: Pin Tracking for Snapshots

 File: bindings/cpython/src/py_handle.c

 struct tl_py_handle_ctx {
     _Atomic(tl_py_drop_node_t*) retired_head;  // Lock-free stack
     _Atomic(uint64_t) pins;                     // Active snapshot count
     uint64_t retired_count_total;               // Metrics
 };

 void tl_py_pins_enter(tl_py_handle_ctx_t* ctx) {
     atomic_fetch_add_explicit(&ctx->pins, 1, memory_order_relaxed);
 }

 void tl_py_pins_exit_and_maybe_drain(tl_py_handle_ctx_t* ctx) {
     uint64_t old = atomic_fetch_sub_explicit(&ctx->pins, 1, memory_order_release);
     if (old == 1) {
         tl_py_drain_retired(ctx, /*force=*/0);
     }
 }

 Component 3: On-Drop Callback (Lock-Free Queue)

 File: bindings/cpython/src/py_handle.c

 void tl_py_on_drop_handle(void* on_drop_ctx, tl_ts_t ts, tl_handle_t handle) {
     tl_py_handle_ctx_t* ctx = (tl_py_handle_ctx_t*)on_drop_ctx;

     tl_py_drop_node_t* node = malloc(sizeof(*node));
     if (!node) {
         // Leak rather than UAF - documented failure mode
         return;
     }

     node->obj = tl_py_handle_decode(handle);
     node->ts = ts;

     // Lock-free push
     tl_py_drop_node_t* head;
     do {
         head = atomic_load_explicit(&ctx->retired_head, memory_order_relaxed);
         node->next = head;
     } while (!atomic_compare_exchange_weak_explicit(
                 &ctx->retired_head, &head, node,
                 memory_order_release, memory_order_relaxed));
 }

 Critical: NO Python C-API calls, NO GIL acquisition, NO Timelog re-entry.

 Component 4: Drain (Quiescent Release)

 File: bindings/cpython/src/py_handle.c

 void tl_py_drain_retired(tl_py_handle_ctx_t* ctx, int force) {
     // MUST hold GIL
     uint64_t pins = atomic_load_explicit(&ctx->pins, memory_order_acquire);
     if (pins != 0 && !force) {
         return;
     }

     // Atomic exchange to claim entire queue
     tl_py_drop_node_t* list = atomic_exchange_explicit(
         &ctx->retired_head, NULL, memory_order_acq_rel);

     while (list) {
         tl_py_drop_node_t* n = list;
         list = n->next;
         Py_DECREF(n->obj);  // May run arbitrary Python code
         free(n);
     }
 }

 Invariant: Py_DECREF only happens when pins == 0 (no snapshots can yield this object).

 ---
 Critical Invariants (from LLD-B1)

 | ID  | Invariant                                                                | Enforcement                                |
 |-----|--------------------------------------------------------------------------|--------------------------------------------|
 | I1  | Handle round-trip: decode(encode(o)) == o                                | Static assert on pointer size              |
 | I2  | Balanced refcounts: 1 INCREF on append, 1 DECREF on physical drop        | Test with custom __del__ tracking          |
 | I3  | No UAF across snapshots: retired objects not freed while snapshots exist | Pin tracking with atomic counter           |
 | I4  | No Python C-API in on_drop callback                                      | Code review + thread ID verification tests |
 | I5  | Iterator handoff uses new references                                     | Py_NewRef() on every yield                 |

 ---
 Integration Points with Core

 1. tl_config_t Setup

 tl_config_t cfg;
 tl_config_init_defaults(&cfg);
 cfg.on_drop_handle = tl_py_on_drop_handle;
 cfg.on_drop_ctx = handle_ctx;
 cfg.maintenance_mode = TL_MAINT_BACKGROUND;  // or DISABLED

 2. Snapshot Wrapper

 tl_status_t py_snapshot_acquire(tl_py_handle_ctx_t* ctx,
                                  tl_timelog_t* tl,
                                  tl_snapshot_t** out) {
     tl_py_pins_enter(ctx);  // BEFORE acquire
     tl_status_t st = tl_snapshot_acquire(tl, out);
     if (st != TL_OK) {
         tl_py_pins_exit_and_maybe_drain(ctx);  // Undo on failure
     }
     return st;
 }

 3. Append Path

 PyObject* py_timelog_append(PyTimelog* self, PyObject* args) {
     long long ts = ...;
     PyObject* obj = ...;

     Py_INCREF(obj);  // Timelog owns one ref
     tl_handle_t h = tl_py_handle_encode(obj);

     tl_status_t st = tl_append(self->tl, (tl_ts_t)ts, h);
     if (st != TL_OK) {
         Py_DECREF(obj);  // Rollback
         return py_raise_from_status(st);
     }

     // Opportunistic drain
     tl_py_drain_retired(self->handle_ctx, /*force=*/0);
     Py_RETURN_NONE;
 }

 ---
 Open Questions

 1. Close semantics: Does tl_close() trigger on_drop for unflushed memtable records?
   - Current behavior: NO - memtable records are destroyed without callback
   - Mitigation: Require flush() before close() in Python-object mode
 2. Epoch-based optimization: Should we expose manifest generation for finer-grained reclamation?
   - V1: Use coarse pins == 0 quiescent point
   - Future: Per-epoch retired queues for earlier reclamation
 3. Allocation failure in callback: Current policy is leak-rather-than-UAF.
   - V1.1: Consider fixed-size slab allocator for drop nodes

 ---
 ---
 Detailed Implementation Plan

 Architecture: Pin-Retire-Quiesce-Release Pattern

 Pin on Insert          Retire on Drop          Quiescence          Release
      |                      |                      |                  |
      v                      v                      v                  v
 Py_INCREF(obj)  -->  on_drop enqueues  -->  pins==0  -->  drain: Py_DECREF
                      (no GIL, no DECREF)                   (GIL held)

 Key Insight: The on-drop callback runs on maintenance thread without GIL. We defer Py_DECREF to a Python thread to avoid running finalizers on wrong thread and potential deadlocks.       

 ---
 Data Structures

 1. Drop Node (Lock-Free Stack Element)

 // bindings/cpython/include/timelogpy/py_handle.h

 typedef struct tl_py_drop_node {
     struct tl_py_drop_node* next;   // Intrusive list link
     PyObject*               obj;    // Object to DECREF
     tl_ts_t                 ts;     // Timestamp for debugging
 } tl_py_drop_node_t;

 2. Handle Context (Per-Timelog State)

 typedef struct tl_py_handle_ctx {
     // Lock-free MPSC stack (many producers, single consumer)
     _Atomic(tl_py_drop_node_t*) retired_head;

     // Active snapshot/iterator count
     _Atomic(uint64_t) pins;

     // Configuration
     uint32_t drain_batch_limit;     // 0 = drain all

     // Metrics
     uint64_t retired_count_total;
     uint64_t drained_count_total;
     uint64_t alloc_failures;
 } tl_py_handle_ctx_t;

 ---
 Memory Ordering Model

 | Operation              | Ordering | Rationale                          |
 |------------------------|----------|------------------------------------|
 | Pin increment          | RELAXED  | Gating counter only; snapshot provides sync |
 | Pin decrement          | RELEASE  | Synchronize with subsequent drains |
 | Stack push CAS         | RELEASE  | Make node fields visible           |
 | Stack exchange (drain) | ACQ_REL  | See all pushed nodes               |

 ---
 Core Algorithms

 On-Drop Callback (Lock-Free Push)

 void tl_py_on_drop_handle(void* ctx, tl_ts_t ts, tl_handle_t handle) {
     tl_py_handle_ctx_t* ctx = (tl_py_handle_ctx_t*)on_drop_ctx;

     tl_py_drop_node_t* node = malloc(sizeof(*node));
     if (!node) {
         ctx->alloc_failures++;  // Leak rather than UAF
         return;
     }

     node->obj = tl_py_handle_decode(handle);
     node->ts = ts;

     // Treiber stack push
     tl_py_drop_node_t* head;
     do {
         head = atomic_load_explicit(&ctx->retired_head, memory_order_relaxed);
         node->next = head;
     } while (!atomic_compare_exchange_weak_explicit(
                 &ctx->retired_head, &head, node,
                 memory_order_release, memory_order_relaxed));
 }

 CRITICAL: NO Python C-API calls, NO GIL, NO Timelog re-entry.

 Drain (Quiescent Release)

 void tl_py_drain_retired(tl_py_handle_ctx_t* ctx, int force) {
     // Must hold GIL
     uint64_t pins = atomic_load_explicit(&ctx->pins, memory_order_acquire);
     if (pins != 0 && !force) return;

     // Atomic snapshot entire retired list
     tl_py_drop_node_t* list = atomic_exchange_explicit(
         &ctx->retired_head, NULL, memory_order_acq_rel);

     while (list) {
         tl_py_drop_node_t* node = list;
         list = node->next;
         Py_DECREF(node->obj);  // May run Python code
         free(node);
     }
 }

 ---
 Integration Protocol

 PyTimelog Initialization

 // Wire up drop callback
 config.on_drop_handle = tl_py_on_drop_handle;
 config.on_drop_ctx = self->handle_ctx;

 Append Path

 Py_INCREF(obj);  // Before append
 tl_status_t st = tl_append(self->tl, ts, tl_py_handle_encode(obj));
 if (st != TL_OK) {
     Py_DECREF(obj);  // Rollback
     return error;
 }
 tl_py_drain_retired(ctx, 0);  // Opportunistic drain

 Iterator Creation

 tl_py_pins_enter(ctx);  // BEFORE snapshot acquire
 st = tl_snapshot_acquire(tl, &snap);
 if (st != TL_OK) {
     tl_py_pins_exit_and_maybe_drain(ctx);  // Rollback
     return error;
 }

 Iterator Destruction

 tl_iter_destroy(iter);
 tl_snapshot_release(snap);
 tl_py_pins_exit_and_maybe_drain(ctx);  // May trigger drain

 Close Sequence

 tl_maint_stop(tl);                    // Stop background
 if (pins != 0) return error;          // Refuse if iterators active
 tl_close(tl);
 tl_py_drain_retired(ctx, /*force=*/1); // Final drain
 tl_py_handle_ctx_free(ctx);

 ---
 File Layout

 timelog/
   core/                              # Existing C engine (MOVED)
     include/timelog/
       timelog.h
     src/
       storage/, delta/, query/, maint/, internal/
     tests/
     CMakeLists.txt                   # Builds libtimelog_core

   bindings/cpython/
     include/timelogpy/
       py_handle.h                    # LLD-B1 interface
       py_errors.h                    # Status → exception mapping
     src/
       py_handle.c                    # LLD-B1 implementation
       py_errors.c                    # Error translation
       py_timelog.c                   # PyTimelog type
       py_iter.c                      # PyTimelogIter type
       module.c                       # PyInit__timelog
     CMakeLists.txt                   # Builds _timelog extension

   python/
     src/timelog/
       __init__.py
       _errors.py
     tests/
       test_refcounts.py
       test_snapshot_safety.py

 ---
 Implementation Phases

 | Phase                  | Week | Deliverables                                       |
 |------------------------|------|----------------------------------------------------|
 | 1. Core Handle Context | 1    | py_handle.h/c, encode/decode, pins, on_drop, drain |
 | 2. PyTimelog Binding   | 2    | PyTimelog type, append, close, callback wiring     |
 | 3. Iterator Binding    | 3    | PyTimelogIter, pin tracking, yield with Py_NewRef  |
 | 4. Integration Tests   | 4    | Refcount tests, snapshot safety, stress tests      |

 ---
 Testing Checklist

 - Balanced refcounts: N inserts → delete_before → compact → N finalizers
 - Snapshot overlap: Iterator outlives compaction, objects still valid
 - Finalizer thread: All __del__ run on Python thread, not maintenance
 - Append rollback: Failure restores refcount exactly
 - Close drains all: No leaks after close()
 - TSan clean: No data races in lock-free code

 ---
 Critical Invariants

 | ID  | Invariant                                       | Enforcement                   |
 |-----|-------------------------------------------------|-------------------------------|
 | I1  | decode(encode(obj)) == obj                      | Static assert on pointer size |
 | I2  | 1 INCREF per append, 1 DECREF per physical drop | Test with __del__ tracking    |
 | I3  | No UAF: pins > 0 blocks drain                   | Atomic pin counter            |
 | I4  | No Python C-API in on_drop                      | Code review, thread ID tests  |
 | I5  | Iterator yields new references                  | Py_NewRef on every yield      |

 ---
 Open Questions (Resolved for V1)

 1. Manifest generation for epoch-based drain? → Not required V1; coarse pins==0 is correct
 2. tl_close() triggers on_drop for memtable? → No; document flush() before close()
 3. Allocation failure in callback? → Leak rather than UAF; track in alloc_failures

 ---
 C17-Reviewer Verification Results

 Verdict: Design is fundamentally sound and aligns with LLD-B1 requirements.

 Critical Items (Addressed)

 | Item | Issue                                            | Resolution                                                                          |
 |------|--------------------------------------------------|-------------------------------------------------------------------------------------|
 | C1   | Pin counter memory orderings not fully specified | Plan updated: RELAXED on increment, RELEASE on decrement, ACQ_REL on drain exchange |
 | C2   | Close semantics for unflushed memtable unclear   | Documented: require flush() before close() in Python-object mode; add runtime check |

 Warnings (Acknowledged)

 | Item | Warning                                          | Mitigation                                                                     |
 |------|--------------------------------------------------|--------------------------------------------------------------------------------|
 | W1   | alloc_failures++ in on_drop is non-atomic        | Accept: metrics counter, not critical path; consider _Atomic(uint64_t) in V1.1 |
 | W2   | Force drain during close could stall if pins > 0 | Check pins before close; return error if iterators active                      |

 Verification Checklist

 - Handle encoding round-trips correctly (static assert)
 - Drop callback runs after manifest publish (verified in tl_compaction.c:1233-1260)
 - Lock ordering prevents deadlock (drop callback runs without engine locks)
 - Pin tracking prevents UAF (atomic counter + quiescent drain)
 - Aligns with HLD Python-object mode goals
 - Aligns with LLD-B1 invariants I1-I5

 ---
 Status

 Phase 3 Complete - c17-reviewer verification passed. Ready for user approval.

 ---
 Next Steps

 1. ~~Launch Plan agent for detailed implementation design~~ ✓
 2. ~~Cross-review with c17-reviewer agent~~ ✓
 3. ~~Finalize engineering plan with verification results~~ ✓
 4. Awaiting user approval to proceed with implementation

 ---
 Implementation Summary (For Approval)

 What We're Building

 Python binding subsystem (LLD-B1) that enables storing CPython objects as tl_handle_t values with correct lifetime management.

 Core Pattern: Pin-Retire-Quiesce-Release

 Py_INCREF(obj)  →  on_drop enqueues  →  pins==0  →  drain: Py_DECREF
     (append)       (no GIL, deferred)   (quiescent)   (GIL held)

 Key Files to Create

 | File                                           | Purpose                              |
 |------------------------------------------------|--------------------------------------|
 | bindings/cpython/include/timelogpy/py_handle.h | Handle encoding, context struct, API |
 | bindings/cpython/src/py_handle.c               | Lock-free stack, pin tracking, drain |
 | bindings/cpython/src/py_timelog.c              | PyTimelog type with callback wiring  |
 | bindings/cpython/src/py_iter.c                 | Iterator with snapshot pinning       |

 Critical Safety Properties

 1. No UAF: Atomic pin counter blocks drain while snapshots exist
 2. No GIL in callback: on_drop only enqueues, never calls Python C-API
 3. Balanced refcounts: 1 INCREF per append, 1 DECREF per physical drop
 4. Thread-safe: Lock-free Treiber stack for MPSC pattern

 Verified By

 - c17-reviewer agent: Design aligns with HLD/LLD requirements
 - Memory ordering model: RELAXED/RELEASE/ACQ_REL properly specified
 - Integration points: Confirmed with existing on_drop_handle callback in compaction
