LLD-B3: PyTimelogIter — Snapshot-Based Iterator Implementation Plan

 Status: Ready for implementation
 Last Updated: 2026-01-14
 Spec: docs/timelog_v1_lld_B3_pytimelogiter_snapshot_iterator.md

 ---
 1. Goal

 Implement PyTimelogIter: a CPython extension type that exposes Timelog's time-range read path to Python. The iterator:
 - Acquires a consistent engine snapshot
 - Constructs a core iterator for range queries
 - Yields (ts: int, obj: object) tuples with correct refcounting
 - Releases all core resources deterministically on exhaustion, close(), or GC

 ---
 2. Prerequisites Verified

 | Dependency                            | Status | Location                                       |
 |---------------------------------------|--------|------------------------------------------------|
 | tl_py_pins_enter()                    | ✓      | bindings/cpython/src/py_handle.c               |
 | tl_py_pins_exit_and_maybe_drain()     | ✓      | bindings/cpython/src/py_handle.c               |
 | tl_py_handle_decode()                 | ✓      | bindings/cpython/include/timelogpy/py_handle.h |
 | tl_snapshot_acquire/release           | ✓      | include/timelog/timelog.h:322-325              |
 | tl_iter_range/since/until/equal/point | ✓      | include/timelog/timelog.h:332-357              |
 | tl_iter_next/destroy                  | ✓      | include/timelog/timelog.h:359-361              |
 | PyTimelog type                        | ✓      | bindings/cpython/src/py_timelog.c              |
 | TlPy_RaiseFromStatus                  | ✓      | bindings/cpython/include/timelogpy/py_errors.h |

 ---
 3. Files to Create/Modify

 New Files

 | File                                         | Purpose                        |
 |----------------------------------------------|--------------------------------|
 | bindings/cpython/include/timelogpy/py_iter.h | PyTimelogIter type declaration |
 | bindings/cpython/src/py_iter.c               | PyTimelogIter implementation   |
 | bindings/cpython/tests/test_py_iter.c        | TDD unit tests                 |

 Files to Modify

 | File                              | Changes                                       |
 |-----------------------------------|-----------------------------------------------|
 | bindings/cpython/src/py_timelog.c | Add range/since/until/all/equal/point methods |
 | bindings/cpython/src/module.c     | Register PyTimelogIter_Type                   |
 | bindings/cpython/CMakeLists.txt   | Add py_iter.c source, test_py_iter target     |

 ---
 4. Data Structures

 4.1 PyTimelogIter (py_iter.h)

 typedef struct {
     PyObject_HEAD

     /* Strong reference to keep engine alive */
     PyObject* owner;              /* (PyTimelog*) */

     /* Core resources (valid only when !closed) */
     tl_snapshot_t* snapshot;      /* acquired snapshot */
     tl_iter_t*     iter;          /* core iterator derived from snapshot */

     /* Handle lifetime context (borrowed; owner keeps it alive) */
     tl_py_handle_ctx_t* handle_ctx;

     /* State flag: 0=open, 1=closed/exhausted */
     uint8_t closed;
 } PyTimelogIter;

 extern PyTypeObject PyTimelogIter_Type;
 #define PyTimelogIter_Check(op) PyObject_TypeCheck(op, &PyTimelogIter_Type)

 Design Rationale:
 - owner: Strong reference prevents engine close while iterator exists
 - handle_ctx: Stored explicitly to avoid dereferencing owner during cleanup (reentrancy-safe)
 - closed: Set early during cleanup to guard against reentrancy from finalizers during drain

 ---
 5. Core Algorithms

 5.1 Iterator Factory (pytimelog_make_iter)

 Lives in py_timelog.c. Steps:

 1. CHECK_CLOSED(self) - validate engine not closed
 2. tl_py_pins_enter(handle_ctx) - increment pin count BEFORE snapshot
 3. tl_snapshot_acquire(self->tl, &snap) - on error: rollback pin, raise
 4. Create core iterator (tl_iter_range, tl_iter_since, etc.) - on error: release snapshot, rollback pin, raise
 5. PyObject_GC_New(PyTimelogIter, &PyTimelogIter_Type) - on error: destroy iter, release snapshot, rollback pin
 6. Initialize fields: owner = Py_NewRef(self), snapshot = snap, iter = it, handle_ctx = ctx, closed = 0
 7. PyObject_GC_Track(pyit) - enable GC tracking
 8. Return iterator

 Failure Safety: Every failure path after pins_enter must call pins_exit_and_maybe_drain exactly once.

 5.2 tp_iternext (PyTimelogIter_iternext)

 static PyObject* PyTimelogIter_iternext(PyTimelogIter* self)
 {
     if (self->closed) return NULL;  /* StopIteration */

     tl_record_t rec;
     tl_status_t st = tl_iter_next(self->iter, &rec);

     if (st == TL_OK) {
         PyObject* obj = Py_NewRef(tl_py_handle_decode(rec.handle));
         PyObject* ts = PyLong_FromLongLong((long long)rec.ts);
         if (!ts) { Py_DECREF(obj); return NULL; }

         PyObject* tup = PyTuple_New(2);
         if (!tup) { Py_DECREF(ts); Py_DECREF(obj); return NULL; }

         PyTuple_SET_ITEM(tup, 0, ts);   /* steals */
         PyTuple_SET_ITEM(tup, 1, obj);  /* steals */
         return tup;
     }

     if (st == TL_EOF) {
         pytimelogiter_cleanup(self);
         return NULL;  /* StopIteration (no exception) */
     }

     /* Error path */
     pytimelogiter_cleanup(self);
     return TlPy_RaiseFromStatus(st);
 }

 Key Points:
 - Py_NewRef for handle decode (yields new reference)
 - PyTuple_SET_ITEM steals references
 - NULL with no exception = StopIteration (CPython convention)

 5.3 Cleanup Routine (Single Source of Truth)

 static void pytimelogiter_cleanup(PyTimelogIter* self)
 {
     if (self->closed) return;  /* Idempotent */
     self->closed = 1;

     /* Clear pointers BEFORE operations that may run Python code */
     tl_iter_t* it = self->iter;           self->iter = NULL;
     tl_snapshot_t* snap = self->snapshot; self->snapshot = NULL;
     tl_py_handle_ctx_t* ctx = self->handle_ctx;  /* borrowed, don't NULL */
     PyObject* owner = self->owner;        self->owner = NULL;

     /* Release resources in order */
     if (it)   tl_iter_destroy(it);
     if (snap) tl_snapshot_release(snap);
     if (ctx)  tl_py_pins_exit_and_maybe_drain(ctx);  /* May trigger Py_DECREF */

     Py_XDECREF(owner);
 }

 Required Ordering:
 1. destroy iterator
 2. release snapshot
 3. exit pins (may drain retired objects)
 4. DECREF owner

 5.4 GC Support

 static int PyTimelogIter_traverse(PyTimelogIter* self, visitproc visit, void* arg)
 {
     Py_VISIT(self->owner);
     return 0;
 }

 static int PyTimelogIter_clear(PyTimelogIter* self)
 {
     pytimelogiter_cleanup(self);
     return 0;
 }

 static void PyTimelogIter_dealloc(PyTimelogIter* self)
 {
     PyObject_GC_UnTrack(self);
     pytimelogiter_cleanup(self);  /* Idempotent */
     Py_TYPE(self)->tp_free((PyObject*)self);
 }

 5.5 Context Manager

 static PyObject* PyTimelogIter_enter(PyTimelogIter* self, PyObject* noargs)
 {
     return Py_NewRef((PyObject*)self);
 }

 static PyObject* PyTimelogIter_exit(PyTimelogIter* self, PyObject* args)
 {
     pytimelogiter_cleanup(self);
     Py_RETURN_FALSE;  /* Don't suppress exceptions */
 }

 5.6 Optional: next_batch(n)

 static PyObject* PyTimelogIter_next_batch(PyTimelogIter* self, PyObject* arg_n)
 {
     Py_ssize_t n = PyLong_AsSsize_t(arg_n);
     if (n < 0 && PyErr_Occurred()) return NULL;
     if (n <= 0 || self->closed) return PyList_New(0);

     PyObject* list = PyList_New(n);
     if (!list) return NULL;

     Py_ssize_t i = 0;
     for (; i < n; i++) {
         tl_record_t rec;
         tl_status_t st = tl_iter_next(self->iter, &rec);

         if (st == TL_OK) {
             PyObject* obj = Py_NewRef(tl_py_handle_decode(rec.handle));
             PyObject* ts = PyLong_FromLongLong((long long)rec.ts);
             if (!ts) { Py_DECREF(obj); goto fail; }

             PyObject* tup = PyTuple_New(2);
             if (!tup) { Py_DECREF(ts); Py_DECREF(obj); goto fail; }

             PyTuple_SET_ITEM(tup, 0, ts);
             PyTuple_SET_ITEM(tup, 1, obj);
             PyList_SET_ITEM(list, i, tup);
             continue;
         }

         if (st == TL_EOF) {
             pytimelogiter_cleanup(self);
             break;
         }

         pytimelogiter_cleanup(self);
         TlPy_RaiseFromStatus(st);
         goto fail;
     }

     /* Shrink list if early EOF */
     if (i < n && PyList_SetSlice(list, i, n, NULL) < 0) goto fail;
     return list;

 fail:
     Py_DECREF(list);
     return NULL;
 }

 ---
 6. PyTimelog Method Additions (py_timelog.c)

 6.1 Factory Helper

 typedef enum {
     ITER_MODE_RANGE,
     ITER_MODE_SINCE,
     ITER_MODE_UNTIL,
     ITER_MODE_EQUAL,
     ITER_MODE_POINT
 } iter_mode_t;

 static PyObject* pytimelog_make_iter(PyTimelog* self,
                                      iter_mode_t mode,
                                      tl_ts_t t1, tl_ts_t t2);

 6.2 Methods to Add

 | Method        | Python Signature                       | Core Call                           |
 |---------------|----------------------------------------|-------------------------------------|
 | range(t1, t2) | range(t1: int, t2: int) -> TimelogIter | tl_iter_range(snap, t1, t2, &it)    |
 | since(t1)     | since(t1: int) -> TimelogIter          | tl_iter_since(snap, t1, &it)        |
 | until(t2)     | until(t2: int) -> TimelogIter          | tl_iter_until(snap, t2, &it)        |
 | all()         | all() -> TimelogIter                   | tl_iter_since(snap, TL_TS_MIN, &it) |
 | equal(ts)     | equal(ts: int) -> TimelogIter          | tl_iter_equal(snap, ts, &it)        |
 | point(ts)     | point(ts: int) -> TimelogIter          | tl_iter_point(snap, ts, &it)        |

 ---
 7. Type Object Definition (py_iter.c)

 PyTypeObject PyTimelogIter_Type = {
     PyVarObject_HEAD_INIT(NULL, 0)
     .tp_name = "timelog._timelog.TimelogIter",
     .tp_doc = PyDoc_STR("Snapshot-based iterator over timelog records."),
     .tp_basicsize = sizeof(PyTimelogIter),
     .tp_itemsize = 0,
     .tp_flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_GC,
     .tp_dealloc = (destructor)PyTimelogIter_dealloc,
     .tp_traverse = (traverseproc)PyTimelogIter_traverse,
     .tp_clear = (inquiry)PyTimelogIter_clear,
     .tp_iter = PyObject_SelfIter,
     .tp_iternext = (iternextfunc)PyTimelogIter_iternext,
     .tp_methods = PyTimelogIter_methods,
 };

 ---
 8. CMakeLists.txt Updates

 # Add to TIMELOG_PY_SOURCES
 set(TIMELOG_PY_SOURCES
     src/py_handle.c
     src/py_errors.c
     src/py_timelog.c
     src/py_iter.c      # NEW: LLD-B3
     src/module.c
 )

 # Add test executable
 if(TIMELOG_BUILD_PY_TESTS)
     add_executable(test_py_iter
         tests/test_py_iter.c
         src/py_handle.c
         src/py_errors.c
         src/py_timelog.c
         src/py_iter.c
     )
     # ... same include/link/compile options as test_py_timelog
 endif()

 ---
 9. TDD Test Plan

 Tests in bindings/cpython/tests/test_py_iter.c. Run with Python initialized.

 9.1 Basic Iteration

 - test_range_basic: Insert 10 records, iterate range(3, 7), verify 4 records
 - test_since_basic: Insert records, since(5) yields all ts >= 5
 - test_until_basic: Insert records, until(5) yields all ts < 5
 - test_all_basic: all() yields all records
 - test_equal_basic: equal(5) yields only ts==5 records
 - test_point_basic: point(5) same as equal but for point queries
 - test_empty_range: range(100, 200) on empty range yields nothing
 - test_yield_tuple_format: Each yield is (int, object) tuple

 9.2 Exhaustion & Cleanup

 - test_exhaust_clears_resources: After full iteration, pins == 0
 - test_exhaust_allows_close: After exhaustion, can call tl.close()
 - test_partial_iter_holds_pin: Iterate 3 of 10, pins == 1

 9.3 Explicit close()

 - test_close_drops_pin: Create iter, close(), pins == 0
 - test_close_is_idempotent: close() twice doesn't crash
 - test_next_after_close: __next__ raises StopIteration after close

 9.4 Context Manager

 - test_context_manager_normal: with tl.range(...) as it: yields records
 - test_context_manager_break: Early break still closes iterator
 - test_context_manager_exception: Exception propagates, iter closed

 9.5 Reference Counting

 - test_yield_new_ref: Yielded object has expected refcount
 - test_no_leak_on_exhaust: Objects not leaked after iteration
 - test_no_premature_free: Object survives iteration (use dict with __del__)

 9.6 Multiple Iterators

 - test_two_iterators_two_pins: Two active iterators → pins == 2
 - test_close_one_keeps_other: Close one, pins == 1, other still works
 - test_overlapping_snapshots: Two iters see same consistent view

 9.7 Compaction Interaction

 - test_snapshot_isolation: Delete + compact during iteration, iter still yields original data
 - test_drain_after_iter_close: Retired objects drained when last iter closes

 9.8 Error Handling

 - test_iter_on_closed_timelog: Factory method raises TimelogError
 - test_invalid_range: range(10, 5) raises ValueError (t1 > t2)

 9.9 Batch (Optional)

 - test_next_batch_full: next_batch(5) returns 5 items
 - test_next_batch_partial: next_batch(100) on 3 items returns 3
 - test_next_batch_zero: next_batch(0) returns empty list
 - test_next_batch_closed: On closed iterator returns empty list

 9.10 GC Behavior

 - test_gc_dealloc_cleanup: Drop reference without exhaust/close, force GC, verify pins == 0

 ---
 10. Implementation Order (TDD)

 Phase 1: Skeleton + Factory

 1. Create py_iter.h with struct and extern type
 2. Create py_iter.c with empty type object
 3. Update module.c to register type
 4. Update CMakeLists.txt
 5. Verify builds

 Phase 2: TDD - Basic Iteration

 1. Write test_range_basic (FAIL)
 2. Implement pytimelog_make_iter + range() method
 3. Implement PyTimelogIter_iternext
 4. Implement pytimelogiter_cleanup
 5. Run test (PASS)

 Phase 3: TDD - All Factory Methods

 1. Write tests for since/until/all/equal/point (FAIL)
 2. Implement each factory method
 3. Run tests (PASS)

 Phase 4: TDD - Cleanup Semantics

 1. Write pin tracking tests (FAIL)
 2. Verify cleanup decrements pins
 3. Implement close() method
 4. Run tests (PASS)

 Phase 5: TDD - Context Manager

 1. Write context manager tests (FAIL)
 2. Implement __enter__/__exit__
 3. Run tests (PASS)

 Phase 6: TDD - GC Support

 1. Write GC dealloc test (FAIL)
 2. Implement traverse/clear/dealloc with GC
 3. Run tests (PASS)

 Phase 7: TDD - Refcount Correctness

 1. Write refcount tests with custom __del__ objects
 2. Verify no leaks, no premature frees
 3. Run tests (PASS)

 Phase 8: Optional - next_batch

 1. Write batch tests (FAIL)
 2. Implement next_batch
 3. Run tests (PASS)

 ---
 11. Critical Invariants

 | ID  | Invariant                                          | Enforcement                               |
 |-----|----------------------------------------------------|-------------------------------------------|
 | I1  | Iterator yields new references                     | Py_NewRef() on handle decode              |
 | I2  | Balanced pins: 1 enter per iter, 1 exit on cleanup | Cleanup routine is single source of truth |
 | I3  | No UAF: cleanup before dealloc                     | GC UnTrack + cleanup + tp_free sequence   |
 | I4  | Reentrancy-safe: clear fields before drain         | Set closed=1, NULL pointers before ops    |
 | I5  | Snapshot isolation: iter sees consistent view      | Pin holds snapshot alive                  |

 ---
 12. Dependencies on py_timelog.c

 The factory methods need access to:
 - self->tl (engine pointer)
 - &self->handle_ctx (for pin tracking)
 - self->closed (for CHECK_CLOSED macro)

 All already available in PyTimelog struct.

 ---
 13. Module Registration (module.c)

 /* After PyTimelog_Type registration */
 if (PyType_Ready(&PyTimelogIter_Type) < 0) {
     goto error;
 }
 Py_INCREF(&PyTimelogIter_Type);
 if (PyModule_AddObject(m, "TimelogIter", (PyObject*)&PyTimelogIter_Type) < 0) {
     Py_DECREF(&PyTimelogIter_Type);
     goto error;
 }

 ---
 14. Checklist Before Implementation

 - LLD-B3 spec reviewed
 - Core iterator API verified (timelog.h)
 - Pin tracking API verified (py_handle.h)
 - PyTimelog struct understood (py_timelog.h)
 - Test patterns understood (test_py_timelog.c)
 - CMakeLists.txt structure understood
 - Module registration understood (module.c)

 ---
 15. Risk Mitigations

 | Risk             | Mitigation                                  |
 |------------------|---------------------------------------------|
 | Refcount bugs    | TDD with custom __del__ tracking objects    |
 | Pin imbalance    | Single cleanup routine, verify with metrics |
 | UAF in finalizer | Clear fields before drain (reentrancy-safe) |
 | GC cycle         | Implement tp_traverse/tp_clear from start   |
 | Memory leak      | Test with Py_DEBUG build, track refcounts   |

 ---
 Status

 Ready for implementation. All design decisions made, all dependencies verified.