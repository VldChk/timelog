╭─────────────────────────────────────────────────────────────────────────────────────────────────────────────────╮
     │ LLD-B4: PageSpan Zero-Copy Timestamp Spans — Implementation Plan                                                │
     │                                                                                                                 │
     │ Status: Ready for implementation                                                                                │
     │ Last Updated: 2026-01-14                                                                                        │
     │ Spec: docs/timelog_v1_lld_B4_pagespan_zero_copy.md                                                              │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ 1. Goal                                                                                                         │
     │                                                                                                                 │
     │ Implement zero-copy exposure of timestamps via CPython buffer protocol:                                         │
     │ - Timelog.page_spans(t1, t2) returns PageSpanIter yielding PageSpan objects                                     │
     │ - Each PageSpan exposes page memory as read-only memoryview directly backed by page->ts[]                       │
     │ - Shared snapshot owner (tl_py_span_owner_t) manages snapshot lifetime across multiple spans                    │
     │ - No data copying unless explicitly requested (.copy(), .tolist(), etc.)                                        │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ 2. Files to Create/Modify                                                                                       │
     │                                                                                                                 │
     │ New Files                                                                                                       │
     │                                                                                                                 │
     │ | File                                                 | Purpose                                              | │
     │ |------------------------------------------------------|------------------------------------------------------| │
     │ | bindings/cpython/include/timelogpy/py_span.h         | PyPageSpan type declaration                          | │
     │ | bindings/cpython/include/timelogpy/py_span_iter.h    | PyPageSpanIter type declaration                      | │
     │ | bindings/cpython/include/timelogpy/py_span_objects.h | PyPageSpanObjectsView type declaration               | │
     │ | bindings/cpython/src/py_span.c                       | PyPageSpan implementation (buffer protocol exporter) | │
     │ | bindings/cpython/src/py_span_iter.c                  | PyPageSpanIter implementation (span collector)       | │
     │ | bindings/cpython/src/py_span_objects.c               | PyPageSpanObjectsView implementation                 | │
     │ | bindings/cpython/tests/test_py_span.c                | TDD unit tests                                       | │
     │                                                                                                                 │
     │ Files to Modify                                                                                                 │
     │                                                                                                                 │
     │ | File                              | Change                                                     |              │
     │ |-----------------------------------|------------------------------------------------------------|              │
     │ | bindings/cpython/src/module.c     | Register PageSpan, PageSpanIter, PageSpanObjectsView types |              │
     │ | bindings/cpython/src/py_timelog.c | Add page_spans() factory method                            |              │
     │ | bindings/cpython/CMakeLists.txt   | Add new source files and test_py_span target               |              │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ 3. Internal Header Dependencies                                                                                 │
     │                                                                                                                 │
     │ B4 requires access to internal headers (unlike B2/B3 which use only public API):                                │
     │                                                                                                                 │
     │ #include "src/storage/tl_page.h"     /* tl_page_t, tl_page_lower_bound */                                       │
     │ #include "src/storage/tl_segment.h"  /* tl_segment_t, catalog access */                                         │
     │ #include "src/storage/tl_manifest.h" /* tl_manifest_t, L1/L0 arrays */                                          │
     │ #include "src/query/tl_snapshot.h"   /* tl_snapshot_t */                                                        │
     │                                                                                                                 │
     │ Verified Internal Structures:                                                                                   │
     │ - tl_manifest_t: l1[], l0[], n_l1, n_l0                                                                         │
     │ - tl_segment_t: catalog (embedded), page_count, tombstones                                                      │
     │ - tl_page_catalog_t: pages[] (tl_page_meta_t*), n_pages                                                         │
     │ - tl_page_meta_t: page (tl_page_t*), min_ts, max_ts, flags                                                      │
     │ - tl_page_t: ts[] (tl_ts_t*), h[] (tl_handle_t*), count, flags                                                  │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ 4. Data Structures                                                                                              │
     │                                                                                                                 │
     │ 4.1 Shared Snapshot Owner (Internal, C-only)                                                                    │
     │                                                                                                                 │
     │ typedef struct tl_py_span_owner {                                                                               │
     │     uint32_t refcnt;                  /* GIL-protected refcount */                                              │
     │     PyObject* timelog;                /* Strong ref to PyTimelog */                                             │
     │     tl_snapshot_t* snapshot;          /* Owned snapshot */                                                      │
     │     tl_py_handle_ctx_t* handle_ctx;   /* Borrowed from timelog */                                               │
     │ } tl_py_span_owner_t;                                                                                           │
     │                                                                                                                 │
     │ 4.2 Span Descriptor                                                                                             │
     │                                                                                                                 │
     │ typedef struct span_desc {                                                                                      │
     │     const tl_page_t* page;            /* Borrowed pointer */                                                    │
     │     size_t row_start;                 /* Inclusive */                                                           │
     │     size_t row_end;                   /* Exclusive */                                                           │
     │ } span_desc_t;                                                                                                  │
     │                                                                                                                 │
     │ 4.3 PyPageSpan                                                                                                  │
     │                                                                                                                 │
     │ typedef struct {                                                                                                │
     │     PyObject_HEAD                                                                                               │
     │     tl_py_span_owner_t* owner;        /* NULL if closed */                                                      │
     │     const tl_page_t* page;            /* NULL if closed */                                                      │
     │     size_t row_start;                 /* Inclusive */                                                           │
     │     size_t row_end;                   /* Exclusive */                                                           │
     │     Py_ssize_t shape[1];              /* For buffer protocol */                                                 │
     │     Py_ssize_t strides[1];            /* For buffer protocol */                                                 │
     │     uint32_t exports;                 /* Active buffer exports */                                               │
     │     uint8_t closed;                                                                                             │
     │ } PyPageSpan;                                                                                                   │
     │                                                                                                                 │
     │ 4.4 PyPageSpanIter                                                                                              │
     │                                                                                                                 │
     │ typedef struct {                                                                                                │
     │     PyObject_HEAD                                                                                               │
     │     tl_py_span_owner_t* owner;        /* NULL if closed */                                                      │
     │     span_desc_t* spans;               /* Precomputed array */                                                   │
     │     size_t count;                     /* Total spans */                                                         │
     │     size_t index;                     /* Current position */                                                    │
     │     uint8_t closed;                                                                                             │
     │ } PyPageSpanIter;                                                                                               │
     │                                                                                                                 │
     │ 4.5 PyPageSpanObjectsView                                                                                       │
     │                                                                                                                 │
     │ typedef struct {                                                                                                │
     │     PyObject_HEAD                                                                                               │
     │     PyObject* span;                   /* Strong ref to PyPageSpan */                                            │
     │ } PyPageSpanObjectsView;                                                                                        │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ 5. Key Algorithms                                                                                               │
     │                                                                                                                 │
     │ 5.1 Span Collection                                                                                             │
     │                                                                                                                 │
     │ For each segment in snapshot (L1 first, then L0):                                                               │
     │   1. Skip tombstone-only segments (page_count == 0)                                                             │
     │   2. Prune by segment min_ts/max_ts bounds                                                                      │
     │   3. Find candidate pages via catalog binary search                                                             │
     │   4. For each candidate page:                                                                                   │
     │      - Skip TL_PAGE_FULLY_DELETED                                                                               │
     │      - row_start = tl_page_lower_bound(page, t1)                                                                │
     │      - row_end = tl_page_lower_bound(page, t2)                                                                  │
     │      - If row_start < row_end, emit span                                                                        │
     │                                                                                                                 │
     │ 5.2 Owner Destruction Order (Critical)                                                                          │
     │                                                                                                                 │
     │ static void span_owner_destroy(tl_py_span_owner_t* owner) {                                                     │
     │     if (!owner) return;                                                                                         │
     │                                                                                                                 │
     │     // 1. Move pointers to locals BEFORE Python code                                                            │
     │     tl_snapshot_t* snap = owner->snapshot; owner->snapshot = NULL;                                              │
     │     tl_py_handle_ctx_t* ctx = owner->handle_ctx; owner->handle_ctx = NULL;                                      │
     │     PyObject* timelog = owner->timelog; owner->timelog = NULL;                                                  │
     │                                                                                                                 │
     │     // 2. Release snapshot (no Python code)                                                                     │
     │     if (snap) tl_snapshot_release(snap);                                                                        │
     │                                                                                                                 │
     │     // 3. Preserve exception state around drain/DECREF                                                          │
     │     PyObject *exc_type, *exc_value, *exc_tb;                                                                    │
     │     PyErr_Fetch(&exc_type, &exc_value, &exc_tb);                                                                │
     │                                                                                                                 │
     │     if (ctx) tl_py_pins_exit_and_maybe_drain(ctx);                                                              │
     │     Py_XDECREF(timelog);                                                                                        │
     │                                                                                                                 │
     │     PyErr_Restore(exc_type, exc_value, exc_tb);                                                                 │
     │     free(owner);                                                                                                │
     │ }                                                                                                               │
     │                                                                                                                 │
     │ 5.3 Buffer Protocol (bf_getbuffer)                                                                              │
     │                                                                                                                 │
     │ static int pagespan_getbuffer(PyObject* exporter, Py_buffer* view, int flags) {                                 │
     │     PyPageSpan* self = (PyPageSpan*)exporter;                                                                   │
     │                                                                                                                 │
     │     if (self->closed) {                                                                                         │
     │         PyErr_SetString(PyExc_ValueError, "PageSpan is closed");                                                │
     │         return -1;                                                                                              │
     │     }                                                                                                           │
     │     if (flags & PyBUF_WRITABLE) {                                                                               │
     │         PyErr_SetString(PyExc_BufferError, "PageSpan buffer is read-only");                                     │
     │         return -1;                                                                                              │
     │     }                                                                                                           │
     │                                                                                                                 │
     │     const Py_ssize_t n = (Py_ssize_t)(self->row_end - self->row_start);                                         │
     │     void* ptr = (void*)(self->page->ts + self->row_start);                                                      │
     │                                                                                                                 │
     │     // Manual init (not PyBuffer_FillInfo)                                                                      │
     │     view->obj = Py_NewRef(exporter);                                                                            │
     │     view->buf = ptr;                                                                                            │
     │     view->len = n * sizeof(tl_ts_t);                                                                            │
     │     view->readonly = 1;                                                                                         │
     │     view->itemsize = sizeof(tl_ts_t);                                                                           │
     │     view->format = (flags & PyBUF_FORMAT) ? (char*)"q" : NULL;  // Static string                                │
     │                                                                                                                 │
     │     if (flags & (PyBUF_ND | PyBUF_STRIDES)) {                                                                   │
     │         view->ndim = 1;                                                                                         │
     │         self->shape[0] = n;                                                                                     │
     │         view->shape = self->shape;                                                                              │
     │         view->strides = (flags & PyBUF_STRIDES) ? self->strides : NULL;                                         │
     │         if (flags & PyBUF_STRIDES) self->strides[0] = sizeof(tl_ts_t);                                          │
     │     } else {                                                                                                    │
     │         view->ndim = 0; view->shape = NULL; view->strides = NULL;                                               │
     │     }                                                                                                           │
     │     view->suboffsets = NULL;                                                                                    │
     │     view->internal = NULL;                                                                                      │
     │                                                                                                                 │
     │     self->exports++;                                                                                            │
     │     return 0;                                                                                                   │
     │ }                                                                                                               │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ 6. TDD Test Plan                                                                                                │
     │                                                                                                                 │
     │ Phase 1: Infrastructure                                                                                         │
     │                                                                                                                 │
     │ - test_types_ready - All 3 types ready and registered                                                           │
     │ - test_direct_instantiation_blocked - TypeError on direct construction                                          │
     │                                                                                                                 │
     │ Phase 2: Owner Lifecycle                                                                                        │
     │                                                                                                                 │
     │ - test_owner_create_destroy - Basic lifecycle                                                                   │
     │ - test_owner_refcount - incref/decref correctness                                                               │
     │ - test_owner_snapshot_pin - pins_enter/exit called                                                              │
     │                                                                                                                 │
     │ Phase 3: Span Collection                                                                                        │
     │                                                                                                                 │
     │ - test_page_spans_empty_timelog - Empty returns empty iterator                                                  │
     │ - test_page_spans_no_match - No overlap returns empty                                                           │
     │ - test_page_spans_single_page - One span returned                                                               │
     │ - test_page_spans_multi_page - Multiple spans                                                                   │
     │                                                                                                                 │
     │ Phase 4: Buffer Protocol                                                                                        │
     │                                                                                                                 │
     │ - test_timestamps_memoryview - mv = span.timestamps works                                                       │
     │ - test_buffer_values_correct - Values match inserted data                                                       │
     │ - test_buffer_write_rejected - Assignment raises TypeError                                                      │
     │ - test_buffer_length - len(mv) == len(span)                                                                     │
     │                                                                                                                 │
     │ Phase 5: Close Semantics                                                                                        │
     │                                                                                                                 │
     │ - test_close_releases_owner - Owner released on close                                                           │
     │ - test_close_idempotent - Multiple close() safe                                                                 │
     │ - test_close_with_exported_buffer_raises - BufferError if exports > 0                                           │
     │ - test_access_after_close_raises - ValueError on closed span                                                    │
     │                                                                                                                 │
     │ Phase 6: Iterator                                                                                               │
     │                                                                                                                 │
     │ - test_iter_yields_spans - Each item is PageSpan                                                                │
     │ - test_iter_close - iter.close() works                                                                          │
     │ - test_iter_context_manager - with statement works                                                              │
     │                                                                                                                 │
     │ Phase 7: Objects View                                                                                           │
     │                                                                                                                 │
     │ - test_objects_len - len(span.objects()) correct                                                                │
     │ - test_objects_getitem - Indexing returns correct object                                                        │
     │ - test_objects_iter - list(span.objects()) works                                                                │
     │                                                                                                                 │
     │ Phase 8: Lifetime Integration                                                                                   │
     │                                                                                                                 │
     │ - test_timelog_close_blocked_by_span - pins prevent close                                                       │
     │ - test_memoryview_outlives_span - mv keeps span alive                                                           │
     │                                                                                                                 │
     │ Phase 9: Segment Correctness                                                                                    │
     │                                                                                                                 │
     │ - test_span_from_l1 - L1 segments work                                                                          │
     │ - test_span_from_l0 - L0 segments work                                                                          │
     │ - test_tombstone_only_segments_skipped - No spans from tombstone-only                                           │
     │                                                                                                                 │
     │ Phase 10: Stress/Sanitizer                                                                                      │
     │                                                                                                                 │
     │ - test_many_spans_no_leak - ASan clean                                                                          │
     │ - test_buffer_lifetime_stress - No UAF                                                                          │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ 7. Implementation Phases                                                                                        │
     │                                                                                                                 │
     │ Phase 1: Headers and Stubs                                                                                      │
     │                                                                                                                 │
     │ 1. Create headers: py_span.h, py_span_iter.h, py_span_objects.h                                                 │
     │ 2. Create stub .c files with type objects (tp_new raises TypeError)                                             │
     │ 3. Update module.c to register types                                                                            │
     │ 4. Update CMakeLists.txt                                                                                        │
     │ 5. Tests: test_types_ready, test_direct_instantiation_blocked                                                   │
     │                                                                                                                 │
     │ Phase 2: Shared Owner                                                                                           │
     │                                                                                                                 │
     │ 1. Implement tl_py_span_owner_t struct                                                                          │
     │ 2. Implement span_owner_create() - snapshot acquire, pins_enter                                                 │
     │ 3. Implement span_owner_incref() / span_owner_decref()                                                          │
     │ 4. Implement span_owner_destroy() with cleanup order                                                            │
     │ 5. Tests: test_owner_*                                                                                          │
     │                                                                                                                 │
     │ Phase 3: Span Collection                                                                                        │
     │                                                                                                                 │
     │ 1. Add internal header includes                                                                                 │
     │ 2. Implement collect_spans() algorithm                                                                          │
     │ 3. Implement PyPageSpanIter factory (page_spans() method)                                                       │
     │ 4. Tests: test_page_spans_*                                                                                     │
     │                                                                                                                 │
     │ Phase 4: Buffer Protocol                                                                                        │
     │                                                                                                                 │
     │ 1. Implement PyPageSpan type with buffer protocol                                                               │
     │ 2. Implement pagespan_getbuffer, pagespan_releasebuffer                                                         │
     │ 3. Add .timestamps property (returns memoryview)                                                                │
     │ 4. Tests: test_timestamps_*, test_buffer_*                                                                      │
     │                                                                                                                 │
     │ Phase 5: Close/Lifecycle                                                                                        │
     │                                                                                                                 │
     │ 1. Implement pagespan_close() with export check                                                                 │
     │ 2. Implement cleanup, dealloc, GC support                                                                       │
     │ 3. Add context manager                                                                                          │
     │ 4. Tests: test_close_*                                                                                          │
     │                                                                                                                 │
     │ Phase 6: Iterator Protocol                                                                                      │
     │                                                                                                                 │
     │ 1. Complete PyPageSpanIter with __next__                                                                        │
     │ 2. Add iter.close() and context manager                                                                         │
     │ 3. Tests: test_iter_*                                                                                           │
     │                                                                                                                 │
     │ Phase 7: Objects View                                                                                           │
     │                                                                                                                 │
     │ 1. Implement PyPageSpanObjectsView type                                                                         │
     │ 2. Sequence protocol: __len__, __getitem__                                                                      │
     │ 3. Iterator protocol, .copy() method                                                                            │
     │ 4. Tests: test_objects_*                                                                                        │
     │                                                                                                                 │
     │ Phase 8: Integration & Stress                                                                                   │
     │                                                                                                                 │
     │ 1. Verify pins interaction                                                                                      │
     │ 2. Run under ASan/UBSan                                                                                         │
     │ 3. Tests: Remaining tests                                                                                       │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ 8. Critical Invariants                                                                                          │
     │                                                                                                                 │
     │ | ID  | Invariant                              | Enforcement                                |                   │
     │ |-----|----------------------------------------|--------------------------------------------|                   │
     │ | I1  | Owner holds snapshot pin               | pins_enter on create, pins_exit on destroy |                   │
     │ | I2  | Page pointers borrowed from snapshot   | Only valid while owner alive               |                   │
     │ | I3  | Buffer exports prevent close           | exports > 0 raises BufferError             |                   │
     │ | I4  | Static format string                   | "q" at file scope                          |                   │
     │ | I5  | Cleanup order: snapshot → pins → owner | Single destroy routine                     |                   │
     │ | I6  | Exception preservation                 | PyErr_Fetch/Restore around drain           |                   │
     │ | I7  | No direct construction                 | tp_new raises TypeError                    |                   │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ 9. Lifetime Chain                                                                                               │
     │                                                                                                                 │
     │ memoryview → holds ref to PyPageSpan (exporter)                                                                 │
     │   ↓                                                                                                             │
     │ PyPageSpan → holds ref to tl_py_span_owner_t (refcounted)                                                       │
     │   ↓                                                                                                             │
     │ span_owner → holds ref to PyTimelog (keeps handle_ctx alive)                                                    │
     │   ↓                                                                                                             │
     │ span_owner → owns tl_snapshot_t (keeps page memory valid)                                                       │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ 10. Risk Mitigations                                                                                            │
     │                                                                                                                 │
     │ | Risk                    | Mitigation                           |                                              │
     │ |-------------------------|--------------------------------------|                                              │
     │ | UAF in page pointer     | Owner strong ref to snapshot         |                                              │
     │ | Buffer memory invalid   | exports tracking prevents close      |                                              │
     │ | Refcount bugs           | TDD with dict objects (non-immortal) |                                              │
     │ | Pin imbalance           | Single owner destroy routine         |                                              │
     │ | Internal header changes | Document coupling, test thoroughly   |                                              │
     │                                                                                                                 │
     │ ---                                                                                                             │
     │ Status                                                                                                          │
     │                                                                                                                 │
     │ Ready for implementation. All structures verified against codebase, TDD test plan complete.