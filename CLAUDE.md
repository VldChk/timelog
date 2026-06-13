# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

# Timelog — Engineering Guide

This is an **IN-MEMORY** LSM-style time-indexed storage engine in C17 with CPython bindings.
**There is NO disk I/O** — all data lives in memory. PyPI package: `timelog-lib`, import as `timelog`.

## Mental Model

### What Timelog Does

Timelog stores `(timestamp, handle)` pairs and answers **time-range queries** efficiently.
The handle is a `uint64_t` that encodes a `PyObject*` in the CPython bindings.

Think of it as a specialized in-memory index optimized for:
- Append-heavy workloads (writes are cheap)
- Range scans (queries like "all events between t1 and t2")
- Snapshot isolation (readers never block writers)
- Background maintenance (compaction happens asynchronously)

### LSM Architecture (All In-Memory)

```
Write Path:                              Read Path:

append(ts, handle) ─┐                    query([t1, t2))
                    │                           │
             ┌──────▼───────┐           ┌───────▼───────┐
             │   Memtable   │◄──────────│   Snapshot    │
             │  (mutable)   │           │  (consistent) │
             └──────┬───────┘           └───────┬───────┘
                    │ seal when full            │
             ┌──────▼───────┐                   │
             │   Memrun     │◄──────────────────┤
             │  (immutable) │                   │
             └──────┬───────┘                   │
                    │ flush (to memory)         │
             ┌──────▼───────┐                   │
             │   L0 Segs    │◄──────────────────┤  k-way merge
             │  (overlap)   │                   │  across all
             └──────┬───────┘                   │  components
                    │ compaction                │
             ┌──────▼───────┐                   │
             │   L1 Segs    │◄──────────────────┘
             │ (non-overlap)│
             └──────────────┘
```

**Key insight**: Data flows downward (memtable → memrun → L0 → L1) but queries
merge across ALL levels simultaneously. This is the essence of LSM.

### Core Data Structures

| Structure | Mutability | Contains | Purpose |
|-----------|------------|----------|---------|
| **Memtable** | Mutable | Sorted run + OOO head + sealed queue | Ingest buffer |
| **OOORunset** | Immutable | Refcounted array of sorted OOO runs | OOO run collection |
| **Memrun** | Immutable | Sealed memtable snapshot | Flush queue (ring buffer) |
| **Memview** | Immutable | Deep copy of active + pinned sealed | Snapshot delta state |
| **Page** | Immutable | `ts[]` + `h[]` arrays | ~64 KiB memory unit (`target_page_bytes`, ≈4K records) |
| **Segment** | Immutable | Page array + fence pointers | In-memory container |
| **Manifest** | Immutable | L0 + L1 segment catalogs (tombstones live on L0 segments) | Current state |
| **Snapshot** | Immutable | Manifest ref + memview | Consistent read view |

### OOO Mini-LSM Architecture (Option B)

Out-of-order records use a mini-LSM within the memtable for O(1) ingestion:

```
append(ts, handle)
       │
       ▼
┌──────────────────┐
│   active_run     │  ← In-order records (sorted)
├──────────────────┤
│   ooo_head       │  ← OOO append buffer (unsorted, O(1) insert)
├──────────────────┤
│   ooo_runs       │  ← Immutable sorted runs (refcounted runset)
└──────────────────┘
       │ seal when full
       ▼
┌──────────────────┐
│   Sealed Queue   │  ← Ring buffer of memruns (FIFO)
└──────────────────┘
```

**Key design decisions:**
- `ooo_head`: Mutable append-only buffer, O(1) ingestion, sorted only at seal
- `ooo_runs`: Immutable sorted runs stored in refcounted `tl_ooorunset_t`
- Queries use `tl_submerge` for internal k-way merge of delta components
- Tie-break ordering: `active_run` before `ooo_runs` (by generation) before `ooo_head`
- Generation numbers (`gen`) ensure deterministic ordering for equal timestamps

**Handles**: The C core stores `tl_handle_t` (uint64_t). For CPython bindings,
`tl_py_handle_encode(PyObject*)` casts the pointer to handle, and
`tl_py_handle_decode(handle)` casts it back. The engine is payload-agnostic.

---

## Critical Invariants (Never Violate)

### 1. Immutability After Publication

Once any structure is visible to snapshots, it MUST NOT be modified.
This enables lock-free reads. Violation = data corruption or crashes.

### 2. L1 Non-Overlap

L1 segments partition the time domain into non-overlapping windows.
Each L1 segment covers `[window_start, window_end)` and no two overlap.
Compaction uses **window bounds** (not record bounds) for L1 selection.

### 3. Sortedness

Within every page, `ts[0] <= ts[1] <= ... <= ts[n-1]`.
This enables binary search within pages.

### 4. Half-Open Intervals [t1, t2)

**EVERYWHERE**. Query ranges, tombstones, windows — all use half-open intervals.
- `[t1, t2)` means "t1 is included, t2 is excluded"
- Empty range: `t1 >= t2`
- Point query at T: `[T, T+1)`

### 5. Tombstone Canonicalization

Tombstones form an interval set that is always:
- Sorted by start time
- Non-overlapping (no two intervals intersect)
- Non-adjacent (touching intervals are merged)
- Half-open `[start, end)`

### 6. Snapshot Consistency

A snapshot sees exactly one consistent state by taking `writer_mu`, which also
serializes every manifest publisher:
```
Lock writer_mu → acquire manifest → capture/ref cached memview → capture op_seq → unlock
```
Publication still wraps manifest swaps and sealed-queue pops in a short
`view_seq` seqlock window, but current snapshot acquisition does not run a
standalone seqlock retry loop because `writer_mu` already prevents torn
manifest/memview captures.

### 7. Sealed Queue Ring Buffer (H-07)

The sealed memrun queue uses a fixed-capacity ring buffer with overflow-safe arithmetic:
```c
// CORRECT: subtraction-based index (handles wraparound)
size_t idx = (sealed_head - sealed_len + offset + cap) % cap;

// WRONG: addition-based (can overflow)
size_t idx = (sealed_head + offset) % cap;  // DON'T USE
```
FIFO order is maintained during memview capture by iterating `offset` from 0 to `sealed_len-1`.

### 8. Two-Phase Copy for Memview (H-09)

Memview capture uses epoch-based change detection with bounded retries:
```
Phase 1: Read sealed queue state (under memtable_mu)
Phase 2: Acquire memruns and validate epoch unchanged
If epoch changed: retry (max 3 times)
If still changing: fallback to locked allocation
```
This minimizes lock contention while ensuring consistency.

### 9. Window Grid Freeze (C-10)

Once any L1 segment exists, the adaptive window grid is **frozen**:
- `window_grid_frozen` flag set on first L1 creation
- Prevents window resizing that would invalidate L1 partitioning
- Checked in `tl_compact_one()` before applying new window size

### 10. L1 Validation in Release Mode (H-12, H-14)

L1 invariants are checked in **release builds**, not just debug:
- **H-12**: Records within window bounds (`min_ts >= window_start`, `max_ts < window_end`)
- **H-14**: Non-overlap validation after manifest sort

These checks prevent data corruption from reaching production.

---

## Lock Ordering

```
maint_mu → flush_mu → writer_mu → memtable.mu
```

**Never acquire a lock while holding a lock to its right.**

| Lock | Purpose | Held By | Duration |
|------|---------|---------|----------|
| `maint_mu` | Coordinate background worker | Maintenance thread | Long (compaction merge) |
| `flush_mu` | Serialize flush operations | Flush path | Medium |
| `writer_mu` | Protect manifest publication | Writers | **SHORT ONLY** |
| `memtable.mu` | Protect memtable internals | Append path | Very short |

**Critical Rule**: Never do expensive work while holding `writer_mu`.
Build segments OFF-LOCK, then briefly acquire to swap manifest.

**Deferred Signaling**: Set flags under `writer_mu`, signal condvars under `maint_mu` after unlock.

---

## Key Algorithms

### K-Way Merge (Read Path)

Queries merge K sorted sources (memview + L0 segments + L1 segments).
Uses a min-heap of iterators, each yielding records in timestamp order.

**Two-level merge architecture:**
1. **Outer merge** (`tl_merge_iter`): Merges segment iterators + memview iterators
2. **Inner merge** (`tl_submerge`): Merges delta components within memview
   - Active run + OOO head + OOO runs → single sorted stream
   - Tie-break by `tie_id` (lower wins): run=0, ooo_runs=1..N, head=N+1

Complexity: O(N log K) where N = total records, K = source count
Memory: O(K) heap entries

### Binary Search (lower_bound)

For half-open `[t1, t2)` queries:
```c
i_start = lower_bound(ts, 0, n, t1);  // First ts >= t1
i_end = lower_bound(ts, 0, n, t2);    // First ts >= t2
// Scan [i_start, i_end)
```
Off-by-one is the #1 bug source. Test boundary conditions exhaustively.

### Tombstone Coalescing

When adding new tombstones, merge with existing interval set:
```
Input: existing intervals + new interval [t1, t2)
Output: minimal interval set covering the union
```
Complexity: O(T) where T = total intervals.

### Interval Filtering

During query, skip records covered by tombstones:
```
For each record at timestamp T:
  If any tombstone [start, end) contains T: skip
  Else: yield record
```
Uses cursor to avoid O(T) lookup per record — amortized O(1).

### Compaction Flow

```
Trigger check → Selection (window-based) → K-way merge (OFF-LOCK) → Publication (brief lock)
```
**Deferred drops**: Handle drop callbacks fire AFTER successful manifest publish, never during merge.

**Strict Publish Protocol (H-17):**
- Publication uses bounded retries (3 attempts) with `TL_EBUSY` on manifest change
- Metrics: `compaction_publish_ebusy` (final EBUSY), `compaction_retries` (interim retries)
- STRICT mode: Returns EBUSY if manifest changed; REBASE mode: Rebuilds and retries

**Delete Debt Calculation (H-18):**
- Uses cursor-based O(T+W) algorithm, not O(T*W)
- Linear sweep with cursor position tracking
- `MAX_DEBT_WINDOWS = 1000` cap preserved
- Short-circuit returns 1.0 for unbounded tombstone counts

**Residual Tombstones (H-19):**
- Tombstones extending beyond merged window are preserved
- `tl__build_residual_tombstones()` uses unclipped context
- Residual segment added to manifest builder after main merge

---

## Memory Management

### Allocation Wrappers

```c
void* tl__malloc(size_t size);
void* tl__calloc(size_t count, size_t size);
void* tl__realloc(void* ptr, size_t size);
void tl__free(void* ptr);
```
Always use these. They respect custom allocators and enable tracking.

### Arena Pattern for Builds

When building a segment:
1. Allocate arena for all pages
2. Fill pages during build
3. On success: publish segment (arena ownership transfers)
4. On failure: free entire arena

### Reference Counting

Manifests and segments use reference counting:
```c
tl_manifest_acquire(m);  // refcnt++
tl_manifest_release(m);  // refcnt--; if (0) destroy
```
Snapshots "pin" the manifest they reference. While pinned, those structures cannot be freed.

### Manifest Builder Validation (H-10, H-11)

The manifest builder performs validation at build time:
- **Level validation (H-10)**: Segments added to correct level (L0/L1)
- **Duplicate detection (H-11)**: Checks for:
  - Within-list duplicates (same segment added twice)
  - Add+remove same segment
  - Adding segment already in base manifest
- On validation failure: Returns error, caller must release manifest

---

## Error Handling

### C Status Codes

```c
typedef enum {
    TL_OK = 0,      // Success
    TL_EOF,         // End of iteration (not an error)
    TL_EINVAL,      // Invalid argument
    TL_ENOMEM,      // Allocation failed
    TL_EBUSY,       // Backpressure (record WAS inserted, but...)
    TL_ESTATE,      // Invalid state (closed, etc.)
    TL_EOVERFLOW,   // Arithmetic overflow
    TL_EINTERNAL,   // Internal bug
} tl_status_t;
```

**Critical**: `TL_EBUSY` means the operation **succeeded** but backpressure occurred.
Do NOT rollback, do NOT retry — the record is already in the log.

### Cleanup Pattern

```c
tl_status_t my_function(args) {
    tl_status_t st = TL_OK;
    void* a = NULL;
    void* b = NULL;

    a = tl__malloc(size_a);
    if (!a) { st = TL_ENOMEM; goto cleanup; }

    b = tl__malloc(size_b);
    if (!b) { st = TL_ENOMEM; goto cleanup; }

    // Do work...
    st = TL_OK;

cleanup:
    if (st != TL_OK) {
        tl__free(a);
        tl__free(b);
    }
    return st;
}
```

---

## CPython Binding Rules

### Thread State and Locking (post-Layer-B)

The binding supports three CPython modes: regular (single interpreter),
subinterpreters with per-interpreter GIL (3.12+), and free-threaded
(3.14t, `Py_mod_gil = Py_MOD_GIL_NOT_USED`). The thread-safety
contract:

- **Always have an attached Python thread state** when calling Python C-API.
  Under free-threaded builds the GIL is absent; an attached thread state on
  the correct interpreter is the only precondition. Probe with
  `PyThreadState_GetUnchecked()` + `PyThreadState_GetInterpreter()` on 3.13+
  (see `tl_py_attached_to_interp`), NOT `PyGILState_Check()`.
- **Detach the active thread state** around long C work, releasing a GIL where
  present: `flush`, `compact`, `maint_step`, `stop_maintenance`, explicit
  user `close`, and iterator range-count precomputation. For `PyTimelog`
  engine entrypoints, use the existing helper pattern: hold `core_lock`,
  detach with `Py_BEGIN_ALLOW_THREADS`, call the core, release `core_lock`
  before reattaching, then do Python cleanup after reattach. Finalizer/dealloc
  cleanup keeps the thread state attached.
- **Internal locks** (see LLD §5.4):
  - L1 `PyTimelog.core_lock` (`PyThread_type_lock`): lifecycle + engine entry.
  - L2 `handle_ctx.live_lock` (`PyMutex` / `PyThread_type_lock` fallback):
    live-handle hash table.
  - L4 per-object `TL_PY_OBJ_LOCK` (`Py_BEGIN_CRITICAL_SECTION`): mutable
    fields on PyTimelog{Iter}, PyPageSpan{Iter}, PyPageSpanObjects{View,Iter}.
- **Hard invariant**: no `Py_DECREF`, weakref callback, warning, or any code
  that may execute Python may run while ANY internal lock is held. Use the
  collect-under-lock / execute-outside-lock pattern.
- **Atomics**: `PyTimelog.closed` and `PyTimelog.tl` are `_Atomic`. Hot-path
  `CHECK_CLOSED` macros use `atomic_load_explicit(acquire)`. Writes happen
  under `core_lock` with `atomic_store_explicit(release)`.

```c
/* PyTimelog engine-entry pattern: self->core_lock is already held. */
Py_BEGIN_ALLOW_THREADS
st = core_call(self->tl);               /* no Python C-API */
PyThread_release_lock(self->core_lock); /* before reattaching */
Py_END_ALLOW_THREADS
/* Python cleanup / Py_DECREF happens here, with no internal locks held. */
```

### Handle Lifecycle (Lock-Free Retired Queue)

When compaction drops handles, the `on_drop_handle` callback enqueues them to a
lock-free Treiber stack (MPSC). The callback does NOT hold the GIL.

```
on_drop_handle: malloc node → push to retired stack (CAS, RELEASE)
drain_retired:   exchange head (ACQ_REL) → Py_DECREF each → free node
```

**Pin Counter**: `pins_enter()` before acquiring snapshot, `pins_exit_and_maybe_drain()`
after releasing. Drain only runs when `pins == 0`.

### Reference Counting

| Rule | Example |
|------|---------|
| Functions return new references | Caller owns result, must DECREF |
| Store object? INCREF first | `Py_INCREF(obj); self->stored = obj;` |
| Remove stored object? DECREF after | `Py_DECREF(self->stored); self->stored = NULL;` |
| Error path? Rollback INCREFs | If INCREF then fail, DECREF before return |
| **TL_EBUSY? Do NOT rollback** | Record is already in engine, don't DECREF |

### Buffer Protocol (PageSpan)

PageSpan provides zero-copy timestamp access via Python's buffer protocol:

```c
// bf_getbuffer: export buffer
view->buf = span->ts;
view->len = span->len * sizeof(int64_t);
view->obj = Py_NewRef((PyObject*)span);
span->exports++;

// bf_releasebuffer: release buffer
span->exports--;
```

**Critical**: Cannot close span while buffers are exported (raise `BufferError`).

### Exception State Preservation

All cleanup paths must preserve exception state across `Py_DECREF` calls:
```c
PyObject *exc_type, *exc_value, *exc_tb;
PyErr_Fetch(&exc_type, &exc_value, &exc_tb);
// Py_DECREF operations that may run __del__
PyErr_Restore(exc_type, exc_value, exc_tb);
```

### Handle Ownership and on_drop_handle

The `on_drop_handle` callback has a specific, narrow contract:

**When it fires:**
- During compaction when a tombstone physically deletes a record
- During flush when a tombstone removes sealed records
- AFTER successful manifest publish (not speculatively)

**When it does NOT fire:**
- During tl_close()
- When segments are released
- For records not covered by tombstones

**Implication for bindings:**
- The CPython binding must track inserted PyObject* refs independently
- At Timelog.close(), the binding should DECREF all tracked refs
- The on_drop_handle callback is for tombstone-based physical deletes only

---

## Testing Strategy

### What to Test

1. **Boundary conditions**: `TL_TS_MIN`, `TL_TS_MAX`, empty inputs
2. **Half-open semantics**: Edge cases of `[t1, t2)`
3. **Tombstone correctness**: Coalescing, filtering, edge overlaps
4. **Concurrency**: Multiple readers, reader vs writer, background worker
5. **Error paths**: `ENOMEM` recovery, cleanup on failure
6. **Invariant preservation**: Run validators after every operation (debug)

### Sanitizers (Non-Negotiable)

ASan+UBSan are **automatically enabled** in `CMAKE_BUILD_TYPE=Debug` on GCC/Clang.
TSan requires a separate build (incompatible with ASan).

```bash
# ASan + UBSan (default in Debug)
cmake -B build -DCMAKE_BUILD_TYPE=Debug && cmake --build build
ctest --test-dir build --output-on-failure

# ThreadSanitizer (separate build, no ASan)
cmake -B build-tsan -DCMAKE_BUILD_TYPE=RelWithDebInfo -DCMAKE_C_FLAGS="-fsanitize=thread -g"
cmake --build build-tsan && ctest --test-dir build-tsan --output-on-failure
```

---

## Project Layout

```
core/include/timelog/timelog.h     # PUBLIC API (source of truth for all C types/functions)
core/src/                          # C core engine
  tl_timelog.c                     # Top-level orchestrator
  internal/                        # Alloc, sync, heap, intervals, recvec
  storage/                         # Page, segment, manifest, window
  delta/                           # Memtable, memrun, memview, OOO run, flush (write path)
  query/                           # Snapshot, plan, filter, iterators, merge (read path)
  maint/                           # Compaction, adaptive segmentation
core/tests/                        # C unit tests (test_main.c entry point)
bindings/cpython/src/              # CPython extension (_timelog): py_timelog, py_iter, py_span, py_handle, py_errors
bindings/cpython/tests/            # C-level binding tests (embedded Python)
python/timelog/                    # Pure Python facade (_api.py + __init__.py)
python/tests/                      # Python facade tests (pytest)
lab/                               # Resilience lab (LOCAL/untracked): oracle-driven concurrency/property harness
demo/ci/                           # CI helper scripts (static phase checks, compat baseline runner)
benchmarks/                        # Benchmark harnesses (see docs/PERFORMANCE_METHODOLOGY.md)
```

---

## Performance Characteristics

### Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Append (in-order) | O(1) amortized | O(1) |
| Append (OOO) | O(1) amortized | O(1) |
| OOO seal | O(H log H) | O(H) |
| Range query [t1, t2) | O(K log P + M) | O(K) |
| Point query at T | O(K log P) | O(K) |
| Delete range | O(log T) | O(T) |
| Delete debt calc | O(T + W) | O(1) |
| Flush | O(M log M) | O(M) |
| Compaction | O(S log K) | O(K + S) |

Where: K = component count, P = pages/component, M = result size, T = tombstones, S = segment records, H = OOO head size, W = window count

### Background Maintenance (Default)

Background maintenance is **enabled by default** (`TL_MAINT_BACKGROUND`). The worker
auto-starts in `tl_open()` and handles flush/compaction asynchronously. This is the
right default for most use cases (streaming writes, typical workloads).

For **bulk ingestion of out-of-order data**, background maintenance causes contention
because compaction holds locks during merge.

**OOO Profiling Results** (5M records, ~17% OOO rate):

| Mode | Throughput | Slow Batches |
|------|------------|--------------|
| Background maintenance (default) | 96K/s | 42% |
| Manual mode | 289K/s | 0% |

**Override for bulk OOO ingestion**:
```python
Timelog(maintenance="disabled", busy_policy="flush")
```
This is 3x faster because compaction of overlapping segments is expensive.
After bulk ingestion, switch back to background maintenance for ongoing writes.

---

## Code Style

### Naming Conventions

| Category | Pattern | Example |
|----------|---------|---------|
| Public C API | `tl_<noun>_<verb>()` | `tl_snapshot_acquire()` |
| Internal C | `tl__<module>_<func>()` | `tl__page_build()` |
| C Types | `tl_<name>_t` | `tl_segment_t` |
| Constants | `TL_<NAME>` | `TL_OK`, `TL_TS_MIN` |
| Python types | `Py<Name>` | `PyTimelog`, `PyPageSpan` |

### Common Pitfalls

**C Core**:
1. Holding `writer_mu` during build — blocks snapshots
2. Manifest or sealed-queue publication outside the short `view_seq` write
   window — snapshots can observe source/output double visibility
3. Off-by-one in binary search — wrong results
4. Signed overflow in timestamp math — UB
5. Using `malloc()` directly — breaks custom allocator
6. L1 selection by record bounds — violates non-overlap (use window bounds)
7. Ring buffer index via addition — use subtraction-based formula (H-07)
8. Memview capture without epoch validation — stale data (H-09)
9. Changing window size after L1 exists — violates grid freeze (C-10)
10. Cross-page ordering not checked — sortedness violation (H-13)
11. Delete debt O(T*W) algorithm — use cursor-based O(T+W) (H-18)
12. PageSpan hook fires before arming — symmetric arm/fire pattern (H-15)
13. Merge iterator ignores error state — must propagate errors (H-16)

**Python Bindings**:
14. Python C-API without an attached thread state on the owning interpreter —
    crash or cross-interpreter corruption; free-threaded builds do not make
    Python C-API calls thread-state-free
15. Missing INCREF on return — leak or UAF
16. Closing span with exported buffer — must raise `BufferError`
17. DECREF before INCREF on borrowed ref — UAF
18. Rollback INCREF on `TL_EBUSY` — wrong (record IS in log)

---

## Design Documents

| Document | Purpose |
|----------|---------|
| `docs/index.md` | Canonical docs entry point |
| `docs/what-is-timelog.md` | Product definition and scope |
| `docs/python-api.md` | Python-facing API reference |
| `docs/configuration.md` | Runtime configuration and presets |
| `docs/errors-and-retry-semantics.md` | Error contracts and retry rules |
| `docs/operations.md` | Lifecycle and troubleshooting |
| `docs/getting-started.md` | Quick-start guide |
| `docs/performance.md` | Performance characteristics |
| `docs/PERFORMANCE_METHODOLOGY.md` | Benchmark methodology |
| `docs/testing-and-ci.md` | Test strategy and CI configuration |
| `docs/pypi-release.md` | Release and publishing process |
| `docs/glossary.md` | Terminology reference |
| `docs/internals/hld.md` | Architecture overview |
| `docs/internals/components/write-path.md` | Memtable/flush write mechanics |
| `docs/internals/components/read-path.md` | Snapshot and query mechanics |
| `docs/internals/components/storage-and-manifest.md` | Storage layout and publication |
| `docs/internals/components/compaction-and-maintenance.md` | Maintenance and compaction |
| `docs/internals/components/adaptive-segmentation.md` | Adaptive window behavior |
| `docs/internals/components/python-binding-architecture.md` | CPython binding design |
| `docs/internals/components/tombstone-watermark-model.md` | Tombstone sequencing model |
| `docs/timelog_lld_gil_free_subinterpreters.md` | GIL-free / subinterpreters LLD (Layer A + Layer B) |
| `docs/CI_TESTS.md` | CI test matrix and execution |
| `docs/BENCHMARK_REPORT.md` | Benchmark results and analysis |
| `docs/BENCHMARK_1GB_7PCT_OOO_UNIX.md` | Large-scale benchmark report (1 GB, 7% OOO) |

---

## Engineering Review Status (June 2026)

All critical and high-priority issues have been resolved:

| Category | Issues | Status |
|----------|--------|--------|
| **Critical (C-01 to C-14)** | 14 issues | ✅ All resolved |
| **High (H-01 to H-21)** | 21 issues | ✅ All resolved |

**Key improvements:**
- **Option B OOO Mini-LSM**: O(1) ingestion for out-of-order records
- **Ring buffer sealed queue**: Overflow-safe arithmetic (H-07)
- **Two-phase memview capture**: Epoch-based validation (H-09)
- **Window grid freeze**: Prevents L1 partitioning violation (C-10)
- **Release-mode L1 validation**: Catches corruption early (H-12, H-14)
- **O(T+W) delete debt**: Linear cursor-based algorithm (H-18)
- **Strict publish protocol**: Bounded retries with metrics (H-17)

**GIL-free milestone (merged June 2026, PR #20):**
- **Layer A (interpreter isolation)**: Multi-phase module init, per-module state,
  heap types, no process-global Python objects; `Py_MOD_PER_INTERPRETER_GIL_SUPPORTED`
  on 3.12+
- **Layer B (free-threaded safety)**: `Py_mod_gil = Py_MOD_GIL_NOT_USED` on 3.13+;
  explicit synchronization (atomics, `core_lock`, `live_lock`, per-object critical
  sections) replaces interpreter-lock serialization
- New test surfaces: `test_subinterpreters.py`, `test_free_threading.py`,
  `test_freethreaded_stress.py`; static phase checker `demo/ci/check_layer_a_static.py`

**v1.3 additions (June 2026):**
- **`bulk_append(timestamps, objects)`**: typed-buffer C ingest fast path on the binding
  (native-endian int64 buffer + parallel sequence; single all-or-nothing `tl_append_batch`;
  see `docs/python-api.md` and `docs/benchmarks/bulk_append.md`)
- **Shared-memview wrapper leak fixed** (`core/src/delta/tl_memview.c`): the wrapper struct
  leaked 152 bytes per shared memview since the snapshot cache landed; CI's pure-C sanitizer
  leg now runs LeakSanitizer (`.lsan-suppressions` covers two by-design misuse tests)

Test coverage: ~485 C core tests (497 in Debug/ASan builds, which add debug-only suites) +
~236 Python facade tests collected, verified with ASan/UBSan+LSan. Counts drift as suites
grow — treat `ctest`/`pytest --collect-only` as the source of truth.

---

## Build & Test Commands

### Linux (Primary Development Platform)

```bash
# Configure + build (Debug with ASan/UBSan linked automatically)
cmake -B build -DCMAKE_BUILD_TYPE=Debug -DTIMELOG_BUILD_PYTHON=ON -DTIMELOG_BUILD_PY_TESTS=ON
cmake --build build -j$(nproc)

# Run all C tests (core + binding)
ctest --test-dir build --output-on-failure

# Run a single C test suite by name
ctest --test-dir build -R timelog_tests --output-on-failure   # core only
ctest --test-dir build -R py_handle_tests --output-on-failure # single binding suite

# Run test exe directly for verbose output
./build/test_timelog 2>&1 | tail -30

# Python facade tests (requires staged _timelog.so)
PYTHONPATH=python python3 -m pytest python/tests/ -v

# Run a single Python test file
PYTHONPATH=python python3 -m pytest python/tests/test_facade.py -v

# Dev install via scikit-build-core (alternative to PYTHONPATH)
pip install -e .

# Release build (no sanitizers)
cmake -B build-rel -DCMAKE_BUILD_TYPE=Release
cmake --build build-rel -j$(nproc)

# Sanitizers (explicit, separate build)
cmake -B build-asan -DCMAKE_BUILD_TYPE=Debug   # ASan+UBSan (default in Debug)
cmake -B build-tsan -DCMAKE_C_FLAGS="-fsanitize=thread -g"  # TSan (separate)
```

### Windows

```bash
# Configure (Visual Studio generator)
cmake -B build -G "Visual Studio 17 2022" -A x64

# Build + test (MUST pass -C Debug on Windows)
cmake --build build --config Debug
ctest --test-dir build -C Debug --output-on-failure

# Python — use the py launcher with explicit version
py -V:3.13 -m pytest python/tests/ -v
```

### Pytest Markers

```bash
# Skip slow/special tests
python3 -m pytest python/tests/ -v -m "not stress"
python3 -m pytest python/tests/ -v -m "not subinterpreters and not freethreading"
```

Markers defined: `subinterpreters`, `freethreading`, `stress`.

### Free-Threaded (3.14t) and Subinterpreter Testing

```bash
# Free-threaded leg (requires a 3.14t interpreter, e.g. via pyenv)
PYTHONPATH=python python3.14t -m pytest python/tests/test_free_threading.py -v

# Compatibility-baseline legs (same harness CI uses; legs: subinterpreters, freethreading, stress)
PYTHONPATH=python python3 demo/ci/run_compat_baseline.py --legs subinterpreters,freethreading

# Static phase checks (run in tests-pr.yml / docs-check.yml)
python3 demo/ci/check_layer_a_static.py      # Layer A interpreter-isolation contract
python3 demo/ci/check_docs_consistency.py    # docs/code consistency
```

### Resilience Lab (differential + property suite)

`lab/` is a LOCAL, UNTRACKED oracle-driven concurrency/property harness (~100+ scenarios
across 3.13 / 3.14t / TSan) maintained outside the repository — it exists on the
maintainer's machine, not in git checkouts. When present: `lab/run_lab.py` is the entry
point, `lab/harness.py` + `lab/oracle.py` + `lab/generators.py` the machinery,
`lab/CONCURRENCY_CONTRACT.md` the contract under test, `lab/RESILIENCE_REPORT.md` the
latest results.

### CMake Options

| Option | Default | Purpose |
|--------|---------|---------|
| `TIMELOG_BUILD_PYTHON` | ON | Build CPython extension |
| `TIMELOG_BUILD_PY_TESTS` | ON | Build C-level binding tests |
| `TIMELOG_BUILD_CORE_TESTS` | ON | Build core C test executable |
| `TIMELOG_STRICT_WARNINGS` | ON | `-Werror` / `/WX` |
| `TIMELOG_STAGE_PYTHON_MODULE` | ON | Copy `_timelog.so` into `python/timelog/` |
| `TIMELOG_NATIVE_OPT` | OFF | `-march=native` for benchmarks |

### CI Workflows

The project has extensive CI in `.github/workflows/` (17 workflows). Key workflows:
- `tests-pr.yml` — C core + binding + Python tests on PR (includes Layer A static check)
- `sanitizers.yml` — ASan/UBSan/TSan matrix (includes a 3.14t free-threaded TSan leg)
- `compatibility-baseline-pr.yml` / `compatibility-baseline-main.yml` — subinterpreters/freethreading/stress legs
- `packaging-pr.yml` — Wheel build + install verification (cp312–cp314 + cp314t)
- `correctness-e2e-pr.yml` / `correctness-e2e-main.yml` — Full E2E correctness
- `benchmark-methodology-pr.yml` / `benchmark-methodology-main.yml` — Benchmark methodology runs
- `coverage.yml` — Code coverage via codecov
- `codeql.yml` / `dependency-review.yml` — Security analysis
- `docs-check.yml` — Docs consistency (`demo/ci/check_docs_consistency.py`)
- `release-pypi.yml` / `release-testpypi.yml` — PyPI publishing
- `claude.yml` / `claude-code-review.yml` — Claude Code automation

### When In Doubt

1. Read the relevant design doc (see table below)
2. Check invariants after every operation
3. Run sanitizers
4. Prefer immutability
5. Test boundary conditions
6. Remember: **NO DISK I/O** — everything is in memory
