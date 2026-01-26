# Timelog — Engineering Guide for Claude

This is an **IN-MEMORY** LSM-style time-indexed storage engine in C17 with CPython bindings.
**There is NO disk I/O** — all data lives in memory. This document is your north-star guide.

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
| **Page** | Immutable | `ts[]` + `h[]` arrays | ~4KB memory unit |
| **Segment** | Immutable | Page array + fence pointers | In-memory container |
| **Manifest** | Immutable | L0 + L1 segment catalogs + tombstones | Current state |
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
- Tie-break ordering: `active_run` before `ooo_head` before oldest `ooo_run`
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

### 6. Snapshot Consistency (Seqlock Protocol)

A snapshot sees exactly one consistent state via seqlock:
```
Lock writer_mu → read seq1 → acquire manifest → capture memview → read seq2 → unlock
If seq1 != seq2 OR seq1 is odd: retry
```
`view_seq` is even when idle, odd during publication.
Writers: `view_seq++` before update, `view_seq++` after update.

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
   - Tie-break by `tie_id` (lower wins): run=0, head=1, ooo_runs=2+

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

### GIL (Global Interpreter Lock)

- ALWAYS hold GIL when calling Python C-API functions
- Release GIL during long C operations: `flush`, `compact`, `stop_maintenance`, `close`
- Re-acquire before any Python calls

```c
Py_BEGIN_ALLOW_THREADS
// Long-running C work (NO Python calls!)
Py_END_ALLOW_THREADS
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
- AFTER successful manifest publish (not speculatively)

**When it does NOT fire:**
- During tl_close()
- During flush (flush moves records, doesn't drop them)
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

```bash
# AddressSanitizer + UndefinedBehaviorSanitizer
cmake -B build-asan -DENABLE_SANITIZERS=ON -DCMAKE_BUILD_TYPE=Debug
cmake --build build-asan
ctest --test-dir build-asan --output-on-failure

# ThreadSanitizer (separate build)
cmake -B build-tsan -DCMAKE_C_FLAGS="-fsanitize=thread -g"
cmake --build build-tsan
ctest --test-dir build-tsan --output-on-failure
```

---

## File Layout

```
core/                              # C core engine (all in-memory)
  include/timelog/
    timelog.h                     # PUBLIC API (source of truth)
    tl_export.h                   # Export macros
  src/
    tl_timelog.c                  # Top-level orchestrator
    internal/                     # Utilities
      tl_alloc.c/h                # Allocation wrappers
      tl_sync.c/h                 # Synchronization primitives
      tl_heap.c/h                 # Min-heap for k-way merge
      tl_intervals.c/h            # Tombstone interval set
      tl_recvec.c/h               # Record vector
    storage/                      # Storage structures
      tl_page.c/h                 # Page (ts[] + h[])
      tl_segment.c/h              # Segment (pages + fences)
      tl_manifest.c/h             # Manifest (L0/L1 + tombstones)
      tl_window.c/h               # Window mapping for L1
    delta/                        # Write path
      tl_memtable.c/h             # Mutable ingest buffer (run + OOO head)
      tl_memrun.c/h               # Sealed immutable snapshot
      tl_memview.c/h              # Memview (deep copy + pinned sealed)
      tl_ooorun.c/h               # OOO run and runset (refcounted)
      tl_flush.c/h                # Flush memrun to L0
    query/                        # Read path
      tl_snapshot.c/h             # Snapshot acquisition (seqlock)
      tl_plan.c/h                 # Query planning
      tl_filter.c/h               # Tombstone filtering
      tl_submerge.c/h             # Internal k-way merge for delta
      tl_active_iter.c/h          # Active buffer iterator
      tl_memrun_iter.c/h          # Memrun iterator
      tl_segment_iter.c/h         # Segment iterator
      tl_merge_iter.c/h           # Top-level k-way merge iterator
      tl_pagespan_iter.c/h        # PageSpan streaming
      tl_point.c/h                # Point query support
    maint/                        # Maintenance
      tl_compaction.c/h           # L0 → L1 compaction
      tl_adaptive.c/h             # Adaptive window segmentation
  tests/                          # C unit tests

bindings/cpython/                 # CPython extension (_timelog)
  include/timelogpy/              # Binding headers
  src/
    module.c                      # Module initialization
    py_timelog.c                  # PyTimelog type (engine wrapper)
    py_iter.c                     # TimelogIter (snapshot iterator)
    py_span.c                     # PageSpan (zero-copy buffer)
    py_span_iter.c                # PageSpanIter (streaming)
    py_span_objects.c             # PageSpanObjectsView (lazy objects)
    py_handle.c                   # Handle encode/decode + retired queue
    py_errors.c                   # tl_status_t → Python exception
  tests/                          # C-level binding tests

python/timelog/                   # Pure Python facade
  _api.py                        # Timelog class with slicing syntax
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
2. `view_seq` not incremented twice — readers stuck in retry loop
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
14. Python C-API without GIL — crash
15. Missing INCREF on return — leak or UAF
16. Closing span with exported buffer — must raise `BufferError`
17. DECREF before INCREF on borrowed ref — UAF
18. Rollback INCREF on `TL_EBUSY` — wrong (record IS in log)

---

## Design Documents

| Document | Purpose |
|----------|---------|
| `docs/V1/timelog_one_pager.md` | Vision and goals |
| `docs/V1/timelog_v1_c_software_design_spec.md` | Public API contracts |
| `docs/V1/timelog_v1_lld_storage_pages.md` | Page/segment/manifest |
| `docs/V1/timelog_v1_lld_write_path.md` | Memtable, flush |
| `docs/V1/timelog_v1_lld_read_path.md` | Snapshot, iterators, merge |
| `docs/V1/timelog_v1_lld_compaction_policy.md` | Compaction logic |
| `docs/V1/timelog_v1_lld_background_maintenance.md` | Worker scheduling |
| `docs/timelog_v1_lld_B1_python_handle_lifetime.md` | Pin/unpin, retired queue, GIL |
| `docs/timelog_v1_lld_B2_pytimelog_engine_wrapper.md` | PyTimelog |
| `docs/timelog_v1_lld_B3_pytimelogiter_snapshot_iterator.md` | Iterators |
| `docs/timelog_v1_lld_B4_pagespan_zero_copy.md` | Buffer protocol |
| `docs/timelog_v2_lld_B5_maintenance_threading_integration.md` | Background worker |
| `docs/timelog_v2_lld_B6_error_model_subsystem.md` | Exception handling |
| `docs/timelog_adaptive_segmentation_lld_c17.md` | Adaptive window segmentation |

---

## Engineering Review Status (January 2026)

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

Test coverage: 428 tests passing, verified with ASan/UBSan.

---

## Quick Reference

### Build Commands

```bash
# Windows Debug
cmake -B build -G "Visual Studio 17 2022" -A x64
cmake --build build --config Debug
ctest --test-dir build --output-on-failure

# With sanitizers (GCC/Clang)
cmake -B build-asan -DENABLE_SANITIZERS=ON -DCMAKE_BUILD_TYPE=Debug
cmake --build build-asan

# Python tests
py -V:3.13 -m pytest python/tests/ -v
```

### When In Doubt

1. Read the relevant LLD
2. Check invariants after every operation
3. Run sanitizers
4. Prefer immutability
5. Test boundary conditions
6. Remember: **NO DISK I/O** — everything is in memory

---

## Windows Tooling (CRITICAL - Read This First!)

**STOP! This project runs on Windows.** Tools are NOT in PATH. You MUST use full paths.

### Tool Locations (Verified January 2026)

| Tool | Full Path | Version |
|------|-----------|---------|
| Python | `py -V:3.13` (launcher) | 3.13.9 |
| clang | `/c/Program Files/LLVM/bin/clang.exe` | 21.1.8 |
| clang-tidy | `/c/Program Files/LLVM/bin/clang-tidy.exe` | 21.1.8 |
| cppcheck | `/c/Program Files/Cppcheck/cppcheck.exe` | 2.19.0 |

---

### Python - ALWAYS Use `py -V:3.13`

```bash
# ✅ CORRECT - Windows py launcher with version
py -V:3.13 script.py
py -V:3.13 -m pytest python/tests/ -v
py -V:3.13 -m pip install -e .
py -V:3.13 combine_sources.py

# ❌ WRONG - These DO NOT work on this system
python script.py        # "not found"
python3 script.py       # "not found"
py -3 script.py         # May pick wrong version
py script.py            # May pick wrong version
```

**Why `-V:3.13`?** Multiple Python versions installed. The `-V:` flag is the ONLY reliable way to get the right one.

---

### CMake Builds

```bash
# Configure (once per build dir)
cmake -B build-test -G "Visual Studio 17 2022" -A x64

# Build
cmake --build build-test --config Debug

# Run tests - MUST have "-C Debug" on Windows!
ctest --test-dir build-test -C Debug --output-on-failure

# Run test exe directly (see detailed output)
U:/Projects/timelog/build-test/Debug/test_timelog.exe 2>&1 | tail -20
```

**Critical:** Without `-C Debug`, ctest on Windows finds no tests!

---

### cppcheck - Full Path Required

```bash
# ✅ WORKING COMMAND (tested)
"/c/Program Files/Cppcheck/cppcheck.exe" \
    --enable=warning,style \
    --std=c17 \
    --suppress=missingIncludeSystem \
    -I U:/Projects/timelog/core/include \
    -I U:/Projects/timelog/core/src \
    U:/Projects/timelog/core/src/maint/tl_compaction.c 2>&1

# Scan entire core/src directory
"/c/Program Files/Cppcheck/cppcheck.exe" \
    --enable=warning,style \
    --std=c17 \
    --suppress=missingIncludeSystem \
    -I U:/Projects/timelog/core/include \
    -I U:/Projects/timelog/core/src \
    U:/Projects/timelog/core/src/ 2>&1 | head -100
```

**Note:** Use `-I` with FULL paths. Relative paths often fail in bash on Windows.

---

### clang-tidy - Full Path + Specific Flags

```bash
# ✅ WORKING COMMAND (tested) - bugprone + analyzer checks
"/c/Program Files/LLVM/bin/clang-tidy.exe" \
    U:/Projects/timelog/core/src/maint/tl_compaction.c \
    --checks='-*,bugprone-*,clang-analyzer-*' \
    -- -std=c17 \
    -I U:/Projects/timelog/core/include \
    -I U:/Projects/timelog/core/src \
    -D_CRT_SECURE_NO_WARNINGS 2>&1 | head -50

# Useful check sets:
#   bugprone-*           - Common bugs (NULL deref, use-after-move, etc.)
#   clang-analyzer-*     - Deep static analysis
#   performance-*        - Performance issues
#   readability-*        - Code style (noisy, skip usually)
#   modernize-*          - C++ only, skip for C

# ❌ AVOID these noisy checks:
#   -clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling  # memset/memcpy spam
#   -bugprone-easily-swappable-parameters  # Too noisy for allocator callbacks
```

**Critical flags:**
- `-D_CRT_SECURE_NO_WARNINGS` - Silences MSVC secure function warnings
- `-- -std=c17` - The `--` separates clang-tidy flags from compiler flags

---

### clang Static Analyzer

```bash
# Direct analysis on single file
"/c/Program Files/LLVM/bin/clang.exe" \
    --analyze \
    -Xanalyzer -analyzer-output=text \
    -std=c17 \
    -I U:/Projects/timelog/core/include \
    -I U:/Projects/timelog/core/src \
    -D_CRT_SECURE_NO_WARNINGS \
    U:/Projects/timelog/core/src/maint/tl_compaction.c 2>&1

# scan-build (wraps full build) - less reliable on Windows
"/c/Program Files/LLVM/bin/scan-build.bat" \
    cmake --build build-test --config Debug
```

---

### Common Pitfalls (Save Yourself Time!)

| Problem | Wrong | Right |
|---------|-------|-------|
| Python not found | `python script.py` | `py -V:3.13 script.py` |
| clang not found | `clang-tidy file.c` | `"/c/Program Files/LLVM/bin/clang-tidy.exe" file.c` |
| cppcheck not found | `cppcheck file.c` | `"/c/Program Files/Cppcheck/cppcheck.exe" file.c` |
| Relative includes fail | `-I core/include` | `-I U:/Projects/timelog/core/include` |
| ctest finds no tests | `ctest --test-dir build` | `ctest --test-dir build -C Debug` |
| Path with spaces | `cd C:\Program Files\...` | `cd "/c/Program Files/..."` |
| Backslashes in bash | `U:\Projects\timelog` | `U:/Projects/timelog` |

---

### Copy-Paste Quick Reference

```bash
# Build and test (the daily workflow)
cmake --build U:/Projects/timelog/build-test --config Debug && \
ctest --test-dir U:/Projects/timelog/build-test -C Debug --output-on-failure

# Quick test count
U:/Projects/timelog/build-test/Debug/test_timelog.exe 2>&1 | grep "Test Results"

# Run Python tests
py -V:3.13 -m pytest U:/Projects/timelog/python/tests/ -v

# cppcheck quick scan
"/c/Program Files/Cppcheck/cppcheck.exe" --enable=warning --std=c17 \
    --suppress=missingIncludeSystem \
    -I U:/Projects/timelog/core/include \
    -I U:/Projects/timelog/core/src \
    U:/Projects/timelog/core/src/maint/tl_compaction.c 2>&1

# clang-tidy quick scan
"/c/Program Files/LLVM/bin/clang-tidy.exe" \
    U:/Projects/timelog/core/src/maint/tl_compaction.c \
    --checks='-*,bugprone-*,clang-analyzer-*' \
    -- -std=c17 -I U:/Projects/timelog/core/include \
    -I U:/Projects/timelog/core/src -D_CRT_SECURE_NO_WARNINGS 2>&1 | head -50
```