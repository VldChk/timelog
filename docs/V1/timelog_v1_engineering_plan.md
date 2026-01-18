# Timelog V1 - Engineering Execution Plan (Refined)

This document defines the engineering execution path for Timelog V1 as a greenfield
implementation. It is derived from and consistent with:
- timelog_v1_c_hld.md (architectural north star)
- timelog_v1_c_software_design_spec.md (API contracts and protocols)
- timelog_v1_lld_storage_pages.md (pages, segments, manifest, tombstones)
- timelog_v1_lld_write_path.md (memtable, flush, publication)
- timelog_v1_lld_read_path.md (snapshot, iterators, merge, filtering)
- timelog_v1_lld_compaction_policy.md (selection, merge, L1 output)
- timelog_v1_lld_background_maintenance.md (scheduling, concurrency)
- timelog.h (public contract, canonical source for API surface)

Each phase builds on the previous. Dependencies are explicit. Deliverables are
testable artifacts. Concurrency and publication invariants are established early
rather than retrofitted.

---

## Terminology (L0/L1 Model)

Throughout this plan:
- **L0** = delta layer (memtable flush outputs, may overlap in time)
- **L1** = main layer (compaction outputs, non-overlapping by time window)
- **Memrun** = sealed, immutable memtable snapshot queued for flush
- **Memview** = immutable snapshot view of active + sealed memruns
- **Window** = fixed time partition [window_start, window_end) for L1 non-overlap
- **Tombstones** = coalesced half-open intervals [t1, t2) representing deletes

---

## Phase 0: Contract Coherence and Project Skeleton

**Goal:** Establish canonical API, module boundaries, build system, and compile-clean
scaffolding. Ensure spec and header are identical before implementation begins.

### 0.1 Contract Coherence Gate

Before writing implementation code, verify spec and header alignment:

- Treat `timelog.h` as the canonical public API source.
- Ensure `timelog_v1_c_software_design_spec.md` code blocks exactly match:
  - `tl_status_t` enum values (TL_OK=0, TL_EOF=1, TL_EINVAL=10, etc.)
  - `tl_allocator_t` field order (malloc_fn, calloc_fn, realloc_fn, free_fn)
  - `tl_config_t` field order and names
  - All public function signatures
- Standardize terminology across all docs and comments (L0/L1, memtable/memrun/memview)

Deliverable: spec code blocks match header byte-for-byte; terminology is consistent.

### 0.2 Build System

- CMakeLists.txt with library target and test target
- Compiler flags for C11, warnings, debug/release configs
- Test harness with assertion macros

### 0.3 Public Header

File: `include/timelog/timelog.h`

Deliverables (verified against canonical header):
- All opaque type forward declarations (tl_timelog_t, tl_snapshot_t, tl_iter_t)
- Fundamental types (tl_ts_t, tl_handle_t, tl_record_t)
- Status codes enum with tl_strerror()
- Configuration struct (tl_config_t) with all parameters:
  - time_unit, target_page_bytes, memtable_max_bytes, ooo_budget_bytes
  - sealed_max_runs, sealed_wait_ms, max_delta_segments
  - window_size, window_origin
  - delete_debt_threshold, compaction_target_bytes
  - max_compaction_inputs, max_compaction_windows
  - maintenance_mode
  - allocator (tl_allocator_t with ctx, malloc_fn, calloc_fn, realloc_fn, free_fn)
  - log_fn, **log_ctx**
  - on_drop_handle, **on_drop_ctx**
- All public API signatures (lifecycle, write, snapshot, read, maintenance, diagnostics)

Reference: Spec Section 5-6, timelog.h

### 0.4 Internal Definitions

File: `src/internal/tl_defs.h`

Deliverables:
- TL_TS_MIN, TL_TS_MAX constants
- Internal struct forward declarations
- Common includes and platform detection

### 0.5 Core Utilities

Files: `src/internal/tl_alloc.[ch]`, `src/internal/tl_log.[ch]`

Deliverables:
- Allocator shim (tl__malloc, tl__calloc, tl__realloc, tl__free)
- Default allocator using libc
- Log shim with level filtering
- tl_strerror() implementation

### 0.6 Minimal Lifecycle

File: `src/tl_timelog.c`

Deliverables:
- tl_config_init_defaults() with documented defaults
- tl_open() creating empty instance
- tl_close() with NULL safety
- is_open state tracking

**Phase 0 Exit Criteria:**
- Spec and header are verified identical
- Library compiles cleanly
- tl_open()/tl_close() work
- Test harness runs

---

## Phase 1: Concurrency and Publication Primitives

**Goal:** Establish the locking and atomic discipline required by all paths before
building data structures that depend on them. This is a prerequisite for correctness,
not an implementation detail.

### 1.1 Synchronization Primitives

Files: `src/internal/tl_atomic.[ch]`, `src/internal/tl_thread.[ch]`

Deliverables:
- Atomic operations: load, store, fetch_add, compare_exchange
- Mutex abstraction (tl_mutex_t)
- Condition variable abstraction (tl_cond_t)
- Thread abstraction (tl_thread_t) for background maintenance

Reference: Background Maintenance LLD Section 2

### 1.2 Required Locks

Deliverables:
- **writer_mu**: serializes manifest publication and snapshot capture
- **flush_mu**: serializes flush build + publish (single flusher at a time)
- **maint_mu**: protects maintenance state flags and thread lifecycle
- **memtable.mu**: protects sealed memrun queue
- **view_seq**: seqlock counter for snapshot consistency (atomic uint64_t)

### 1.3 Lock Ordering Definition

Enforce strict ordering to prevent deadlocks:

```
maint_mu -> flush_mu -> writer_mu -> memtable.mu
```

Rules (enforced by code structure):
- Long-running build phases must not hold writer_mu
- writer_mu is held only during publication (short critical section)
- memtable.mu is used only to access the sealed queue or to mark memruns
- Writers must not take maint_mu while holding writer_mu; use deferred signaling

Reference: Background Maintenance LLD Section 2.2

### 1.4 Publication Protocol Scaffolding

Define the atomic publish pattern used by both flush and compaction:

```c
// Publication template (used by flush and compaction)
void publish_manifest(tl_timelog_t* tl, tl_manifest_t* new_manifest) {
    lock(writer_mu);
    atomic_fetch_add(&view_seq, 1);  // -> odd (publish in progress)
    // swap manifest pointer
    // optional: update memtable state (for flush)
    atomic_fetch_add(&view_seq, 1);  // -> even (publish complete)
    unlock(writer_mu);
}
```

Snapshots retry if they see odd or mismatched view_seq.

Reference: Background Maintenance LLD Section 2.3, Write-Path LLD Section 5

### 1.5 Unit Tests for Concurrency Primitives

Tests:
- Lock ordering violations detected in debug mode
- view_seq increment/read correctness
- Basic mutex/cond functionality

**Phase 1 Exit Criteria:**
- All locks/atomics implemented and testable
- Lock ordering documented and enforced
- Publication protocol helper implemented

---

## Phase 2: Shared Data Structures

**Goal:** Implement primitives used by both write and read paths.

### 2.1 Record Vector

File: `src/internal/tl_recvec.[ch]`

Deliverables:
- Dynamic array of tl_record_t with amortized O(1) append
- Reserve, push, clear, destroy operations
- Binary search helpers (lower_bound, upper_bound)

Tests:
- Growth semantics
- Binary search correctness at boundaries

### 2.2 Interval Set (Tombstones)

File: `src/internal/tl_intervals.[ch]`

Deliverables:
- Mutable interval set with insert and coalescing
- Immutable interval array for storage
- Invariants: sorted, non-overlapping, non-adjacent, half-open [t1, t2)
- Support for unbounded end (end_unbounded flag)
- Binary search for point containment check
- Union operation for merging tombstone sets
- Clipping operation for range restriction

Tests:
- Coalescing of overlapping intervals
- Coalescing of adjacent intervals
- Point containment queries
- Empty interval rejection (t1 >= t2)
- Union correctness

Reference: Storage LLD Section 2.5, Section 7

### 2.3 Min-Heap for K-way Merge

File: `src/internal/tl_heap.[ch]`

Deliverables:
- Generic min-heap over (ts, component_id) keys
- Push, pop, peek operations
- Heapify for initial construction

Reference: Read Path LLD Section 6

**Phase 2 Exit Criteria:**
- All primitives have unit tests
- Interval coalescing invariants verified

---

## Phase 3: Immutable Storage Layer

**Goal:** Build the immutable representation that flush produces and queries consume.

### 3.1 Page Structure

File: `src/storage/tl_page.[ch]`

Deliverables:
- tl_page_t with SoA layout (ts[], h[])
- Page metadata: min_ts, max_ts, count, flags
- Page delete flags enum (FULLY_LIVE, FULLY_DELETED, PARTIAL_DELETED)
- Row delete metadata pointer (reserved for V2, always NULL in V1)
- Page builder: accepts sorted records, computes metadata
- Within-page binary search for range boundaries

Invariants:
- ts[] is non-decreasing
- min_ts == ts[0], max_ts == ts[count-1]

Reference: Storage LLD Section 3.3, Section 4

### 3.2 Page Catalog (Fence Pointers)

File: `src/storage/tl_page.[ch]` (continued)

Deliverables:
- tl_page_meta_t per-page summary
- tl_page_catalog_t array sorted by min_ts
- Binary search over catalog for page selection

Reference: Storage LLD Section 3.4

### 3.3 Segment Structure

File: `src/storage/tl_segment.[ch]`

Deliverables:
- tl_segment_t with level (L0/L1), generation, bounds
- Page catalog ownership
- Tombstone attachment (allowed in L0, forbidden in L1)
- Window bounds (window_start, window_end) for L1 segments
- Reference counting (_Atomic uint32_t refcnt)
- Segment builder from sorted record stream

L0 Segment Rules:
- level = TL_SEG_L0
- window_start = window_end = 0
- tombstones allowed

L1 Segment Rules:
- level = TL_SEG_L1
- window_start/window_end set to partition boundaries
- tombstones must be NULL
- All records satisfy: window_start <= ts < window_end

Reference: Storage LLD Section 3.6, Section 5

### 3.4 Tombstone-Only Segments

File: `src/storage/tl_segment.[ch]` (continued)

Deliverables:
- Support for L0 segments with page_count = 0, record_count = 0
- min_ts/max_ts derived from tombstone intervals
- Used for residual tombstones when compaction is capped

Reference: Storage LLD Section 5.3, Compaction Policy LLD Section 7.2

### 3.5 Manifest Structure

File: `src/storage/tl_manifest.[ch]`

Deliverables:
- tl_manifest_t with L0 list (flush order) and L1 list (sorted by window_start)
- Cached global bounds (optional optimization)
- Monotonic version counter (for debugging/metrics, not CAS)
- Reference counting for snapshot pinning
- Copy-on-write manifest builder
- Acquire/release operations

Invariants:
- L1 segments sorted by window_start
- L1 segments non-overlapping by window
- L0 segments may overlap anything

Reference: Storage LLD Section 3.7, Section 8

### 3.6 Window Mapping Utilities

File: `src/storage/tl_window.[ch]`

Deliverables:
- window_id_for_ts(ts, window_size, window_origin)
- window_bounds(window_id, window_size, window_origin) -> (start, end)
- Default window_size calculation based on time_unit (1 hour equivalent)

Reference: Storage LLD Section 6.1, Compaction Policy LLD Section 4

**Phase 3 Exit Criteria:**
- Page builder creates correct pages from sorted streams
- Segment builder creates correct segments
- Manifest copy-on-write produces valid new manifests
- Window mapping is correct

---

## Phase 4: Memtable and Write Path

**Goal:** Implement ingestion, sealing, flush, and publication.

### 4.1 Memtable Structure

File: `src/delta/tl_memtable.[ch]`

Deliverables:
- tl_memtable_t with:
  - active_run (append-only, non-decreasing by ts)
  - active_ooo (sorted vector for out-of-order records)
  - active_tombs (coalesced interval set)
  - sealed queue (FIFO of tl_memrun_t*)
  - last_inorder_ts tracking
  - active_bytes_est for threshold checks
  - epoch counter for snapshot caching
  - memtable.mu protecting sealed queue

Configuration inputs:
- memtable_max_bytes (active budget)
- ooo_budget_bytes (OOO buffer limit, default memtable_max_bytes / 10)
- sealed_max_runs (backpressure threshold)

Reference: Write Path LLD Section 3

### 4.2 Memtable Insert Algorithm

File: `src/delta/tl_memtable.[ch]` (continued)

Single record insert:
```
if active_run empty OR ts >= last_inorder_ts:
    append to active_run
    last_inorder_ts = ts
else:
    binary search active_ooo for insertion point
    memmove to create gap
    insert record
    increment ooo_len
```

If active_ooo exceeds ooo_budget_bytes, seal early.

Batch insert:
- If hint says mostly ordered and batch[0].ts >= last_inorder_ts:
  - Quick monotonicity check
  - If sorted, append entire batch to active_run
- Otherwise, per-record insert

Tombstone insert:
- Validate t1 < t2 (else TL_EINVAL)
- Insert into active_tombs with coalescing

Reference: Write Path LLD Section 3.6, Section 3.7, Section 3.8

### 4.3 Memrun Structure

File: `src/delta/tl_memtable.[ch]` (continued)

Deliverables:
- tl_memrun_t with:
  - run[] (sorted records from active_run)
  - ooo[] (sorted records from active_ooo)
  - tombs[] (coalesced intervals)
  - min_ts, max_ts computed from run + ooo
  - refcnt for pin/unpin

Reference: Write Path LLD Section 3.5

### 4.4 Sealing

File: `src/delta/tl_memtable.[ch]` (continued)

Seal triggers:
- active_bytes_est >= memtable_max_bytes
- active_ooo bytes >= ooo_budget_bytes
- Explicit tl_flush() call

Seal steps:
1. Move active_run, active_ooo, active_tombs ownership to new memrun
2. Compute memrun min_ts/max_ts
3. Reset active buffers to empty
4. Push memrun to sealed queue (under memtable.mu)

Reference: Write Path LLD Section 4.1

### 4.5 Flush Builder

File: `src/delta/tl_flush.[ch]`

Deliverables:
- Two-way merge of memrun.run + memrun.ooo into sorted stream
- Page building from merged stream
- Segment creation with tombstone attachment
- Tombstone-only segment creation if no records

Reference: Write Path LLD Section 4.3

### 4.6 Flush Publication Protocol

File: `src/tl_timelog.c`

Flush publication is a two-phase process:

1. Build phase (off-lock relative to writer_mu):
   - Acquire flush_mu (single flusher)
   - Peek + pin oldest sealed memrun (under memtable.mu)
   - Build L0 segment from memrun (off-lock)

2. Publish phase (short critical section):
   - Lock writer_mu
   - view_seq = atomic_fetch_add(+1) -> odd
   - Build new manifest with L0 segment appended
   - Swap manifest pointer
   - Remove memrun from sealed queue (under memtable.mu)
   - view_seq = atomic_fetch_add(+1) -> even
   - Unlock writer_mu
   - Unpin memrun
   - Unlock flush_mu

Critical invariant: No snapshot sees both memrun and its flushed segment.

Reference: Write Path LLD Section 5, Background Maintenance LLD Section 2

### 4.7 Backpressure

File: `src/tl_timelog.c` (continued)

Deliverables:
- Check sealed queue length against sealed_max_runs
- Manual mode: return TL_EBUSY if full
- Background mode: bounded wait (sealed_wait_ms), then TL_EBUSY

Reference: Write Path LLD Section 6.1

### 4.8 Write API Wiring

File: `src/tl_timelog.c` (continued)

Deliverables:
- tl_append(): insert + conditional seal + deferred signal
- tl_append_batch(): batch insert with hint processing
- tl_delete_range(): tombstone insert
- tl_delete_before(): tombstone [TL_TS_MIN, cutoff)
- tl_flush(): synchronous seal + flush all sealed memruns
- **tl_compact(): set compact_pending flag + signal maintenance**

Signal rule: maint_signal_flush() and maint_signal_compact() called outside
writer_mu to preserve lock ordering.

tl_compact() semantics:
- In manual mode: sets compact_pending, returns TL_OK (work done by tl_maint_step)
- In background mode: sets compact_pending, signals worker, returns TL_OK

Reference: Write Path LLD Section 7, Spec Section 6.4

**Phase 4 Exit Criteria:**
- Append creates records in memtable
- Seal creates immutable memruns
- Flush creates L0 segments visible in manifest
- Publication protocol prevents dirty reads
- Backpressure returns TL_EBUSY appropriately
- tl_compact() signals compaction request

---

## Phase 5: Snapshot and Read Path

**Goal:** Implement snapshot-consistent range queries with tombstone filtering.

### 5.1 Memview Structure

File: `src/delta/tl_memview.[ch]`

Deliverables:
- tl_memview_t capturing:
  - Immutable copy of active_run (or cached immutable snapshot if epoch unchanged)
  - Immutable copy of active_ooo
  - Immutable copy of active_tombs
  - Array of sealed memrun pointers (pinned)
  - min_ts/max_ts bounds

The memview is immutable for the lifetime of a snapshot.
It must not reference mutable active buffers after writer_mu is released.

### 5.2 Snapshot Acquisition Protocol

File: `src/query/tl_snapshot.[ch]`

Acquisition steps (holding writer_mu):
1. lock(writer_mu)
2. seq1 = atomic_load(view_seq) - must be even
3. Acquire manifest reference (refcnt++)
4. Capture memview
5. seq2 = atomic_load(view_seq)
6. unlock(writer_mu)
7. If seq1 != seq2 OR seq1 is odd: release and retry

Deliverables:
- tl_snapshot_acquire(): returns pinned snapshot
- tl_snapshot_release(): releases manifest and memview pins
- Snapshot contains: manifest ref, memview, cached bounds, allocator ref

Reference: Read Path LLD Section 1

### 5.3 Query Planning

File: `src/query/tl_plan.[ch]`

Given [t1, t2):

L1 pruning (sorted, non-overlapping):
- Binary search first L1 with max_ts >= t1
- Scan forward until min_ts >= t2

L0 pruning (small, overlapping):
- Linear scan: include if seg.max_ts >= t1 AND seg.min_ts < t2

Memview pruning:
- Include active if bounds overlap [t1, t2)
- Include sealed memruns whose bounds overlap

Effective tombstones:
- Union of L0 tombstones + L1 tombstones (if present) + memview tombstones
- L1 tombstones should be empty in V1, but include defensively for correctness
- Clip to [t1, t2)

Deliverables:
- tl_qplan_t containing selected components and tombstone set
- tl_qplan_build() function

Reference: Read Path LLD Section 4

### 5.4 Component Iterators

File: `src/query/tl_segment_iter.[ch]`, `src/query/tl_memrun_iter.[ch]`

Segment iterator:
1. Prune by segment min/max
2. Locate candidate pages via catalog binary search
3. For each page:
   - Skip FULLY_DELETED
   - row_start = lower_bound(ts[], t1)
   - row_end = lower_bound(ts[], t2)
   - Iterate rows
4. Output: sorted stream from segment

Memrun iterator:
- Two-way merge of run[] and ooo[] (both sorted)
- Seek uses binary search in both arrays

Active memview iterator:
- Same two-way merge of active_run and active_ooo

Memview iterator:
- K-way merge over active iterator + sealed memrun iterators

Reference: Read Path LLD Section 5

### 5.5 Merge Iterator

File: `src/query/tl_merge.[ch]`

Deliverables:
- Min-heap over component iterators
- Key = (ts, component_id)
- Initialize heap with head record from each iterator
- Pop min, advance that iterator, push new head
- Complexity: O(log K) per record

Reference: Read Path LLD Section 6

### 5.6 Tombstone Filtering

File: `src/query/tl_filter.[ch]`

Cursor-based filtering:
- Maintain cursor over sorted tombstone intervals
- Advance cursor while ts >= cur.end
- Record deleted if cur.start <= ts < cur.end

Skip-ahead optimization (optional):
- If record falls inside [d1, d2), call iterator.seek(d2)

Deliverables:
- tl_filtered_iter_t wrapping merge iterator + tombstone cursor
- Amortized O(1) per record filtering

Reference: Read Path LLD Section 7

### 5.7 Point Lookup Fast Path

File: `src/query/tl_point.[ch]`

Contract:
- Return all visible records with timestamp == ts
- Duplicates preserved, tie order unspecified
- If any tombstone covers ts, return empty

Algorithm:
1. Snapshot acquisition
2. Tombstone check: binary search all tombstone sets for ts containment
   - If any contains ts, return empty iterator
3. For L1: binary search window containing ts, then page catalog, then ts[]
4. For L0: scan overlapping segments with same binary search
5. For memview: binary search active_run, active_ooo, sealed memruns
6. Concatenate results (no k-way merge needed for single timestamp)

Reference: Read Path LLD Section 9

### 5.8 Read API Wiring

File: `src/tl_timelog.c`

Deliverables:
- tl_iter_range(snap, t1, t2): standard range [t1, t2)
- tl_iter_since(snap, t1): [t1, +inf)
- tl_iter_until(snap, t2): [TL_TS_MIN, t2)
- tl_iter_equal(snap, ts): [ts, ts+1) with overflow guard
- tl_iter_point(snap, ts): point lookup fast path
- tl_iter_next(it, out): advance iterator
- tl_iter_destroy(it): cleanup
- tl_scan_range(): visitor pattern wrapper

Edge cases:
- ts == TL_TS_MAX for iter_equal: use unbounded range
- Empty snapshots: iterator creation returns TL_OK; first tl_iter_next returns TL_EOF

Reference: Read Path LLD Section 2, Section 8

### 5.9 Timestamp Navigation

File: `src/tl_timelog.c` (continued)

Deliverables:
- tl_min_ts(): first visible timestamp (tombstone-aware)
- tl_max_ts(): last visible timestamp (tombstone-aware)
- tl_next_ts(ts): first timestamp > ts
- tl_prev_ts(ts): last timestamp < ts

Implementation notes:
- Without tombstones, use cached bounds
- With tombstones, iterate to find actual visible bounds

Reference: Spec Section 6.7

**Phase 5 Exit Criteria:**
- Snapshot acquisition is race-free
- Range queries return correct, sorted results
- Tombstone filtering is correct
- Point lookup avoids full merge
- All read APIs work end-to-end

---

## Phase 6: Diagnostics and Validation

**Goal:** Build observability and invariant checking early.

### 6.1 Statistics

File: `src/tl_timelog.c`

Deliverables:
- tl_stats(snap, out) populating:
  - segments_l0, segments_l1
  - pages_total
  - records_estimate
  - min_ts, max_ts (from manifest bounds)
  - tombstone_count

### 6.2 Validation

File: `src/tl_timelog.c` (continued)

Invariants to check:
- Page ts[] is non-decreasing
- Page min_ts/max_ts match ts[0]/ts[count-1]
- Page flags consistent with row_del pointer
- Segment catalog sorted by min_ts
- Segment min_ts/max_ts match page bounds
- L1 segments: window_start <= all ts < window_end
- L1 segments: non-overlapping by window
- L0 segments: tombstones valid if present
- Tombstones: sorted, non-overlapping, non-adjacent
- Snapshot bounds: min_ts <= max_ts

Deliverables:
- tl_validate(snap) returning TL_OK or TL_EINTERNAL

Reference: Storage LLD Section 10, Spec Section 9

**Phase 6 Exit Criteria:**
- Stats accurately reflect snapshot state
- Validation catches invariant violations

---

## Phase 7: Maintenance Control Plane

**Goal:** Implement maintenance modes (manual/background) with correct API semantics.

### 7.1 Maintenance State

File: `src/maint/tl_scheduler.[ch]`

Deliverables:
- tl_maint_state_t with:
  - maint_mu, cond
- state machine (STOPPED/RUNNING/STOPPING), shutdown flag
  - flush_pending, compact_pending flags

Reference: Background Maintenance LLD Section 4

### 7.2 Maintenance API Semantics

File: `src/tl_timelog.c`

**Critical lifecycle contract:**
- `tl_open()` does NOT start background maintenance threads, even in TL_MAINT_BACKGROUND mode
- Callers MUST invoke `tl_maint_start()` after `tl_open()` to start the worker in background mode
- This separation allows callers to perform setup between open and maintenance start

**tl_maint_start():**
- Valid only in TL_MAINT_BACKGROUND mode; return TL_ESTATE otherwise
- Idempotent if already running (return TL_OK)
- Returns TL_EBUSY if a stop is in progress (STOPPING); retry later
- Spawns worker thread, sets state = RUNNING

**tl_maint_stop():**
- Sets shutdown = true, signals cond, joins worker thread
- Idempotent if already stopped or stopping (return TL_OK)
- TL_OK does not guarantee the worker has exited if another stop is in progress

**tl_maint_step():**
- Valid only in TL_MAINT_DISABLED mode; return TL_ESTATE otherwise
- Attempts one unit of work
- Priority: flush one sealed memrun; else compact one step if needed
- Returns TL_OK if work performed, TL_EOF if nothing to do

Reference: Background Maintenance LLD Section 3, Section 11

### 7.3 Manual Mode Implementation

File: `src/tl_timelog.c` (continued)

Deliverables:
- tl_maint_step() performs one unit of work:
  - If flush_pending and sealed queue non-empty: flush one memrun
  - Else if compact_pending and compaction_needed(): compact one step
  - Else: return TL_EOF

Reference: Background Maintenance LLD Section 3.2

### 7.4 Background Mode Worker Loop

File: `src/maint/tl_scheduler.[ch]` (continued)

Worker thread loop:
```
while not shutdown:
    lock(maint_mu)
    wait until flush_pending OR compact_pending OR shutdown
    if shutdown: break
    copy pending flags, clear them
    unlock(maint_mu)

    if do_flush:
        while flush_one_and_publish() == TL_OK:
            if compaction_needed():
                compact_one_step()
                break  // fairness: one compaction per flush batch

    if do_compact AND compaction_needed():
        compact_one_step()
```

Deliverables:
- Worker thread spawn/join
- Deferred signaling: set flag under writer_mu (or after unlock), signal under maint_mu

Reference: Background Maintenance LLD Section 6, Section 7

### 7.5 Backpressure Rules

File: `src/maint/tl_scheduler.[ch]` (continued)

If sealed queue length reaches sealed_max_runs:
- In manual mode: writer returns TL_EBUSY
- In background mode: bounded wait (sealed_wait_ms), then TL_EBUSY

Bounded wait must not hold writer_mu.

Reference: Background Maintenance LLD Section 9

**Phase 7 Exit Criteria:**
- Manual mode tl_maint_step() works
- Background mode worker thread runs flush + signals compaction
- API mode validation enforced (TL_ESTATE for wrong mode)
- Idempotency of start/stop verified
- Backpressure behavior correct

---

## Phase 8: Compaction Implementation

**Goal:** Implement L0 -> L1 compaction with windowed non-overlap and correct publication.
Compaction is **required** for V1 to bound read amplification via max_delta_segments.

### 8.1 Compaction Triggers

File: `src/maint/tl_compaction.[ch]`

Compaction is requested when any of:
- L0 count >= max_delta_segments
- Explicit tl_compact() call
- Delete debt exceeds delete_debt_threshold (optional)

Delete debt metric (window-scoped):
- tombstone_covered_span = union length of tombstones in window
- delete_debt_ratio = tombstone_covered_span / window_size
- If ratio >= threshold, request compaction for that window

Reference: Compaction Policy LLD Section 5

### 8.2 Compaction Selection Policy

File: `src/maint/tl_compaction.[ch]` (continued)

**Baseline policy (simple, correct):**
1. Select all L0 segments as inputs
2. Compute global [min_ts, max_ts) across L0 records AND tombstones
3. Determine covered window_ids
4. Select all L1 segments whose windows intersect

**Bounded policy (heuristic):**
- Cap L0 inputs to max_compaction_inputs
- Cap windows to max_compaction_windows
- Defer remaining to future compactions

Reference: Compaction Policy LLD Section 6

### 8.3 Compaction Merge Algorithm

File: `src/maint/tl_compaction.[ch]` (continued)

Inputs:
- L0 segments (may have tombstones)
- L1 segments (tombstones should be empty)

Steps:
1. Build effective tombstone set (union of all tombstones from L0 and L1 if present)
2. Clip tombstones to compaction output range
3. Create iterators for all input segments
4. K-way merge by timestamp
5. Skip records covered by effective tombstones
6. Partition output by window boundaries
7. For each window with live records:
   - Build pages
   - Build L1 segment (tombstones = NULL)
8. If window has no live records, emit no segment

**Residual tombstones:**
- If tombstone extends beyond selected output windows (due to caps), emit
  tombstone-only L0 segment carrying residual intervals

Reference: Compaction Policy LLD Section 7

### 8.4 Compaction Publication Protocol

File: `src/maint/tl_compaction.[ch]` (continued)

Publication steps:
1. Build outputs off-lock
2. lock(writer_mu)
3. view_seq = atomic_fetch_add(+1) -> odd
4. Verify manifest unchanged (if changed, retry)
5. Build new manifest:
   - Remove selected L0 segments
   - Remove selected L1 windows
   - Insert new L1 segments (sorted by window_start)
   - Append residual tombstone-only L0 segments (if any)
6. Swap manifest pointer
7. view_seq = atomic_fetch_add(+1) -> even
8. unlock(writer_mu)

**Retry policy:**
- Retry up to 3 times if manifest changes during publish
- If still changing, return TL_EBUSY and retry later

Reference: Compaction Policy LLD Section 8

### 8.5 Handle Drop Callback

File: `src/maint/tl_compaction.[ch]` (continued)

When records are physically deleted during compaction:
- If on_drop_handle callback is configured, invoke it with (ctx, ts, handle)
- Callback runs on maintenance thread; must be fast and thread-safe

Reference: Spec Section 5.2

**Phase 8 Exit Criteria:**
- L0 count is bounded by compaction
- L1 remains non-overlapping after compaction
- Tombstones are folded into output
- Residual tombstones are preserved in L0
- Handle drop callback is invoked

---

## Phase 9: Failure Handling and Retry Policies

**Goal:** Ensure the system recovers gracefully from allocation failures and
concurrent manifest changes.

### 9.1 ENOMEM Handling

File: `src/maint/tl_scheduler.[ch]`, `src/maint/tl_compaction.[ch]`

**Flush build failure (ENOMEM):**
- Memrun remains sealed and visible to snapshots
- Drop pin on memrun
- Set flush_pending = true
- Retry on next maintenance cycle

**Compaction build failure (ENOMEM):**
- Leave input segments intact
- Set compact_pending = true
- Retry on next maintenance cycle

Reference: Background Maintenance LLD Section 12

### 9.2 Manifest Change Detection

File: `src/maint/tl_compaction.[ch]` (continued)

If manifest pointer changes during compaction build phase:
- Abort compaction (discard built outputs)
- Return TL_EBUSY
- Retry on next compaction request

### 9.3 Allocator Fault Injection Tests

Deliverables:
- Test harness with allocator shim that can force ENOMEM
- Tests validating:
  - Inputs remain visible after ENOMEM
  - Work is retried on next tl_maint_step / worker wakeup
  - No leaks or double-frees

Reference: Background Maintenance LLD Section 12

**Phase 9 Exit Criteria:**
- ENOMEM during flush/compaction is recoverable
- Manifest change during compaction is handled
- Fault injection tests pass

---

## Phase 10: Integration Testing and Hardening

**Goal:** Validate end-to-end correctness and concurrency safety.

### 10.1 Functional Tests

- Write + read round-trip
- Tombstone suppression
- Out-of-order ingestion ordering
- Batch append with hints
- Point lookup correctness
- TL_TS_MIN/TL_TS_MAX edge cases
- Empty snapshot handling
- tl_compact() trigger behavior

### 10.2 API Semantics Tests

- tl_maint_start/stop idempotency
- Mode validation (TL_ESTATE for wrong mode)
- Backpressure returns TL_EBUSY
- Snapshot lifetime misuse (debug asserts)

### 10.3 Concurrency Tests

- Snapshot stability during flush
- Snapshot stability during compaction
- Concurrent readers during maintenance
- Writer backpressure behavior
- Race-free publication (view_seq validation)

### 10.4 Stress Tests

- High volume append + query
- Heavy out-of-order ingestion
- High delete churn
- Long-running maintenance

### 10.5 Invariant Verification

- Run tl_validate() after every operation in debug mode
- Verify L1 non-overlap after every compaction
- Verify tombstone canonicalization

### 10.6 Snapshot Lifetime Enforcement

Deliverables:
- Debug-mode assertion if snapshot released while iterators exist
- Debug-mode assertion if tl_close() called with outstanding snapshots
- Document as UB in release mode

Reference: Spec Section 6.5

---

## Definition of Done (V1 Feature Complete)

V1 is complete when:

1. **Contract coherence:**
   - Spec code blocks match timelog.h exactly
   - All config fields documented and implemented

2. **Write path correct:**
   - Append, batch append, delete_range, delete_before work
   - Flush creates L0 segments visible in new snapshots
   - Publication protocol prevents dirty reads
   - tl_compact() signals compaction request

3. **Read path correct:**
   - Snapshot acquisition is race-free under concurrent flush/compaction
   - Range queries return correct, sorted, tombstone-filtered results
   - Point lookup fast path works

4. **Compaction correct:**
   - L1 remains non-overlapping by window
   - Tombstones are folded
   - Residual tombstones are preserved in L0
   - L0 count bounded by max_delta_segments

5. **Maintenance correct:**
   - Manual and background modes work as documented
   - API mode validation enforced
   - Start/stop idempotency
   - Failure handling and retry work

6. **Concurrency correct:**
   - Lock ordering prevents deadlocks
   - view_seq seqlock prevents torn reads
   - Background maintenance doesn't corrupt state

7. **Observability:**
   - Stats and validation work
   - Invariant violations are detectable

---

## Appendix A: Lock Ordering Summary

Strict ordering to prevent deadlocks:

```
maint_mu -> flush_mu -> writer_mu -> memtable.mu
```

Rules:
- Never acquire a lock while holding one to its right
- Long builds happen off-lock (only short critical sections under writer_mu)
- Deferred signaling: set flag under writer_mu (or after unlock), signal under maint_mu later

---

## Appendix B: Configuration Defaults

| Parameter | Default | Notes |
|-----------|---------|-------|
| time_unit | TL_TIME_MS | |
| target_page_bytes | 65536 | ~64 KiB |
| memtable_max_bytes | 1048576 | ~1 MiB |
| ooo_budget_bytes | 0 | -> memtable_max_bytes / 10 |
| sealed_max_runs | 4 | |
| sealed_wait_ms | 100 | |
| max_delta_segments | 8 | |
| window_size | 0 | -> 1 hour in time_unit |
| window_origin | 0 | |
| delete_debt_threshold | 0.0 | disabled |
| compaction_target_bytes | 0 | unlimited |
| max_compaction_inputs | 0 | unlimited |
| max_compaction_windows | 0 | unlimited |
| maintenance_mode | TL_MAINT_DISABLED | |

---

## Appendix C: Status Code Values (Canonical)

From `timelog.h`:

| Code | Value | Meaning |
|------|-------|---------|
| TL_OK | 0 | Success |
| TL_EOF | 1 | End of iteration |
| TL_EINVAL | 10 | Invalid argument |
| TL_ESTATE | 20 | Invalid state |
| TL_EBUSY | 21 | Resource busy / backpressure |
| TL_ENOMEM | 30 | Allocation failure |
| TL_EINTERNAL | 90 | Internal error |

---

## Appendix D: Document Cross-Reference

| Plan Phase | Primary LLD Reference |
|------------|----------------------|
| Phase 0 | Spec, timelog.h |
| Phase 1 | Background Maintenance LLD Section 2 |
| Phase 2 | Storage LLD Section 2.5, Section 7; Read Path LLD Section 6 |
| Phase 3 | Storage LLD Section 3-8 |
| Phase 4 | Write Path LLD Section 3-7 |
| Phase 5 | Read Path LLD Section 1-9 |
| Phase 6 | Spec Section 9, Storage LLD Section 10 |
| Phase 7 | Background Maintenance LLD Section 3-4, Section 9, Section 11 |
| Phase 8 | Compaction Policy LLD Section 5-9 |
| Phase 9 | Background Maintenance LLD Section 12 |
| Phase 10 | All LLDs |

---

This plan provides a clear engineering path from empty repository to feature-complete
Timelog V1 implementation, with concurrency invariants established early and
compaction treated as a required V1 component.

