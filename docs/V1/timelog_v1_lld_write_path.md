# Timelog V1 LLD (Write Path)

This document defines the write-path LLD for Timelog V1. It aligns with:
- proposal_unified.md
- timelog_v1_c_hld.md
- timelog_v1_lld_storage_pages.md
- timelog_v1_lld_read_path.md

Scope:
- Memtable design and ingestion algorithms.
- Sealing and flush to L0 segments.
- Manifest updates for flush publication.
- Compaction triggering and scheduling hooks (policy is in a separate LLD).

Out of scope:
- Compaction selection, merge, and L1 output rules.
  See docs/timelog_v1_lld_compaction_policy.md.

---

## 1. Non-negotiable invariants (write-path view)

1) L0-first writes: all writes go to the memtable.
2) Snapshot isolation: readers see a stable manifest + memview.
3) Immutable storage: pages/segments/manifests are immutable after publish.
4) L0 overlap allowed; L1 non-overlap enforced by compaction policy.
5) Tombstones are primary deletes; bitsets are optional optimization only.
6) Publication is atomic: new manifest pointer swap, old remains pinned.
7) Single writer externally; multi-reader supported.

---

## 2. Write-path objects and responsibilities

### 2.1 timelog write facade
- Owns writer lock and publication sequence.
- Routes append and delete calls to memtable.
- Initiates sealing and flush when thresholds are exceeded.
- Requests compaction when L0 grows too large.

### 2.2 Memtable (L0 intake)
- Accepts inserts and tombstones.
- Provides ordered view for snapshots.
- Seals active state into immutable memruns.
- Exposes sealed memruns for flush.

### 2.3 Flush builder
- Builds L0 segments from sealed memruns.
- Attaches tombstones to L0 segments.
- Serialized by flush_mu to prevent concurrent flushes.

### 2.4 Manifest manager
- Copy-on-write manifest builds for flush publication.
- Reference counting for snapshot safety.

Compactor is defined in the compaction-policy LLD. The write path only
triggers it; it does not define selection or output rules.

---

## 3. Memtable design (new baseline)

### 3.1 Requirements
- High ingest throughput for mostly ordered writes.
- Efficient range and point lookups (lower_bound + scan).
- Avoid snapshot-time sorting.
- Support tombstone inserts with coalescing.

### 3.2 Data structures

Active state (single-writer only):
- active_run: append-only vector of records, always non-decreasing by ts.
- active_ooo: small sorted vector of out-of-order records (ts < last_inorder_ts).
- active_tombs: coalesced interval set [t1, t2).

Sealed state:
- sealed queue of memruns (FIFO), each immutable.

Metadata:
- last_inorder_ts
- active_bytes_est
- ooo_len and ooo_budget thresholds
- memtable_epoch (monotonic counter of writes) for snapshot caching

Config (tl_config_t):
- memtable_max_bytes (active memtable budget)
- ooo_budget_bytes (if 0, default to memtable_max_bytes / 10)

### 3.3 Chosen OOO structure (rationale)

- Sorted OOO vector is chosen for V1.
- It keeps snapshots cheap (no sort at snapshot time).
- Insert cost is O(log n + n) for OOO inserts, but OOO is bounded by budget.
- Better for high hit-rate reads than sorting at snapshot time.

### 3.4 High hit-rate read considerations

- active_ooo is always sorted; memview iterators use lower_bound on both arrays.
- memtable snapshots reuse a cached memview if epoch unchanged, avoiding copies.
- Optional future: a small recent-index for point lookups on newest data.

### 3.5 Memtable structs (LLD shape)

```c
typedef struct tl_memtable {
    tl_alloc_ctx_t* alloc;          /* allocator context (not owned) */

    tl_recvec_t    active_run;      /* append-only, sorted */
    tl_recvec_t    active_ooo;      /* sorted vector */
    tl_intervals_t active_tombs;    /* coalesced intervals */

    tl_memrun_t**  sealed;          /* FIFO queue (preallocated) */
    size_t         sealed_len;
    size_t         sealed_max_runs; /* capacity of sealed[] */

    tl_ts_t        last_inorder_ts;
    size_t         active_bytes_est;
    size_t         memtable_max_bytes;
    size_t         ooo_budget_bytes; /* 0 = unlimited OOO budget */

    uint64_t       epoch;           /* increments on any write */

    /*
     * NOTE: The sealed queue lock (memtable_mu) is owned by tl_timelog_t,
     * not by tl_memtable_t itself. This follows the lock hierarchy:
     *   maint_mu -> flush_mu -> writer_mu -> memtable_mu
     * The memtable operations receive the lock as a parameter.
     */
} tl_memtable_t;

typedef struct tl_memrun {
    tl_alloc_ctx_t* alloc;         /* allocator for freeing arrays */

    tl_record_t*   run;
    size_t         run_len;

    tl_record_t*   ooo;
    size_t         ooo_len;

    tl_interval_t* tombs;
    size_t         tombs_len;

    tl_ts_t        min_ts;         /* includes tombstone bounds */
    tl_ts_t        max_ts;         /* includes tombstone bounds */

    tl_atomic_u32  refcnt;
} tl_memrun_t;
```

### 3.6 Insert algorithm (single record)

```
if active_run empty:
    append to active_run
    last_inorder_ts = ts
else if ts >= last_inorder_ts:
    append to active_run
    last_inorder_ts = ts
else:
    insert into active_ooo:
      - binary search insertion point
      - memmove to create a gap (O(n))
      - store record
      - increment ooo_len
```

If active_ooo exceeds ooo_budget_bytes, seal early.

### 3.7 Batch insert algorithm

- If hint says mostly ordered and records[0].ts >= last_inorder_ts, do a quick
  monotonicity check (sample or full).
- If likely sorted, append batch to active_run in one reserve.
- Otherwise, insert per-record with logic above.

### 3.8 Tombstone insert algorithm

Insert [t1, t2) into active_tombs (coalesced interval set).
- if t2 < t1: TL_EINVAL
- if t1 == t2: no-op
- coalesce overlapping and adjacent intervals

---

## 4. Sealing and flush to L0

### 4.1 Seal policy

Seal if any of:
- active_bytes_est >= memtable_max_bytes
- active_ooo_bytes >= ooo_budget_bytes
- explicit tl_flush

Sealing steps:
1) Move ownership of active_run, active_ooo, active_tombs into a memrun.
2) Compute memrun min_ts/max_ts from run and ooo.
3) Reset active buffers to empty.
4) Push memrun into sealed queue (FIFO).

### 4.2 Flush policy

Flush targets the oldest sealed memrun. Selection uses peek + pin:
- choose the oldest memrun under memtable.mu
- increment its refcnt (pin)
- do not remove it from the sealed queue until publish

### 4.3 Building an L0 segment from a memrun

Inputs:
- memrun.run (sorted)
- memrun.ooo (sorted)
- memrun.tombs (interval list)

Algorithm:
1) Two-way merge run + ooo to produce a sorted stream.
2) Build pages from the stream using storage LLD page builder.
3) Build page catalog.
4) Attach tombstones (if any).
5) Output L0 segment (level = L0).

If memrun has no records and only tombstones:
- build a tombstone-only L0 segment.

---

## 5. Publication protocol (flush)

Flush publication is a two-phase process:

1) Build phase (off-lock):
   - acquire flush_mu (single flusher)
   - peek + pin the oldest sealed memrun (memtable.mu)
   - build the L0 segment from the memrun
2) Publish phase (short critical section):
   - view_seq = atomic_fetch_add(+1) (odd)
   - build new manifest with L0 segment appended
   - swap manifest pointer
   - remove memrun from sealed queue (memtable.mu)
   - view_seq = atomic_fetch_add(+1) (even)

This ensures snapshots never see both memrun and published segment.
flush_mu is released after publication and memrun unpin.

---

## 6. Backpressure and scheduling

### 6.1 Backpressure policy

To prevent unbounded memory growth:
- sealed queue has a max length (sealed_max_runs, default 4, configurable)
- sealed_wait_ms controls bounded wait in background mode (default 100 ms)
- if full, writes return TL_EBUSY (manual mode)
- in background mode, wait up to sealed_wait_ms; then return TL_EBUSY

### 6.2 Maintenance scheduling

Priority order for background worker:
1) Flush sealed memruns (bounds memory)
2) Request compaction when L0 too large (see compaction-policy LLD)

Manual mode:
- tl_maint_step performs one unit of work (flush first)

Signal rule:
- maint_signal_flush acquires maint_mu; it must be called outside writer_mu to
  preserve lock ordering (see background-maintenance LLD).

---

## 7. Write API algorithms (pseudocode)

### 7.1 tl_append

```
bool need_signal = false;
lock(writer_mu)
  memtable_insert(ts, handle)
  if should_seal:
    seal_active()
    need_signal = true
unlock
if need_signal:
  maint_signal_flush()
```

### 7.2 tl_append_batch

```
bool need_signal = false;
lock(writer_mu)
  if likely_sorted: append batch to active_run
  else: per-record insert
  if should_seal:
    seal_active()
    need_signal = true
unlock
if need_signal:
  maint_signal_flush()
```

### 7.3 tl_delete_range

```
bool need_signal = false;
lock(writer_mu)
  insert tombstone [t1,t2)
  if should_seal:
    seal_active()
    need_signal = true
unlock
if need_signal:
  maint_signal_flush()
```

### 7.4 tl_delete_before

```
bool need_signal = false;
lock(writer_mu)
  insert tombstone [MIN_TS, cutoff)
  optional: manifest prune for segments fully below cutoff
  if should_seal:
    seal_active()
    need_signal = true
unlock
if need_signal:
  maint_signal_flush()
```

### 7.5 tl_flush (synchronous)

```
seal active if non-empty
repeat:
  lock(flush_mu)
    if no sealed memruns:
      unlock(flush_mu)
      break
    peek + pin oldest memrun (memtable.mu)
    build L0 segment off-lock
    publish under writer_mu and remove memrun (memtable.mu)
    unpin memrun
  unlock(flush_mu)
until no sealed memruns
```

### 7.6 tl_compact (request)

```
signal compaction worker or run compaction once in manual mode
```

---

## 8. Edge cases and correctness rules

1) Tombstone-only memruns must flush to tombstone-only L0 segments.
2) Allocation failure during flush must leave memrun visible for retry.
3) Snapshot isolation requires: no memrun is visible both in memview and
   as an L0 segment in the same snapshot.

---

This LLD defines the write path only. Compaction selection, merge, L1 output,
and manifest updates for compaction are defined in
 docs/timelog_v1_lld_compaction_policy.md.
