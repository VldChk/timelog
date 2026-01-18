# Timelog V1 HLD (Refined North Star)

This document defines the high-level design for Timelog V1 as a greenfield
system. It aligns with timelog_one_pager.md and incorporates the refined
decisions in proposal_unified.md.

The intent is to set stable architectural choices for the entire V1 program.
No API or LLD details are prescribed here beyond what is required to define
the system behavior and constraints.

---

## 0. Definition

Timelog V1 is an in-memory, time-indexed multimap keyed by int64 timestamps
(unit selected at initialization: s/ms/us/ns). It is optimized for:
- Fast time-range selection: [t1, t2), since(t), until(t), last(duration).
- Fast time-based eviction: delete older than T, delete [t1, t2).
- Mostly-ordered ingestion with safe handling of out-of-order records.

Records store (timestamp, handle). The handle is an opaque token for payloads
managed elsewhere (Python object refs, native structs, etc.). Timelog does not
interpret payloads and is not a vectorized analytics engine.

Terminology:
- L0: delta layer (memtable flush outputs, may overlap).
- L1: main layer (compaction outputs, non-overlapping).
This document uses L0/L1 consistently.

---

## 1. Workload model and assumptions

1.1 Expected workload
- Append-heavy ingestion with strong time locality.
- Predominantly range queries and recency windows.
- Frequent retention deletes and occasional explicit range deletes.

1.2 Explicit assumptions
- Timestamps are mostly increasing, but out-of-order entries are inevitable.
- Duplicates are allowed and expected in some workloads.
- The core value is fast boundary finding and pruning, not O(1) array indexing.

---

## 2. Semantics

2.1 Timestamp and intervals
- Timestamp is int64 in a chosen resolution.
- Range semantics are half-open: [t1, t2) (inclusive start, exclusive end).

2.2 Duplicates and ordering
- Duplicates are preserved.
- Tie order across components is unspecified in V1.
- Query results are non-decreasing by timestamp.

2.3 Record identity
- V1 is a time-indexed multimap, not a stable row-id store.
- Deleting exactly one of N duplicates at timestamp T is out of scope for V1.

2.4 "Now" and recency windows
- "Now" is supplied by the caller. last(duration) is a wrapper around
  range(now - duration, now). The core remains deterministic.

---

## 3. Data model

Each record is:
- ts: int64 timestamp
- h: opaque handle (pointer-sized or 64-bit token)

The TimeIndex stores and returns handles without dereferencing them.

---

## 4. High-level architecture

Timelog V1 consists of five subsystems:
1) L1 Store (immutable L1 segments, non-overlapping)
2) L0 Store (memtable + L0 segments)
3) Delete Layer (range tombstones, per-page masks reserved for V2)
4) Manifest / Catalog (atomic publish root)
5) Maintenance / Compaction (flush + leveled merge)

This is an LSM-style architecture specialized for time-ordered access.

---

## 5. Storage organization

### 5.1 Segments

Segments are immutable, time-sorted runs composed of pages.

There are two logical levels:
- L0: segments produced by memtable flush; may overlap in time.
- L1: segments produced by compaction; must be non-overlapping by time.

L1 non-overlap is enforced by compaction policy (see Section 9).

### 5.2 Pages

Pages are contiguous blocks of records sized for cache-friendly scans and
bounded rewrite cost. A typical default target is ~64 KiB (configurable).

Each page contains:
- header: min_ts, max_ts, count, delete flags
- data: SoA arrays of timestamps and handles
- optional row-delete mask (reserved for V2; not emitted in V1)

Page size tradeoffs:
- smaller pages: more catalog overhead, more page transitions per query
- larger pages: higher rewrite cost, worse point lookup locality

### 5.3 Page catalog (fence pointers)

Each segment maintains a small page catalog:
- per-page min_ts, max_ts, count, flags, page pointer
- sorted by min_ts

Navigation is two-level:
1) Binary search the catalog to locate candidate pages.
2) Binary search within a page for exact offsets.

### 5.4 Manifest (catalog root)

The manifest is the immutable root catalog:
- list of L1 segments (sorted by min_ts, non-overlapping)
- list of L0 segments (in flush order, may overlap)
- cached global bounds (optional)

Manifests are published via atomic pointer swap.

---

## 6. Write path

### 6.1 Uniform rule: writes go to the memtable

All writes enter L0 first. This avoids "1 ns out of order"
slow paths and ensures consistent snapshot semantics.

### 6.2 Memtable structure

Memtable must support:
- high ingest throughput
- ordered iteration by timestamp
- efficient range seek (lower_bound and onward)

Recommended V1 structure:
- append-only in-order run (sorted by construction)
- small out-of-order buffer maintained in sorted form (sorted vector or skiplist)
- out-of-order budget triggers early seal

Goal: avoid snapshot-time sorting; keep ordering cost in the write path.

### 6.3 Sealing and flush

When thresholds are exceeded (size, count, or OOO budget):
- seal the memtable into an immutable memrun
- flush the memrun into an L0 segment (paged, cataloged, time-sorted)

Flush output is immutable and immediately visible after manifest publish.

---

## 7. Read path

### 7.1 Snapshot semantics

Each query runs against a snapshot:
- manifest version
- memtable view (active + sealed memruns)

Snapshots are immutable and pinned for the lifetime of the query.

### 7.2 Range query algorithm

Given [t1, t2):
1) Segment pruning
   - include L1 segments whose [min_ts, max_ts] overlap the range
   - include all L0 segments that overlap the range
2) Page pruning (within each segment)
   - binary search page catalog for candidate pages
3) Iterator construction
   - segment iterators for pages
   - memtable iterators for active + sealed memruns
4) Merge
   - k-way merge on timestamp only (ties unspecified)
5) Delete filtering
   - apply range tombstones; consult per-page masks if present

Result: non-decreasing timestamp order, duplicates preserved.

### 7.3 Point lookup fast path

V1 provides a dedicated point-lookup API: point(ts).
Contract:
- Returns all visible records with timestamp == ts in the snapshot.
- Duplicates are preserved; tie order is unspecified.
- If any tombstone covers ts in the snapshot, the result is empty.

Implementation sketch:
- locate candidate pages via catalog
- binary search within page to find all records with ts
- consult memtable via its ordered structures

This is not O(1), but it avoids full k-way merge for a single timestamp.

---

## 8. Delete model

### 8.1 Primary delete primitive: range tombstones

The primary delete is time-range [t1, t2). Deletes are logical at read time and
physically reclaimed by compaction.

### 8.2 Optional per-page delete masks

Bitsets or compressed masks are reserved for V2. V1 always rewrites pages
during compaction and does not emit partial-delete masks.

### 8.3 Delete visibility

Deletes are stored in L0 alongside writes:
- in memtable (active tombstones)
- in L0 segments (tombstone sets)
- folded into L1 on compaction

---

## 9. Compaction and maintenance

### 9.1 Leveled compaction with non-overlapping L1

V1 uses two levels:
- L0: overlapping segments
- L1: non-overlapping segments

Compaction selects:
- a set of L0 segments
- any L1 segments whose time ranges overlap those L0 segments

It merges all inputs, applies tombstones, and produces new L1 output segments
that cover exactly the same time range, with no overlap.

### 9.2 Partitioning strategy for L1 (time windows)

L1 is partitioned by fixed time windows (configurable duration). Each window
may have at most one L1 segment after compaction. This provides:
- predictable non-overlap
- natural retention and eviction boundaries
- bounded read amplification

Compaction splits output on window boundaries and publishes new L1 segments.

Key config parameters (tl_config_t):
- window_size: L1 partition width in timestamp units. Default: 1 hour in the
  selected time unit. If 0, the system selects the default at init.
- window_origin: alignment origin for window boundaries. Default: 0.
- memtable_max_bytes: active memtable size budget (configurable).
- ooo_budget_bytes: out-of-order budget within memtable. If 0, default to
  memtable_max_bytes / 10.
- sealed_max_runs: max sealed memruns before backpressure (default 4).
- sealed_wait_ms: bounded wait for background mode (default 100 ms).
- max_delta_segments: max L0 segments before compaction is required.
- delete_debt_threshold: tombstone density trigger (default 0.0 = disabled).
- compaction_target_bytes: optional cap on compaction output size.
- max_compaction_inputs: optional cap on input segments per compaction.
- max_compaction_windows: optional cap on windows per compaction.

### 9.3 Delete reclamation

Compaction folds tombstones into output pages and drops deleted records:
- fully deleted pages are removed
- partially deleted pages are rewritten without deleted rows (preferred)
- optional masks only when rewrite is not chosen

### 9.4 Atomic publication

Maintenance builds new segments off-lock and publishes with an atomic manifest
swap. Old manifests and segments remain readable until no snapshots reference
them.

---

## 10. Concurrency model

10.1 External contract
- Multiple readers supported.
- Single writer required; external synchronization is the caller's job.

  10.2 Internal concurrency
  - Background maintenance threads are allowed.
  - Background maintenance is explicit: callers start it via tl_maint_start().
  - tl_maint_start() may return TL_EBUSY if a stop is in progress; callers retry
    after tl_maint_stop() completes.
  - tl_maint_stop() is idempotent and may return while a stop is in progress.
  - Immutable segments + snapshot reads prevent dirty reads.
  - Publication uses a seqlock-style counter plus manifest swap to avoid
    inconsistent roots (manifest vs memtable view).

---

## 11. Non-functional goals and degradation modes

1) Heavy out-of-order ingestion
- more L0 overlap
- higher merge cost
- compaction becomes more frequent

2) High delete churn
- more tombstones, more compaction pressure
- correctness preserved; performance depends on maintenance

3) Payload cost dominates (Python-object mode)
- selection is fast; dereferencing payloads remains external cost

---

## 12. Frozen V1 decisions summary

- Immutable segments and pages; atomic manifest swap.
- L0 overlap allowed; L1 non-overlapping by design.
- Range tombstones are primary delete mechanism.
- Optional per-page masks are optimization only.
- V1 does not emit per-page masks (reserved for V2).
- Snapshot-based reads with k-way merge.
- Dedicated point-lookup fast path (no O(1) promise).
- Single-writer, multi-reader concurrency contract.

This HLD is the north star for V1. It should remain stable while APIs and LLD
details evolve.
