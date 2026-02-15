# Timelog V2 LLD (Read Path)

This document defines the read-path LLD for Timelog V2, aligned with:
- proposal_unified.md
- docs/V2/timelog_v2_c_hld.md
- docs/V2/timelog_v2_lld_storage_pages.md
- docs/V2/timelog_v2_lld_write_path.md

It updates the read path for the L0/L1 model, windowed L1 non-overlap, and the
new memtable design. It targets maximum lookup performance while preserving
snapshot isolation and delete correctness.

---

## 0. Read-path objectives (non-negotiable)

1) Correctness: return exactly all visible records in [t1, t2) not deleted by
   tombstones in the snapshot.
2) Ordering: emit non-decreasing ts; duplicates preserved; tie order deterministic
   by source priority/handle but not a public contract.
3) Snapshot isolation: a query sees a consistent manifest + memview.
4) Performance: prune aggressively, scan sequentially, avoid unnecessary work.

---

## 1. Snapshot model (foundation)

### 1.1 Snapshot contents
A snapshot pins:
- manifest (immutable L0 + L1 lists)
- memview (active + sealed memruns, ordered)

### 1.2 Acquisition protocol
Acquire writer_mu during snapshot capture, then use view_seq for validation:

1. lock(writer_mu)
2. atomic_load view_seq (must be even)
3. acquire manifest ref
4. capture memview
5. atomic_load view_seq again
6. unlock(writer_mu)
7. if equal and even: success; else release and retry

This prevents inconsistent pairings and avoids torn memview capture.

---

## 2. Read APIs and range normalization

Public APIs include range-based and point lookup:
- range(t1, t2)
- since(t1) => [t1, +inf)
- until(t2) => [MIN_TS, t2)
- equal(ts) => [ts, ts+1) (range semantics)
- point(ts): return all visible records with timestamp == ts

No O(1) guarantee is implied. point(ts) is a dedicated fast path (Section 9)
and is equivalent to equal(ts) but uses direct equality to avoid ts+1 overflow.

---

## 3. Data sources in a snapshot

A query sees three data sources:

1) L1 segments (main):
   - non-overlapping by window
   - sorted by window_start

2) L0 segments:
   - may overlap each other and L1
   - bounded by max_delta_segments

3) Memview:
   - active_run (sorted)
   - ooo_head (sorted in memview)
   - ooo_runs (immutable sorted runs)
   - sealed memruns (run + OOO runs)

All component iterators must yield non-decreasing ts.

---

## 4. Query planning (prune + build iterators)

### 4.1 Segment pruning

Given [t1, t2):

L1 (sorted, non-overlapping):
- binary search first L1 with max_ts >= t1
- scan forward until min_ts >= t2

L0 (small, overlapping):
- linear scan and select seg if **records overlap** OR **tombstones overlap**
  the query range. Use record_min/max and tomb_min/max independently to
  avoid false positives when tombstones are disjoint from records.

### 4.2 Page pruning (segment iterator internal)

Segment iterator uses page catalog (fence pointers):
- find first page with page.max_ts >= t1
- find last page with page.min_ts >= t2
- within-page lower_bound for row_start and row_end

### 4.3 Memview overlap

Active buffers:
- compute active_min/active_max from active_run, ooo_head, and ooo_runs
- include if overlap with [t1, t2)

Sealed memruns:
- include if memrun.min_ts/max_ts overlap range

### 4.4 Effective tombstones

Build eff_tombs as union of:
- L0 segment tombstones (all overlapping L0 segments)
- L1 segment tombstones (should be empty in V2, but include for safety)
- memview tombstones (active + sealed)

Clip to [t1, t2) during union.

---

## 5. Component iterators

### 5.1 Segment iterator (L0/L1)

Inputs:
- segment, [t1, t2)

Algorithm:
1) prune by seg min/max
2) locate candidate pages via catalog
3) for each page:
   - skip FULLY_DELETED
   - row_start = lower_bound(ts[], t1)
   - row_end = lower_bound(ts[], t2) (or count if unbounded)
   - iterate rows; if PARTIAL_DELETED, consult row bitset

Output: sorted stream of records from that segment.

V2 note: PARTIAL_DELETED pages are not emitted in V2; this path is defensive.

### 5.2 Memrun iterator

Each memrun has run[] and OOO runs (all sorted). Internal K-way merge:
- heap over run + OOO runs
- ties resolved by run-first, then OOO run generation
- seek uses selective pop + per-source lower_bound (forward-only)

### 5.3 Active memview iterator

Active_run, ooo_head (sorted copy), and ooo_runs are merged with the same
internal K-way merge logic as memrun (run-first tie-break).

### 5.4 Memview iterator

Memview iterator is a k-way merge of:
- active iterator (if any)
- one iterator per sealed memrun

---

## 6. Merge iterator (global)

Use a min-heap over component iterators:
- key = (ts, component_id)
- component_id assigned by plan order

Operations:
- initialize heap with head record from each iterator
- pop min, advance that iterator, push new head

Complexity: O(log K) per record, where K = total components.

---

## 7. Delete filtering

### 7.1 Cursor-based filtering

Use a cursor over eff_tombs (sorted intervals):
- advance cursor while ts >= cur.end
- if cur.start <= ts < cur.end: deleted

Amortized O(1) per record.

### 7.2 Skip-ahead optimization (optional)

If a record falls inside [d1, d2):
- call iterator.seek(d2) on that component
- update heap

This avoids per-record skipping across large delete ranges.

---

## 8. Range edges and unbounded ranges

Helper:
- ts_before_end(ts, end, end_unbounded) => end_unbounded || ts < end

Handling:
- since(t1): t2_unbounded=true
- until(t2): t1=MIN_TS
- equal(ts): [ts, ts+1) with overflow guard
- point(ts): direct equality, no overflow risk

---

## 9. Dedicated point-lookup API

Contract:
- Return all visible records with timestamp == ts in the snapshot.
- Duplicates preserved; tie order unspecified.
- If any tombstone in the snapshot covers ts, return empty.

Algorithm:
1) Snapshot acquisition (Section 1).
2) Tombstone check:
   - For each tombstone set (memview + L0 + L1 if present), binary search
     intervals for ts. If any contains ts, return empty.
3) For L1:
   - binary search window containing ts
   - within that segment, binary search page catalog
   - within page, binary search ts[] to find all duplicates
4) For L0:
   - scan overlapping L0 segments; for each:
     - binary search page catalog and ts[] as above
5) For memview:
   - binary search active_run and ooo_head
   - for each active OOO run, binary search run array
   - for each sealed memrun, binary search run and each OOO run
6) Concatenate results from all components (duplicates preserved).

This avoids the full k-way merge when the query is a single timestamp.

---

## 10. Complexity summary

Let:
- S1 = selected L1 segments (non-overlapping)
- S0 = selected L0 segments (overlapping)
- R  = sealed memruns
- K  = S1 + S0 + R + (active if non-empty)

Costs:
- L1 pruning: O(log N1 + S1)
- L0 pruning: O(S0)
- Page seek: O(log P) per segment
- Merge: O(N log K)
- Tombstone filter: O(N) amortized

---

## 11. Validation rules

- Each component iterator yields non-decreasing ts.
- eff_tombs is sorted, disjoint, and clipped to [t1, t2).
- No component appears twice in plan.
- Snapshot pinning prevents use-after-free of pages/segments.

---

## 12. Integration points

Read path depends on:
- storage LLD: page catalog + segment metadata
- write path LLD: sorted memtable buffers and sealed memruns
- manifest LLD: L0/L1 lists and atomic publication

If any of these invariants break, read correctness fails.

---

This LLD defines the complete read path for Timelog V2 with L0/L1 model,
windowed non-overlap in L1, and a high-performance lookup path.

