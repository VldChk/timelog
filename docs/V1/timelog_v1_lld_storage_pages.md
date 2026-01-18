# Timelog V1 LLD (Storage Layer): Pages, Segments, Manifest, Delete Metadata

This document defines the immutable storage representation for Timelog V1. It
reflects the refined HLD and proposal (L0 overlap, L1 non-overlap, tombstones
as primary deletes, optional per-page masks). It is a greenfield storage "Bible"
for V1.

Scope:
- Defines pages, segments, tombstones, manifest, and their invariants.
- Defines how L0 and L1 are represented and how non-overlap is enforced.
- Defines storage-layer build rules for flush and compaction outputs.
- Does NOT define API or read/write orchestration beyond storage requirements.

---

## 1. Core definitions

Record:
- (ts:int64, h:uint64) where h is an opaque payload handle.

Levels:
- L0: flush outputs, may overlap in time.
- L1: compaction outputs, non-overlapping by time window.

Window:
- A fixed time partition [window_start, window_end).
- All L1 segments align to window boundaries.

---

## 2. Storage-level invariants

2.1 Immutability
- Once published, pages, segments, and manifests never mutate.
- Updates are copy-on-write: build new objects, publish via pointer swap.

2.2 Sortedness
- Within a page: ts[] is non-decreasing.
- Within a segment: pages are ordered by page.min_ts.

2.3 Metadata correctness
- page.min_ts == ts[0] when count > 0.
- page.max_ts == ts[count-1] when count > 0.
- segment.min_ts == first page.min_ts (when pages exist).
- segment.max_ts == last page.max_ts (when pages exist).
- tombstone-only segments derive min/max from tombstones.

2.4 L1 non-overlap
- L1 segments are non-overlapping by time window.
- For any two L1 segments i < j:
  seg[i].window_end <= seg[j].window_start
- Each L1 segment's records satisfy:
  window_start <= ts < window_end

2.5 Tombstone canonicalization
- Tombstone intervals are half-open [t1, t2) with t1 < t2.
- Intervals are sorted, non-overlapping, and non-adjacent (coalesced).

2.6 Snapshot safety
- A snapshot pins one manifest and all reachable segments/pages.
- Storage objects remain valid until refcount reaches zero.

---

## 3. Data structures (LLD shapes)

### 3.1 Page delete flags

```c
typedef enum tl_page_del_flags {
    TL_PAGE_FULLY_LIVE      = 0,
    TL_PAGE_FULLY_DELETED   = 1 << 0,
    TL_PAGE_PARTIAL_DELETED = 1 << 1
} tl_page_del_flags_t;
```

### 3.2 Row delete metadata (optional)

```c
typedef enum tl_rowdel_kind {
    TL_ROWDEL_NONE   = 0,
    TL_ROWDEL_BITSET = 1
} tl_rowdel_kind_t;

typedef struct tl_rowbitset {
    uint32_t nbits;
    uint32_t nwords;
    uint64_t words[];  /* bit i set => row i deleted */
} tl_rowbitset_t;
```

V1 note:
- Row bitsets are reserved for V2. V1 does not emit PARTIAL_DELETED pages.

### 3.3 Page structure

```c
typedef struct tl_page {
    tl_ts_t   min_ts;
    tl_ts_t   max_ts;
    uint32_t  count;
    uint32_t  flags;        /* tl_page_del_flags_t */

    void*     row_del;      /* NULL unless PARTIAL_DELETED */
    uint32_t  row_del_kind; /* tl_rowdel_kind_t */
    uint32_t  reserved;

    tl_ts_t*     ts;        /* length == count */
    tl_handle_t* h;         /* length == count */

    void*     backing;      /* slab pointer, if used */
} tl_page_t;
```

Layout rule:
- ts[] and h[] are contiguous arrays; slab allocation is recommended.

### 3.4 Page catalog (fence pointers)

```c
typedef struct tl_page_meta {
    tl_ts_t    min_ts;
    tl_ts_t    max_ts;
    uint32_t   count;
    uint32_t   flags;
    tl_page_t* page;
} tl_page_meta_t;

typedef struct tl_page_catalog {
    uint32_t        n_pages;
    tl_page_meta_t* pages;  /* sorted by min_ts */
} tl_page_catalog_t;
```

### 3.5 Tombstones (immutable interval set)

```c
typedef struct tl_interval {
    tl_ts_t start;          /* inclusive */
    tl_ts_t end;            /* exclusive */
    bool    end_unbounded;  /* true => [start, +inf) */
} tl_interval_t;

typedef struct tl_tombstones {
    uint32_t       n;
    tl_interval_t* v;  /* sorted, non-overlapping, coalesced */
} tl_tombstones_t;
```

### 3.6 Segment structure

```c
typedef enum tl_segment_level {
    TL_SEG_L0 = 0,
    TL_SEG_L1 = 1
} tl_segment_level_t;

typedef struct tl_segment {
    tl_ts_t   min_ts;
    tl_ts_t   max_ts;
    uint64_t  record_count;
    uint32_t  page_count;

    uint32_t  level;          /* tl_segment_level_t */
    uint32_t  generation;     /* diagnostics */

    tl_ts_t   window_start;   /* valid for L1, 0 for L0 */
    tl_ts_t   window_end;     /* valid for L1, 0 for L0 */

    tl_page_catalog_t catalog;
    tl_tombstones_t*  tombstones; /* allowed in L0, forbidden in L1 */

    _Atomic uint32_t  refcnt;
} tl_segment_t;
```

Segment rules:
- L0 segments may contain tombstones.
- L1 segments must have tombstones == NULL or empty (tombstones folded).
- L1 segments must align to window boundaries.

### 3.7 Manifest structure

```c
typedef struct tl_manifest {
    uint64_t      version;

    /* L1: non-overlapping, sorted by window_start */
    uint32_t      n_l1;
    tl_segment_t** l1;

    /* L0: overlapping, in flush order */
    uint32_t      n_l0;
    tl_segment_t** l0;

    bool          has_bounds;
    tl_ts_t       min_ts;
    tl_ts_t       max_ts;

    _Atomic uint32_t refcnt;
} tl_manifest_t;
```

Manifest rules:
- L1 segments are sorted by window_start.
- No two L1 segments overlap in time.
- L0 segments may overlap L0 and L1.
- version is a monotonically increasing publish counter for debugging,
  metrics, and snapshot caching (not used for CAS).

---

## 4. Page building

### 4.1 Target sizing

Given target_page_bytes and record size (ts + handle):
- cap = floor((target_page_bytes - header_overhead) / record_bytes)
- cap = max(cap, MIN_PAGE_ROWS)

### 4.2 Build algorithm (from sorted record stream)

1. Allocate a slab for page header + ts[] + h[].
2. Copy records into ts[] and h[].
3. Set count, min_ts, max_ts.
4. Set flags = FULLY_LIVE, row_del = NULL.

Pages are immutable after build.

---

## 5. Segment building

### 5.1 L0 segment (flush output)

Inputs:
- sorted record stream from memrun (run + OOO merged)
- optional tombstone list (coalesced)

Algorithm:
1. Build pages with page builder.
2. Build page catalog (one entry per page).
3. Compute segment min/max from first/last page.
4. Attach tombstones if present.
5. Set level = L0; window_start/end = 0.

### 5.2 L1 segment (compaction output)

Inputs:
- sorted record stream after merging L0 + overlapping L1
- tombstones already applied (filtered out)
- fixed window boundaries

Algorithm:
1. Partition the merged stream by window boundaries.
2. For each window with at least one record:
   - build pages
   - build page catalog
   - set segment min/max
   - set window_start/window_end
   - set tombstones = NULL
   - set level = L1
3. If a window has no live records, emit no segment for that window.

### 5.3 Tombstone-only segments

Allowed only in L0:
- page_count = 0, record_count = 0
- tombstones non-empty
- min/max derived from tombstones
Used to preserve residual tombstone ranges when compaction output is capped.

---

## 6. Partitioning and overlap rules

### 6.1 Window mapping

window_size and window_origin are configuration parameters (tl_config_t).
window_size is in the same time unit as timestamps; if 0, the system selects
the default at init (1 hour in the chosen time unit). window_origin defaults
to 0 unless configured otherwise.

window_id = floor((ts - window_origin) / window_size)
window_start = window_origin + window_id * window_size
window_end = window_start + window_size

All L1 records must satisfy:
window_start <= ts < window_end

### 6.2 L1 non-overlap enforcement

Compaction must replace all L1 segments whose windows intersect the compaction
input. The output must include at most one segment per window.

This guarantees L1 non-overlap and bounds read amplification.

### 6.3 L0 overlap

L0 segments may overlap each other and L1 segments. Overlap is bounded by
max_delta_segments and compaction scheduling.

---

## 7. Tombstone handling (storage layer)

### 7.1 Canonicalization

When inserting tombstones into a set:
- validate t1 < t2 (if bounded)
- insert in sorted order
- coalesce overlapping or adjacent intervals

### 7.2 L0 vs L1

- L0 segments may carry tombstones as flushed delete intent.
- L1 segments must be tombstone-free (tombstones folded during compaction).

---

## 8. Manifest operations (storage view)

### 8.1 Copy-on-write build

To update the manifest:
1. Allocate new manifest M_new.
2. Copy l1 and l0 arrays from M_old (retain pointers, increment refcnts).
3. Apply adds/removes (flush or compaction outputs).
4. Set M_new->version = M_old->version + 1.
5. Recompute cached bounds if desired.
6. Publish M_new by atomic pointer swap under seqlock.
7. Release M_old (decrement refcnts, free when zero).

### 8.2 Reference counting

Segments are refcounted. Manifests hold strong references. Snapshots pin
manifests. When a manifest is released, it releases all segments it references.

---

## 9. Delete metadata and read integration

Primary delete mechanism:
- Range tombstones, applied at read time, folded at compaction.

Optional per-page bitsets:
- Reserved for V2; V1 always rewrites pages during compaction and does not
  emit PARTIAL_DELETED pages. Readers may still handle them defensively.

Page flags:
- FULLY_DELETED pages should be dropped during compaction when possible.
- PARTIAL_DELETED pages consult row bitsets.

---

## 10. Validation checklist (storage invariants)

- Page ts[] sorted, min_ts/max_ts correct.
- Page flags consistent with row_del pointers.
- Segment catalog sorted by min_ts.
- Segment min_ts/max_ts match page bounds.
- Tombstones sorted, coalesced, valid.
- L1 segments aligned to window boundaries.
- L1 segments non-overlapping by window.

---

## 11. Out-of-scope (future LLDs)

- Compaction scheduling policy (when to compact, how many L0 segments).
- Memory reclamation details beyond refcounting.
- Background thread scheduling and backpressure.
- Point-lookup API details (read-path LLD).

---

This LLD is the storage "Bible" for V1. It is designed so that the write-path
LLD and read-path LLD can implement their logic without violating storage
invariants, while keeping overlap bounded and read amplification predictable.
