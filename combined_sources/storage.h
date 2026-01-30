/*
============================================================================

   COMBINED HEADER FILE: storage.h

   Generated from: core\src\storage
   Generated at:   2026-01-26 20:20:58

   This file combines all .h files from the storage/ subfolder.

   Files included:
 *   - tl_manifest.h
 *   - tl_page.h
 *   - tl_segment.h
 *   - tl_window.h

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: tl_manifest.h
/*   FROM: storage/
/*
/******************************************************************************/
#ifndef TL_MANIFEST_H
#define TL_MANIFEST_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_atomic.h"
#include "tl_segment.h"

/*===========================================================================
 * Manifest Structure
 *
 * The manifest is the atomic publication root for the storage layer.
 * Immutable after publication. Replaced via copy-on-write.
 *
 * Invariants:
 * - L1 segments sorted by window_start
 * - L1 segments non-overlapping by window
 * - L0 segments in flush order (oldest first)
 * - version monotonically increasing
 *
 * Ownership:
 * - Manifest holds strong references to all its segments (acquired on build)
 * - When manifest is released and refcnt hits 0, all segment references are
 *   released
 *
 * Reference: Storage LLD Section 3.7, Section 8
 *===========================================================================*/

typedef struct tl_manifest {
    /* Version for debugging and metrics */
    uint64_t version;

    /* L1 segments: non-overlapping, sorted by window_start */
    tl_segment_t** l1;
    uint32_t       n_l1;
    uint32_t       cap_l1;

    /* L0 segments: may overlap, in flush order */
    tl_segment_t** l0;
    uint32_t       n_l0;
    uint32_t       cap_l0;

    /* Cached global bounds (optional optimization) */
    bool      has_bounds;
    tl_ts_t   min_ts;
    tl_ts_t   max_ts;

    /* Reference counting */
    tl_atomic_u32 refcnt;

    /* Allocator (for destruction) */
    tl_alloc_ctx_t* alloc;
} tl_manifest_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Create an empty manifest.
 * Returned manifest has refcnt = 1 (caller owns reference).
 */
tl_status_t tl_manifest_create(tl_alloc_ctx_t* alloc, tl_manifest_t** out);

/*===========================================================================
 * Reference Counting
 *
 * Same memory ordering rules as segment reference counting.
 * When refcnt hits 0, all segment references are released.
 *===========================================================================*/

/**
 * Increment reference count (pin manifest).
 * Returns the manifest for convenience.
 */
tl_manifest_t* tl_manifest_acquire(tl_manifest_t* m);

/**
 * Decrement reference count.
 * Destroys manifest and releases all segment references when refcnt reaches 0.
 */
void tl_manifest_release(tl_manifest_t* m);

/**
 * Get current reference count (for debugging).
 */
TL_INLINE uint32_t tl_manifest_refcnt(const tl_manifest_t* m) {
    return tl_atomic_load_relaxed_u32(&((tl_manifest_t*)m)->refcnt);
}

/*===========================================================================
 * Copy-on-Write Builder
 *
 * For manifest updates (flush or compaction), we build a new manifest
 * from the old one with modifications.
 *
 * Usage pattern:
 * 1. Initialize builder with base manifest (or NULL for initial)
 * 2. Queue additions/removals
 * 3. Build new manifest
 * 4. Destroy builder (cleans up temporary buffers)
 *
 * Reference: Storage LLD Section 8
 *===========================================================================*/

typedef struct tl_manifest_builder {
    tl_alloc_ctx_t* alloc;
    tl_manifest_t*  base;           /* Old manifest (NULL for initial) */

    /* Pending additions */
    tl_segment_t**  add_l0;
    size_t          add_l0_len;
    size_t          add_l0_cap;

    tl_segment_t**  add_l1;
    size_t          add_l1_len;
    size_t          add_l1_cap;

    /* Pending removals (by pointer comparison) */
    tl_segment_t**  remove_l0;
    size_t          remove_l0_len;
    size_t          remove_l0_cap;

    tl_segment_t**  remove_l1;
    size_t          remove_l1_len;
    size_t          remove_l1_cap;
} tl_manifest_builder_t;

/**
 * Initialize builder from existing manifest (or NULL for initial).
 * Does NOT acquire reference on base (builder is short-lived).
 */
void tl_manifest_builder_init(tl_manifest_builder_t* mb,
                               tl_alloc_ctx_t* alloc,
                               tl_manifest_t* base);

/**
 * Destroy builder and free temporary buffers.
 * Does NOT destroy base manifest or any segments.
 */
void tl_manifest_builder_destroy(tl_manifest_builder_t* mb);

/**
 * Queue an L0 segment for addition.
 * Segment is NOT acquired until build().
 */
tl_status_t tl_manifest_builder_add_l0(tl_manifest_builder_t* mb,
                                        tl_segment_t* seg);

/**
 * Queue an L1 segment for addition.
 * Segment is NOT acquired until build().
 */
tl_status_t tl_manifest_builder_add_l1(tl_manifest_builder_t* mb,
                                        tl_segment_t* seg);

/**
 * Queue an L0 segment for removal.
 */
tl_status_t tl_manifest_builder_remove_l0(tl_manifest_builder_t* mb,
                                           tl_segment_t* seg);

/**
 * Queue an L1 segment for removal.
 */
tl_status_t tl_manifest_builder_remove_l1(tl_manifest_builder_t* mb,
                                           tl_segment_t* seg);

/**
 * Build the new manifest.
 *
 * Steps:
 * 1. Allocate new manifest
 * 2. Copy segments from base, excluding removals
 * 3. Add new segments
 * 4. Sort L1 by window_start
 * 5. Compute cached bounds
 * 6. Set version = base->version + 1 (or 1 if base is NULL)
 * 7. Acquire references on ALL included segments
 *
 * Returned manifest has refcnt = 1 (caller owns reference).
 *
 * @param mb  Builder
 * @param out Output new manifest
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EINVAL if removal list contains non-existent or duplicate segments,
 *         TL_EOVERFLOW if resulting segment count exceeds UINT32_MAX
 */
tl_status_t tl_manifest_builder_build(tl_manifest_builder_t* mb,
                                       tl_manifest_t** out);

/*===========================================================================
 * Accessors
 *===========================================================================*/

TL_INLINE uint32_t tl_manifest_l0_count(const tl_manifest_t* m) {
    return m->n_l0;
}

TL_INLINE uint32_t tl_manifest_l1_count(const tl_manifest_t* m) {
    return m->n_l1;
}

TL_INLINE tl_segment_t* tl_manifest_l0_get(const tl_manifest_t* m, size_t idx) {
    TL_ASSERT(idx < m->n_l0);
    return m->l0[idx];
}

TL_INLINE tl_segment_t* tl_manifest_l1_get(const tl_manifest_t* m, size_t idx) {
    TL_ASSERT(idx < m->n_l1);
    return m->l1[idx];
}

TL_INLINE uint64_t tl_manifest_version(const tl_manifest_t* m) {
    return m->version;
}

/*===========================================================================
 * Navigation
 *===========================================================================*/

/**
 * Binary search L1 segments for first with seg->max_ts >= t1.
 * Returns index of first potentially overlapping segment.
 * Returns m->n_l1 if no such segment exists.
 *
 * Used by read path for L1 pruning (Read Path LLD Section 4.1).
 *
 * Note: Uses max_ts (not window_end) for precise pruning.
 * Since L1 segments are non-overlapping by window and sorted by window_start,
 * max_ts is also monotonically non-decreasing.
 *
 * Complexity: O(log n_l1)
 */
size_t tl_manifest_l1_find_first_overlap(const tl_manifest_t* m, tl_ts_t t1);

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG
/**
 * Validate manifest invariants.
 * @return true if valid, false if invariants violated
 *
 * Checks:
 * - L1 segments sorted by window_start
 * - L1 segments non-overlapping by window
 * - All segment pointers non-NULL
 * - Cached bounds correct (if has_bounds)
 */
bool tl_manifest_validate(const tl_manifest_t* m);
#endif

#endif /* TL_MANIFEST_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_manifest.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_page.h
/*   FROM: storage/
/*
/******************************************************************************/
#ifndef TL_PAGE_H
#define TL_PAGE_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"

/*===========================================================================
 * Page Delete Flags
 *
 * These flags indicate the delete status of a page for read-path pruning.
 * V1 only produces FULLY_LIVE pages; other values are reserved for V2.
 *
 * Reference: Storage LLD Section 3.1
 *===========================================================================*/

typedef enum tl_page_del_flags {
    TL_PAGE_FULLY_LIVE      = 0,        /* All rows are live */
    TL_PAGE_FULLY_DELETED   = 1 << 0,   /* All rows are deleted (skip page) */
    TL_PAGE_PARTIAL_DELETED = 1 << 1    /* Some rows deleted (consult bitset) */
} tl_page_del_flags_t;

/*===========================================================================
 * Row Delete Metadata (V2 reserved)
 *
 * V1 does not emit per-page delete masks. These types are defined for
 * forward compatibility but are never instantiated in V1.
 *
 * Reference: Storage LLD Section 3.2
 *===========================================================================*/

typedef enum tl_rowdel_kind {
    TL_ROWDEL_NONE   = 0,               /* No row-level deletes */
    TL_ROWDEL_BITSET = 1                /* Bitset: bit i set => row i deleted */
} tl_rowdel_kind_t;

typedef struct tl_rowbitset {
    uint32_t nbits;
    uint32_t nwords;
    uint64_t words[];  /* bit i set => row i deleted */
} tl_rowbitset_t;

/*===========================================================================
 * Page Structure
 *
 * Immutable after construction. Contains records in SoA (Structure of Arrays)
 * layout for cache-friendly timestamp scans.
 *
 * Memory Layout (single allocation):
 * +-------------------+
 * | tl_page_t header  |
 * +-------------------+
 * | (padding)         |  <- TL_ALIGN_UP to alignof(tl_ts_t)
 * +-------------------+
 * | ts[0..count-1]    |  <- page->ts points here
 * +-------------------+
 * | (padding)         |  <- TL_ALIGN_UP to alignof(tl_handle_t)
 * +-------------------+
 * | h[0..count-1]     |  <- page->h points here
 * +-------------------+
 *
 * Invariants:
 * - ts[] is non-decreasing (sorted by timestamp)
 * - count > 0 => min_ts == ts[0] && max_ts == ts[count-1]
 * - flags == FULLY_LIVE in V1
 * - row_del == NULL in V1
 *
 * Reference: Storage LLD Section 3.3
 *===========================================================================*/

typedef struct tl_page {
    /* Metadata (for pruning without scanning data) */
    tl_ts_t   min_ts;           /* ts[0] when count > 0 */
    tl_ts_t   max_ts;           /* ts[count-1] when count > 0 */
    uint32_t  count;            /* Number of records */
    uint32_t  flags;            /* tl_page_del_flags_t */

    /* Row-level delete metadata (V2 reserved, NULL in V1) */
    void*     row_del;          /* Pointer to tl_rowbitset_t if PARTIAL_DELETED */
    uint32_t  row_del_kind;     /* tl_rowdel_kind_t */
    uint32_t  reserved;         /* Padding for alignment */

    /* Data arrays (SoA layout) */
    tl_ts_t*     ts;            /* Timestamp array, length == count */
    tl_handle_t* h;             /* Handle array, length == count */

    /* Backing storage (for single-allocation pattern) */
    void*     backing;          /* Slab pointer if used, else NULL */
} tl_page_t;

/*===========================================================================
 * Page Builder
 *
 * Constructs immutable pages from a sorted record stream.
 *
 * Reference: Storage LLD Section 4
 *===========================================================================*/

typedef struct tl_page_builder {
    tl_alloc_ctx_t* alloc;
    size_t          target_page_bytes;
    size_t          records_per_page;   /* Computed from target_page_bytes */
} tl_page_builder_t;

/*---------------------------------------------------------------------------
 * Lifecycle
 *---------------------------------------------------------------------------*/

/**
 * Initialize page builder with target page size.
 * Computes records_per_page with underflow protection.
 */
void tl_page_builder_init(tl_page_builder_t* pb, tl_alloc_ctx_t* alloc,
                          size_t target_page_bytes);

/*---------------------------------------------------------------------------
 * Capacity Computation
 *---------------------------------------------------------------------------*/

/**
 * Compute capacity (records per page) for given target bytes.
 * Returns at least TL_MIN_PAGE_ROWS.
 *
 * NOTE: This is an approximate capacity. The actual page size may be
 * slightly larger than target_page_bytes due to alignment requirements.
 * This is acceptable because target_page_bytes is a soft target, not
 * a hard cap.
 */
size_t tl_page_builder_compute_capacity(size_t target_page_bytes);

/*---------------------------------------------------------------------------
 * Page Building
 *---------------------------------------------------------------------------*/

/**
 * Build a page from records.
 *
 * Precondition: records are sorted by timestamp (non-decreasing).
 *
 * @param pb      Page builder
 * @param records Sorted record array
 * @param count   Number of records (must be > 0, must be <= UINT32_MAX)
 * @param out     Output page pointer
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EINVAL if count == 0 or count > UINT32_MAX,
 *         TL_EOVERFLOW if size arithmetic overflows
 *
 * Note: count is size_t for API consistency, but tl_page_t.count is uint32_t.
 * Values > UINT32_MAX are rejected to prevent silent truncation.
 */
tl_status_t tl_page_builder_build(tl_page_builder_t* pb,
                                   const tl_record_t* records, size_t count,
                                   tl_page_t** out);

/*---------------------------------------------------------------------------
 * Page Destruction
 *---------------------------------------------------------------------------*/

/**
 * Destroy a page and free its memory.
 * Idempotent: safe to call on NULL.
 *
 * @param page  Page to destroy (may be NULL)
 * @param alloc Allocator context
 */
void tl_page_destroy(tl_page_t* page, tl_alloc_ctx_t* alloc);

/*===========================================================================
 * Within-Page Binary Search
 *
 * For range queries [t1, t2), the read path uses:
 * - row_start = lower_bound(t1)  -> first ts >= t1
 * - row_end   = lower_bound(t2)  -> first ts >= t2 (exclusive boundary)
 *
 * For point queries (all records with ts == target):
 * - start = lower_bound(target)
 * - end   = upper_bound(target)
 *
 * Reference: Read Path LLD Section 5.1
 *===========================================================================*/

/**
 * Find first row index where ts[i] >= target.
 * Returns page->count if all ts < target.
 *
 * Complexity: O(log count)
 */
size_t tl_page_lower_bound(const tl_page_t* page, tl_ts_t target);

/**
 * Find first row index where ts[i] > target.
 * Returns page->count if all ts <= target.
 *
 * Complexity: O(log count)
 */
size_t tl_page_upper_bound(const tl_page_t* page, tl_ts_t target);

/*===========================================================================
 * Record Access
 *===========================================================================*/

/**
 * Get record at index (no bounds check in release).
 */
TL_INLINE void tl_page_get_record(const tl_page_t* page, size_t idx,
                                   tl_record_t* out) {
    TL_ASSERT(idx < page->count);
    out->ts = page->ts[idx];
    out->handle = page->h[idx];
}

/**
 * Check if a row is deleted via row-level metadata.
 *
 * Defensive behavior: if metadata is missing or inconsistent for a
 * PARTIAL_DELETED page, treat the row as deleted to avoid leaks.
 */
TL_INLINE bool tl_page_row_is_deleted(const tl_page_t* page, size_t idx) {
    TL_ASSERT(page != NULL);

    if ((page->flags & TL_PAGE_PARTIAL_DELETED) == 0) {
        return false;
    }

    if (page->row_del_kind != TL_ROWDEL_BITSET || page->row_del == NULL) {
        return true; /* Unknown or missing metadata - conservative skip */
    }

    const tl_rowbitset_t* bs = (const tl_rowbitset_t*)page->row_del;
    if (bs->nwords == 0) {
        return true;
    }

    if ((uint64_t)bs->nwords * 64u < (uint64_t)bs->nbits) {
        return true;
    }

    if (idx >= (size_t)bs->nbits) {
        return true;
    }

    size_t word_idx = idx / 64;
    if (word_idx >= (size_t)bs->nwords) {
        return true;
    }

    uint64_t mask = (uint64_t)1u << (idx % 64);
    return (bs->words[word_idx] & mask) != 0;
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG
/**
 * Validate page invariants.
 * @return true if valid, false if invariants violated
 *
 * Checks:
 * - ts[] is non-decreasing
 * - min_ts == ts[0] when count > 0
 * - max_ts == ts[count-1] when count > 0
 * - flags is valid
 * - row_del == NULL when flags != PARTIAL_DELETED
 */
bool tl_page_validate(const tl_page_t* page);
#endif

/*===========================================================================
 * Page Metadata (Catalog Entry)
 *
 * Stores per-page summary for fence-pointer navigation.
 * Used by tl_page_catalog_t.
 *
 * Reference: Storage LLD Section 3.4
 *===========================================================================*/

typedef struct tl_page_meta {
    tl_ts_t    min_ts;          /* Page min_ts (for pruning) */
    tl_ts_t    max_ts;          /* Page max_ts (for pruning) */
    uint32_t   count;           /* Page record count */
    uint32_t   flags;           /* Page delete flags */
    tl_page_t* page;            /* Pointer to actual page */
} tl_page_meta_t;

/*===========================================================================
 * Page Catalog
 *
 * Array of page metadata sorted by min_ts.
 *
 * Invariants:
 * - pages[i].min_ts <= pages[i+1].min_ts (sorted by min_ts)
 * - pages[i].max_ts <= pages[i+1].max_ts (max_ts also monotonic)
 * - n_pages > 0 => all page pointers are non-NULL
 *
 * WHY max_ts IS MONOTONIC:
 * Pages within a segment are built from a single sorted record stream.
 * Records are partitioned into pages in order, so pages are non-overlapping
 * and max_ts is also monotonically non-decreasing. This property allows
 * binary search on max_ts for range start queries (find first page that
 * might contain records >= t1).
 *
 * Ownership:
 * - Catalog does NOT own pages; segment owns both catalog and pages.
 * - tl_page_catalog_destroy() only frees the metadata array.
 *
 * Reference: Storage LLD Section 3.4
 *===========================================================================*/

typedef struct tl_page_catalog {
    tl_page_meta_t* pages;      /* Array of page metadata */
    uint32_t        n_pages;    /* Number of pages */
    uint32_t        capacity;   /* Allocated capacity */
    tl_alloc_ctx_t* alloc;      /* Allocator (borrowed) */
} tl_page_catalog_t;

/*---------------------------------------------------------------------------
 * Lifecycle
 *---------------------------------------------------------------------------*/

void tl_page_catalog_init(tl_page_catalog_t* cat, tl_alloc_ctx_t* alloc);

/**
 * Destroy catalog and free metadata array.
 * Does NOT destroy pages (segment owns pages).
 */
void tl_page_catalog_destroy(tl_page_catalog_t* cat);

/*---------------------------------------------------------------------------
 * Building (used by segment builder)
 *---------------------------------------------------------------------------*/

/**
 * Reserve capacity for at least n pages.
 *
 * @param cat Catalog
 * @param n   Requested capacity (must be <= UINT32_MAX)
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EINVAL if n > UINT32_MAX,
 *         TL_EOVERFLOW if capacity growth overflows
 *
 * Note: n is size_t for API consistency, but n_pages is uint32_t.
 * Values > UINT32_MAX are rejected to prevent silent truncation.
 */
tl_status_t tl_page_catalog_reserve(tl_page_catalog_t* cat, size_t n);

/**
 * Append a page to the catalog.
 * Copies metadata from page into catalog entry.
 *
 * Precondition: pages must be added in min_ts order.
 *
 * @param cat  Catalog
 * @param page Page to add
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_page_catalog_push(tl_page_catalog_t* cat, tl_page_t* page);

/*---------------------------------------------------------------------------
 * Navigation (used by segment iterator)
 *---------------------------------------------------------------------------*/

/**
 * Find first page index where page.max_ts >= ts.
 * Returns cat->n_pages if all pages have max_ts < ts.
 *
 * Used for: finding the first page that might contain records >= ts.
 *
 * Complexity: O(log n_pages)
 */
size_t tl_page_catalog_find_first_ge(const tl_page_catalog_t* cat, tl_ts_t ts);

/**
 * Find first page index where page.min_ts >= ts.
 * Returns cat->n_pages if all pages have min_ts < ts.
 *
 * Used for: finding pages that definitely start after ts.
 *
 * Complexity: O(log n_pages)
 */
size_t tl_page_catalog_find_start_ge(const tl_page_catalog_t* cat, tl_ts_t ts);

/*---------------------------------------------------------------------------
 * Accessors
 *---------------------------------------------------------------------------*/

TL_INLINE const tl_page_meta_t* tl_page_catalog_get(const tl_page_catalog_t* cat,
                                                     size_t idx) {
    TL_ASSERT(idx < cat->n_pages);
    return &cat->pages[idx];
}

TL_INLINE uint32_t tl_page_catalog_count(const tl_page_catalog_t* cat) {
    return cat->n_pages;
}

/*---------------------------------------------------------------------------
 * Validation (Debug Only)
 *---------------------------------------------------------------------------*/

#ifdef TL_DEBUG
/**
 * Validate catalog invariants.
 * @return true if valid, false if invariants violated
 *
 * Checks:
 * - pages sorted by min_ts
 * - max_ts is monotonically non-decreasing
 * - all page pointers non-NULL
 */
bool tl_page_catalog_validate(const tl_page_catalog_t* cat);
#endif

#endif /* TL_PAGE_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_page.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_segment.h
/*   FROM: storage/
/*
/******************************************************************************/
#ifndef TL_SEGMENT_H
#define TL_SEGMENT_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_atomic.h"
#include "../internal/tl_intervals.h"
#include "tl_page.h"

/*===========================================================================
 * Segment Level
 *
 * Segments are classified by their level:
 * - L0 (delta layer): Flush outputs, may overlap, may carry tombstones
 * - L1 (main layer): Compaction outputs, non-overlapping, no tombstones
 *
 * Reference: Storage LLD Section 3.6
 *===========================================================================*/

typedef enum tl_segment_level {
    TL_SEG_L0 = 0,              /* Delta layer (flush output) */
    TL_SEG_L1 = 1               /* Main layer (compaction output) */
} tl_segment_level_t;

/*===========================================================================
 * Tombstones (Immutable Interval Set)
 *
 * Matches Storage LLD Section 3.5 exactly.
 * Segment holds a POINTER to this struct (NULL if no tombstones).
 *
 * Invariants:
 * - Intervals are sorted by start
 * - Non-overlapping
 * - Coalesced (no adjacent intervals)
 *===========================================================================*/

typedef struct tl_tombstones {
    uint32_t       n;           /* Number of intervals */
    tl_interval_t* v;           /* Sorted, non-overlapping, coalesced */
} tl_tombstones_t;

/*===========================================================================
 * Segment Structure
 *
 * Immutable after construction.
 *
 * L0 Segment Rules:
 * - level = TL_SEG_L0
 * - window_start = window_end = 0
 * - tombstones allowed (may be non-NULL)
 *
 * L1 Segment Rules:
 * - level = TL_SEG_L1
 * - window_start/window_end set to partition boundaries
 * - tombstones must be NULL (tombstones folded during compaction)
 * - All records satisfy: window_start <= ts < window_end
 *
 * Tombstone-Only Segment (L0 only):
 * - page_count = 0, record_count = 0
 * - tombstones != NULL && tombstones->n > 0
 * - min_ts/max_ts derived from tombstones
 *
 * Reference: Storage LLD Section 3.6, Section 5
 *===========================================================================*/

typedef struct tl_segment {
    /* Bounds (for pruning) - max_ts is INCLUSIVE for pruning purposes */
    tl_ts_t   min_ts;           /* Minimum timestamp (inclusive) */
    tl_ts_t   max_ts;           /* Maximum timestamp (inclusive) */

    /* Counts */
    uint64_t  record_count;     /* Total records (sum of page counts) */
    uint32_t  page_count;       /* Number of pages (0 for tombstone-only) */

    /* Level and generation */
    uint32_t  level;            /* tl_segment_level_t */
    uint32_t  generation;       /* Monotonic generation counter (diagnostics) */

    /* Window bounds (L1 only, 0 for L0) */
    tl_ts_t   window_start;     /* Inclusive start (L1 only) */
    tl_ts_t   window_end;       /* Exclusive end (L1 only) */
    bool      window_end_unbounded; /* True if window extends to +infinity (L1 only) */

    /* Page catalog */
    tl_page_catalog_t catalog;

    /* Tombstones (L0 only, NULL for L1) */
    tl_tombstones_t* tombstones;

    /* Reference counting for snapshot safety */
    tl_atomic_u32 refcnt;

    /* Allocator (for destruction) */
    tl_alloc_ctx_t* alloc;
} tl_segment_t;

/*===========================================================================
 * Segment Builder API
 *===========================================================================*/

/**
 * Build an L0 segment from sorted records and optional tombstones.
 *
 * Used by flush builder (Write Path LLD Section 4.3).
 *
 * @param alloc             Allocator context
 * @param records           Sorted record array (may be NULL if tombstone-only)
 * @param record_count      Number of records (may be 0)
 * @param tombstones        Tombstone array (borrowed, copied into segment)
 * @param tombstones_len    Number of tombstones (must be <= UINT32_MAX)
 * @param target_page_bytes Target page size
 * @param generation        Generation counter for diagnostics
 * @param out               Output segment pointer
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EINVAL if both record_count == 0 and tombstones_len == 0,
 *         TL_EINVAL if tombstones_len > UINT32_MAX,
 *         TL_EINVAL if tombstones_len > 0 but tombstones == NULL,
 *         TL_EINVAL if record_count > 0 but records == NULL
 *
 * Segment bounds for tombstone-only segments:
 * - min_ts = min(tombstones[i].start)
 * - max_ts = max(tombstones[i].end - 1) for bounded, TL_TS_MAX for unbounded
 *
 * Returned segment has refcnt = 1 (caller owns reference).
 */
tl_status_t tl_segment_build_l0(tl_alloc_ctx_t* alloc,
                                 const tl_record_t* records, size_t record_count,
                                 const tl_interval_t* tombstones, size_t tombstones_len,
                                 size_t target_page_bytes,
                                 uint32_t generation,
                                 tl_segment_t** out);

/**
 * Build an L1 segment from sorted records within a window.
 *
 * Used by compaction builder (Compaction Policy LLD Section 7).
 *
 * @param alloc               Allocator context
 * @param records             Sorted record array (must not be NULL, count > 0)
 * @param record_count        Number of records
 * @param target_page_bytes   Target page size
 * @param window_start        Window start (inclusive)
 * @param window_end          Window end (exclusive); TL_TS_MAX when unbounded
 * @param window_end_unbounded True if window extends to +infinity
 * @param generation          Generation counter
 * @param out                 Output segment pointer (set to NULL on error)
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EINVAL if records empty or NULL,
 *         TL_EINVAL if window_end_unbounded is true but window_end != TL_TS_MAX
 *
 * Precondition: All records satisfy window_start <= ts < window_end
 *               (or ts >= window_start if window_end_unbounded).
 * Invariant: window_end_unbounded implies window_end == TL_TS_MAX.
 *            This is enforced at runtime (returns TL_EINVAL on violation).
 *
 * Returned segment has refcnt = 1 (caller owns reference).
 */
tl_status_t tl_segment_build_l1(tl_alloc_ctx_t* alloc,
                                 const tl_record_t* records, size_t record_count,
                                 size_t target_page_bytes,
                                 tl_ts_t window_start, tl_ts_t window_end,
                                 bool window_end_unbounded,
                                 uint32_t generation,
                                 tl_segment_t** out);

/*===========================================================================
 * Reference Counting
 *
 * Memory ordering for reference counting:
 * - Acquire (increment): relaxed is sufficient for the fetch-add itself
 * - Release (decrement): release ordering ensures all prior writes are visible
 *   before the potential destruction
 * - Destruction: acquire fence before destroy to synchronize with releasers
 *
 * Pattern for release:
 *   uint32_t old = tl_atomic_fetch_sub_u32(&refcnt, 1, TL_MO_RELEASE);
 *   if (old == 1) {
 *       tl_atomic_fence(TL_MO_ACQUIRE);
 *       destroy(obj);
 *   }
 *
 * Reference: Implementation Notes Section 7.2, 7.3
 *===========================================================================*/

/**
 * Increment reference count (pin segment).
 * Returns the segment for convenience.
 */
tl_segment_t* tl_segment_acquire(tl_segment_t* seg);

/**
 * Decrement reference count. Destroys segment when refcnt reaches 0.
 */
void tl_segment_release(tl_segment_t* seg);

/**
 * Get current reference count (for debugging).
 */
TL_INLINE uint32_t tl_segment_refcnt(const tl_segment_t* seg) {
    return tl_atomic_load_relaxed_u32(&((tl_segment_t*)seg)->refcnt);
}

/*===========================================================================
 * Accessors
 *===========================================================================*/

TL_INLINE bool tl_segment_is_l0(const tl_segment_t* seg) {
    return seg->level == TL_SEG_L0;
}

TL_INLINE bool tl_segment_is_l1(const tl_segment_t* seg) {
    return seg->level == TL_SEG_L1;
}

TL_INLINE bool tl_segment_is_tombstone_only(const tl_segment_t* seg) {
    return seg->page_count == 0 && seg->tombstones != NULL && seg->tombstones->n > 0;
}

TL_INLINE bool tl_segment_has_tombstones(const tl_segment_t* seg) {
    return seg->tombstones != NULL && seg->tombstones->n > 0;
}

/**
 * Get immutable view of tombstones for read path.
 * Returns empty view if tombstones is NULL.
 */
TL_INLINE tl_intervals_imm_t tl_segment_tombstones_imm(const tl_segment_t* seg) {
    tl_intervals_imm_t imm;
    if (seg->tombstones != NULL) {
        imm.data = seg->tombstones->v;
        imm.len = seg->tombstones->n;
    } else {
        imm.data = NULL;
        imm.len = 0;
    }
    return imm;
}

/**
 * Get page catalog (for iteration).
 */
TL_INLINE const tl_page_catalog_t* tl_segment_catalog(const tl_segment_t* seg) {
    return &seg->catalog;
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG
/**
 * Validate segment invariants.
 * @return true if valid, false if invariants violated
 *
 * Checks:
 * - L0: window_start == window_end == 0
 * - L1: tombstones == NULL, records within window bounds
 * - Tombstone-only: page_count == 0, tombstones non-empty
 * - Page catalog valid
 * - min_ts/max_ts correct
 */
bool tl_segment_validate(const tl_segment_t* seg);
#endif

#endif /* TL_SEGMENT_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_segment.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_window.h
/*   FROM: storage/
/*
/******************************************************************************/
#ifndef TL_WINDOW_H
#define TL_WINDOW_H

#include "../internal/tl_defs.h"

/*===========================================================================
 * Window Mapping
 *
 * Computes window boundaries for L1 time partitioning.
 * All L1 segments align to window boundaries.
 *
 * Window ID formula (mathematical floor):
 *   window_id = floor((ts - window_origin) / window_size)
 *
 * Window bounds:
 *   window_start = window_origin + window_id * window_size
 *   window_end   = window_start + window_size  (may be unbounded)
 *
 * IMPORTANT: C integer division truncates toward zero, NOT floor.
 * For negative numerators, we must use floor division.
 *
 * The last window containing TL_TS_MAX has an unbounded end because
 * window_start + window_size would exceed int64_t range. This is
 * represented by end_unbounded=true, similar to unbounded tombstones.
 *
 * Reference: Storage LLD Section 6.1, HLD Section 9.2
 *===========================================================================*/

/*---------------------------------------------------------------------------
 * Overflow-Safe Arithmetic Helpers
 *
 * These return true on overflow, false on success.
 * On success, result is stored in *out.
 *---------------------------------------------------------------------------*/

/*
 * Overflow-safe subtraction: computes a - b.
 * Returns true if overflow would occur, false otherwise.
 */
TL_INLINE bool tl_sub_overflow_i64(int64_t a, int64_t b, int64_t* out) {
    /*
     * Overflow cases:
     * 1. b > 0 && a < INT64_MIN + b  (a - b would underflow)
     * 2. b < 0 && a > INT64_MAX + b  (a - b would overflow)
     *
     * Note: INT64_MAX + b when b < 0 is safe (result < INT64_MAX)
     *       INT64_MIN + b when b > 0 is safe (result > INT64_MIN)
     */
    if (b > 0 && a < INT64_MIN + b) {
        return true; /* Underflow */
    }
    if (b < 0 && a > INT64_MAX + b) {
        return true; /* Overflow */
    }
    *out = a - b;
    return false;
}

/*---------------------------------------------------------------------------
 * Floor Division for Signed Integers
 *
 * C's / operator truncates toward zero. For correct window mapping,
 * we need mathematical floor(a / b), which always rounds toward -infinity.
 *
 * Examples:
 *   tl_floor_div_i64(-1, 10)  = -1   (C gives 0)
 *   tl_floor_div_i64(-10, 10) = -1   (C gives -1, same)
 *   tl_floor_div_i64(-11, 10) = -2   (C gives -1)
 *   tl_floor_div_i64(9, 10)   = 0    (C gives 0, same)
 *   tl_floor_div_i64(10, 10)  = 1    (C gives 1, same)
 *
 * If b <= 0, returns 0 as defensive fallback to prevent UB.
 * Callers should validate b > 0 before calling.
 *---------------------------------------------------------------------------*/

TL_INLINE int64_t tl_floor_div_i64(int64_t a, int64_t b) {
    /* C-06 fix: Runtime guard against division by zero.
     * TL_ASSERT becomes UB in release builds. Return 0 as safe fallback. */
    if (b <= 0) {
        return 0;
    }
    int64_t q = a / b;
    int64_t r = a % b;
    /* Adjust if remainder is non-zero and numerator is negative */
    if (r != 0 && a < 0) {
        q -= 1;
    }
    return q;
}

/*---------------------------------------------------------------------------
 * Default Window Size
 *
 * Returns 1 hour in the specified time unit.
 * Uses constants from tl_defs.h.
 *---------------------------------------------------------------------------*/

tl_ts_t tl_window_default_size(tl_time_unit_t unit);

/*---------------------------------------------------------------------------
 * Window ID Computation
 *
 * Computes the window ID for a given timestamp.
 * Uses floor division for correctness with negative timestamps.
 *
 * @param ts            Timestamp
 * @param window_size   Window width (must be > 0)
 * @param window_origin Origin for window alignment
 * @param out_id        Output: window ID (may be negative)
 * @return TL_OK on success,
 *         TL_EINVAL if window_size <= 0,
 *         TL_EOVERFLOW if ts - origin overflows
 *---------------------------------------------------------------------------*/

tl_status_t tl_window_id_for_ts(tl_ts_t ts, tl_ts_t window_size,
                                 tl_ts_t window_origin, int64_t* out_id);

/*---------------------------------------------------------------------------
 * Window Bounds Computation
 *
 * Computes the start and end boundaries for a given window ID.
 * Uses overflow-safe arithmetic.
 *
 * When window_end would exceed INT64_MAX, end_unbounded is set to true
 * and out_end is set to TL_TS_MAX. Callers must check end_unbounded
 * when comparing timestamps against window_end.
 *
 * If window_size <= 0, returns degenerate empty window [origin, origin)
 * with end_unbounded = false. Callers should validate window_size > 0
 * before calling; this defensive behavior prevents UB on bad input.
 *
 * @param window_id      Window ID
 * @param window_size    Window width (must be > 0; returns degenerate if not)
 * @param window_origin  Origin for window alignment
 * @param out_start      Output: window start (inclusive)
 * @param out_end        Output: window end (exclusive), or TL_TS_MAX if unbounded
 * @param end_unbounded  Output: true if end extends to +infinity
 *---------------------------------------------------------------------------*/

void tl_window_bounds(int64_t window_id, tl_ts_t window_size, tl_ts_t window_origin,
                      tl_ts_t* out_start, tl_ts_t* out_end, bool* end_unbounded);

/*---------------------------------------------------------------------------
 * Window Bounds for Timestamp (Convenience)
 *
 * Computes window boundaries containing a given timestamp.
 * Combines window_id_for_ts and window_bounds.
 *
 * @param ts             Timestamp
 * @param window_size    Window width (must be > 0)
 * @param window_origin  Origin for window alignment
 * @param out_start      Output: window start (inclusive)
 * @param out_end        Output: window end (exclusive), or TL_TS_MAX if unbounded
 * @param end_unbounded  Output: true if end extends to +infinity
 * @return TL_OK on success,
 *         TL_EINVAL if window_size <= 0,
 *         TL_EOVERFLOW if computation overflows
 *---------------------------------------------------------------------------*/

tl_status_t tl_window_bounds_for_ts(tl_ts_t ts, tl_ts_t window_size,
                                     tl_ts_t window_origin,
                                     tl_ts_t* out_start, tl_ts_t* out_end,
                                     bool* end_unbounded);

/*---------------------------------------------------------------------------
 * Window Containment Check
 *
 * Checks if a timestamp falls within a window [window_start, window_end).
 * Handles unbounded windows correctly.
 *---------------------------------------------------------------------------*/

TL_INLINE bool tl_window_contains(tl_ts_t window_start, tl_ts_t window_end,
                                   bool end_unbounded, tl_ts_t ts) {
    if (ts < window_start) {
        return false;
    }
    if (end_unbounded) {
        return true; /* ts >= start and no upper bound */
    }
    return ts < window_end;
}

/*---------------------------------------------------------------------------
 * Window Containment Check (Simple)
 *
 * For windows known to be bounded (e.g., internal use where overflow
 * is not possible). Caller must ensure window_end is valid.
 *---------------------------------------------------------------------------*/

TL_INLINE bool tl_window_contains_bounded(tl_ts_t window_start,
                                           tl_ts_t window_end,
                                           tl_ts_t ts) {
    return ts >= window_start && ts < window_end;
}

#endif /* TL_WINDOW_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_window.h
/------------------------------------------------------------------------------/
