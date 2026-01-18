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
