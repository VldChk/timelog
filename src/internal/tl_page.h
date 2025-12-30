#ifndef TL_PAGE_H
#define TL_PAGE_H

#include "tl_defs.h"
#include "tl_alloc.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Forward declarations */
typedef struct tl_page      tl_page_t;
typedef struct tl_rowbitset tl_rowbitset_t;

/*===========================================================================
 * Page Delete Flags
 *===========================================================================*/

/**
 * Page-level delete summary flags.
 *
 * These flags are set at page build time (flush/compaction) and never
 * mutated after publication. They enable fast-path optimizations:
 *
 * - FULLY_LIVE: No per-row delete checks needed (except query tombstones)
 * - FULLY_DELETED: Skip entire page (rare; page usually dropped instead)
 * - PARTIAL_DELETED: Consult row_del metadata for this page
 *
 * V1 default: Pages produced by flush are FULLY_LIVE because tombstones
 * are applied logically at read time. Partial masks exist as an output
 * option for future compaction optimizations.
 */
typedef enum tl_page_del_flags {
    TL_PAGE_FULLY_LIVE      = 0,       /* Fast-path: all rows live */
    TL_PAGE_FULLY_DELETED   = 1 << 0,  /* Skip page entirely */
    TL_PAGE_PARTIAL_DELETED = 1 << 1   /* Consult row_del metadata */
} tl_page_del_flags_t;

/**
 * Row delete metadata kind discriminator.
 *
 * When page has PARTIAL_DELETED, row_del points to one of these formats.
 * V1 implements only BITSET; others reserved for future use.
 */
typedef enum tl_rowdel_kind {
    TL_ROWDEL_NONE   = 0,  /* No per-row delete info */
    TL_ROWDEL_BITSET = 1   /* tl_rowbitset_t */
} tl_rowdel_kind_t;

/*===========================================================================
 * Row Bitset
 *===========================================================================*/

/**
 * Row deletion bitset for partial page deletes.
 *
 * Bit i is set if row i is deleted.
 * Space: ceil(nbits/64) * 8 bytes.
 */
#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable: 4200)  /* nonstandard extension: zero-sized array */
#endif
struct tl_rowbitset {
    uint32_t  nbits;    /* Number of rows (== page count) */
    uint32_t  nwords;   /* Number of 64-bit words */
    uint64_t  words[];  /* Flexible array member (C99) */
};
#ifdef _MSC_VER
#pragma warning(pop)
#endif

/*===========================================================================
 * Page Structure
 *===========================================================================*/

/**
 * Immutable page structure.
 *
 * Design principles:
 * - SoA layout: ts[] and h[] are separate arrays for cache efficiency
 * - Single slab allocation for locality
 * - Immutable after creation (no mutation after build)
 * - Supports within-page binary search via lower_bound
 *
 * Memory layout (when slab-allocated):
 *   [tl_page_t header][padding][ts[count]][h[count]][optional row_del]
 *
 * The `backing` pointer tracks the slab for deallocation.
 */
struct tl_page {
    /* Hot metadata (fits in cache line) */
    tl_ts_t             min_ts;       /* == ts[0] when count > 0 */
    tl_ts_t             max_ts;       /* == ts[count-1] when count > 0 */
    uint32_t            count;        /* Number of records in this page */
    uint32_t            flags;        /* tl_page_del_flags_t + reserved bits */

    /* Row-delete metadata (NULL for FULLY_LIVE pages) */
    void*               row_del;      /* Pointer to tl_rowbitset_t or future format */
    uint32_t            row_del_kind; /* tl_rowdel_kind_t discriminator */
    uint32_t            reserved;     /* Padding for alignment */

    /* Data arrays (contiguous, aligned) */
    tl_ts_t*            ts;           /* Timestamp array, length == count */
    tl_handle_t*        h;            /* Handle array, length == count */

    /* Memory ownership */
    void*               backing;      /* Slab base for deallocation (NULL if separate) */
};

/*===========================================================================
 * Page Functions
 *===========================================================================*/

/**
 * Compute required allocation size for a page with given row count.
 *
 * @param count    Number of records
 * @param with_del Whether to include space for row delete bitset
 * @return Total bytes needed for slab allocation
 */
size_t tl_page_alloc_size(uint32_t count, bool with_del);

/**
 * Create an immutable page from sorted records.
 *
 * Precondition: records must be sorted by timestamp (non-decreasing).
 *
 * @param alloc   Allocator to use
 * @param records Source records (copied into page)
 * @param count   Number of records
 * @param out     Output pointer for new page
 * @return TL_OK on success, TL_EINVAL if invalid args, TL_ENOMEM if alloc fails
 */
tl_status_t tl_page_create(const tl_allocator_t* alloc,
                           const tl_record_t* records,
                           uint32_t count,
                           tl_page_t** out);

/**
 * Create an immutable page from separate ts/handle arrays.
 *
 * Precondition: ts[] must be sorted (non-decreasing).
 *
 * @param alloc  Allocator to use
 * @param ts     Timestamp array (copied)
 * @param h      Handle array (copied)
 * @param count  Number of records
 * @param out    Output pointer for new page
 * @return TL_OK on success
 */
tl_status_t tl_page_create_soa(const tl_allocator_t* alloc,
                               const tl_ts_t* ts,
                               const tl_handle_t* h,
                               uint32_t count,
                               tl_page_t** out);

/**
 * Destroy a page and free its memory.
 */
void tl_page_destroy(const tl_allocator_t* alloc, tl_page_t* page);

/**
 * Binary search for lower_bound within page.
 *
 * @param page Page to search
 * @param ts   Target timestamp
 * @return Index of first row with page->ts[i] >= ts, or count if none
 */
uint32_t tl_page_lower_bound(const tl_page_t* page, tl_ts_t ts);

/**
 * Binary search for upper_bound within page.
 *
 * @param page Page to search
 * @param ts   Target timestamp
 * @return Index of first row with page->ts[i] > ts, or count if none
 */
uint32_t tl_page_upper_bound(const tl_page_t* page, tl_ts_t ts);

/**
 * Check if a specific row is deleted (for PARTIAL_DELETED pages).
 *
 * @param page Page to check
 * @param row  Row index
 * @return true if row is deleted, false otherwise
 */
bool tl_page_row_deleted(const tl_page_t* page, uint32_t row);

/**
 * Check if page overlaps with query range [t1, t2).
 *
 * @param page Page to check
 * @param t1   Range start (inclusive)
 * @param t2   Range end (exclusive)
 * @return true if page overlaps range
 */
TL_INLINE bool tl_page_overlaps(const tl_page_t* page, tl_ts_t t1, tl_ts_t t2) {
    if (page == NULL || page->count == 0) return false;
    return page->max_ts >= t1 && tl_ts_before_end(page->min_ts, t2);
}

/**
 * Validate page invariants (debug/test).
 *
 * Checks:
 * - min_ts == ts[0], max_ts == ts[count-1]
 * - ts[] is non-decreasing
 * - flags are valid
 *
 * @param page Page to validate
 * @return TL_OK if valid, TL_EINTERNAL if invariant violated
 */
tl_status_t tl_page_validate(const tl_page_t* page);

/*===========================================================================
 * Page Catalog (Fence Pointers)
 *===========================================================================*/

/**
 * Page metadata for catalog entries ("fence pointers").
 *
 * Duplicates hot metadata from page to avoid pointer chasing during scans.
 * Stored in segment's page catalog array, sorted by min_ts.
 */
typedef struct tl_page_meta {
    tl_ts_t     min_ts;   /* Page minimum timestamp */
    tl_ts_t     max_ts;   /* Page maximum timestamp */
    uint32_t    count;    /* Number of records in page */
    uint32_t    flags;    /* tl_page_del_flags_t */
    tl_page_t*  page;     /* Pointer to immutable page */
} tl_page_meta_t;

/**
 * Page catalog: immutable array of page metadata.
 *
 * Sorted by min_ts (and implicitly by max_ts due to page sortedness).
 */
typedef struct tl_page_catalog {
    uint32_t         n_pages;  /* Number of pages */
    tl_page_meta_t*  pages;    /* Array of page metadata (sorted by min_ts) */
} tl_page_catalog_t;

/**
 * Initialize an empty page catalog.
 */
void tl_page_catalog_init(tl_page_catalog_t* cat);

/**
 * Destroy a page catalog (frees metadata array but NOT the pages).
 *
 * Pages are owned by the segment and freed via tl_segment_destroy().
 */
void tl_page_catalog_destroy(const tl_allocator_t* alloc, tl_page_catalog_t* cat);

/**
 * Find first page that might overlap [t1, t2).
 *
 * Returns index of first page where max_ts >= t1, or n_pages if none.
 */
uint32_t tl_page_catalog_find_first(const tl_page_catalog_t* cat, tl_ts_t t1);

/**
 * Find last page that might overlap [t1, t2).
 *
 * Returns index+1 of last page where min_ts < t2, or 0 if none.
 */
uint32_t tl_page_catalog_find_last(const tl_page_catalog_t* cat, tl_ts_t t2);

/*===========================================================================
 * Page Builder
 *===========================================================================*/

/**
 * Page builder for constructing pages from sorted record streams.
 *
 * Usage:
 *   1. tl_page_builder_init() with target capacity
 *   2. tl_page_builder_add() records in sorted order
 *   3. tl_page_builder_finish() to create the page
 *
 * This builder is used by flush and compaction to construct pages
 * from merged/sorted record streams.
 */
typedef struct tl_page_builder {
    const tl_allocator_t* alloc;
    tl_record_t*          records;     /* Temporary record buffer */
    uint32_t              count;       /* Current record count */
    uint32_t              capacity;    /* Maximum records per page */
} tl_page_builder_t;

/**
 * Initialize a page builder.
 *
 * @param builder  Builder to initialize
 * @param alloc    Allocator to use
 * @param capacity Maximum records per page (from config)
 * @return TL_OK on success
 */
tl_status_t tl_page_builder_init(tl_page_builder_t* builder,
                                  const tl_allocator_t* alloc,
                                  uint32_t capacity);

/**
 * Destroy page builder resources.
 */
void tl_page_builder_destroy(tl_page_builder_t* builder);

/**
 * Reset builder for reuse (clears buffer without freeing).
 */
void tl_page_builder_reset(tl_page_builder_t* builder);

/**
 * Add a record to the builder.
 *
 * Precondition: records must be added in non-decreasing timestamp order.
 *
 * @param builder Builder to add to
 * @param ts      Timestamp
 * @param handle  Handle
 * @return TL_OK if added, TL_EBUSY if builder is full
 */
tl_status_t tl_page_builder_add(tl_page_builder_t* builder,
                                 tl_ts_t ts,
                                 tl_handle_t handle);

/**
 * Check if builder has room for more records.
 */
TL_INLINE bool tl_page_builder_has_room(const tl_page_builder_t* builder) {
    return builder && builder->count < builder->capacity;
}

/**
 * Check if builder is empty.
 */
TL_INLINE bool tl_page_builder_empty(const tl_page_builder_t* builder) {
    return !builder || builder->count == 0;
}

/**
 * Get current record count in builder.
 */
TL_INLINE uint32_t tl_page_builder_count(const tl_page_builder_t* builder) {
    return builder ? builder->count : 0;
}

/**
 * Finish building and create an immutable page.
 *
 * After this call, the builder is reset and can be reused.
 *
 * @param builder Builder to finish
 * @param out     Output pointer for new page
 * @return TL_OK on success, TL_EOF if builder is empty
 */
tl_status_t tl_page_builder_finish(tl_page_builder_t* builder, tl_page_t** out);

#ifdef __cplusplus
}
#endif

#endif /* TL_PAGE_H */
