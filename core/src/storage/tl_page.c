#include "tl_page.h"
#include <string.h>  /* memcpy */

/*===========================================================================
 * Page Builder
 *===========================================================================*/

size_t tl_page_builder_compute_capacity(size_t target_page_bytes) {
    const size_t header_size = sizeof(tl_page_t);
    const size_t record_size = sizeof(tl_ts_t) + sizeof(tl_handle_t);

    /* Guard against underflow */
    if (target_page_bytes <= header_size) {
        return TL_MIN_PAGE_ROWS;
    }

    size_t usable = target_page_bytes - header_size;
    size_t cap = usable / record_size;

    /* Enforce minimum */
    return (cap < TL_MIN_PAGE_ROWS) ? TL_MIN_PAGE_ROWS : cap;
}

void tl_page_builder_init(tl_page_builder_t* pb, tl_alloc_ctx_t* alloc,
                          size_t target_page_bytes) {
    TL_ASSERT(pb != NULL);
    TL_ASSERT(alloc != NULL);

    pb->alloc = alloc;
    pb->target_page_bytes = target_page_bytes;
    pb->records_per_page = tl_page_builder_compute_capacity(target_page_bytes);
}

/*---------------------------------------------------------------------------
 * Single-Allocation Page Layout
 *
 * We allocate one block containing:
 * - tl_page_t header
 * - padding for ts[] alignment
 * - ts[] array
 * - padding for h[] alignment
 * - h[] array
 *
 * This minimizes allocations and improves cache locality.
 *---------------------------------------------------------------------------*/

tl_status_t tl_page_builder_build(tl_page_builder_t* pb,
                                   const tl_record_t* records, size_t count,
                                   tl_page_t** out) {
    TL_ASSERT(pb != NULL);
    TL_ASSERT(out != NULL);

    /* Validate count */
    if (count == 0) {
        return TL_EINVAL;
    }
    if (count > UINT32_MAX) {
        return TL_EINVAL;
    }

    TL_ASSERT(records != NULL);

    /*
     * Debug: verify records are sorted (catches upstream bugs early)
     */
#ifdef TL_DEBUG
    for (size_t i = 1; i < count; i++) {
        TL_ASSERT(records[i].ts >= records[i - 1].ts &&
                  "records must be sorted by timestamp");
    }
#endif

    /*
     * Compute layout with proper alignment.
     *
     * Layout:
     *   [0, sizeof(tl_page_t))                -> header
     *   [ts_offset, ts_offset + count*8)      -> ts[]
     *   [h_offset, h_offset + count*8)        -> h[]
     *
     * Check for size_t overflow in all arithmetic.
     */
    const size_t ts_align = _Alignof(tl_ts_t);
    const size_t h_align = _Alignof(tl_handle_t);

    /* Check: count * sizeof(tl_ts_t) */
    if (count > SIZE_MAX / sizeof(tl_ts_t)) {
        return TL_EOVERFLOW;
    }
    size_t ts_array_size = count * sizeof(tl_ts_t);

    /* Check: count * sizeof(tl_handle_t) */
    if (count > SIZE_MAX / sizeof(tl_handle_t)) {
        return TL_EOVERFLOW;
    }
    size_t h_array_size = count * sizeof(tl_handle_t);

    size_t ts_offset = TL_ALIGN_UP(sizeof(tl_page_t), ts_align);

    /* Check: ts_offset + ts_array_size */
    if (ts_offset > SIZE_MAX - ts_array_size) {
        return TL_EOVERFLOW;
    }
    size_t h_offset = TL_ALIGN_UP(ts_offset + ts_array_size, h_align);

    /* Check: h_offset + h_array_size */
    if (h_offset > SIZE_MAX - h_array_size) {
        return TL_EOVERFLOW;
    }
    size_t total_size = h_offset + h_array_size;

    /* Allocate single block */
    void* backing = tl__malloc(pb->alloc, total_size);
    if (backing == NULL) {
        return TL_ENOMEM;
    }

    /* Zero the header portion for safety */
    memset(backing, 0, sizeof(tl_page_t));

    /* Set up pointers */
    tl_page_t* page = (tl_page_t*)backing;
    page->ts = (tl_ts_t*)((char*)backing + ts_offset);
    page->h = (tl_handle_t*)((char*)backing + h_offset);
    page->backing = backing;

    /* Copy data */
    for (size_t i = 0; i < count; i++) {
        page->ts[i] = records[i].ts;
        page->h[i] = records[i].handle;
    }

    /* Set metadata */
    page->count = (uint32_t)count;
    page->min_ts = records[0].ts;
    page->max_ts = records[count - 1].ts;
    page->flags = TL_PAGE_FULLY_LIVE;
    page->row_del = NULL;
    page->row_del_kind = TL_ROWDEL_NONE;
    page->reserved = 0;

    *out = page;
    return TL_OK;
}

void tl_page_destroy(tl_page_t* page, tl_alloc_ctx_t* alloc) {
    if (page == NULL) {
        return;
    }

    /* Free the single backing allocation */
    if (page->backing != NULL) {
        tl__free(alloc, page->backing);
    }
    /* Note: page itself is part of backing, so no separate free needed */
}

/*===========================================================================
 * Binary Search Functions
 *===========================================================================*/

size_t tl_page_lower_bound(const tl_page_t* page, tl_ts_t target) {
    TL_ASSERT(page != NULL);

    if (page->count == 0) {
        return 0;
    }

    /*
     * Standard lower_bound: find first i where ts[i] >= target.
     * Uses binary search with invariant: answer is in [lo, hi].
     */
    const tl_ts_t* ts = page->ts;
    size_t lo = 0;
    size_t hi = page->count;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (ts[mid] < target) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

size_t tl_page_upper_bound(const tl_page_t* page, tl_ts_t target) {
    TL_ASSERT(page != NULL);

    if (page->count == 0) {
        return 0;
    }

    /*
     * Upper_bound: find first i where ts[i] > target.
     * Uses binary search with invariant: answer is in [lo, hi].
     */
    const tl_ts_t* ts = page->ts;
    size_t lo = 0;
    size_t hi = page->count;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (ts[mid] <= target) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

/*===========================================================================
 * Page Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/**
 * Validate page invariants.
 *
 * Invariants:
 * 1. count > 0 => min_ts == ts[0] && max_ts == ts[count-1]
 * 2. ts[] is non-decreasing (sorted)
 * 3. Flags are mutually exclusive:
 *    - FULLY_LIVE=0, FULLY_DELETED=1, PARTIAL_DELETED=2
 *    - Value 3 (both bits set) is INVALID
 * 4. row_del consistency: non-NULL IFF flags == PARTIAL_DELETED
 * 5. V1: flags MUST be FULLY_LIVE (hard error in V1)
 */
bool tl_page_validate(const tl_page_t* page) {
    if (page == NULL) {
        return false;
    }

    /* Empty page is valid (though unusual) */
    if (page->count == 0) {
        return true;
    }

    /* Invariant 1: Bounds match data */
    if (page->min_ts != page->ts[0]) {
        return false;
    }
    if (page->max_ts != page->ts[page->count - 1]) {
        return false;
    }

    /* Invariant 2: ts[] is non-decreasing */
    for (uint32_t i = 1; i < page->count; i++) {
        if (page->ts[i] < page->ts[i - 1]) {
            return false;
        }
    }

    /*
     * Invariant 3: Flags mutual exclusivity
     *
     * Flag values:
     *   TL_PAGE_FULLY_LIVE      = 0       (binary: 00)
     *   TL_PAGE_FULLY_DELETED   = 1 << 0  (binary: 01)
     *   TL_PAGE_PARTIAL_DELETED = 1 << 1  (binary: 10)
     *
     * Valid values: 0, 1, 2
     * Invalid: 3 (binary: 11 - both delete bits set)
     */
    uint32_t del_bits = page->flags & (TL_PAGE_FULLY_DELETED | TL_PAGE_PARTIAL_DELETED);
    if (del_bits == (TL_PAGE_FULLY_DELETED | TL_PAGE_PARTIAL_DELETED)) {
        /* Both delete flags set - invalid (value 3) */
        return false;
    }

    /*
     * Invariant 5: V1 MUST be FULLY_LIVE (hard error)
     *
     * In V1, we do not emit FULLY_DELETED or PARTIAL_DELETED pages.
     * Any page with flags != FULLY_LIVE indicates corruption or bug.
     *
     * Invariant 4 (row_del consistency) is implicitly satisfied:
     * FULLY_LIVE requires row_del == NULL, which is enforced at build time.
     */
    if (page->flags != TL_PAGE_FULLY_LIVE) {
        return false;
    }

    /* row_del must be NULL for FULLY_LIVE pages */
    if (page->row_del != NULL) {
        return false;
    }

    return true;
}

#endif /* TL_DEBUG */

/*===========================================================================
 * Page Catalog
 *===========================================================================*/

void tl_page_catalog_init(tl_page_catalog_t* cat, tl_alloc_ctx_t* alloc) {
    TL_ASSERT(cat != NULL);
    TL_ASSERT(alloc != NULL);

    cat->pages = NULL;
    cat->n_pages = 0;
    cat->capacity = 0;
    cat->alloc = alloc;
}

void tl_page_catalog_destroy(tl_page_catalog_t* cat) {
    if (cat == NULL) {
        return;
    }

    if (cat->pages != NULL) {
        TL_FREE(cat->alloc, cat->pages);
    }

    cat->n_pages = 0;
    cat->capacity = 0;
}

/**
 * Reserve capacity in page catalog.
 *
 * Error handling:
 * - TL_EINVAL: n exceeds UINT32_MAX (invalid argument)
 * - TL_EOVERFLOW: Internal size_t overflow during growth calculation
 * - TL_ENOMEM: Allocation failed
 *
 * On ANY error, the catalog state remains unchanged. The existing pages
 * array is preserved (per realloc semantics), so callers can:
 * - Retry the operation later
 * - Continue with existing capacity
 * - Safely destroy the catalog
 *
 * @param cat  Catalog to reserve space in
 * @param n    Minimum capacity needed
 * @return TL_OK on success, error code on failure
 */
tl_status_t tl_page_catalog_reserve(tl_page_catalog_t* cat, size_t n) {
    TL_ASSERT(cat != NULL);

    /* Check for overflow */
    if (n > UINT32_MAX) {
        return TL_EINVAL;
    }

    if (n <= cat->capacity) {
        return TL_OK;
    }

    /* Grow capacity - cast to size_t before multiply to avoid 32-bit wrap */
    size_t new_cap = (cat->capacity == 0) ? 16 : (size_t)cat->capacity * 2;
    while (new_cap < n) {
        new_cap *= 2;
        /* Guard against size_t overflow */
        if (new_cap < n) {
            return TL_EOVERFLOW;
        }
    }

    /* Clamp to UINT32_MAX */
    if (new_cap > UINT32_MAX) {
        new_cap = UINT32_MAX;
    }

    tl_page_meta_t* new_pages = tl__realloc(cat->alloc, cat->pages,
                                             new_cap * sizeof(tl_page_meta_t));
    if (new_pages == NULL) {
        return TL_ENOMEM;
    }

    cat->pages = new_pages;
    cat->capacity = (uint32_t)new_cap;
    return TL_OK;
}

tl_status_t tl_page_catalog_push(tl_page_catalog_t* cat, tl_page_t* page) {
    TL_ASSERT(cat != NULL);
    TL_ASSERT(page != NULL);

    /* Ensure capacity */
    if (cat->n_pages >= cat->capacity) {
        tl_status_t st = tl_page_catalog_reserve(cat, (size_t)cat->n_pages + 1);
        if (st != TL_OK) {
            return st;
        }
    }

    /* Add metadata entry */
    tl_page_meta_t* meta = &cat->pages[cat->n_pages];
    meta->min_ts = page->min_ts;
    meta->max_ts = page->max_ts;
    meta->count = page->count;
    meta->flags = page->flags;
    meta->page = page;

    cat->n_pages++;
    return TL_OK;
}

/*---------------------------------------------------------------------------
 * Catalog Navigation
 *---------------------------------------------------------------------------*/

size_t tl_page_catalog_find_first_ge(const tl_page_catalog_t* cat, tl_ts_t ts) {
    TL_ASSERT(cat != NULL);

    if (cat->n_pages == 0) {
        return 0;
    }

    /*
     * Binary search for first page where max_ts >= ts.
     * Since max_ts is monotonically non-decreasing (invariant documented
     * in header), this is a valid lower_bound search.
     */
    size_t lo = 0;
    size_t hi = cat->n_pages;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (cat->pages[mid].max_ts < ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

size_t tl_page_catalog_find_start_ge(const tl_page_catalog_t* cat, tl_ts_t ts) {
    TL_ASSERT(cat != NULL);

    if (cat->n_pages == 0) {
        return 0;
    }

    /*
     * Binary search for first page where min_ts >= ts.
     * Catalog is sorted by min_ts (invariant).
     */
    size_t lo = 0;
    size_t hi = cat->n_pages;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (cat->pages[mid].min_ts < ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

/*===========================================================================
 * Catalog Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/**
 * Validate page catalog invariants.
 *
 * Invariants:
 * 1. All page pointers non-NULL
 * 2. Pages sorted by min_ts (non-decreasing)
 * 3. max_ts monotonically non-decreasing
 * 4. Metadata matches actual page values (min_ts, max_ts, count, flags)
 * 5. Each page validates via tl_page_validate()
 */
bool tl_page_catalog_validate(const tl_page_catalog_t* cat) {
    if (cat == NULL) {
        return false;
    }

    if (cat->n_pages == 0) {
        return true; /* Empty catalog is valid */
    }

    tl_ts_t prev_min = TL_TS_MIN;
    tl_ts_t prev_max = TL_TS_MIN;

    for (uint32_t i = 0; i < cat->n_pages; i++) {
        const tl_page_meta_t* m = &cat->pages[i];

        /* Invariant 1: page pointer non-NULL */
        if (m->page == NULL) {
            return false;
        }

        /* Invariant 2: sorted by min_ts */
        if (m->min_ts < prev_min) {
            return false;
        }

        /* Invariant 3: max_ts monotonically non-decreasing */
        if (m->max_ts < prev_max) {
            return false;
        }

        /*
         * Invariant 4: Metadata matches actual page values
         *
         * The catalog metadata must exactly match the page's values.
         * A mismatch indicates corruption or bug in catalog building.
         */
        if (m->min_ts != m->page->min_ts) {
            return false;
        }
        if (m->max_ts != m->page->max_ts) {
            return false;
        }
        if (m->count != m->page->count) {
            return false;
        }
        if (m->flags != m->page->flags) {
            return false;
        }

        /* Invariant 5: Each page validates */
        if (!tl_page_validate(m->page)) {
            return false;
        }

        prev_min = m->min_ts;
        prev_max = m->max_ts;
    }

    return true;
}

#endif /* TL_DEBUG */
