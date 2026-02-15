#include "tl_page.h"
#include <string.h>  /* memcpy */

/*===========================================================================
 * Page Builder
 *===========================================================================*/

size_t tl_page_builder_compute_capacity(size_t target_page_bytes) {
    const size_t header_size = sizeof(tl_page_t);
    const size_t record_size = sizeof(tl_ts_t) + sizeof(tl_handle_t);

    if (target_page_bytes <= header_size) {
        return TL_MIN_PAGE_ROWS;
    }

    size_t usable = target_page_bytes - header_size;
    size_t cap = usable / record_size;

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

    if (count == 0) {
        return TL_EINVAL;
    }
    if (count > UINT32_MAX) {
        return TL_EINVAL;
    }

    if (records == NULL) {
        return TL_EINVAL;
    }

#ifdef TL_DEBUG
    for (size_t i = 1; i < count; i++) {
        TL_ASSERT(records[i].ts >= records[i - 1].ts &&
                  "records must be sorted by timestamp");
    }
#endif

    /* Compute single-allocation layout with overflow checks */
    const size_t ts_align = _Alignof(tl_ts_t);
    const size_t h_align = _Alignof(tl_handle_t);

    if (count > SIZE_MAX / sizeof(tl_ts_t)) {
        return TL_EOVERFLOW;
    }
    size_t ts_array_size = count * sizeof(tl_ts_t);

    if (count > SIZE_MAX / sizeof(tl_handle_t)) {
        return TL_EOVERFLOW;
    }
    size_t h_array_size = count * sizeof(tl_handle_t);

    size_t ts_offset = 0;
    if (!tl_align_up_safe(sizeof(tl_page_t), ts_align, &ts_offset)) {
        return TL_EOVERFLOW;
    }

    if (ts_offset > SIZE_MAX - ts_array_size) {
        return TL_EOVERFLOW;
    }
    size_t ts_end = ts_offset + ts_array_size;

    size_t h_offset = 0;
    if (!tl_align_up_safe(ts_end, h_align, &h_offset)) {
        return TL_EOVERFLOW;
    }

    if (h_offset > SIZE_MAX - h_array_size) {
        return TL_EOVERFLOW;
    }
    size_t total_size = h_offset + h_array_size;

    void* backing = tl__malloc(pb->alloc, total_size);
    if (backing == NULL) {
        return TL_ENOMEM;
    }

    memset(backing, 0, sizeof(tl_page_t));

    tl_page_t* page = (tl_page_t*)backing;
    page->ts = (tl_ts_t*)((char*)backing + ts_offset);
    page->h = (tl_handle_t*)((char*)backing + h_offset);
    page->backing = backing;

    for (size_t i = 0; i < count; i++) {
        page->ts[i] = records[i].ts;
        page->h[i] = records[i].handle;
    }

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

    /* Page struct is part of backing, so a single free covers both */
    if (page->backing != NULL) {
        tl__free(alloc, page->backing);
    }
}

/*===========================================================================
 * Binary Search Functions
 *===========================================================================*/

size_t tl_page_lower_bound(const tl_page_t* page, tl_ts_t target) {
    TL_ASSERT(page != NULL);

    if (page->count == 0) {
        return 0;
    }

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

/** Validate page invariants (bounds, sortedness, flags). */
bool tl_page_validate(const tl_page_t* page) {
    if (page == NULL) {
        return false;
    }

    if (page->count == 0) {
        return true;
    }

    if (page->min_ts != page->ts[0]) {
        return false;
    }
    if (page->max_ts != page->ts[page->count - 1]) {
        return false;
    }

    for (uint32_t i = 1; i < page->count; i++) {
        if (page->ts[i] < page->ts[i - 1]) {
            return false;
        }
    }

    /* Both delete bits set simultaneously is invalid */
    uint32_t del_bits = page->flags & (TL_PAGE_FULLY_DELETED | TL_PAGE_PARTIAL_DELETED);
    if (del_bits == (TL_PAGE_FULLY_DELETED | TL_PAGE_PARTIAL_DELETED)) {
        return false;
    }

    /* Only FULLY_LIVE pages are valid in the current on-disk format. */
    if (page->flags != TL_PAGE_FULLY_LIVE) {
        return false;
    }

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

/* On error, catalog state is unchanged (safe to retry or destroy). */
tl_status_t tl_page_catalog_reserve(tl_page_catalog_t* cat, size_t n) {
    TL_ASSERT(cat != NULL);

    if (n > UINT32_MAX) {
        return TL_EINVAL;
    }

    if (n <= cat->capacity) {
        return TL_OK;
    }

    size_t new_cap = tl__grow_capacity(cat->capacity, n, 16);
    if (new_cap == 0) {
        return TL_EOVERFLOW;
    }

    if (new_cap > UINT32_MAX) {
        new_cap = UINT32_MAX;
    }

    if (tl__alloc_would_overflow(new_cap, sizeof(tl_page_meta_t))) {
        return TL_EOVERFLOW;
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

    if (cat->n_pages >= cat->capacity) {
        tl_status_t st = tl_page_catalog_reserve(cat, (size_t)cat->n_pages + 1);
        if (st != TL_OK) {
            return st;
        }
    }

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

    /* Lower-bound on max_ts (monotonically non-decreasing) */
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

    /* Lower-bound on min_ts */
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

/** Validate catalog invariants (sort order, metadata consistency, page validity). */
bool tl_page_catalog_validate(const tl_page_catalog_t* cat) {
    if (cat == NULL) {
        return false;
    }

    if (cat->n_pages == 0) {
        return true;
    }

    tl_ts_t prev_min = TL_TS_MIN;
    tl_ts_t prev_max = TL_TS_MIN;

    for (uint32_t i = 0; i < cat->n_pages; i++) {
        const tl_page_meta_t* m = &cat->pages[i];

        if (m->page == NULL) {
            return false;
        }
        if (m->min_ts < prev_min) {
            return false;
        }
        if (m->max_ts < prev_max) {
            return false;
        }

        /* Metadata must match actual page values */
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

        if (!tl_page_validate(m->page)) {
            return false;
        }

        prev_min = m->min_ts;
        prev_max = m->max_ts;
    }

    return true;
}

#endif /* TL_DEBUG */
