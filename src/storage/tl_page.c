#include "../internal/tl_page.h"
#include <string.h>
#include <stddef.h>

/*===========================================================================
 * Alignment helpers
 *===========================================================================*/

#define TL_ALIGN_UP(x, a) (((x) + (a) - 1) & ~((a) - 1))

/*===========================================================================
 * Page Functions
 *===========================================================================*/

size_t tl_page_alloc_size(uint32_t count, bool with_del) {
    /*
     * Layout:
     *   tl_page_t header (aligned)
     *   ts[count] (8-byte aligned)
     *   h[count]  (8-byte aligned)
     *   optional: rowbitset (8-byte aligned)
     */
    size_t size = sizeof(tl_page_t);
    size = TL_ALIGN_UP(size, 8);
    size += count * sizeof(tl_ts_t);
    size += count * sizeof(tl_handle_t);

    if (with_del && count > 0) {
        uint32_t nwords = (count + 63) / 64;
        size += sizeof(tl_rowbitset_t) + nwords * sizeof(uint64_t);
    }

    return size;
}

tl_status_t tl_page_create(const tl_allocator_t* alloc,
                           const tl_record_t* records,
                           uint32_t count,
                           tl_page_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    if (count > 0 && records == NULL) return TL_EINVAL;

    /* Handle empty page */
    if (count == 0) {
        tl_page_t* page = tl__calloc(alloc, 1, sizeof(tl_page_t));
        if (page == NULL) return TL_ENOMEM;
        page->flags = TL_PAGE_FULLY_LIVE;
        page->backing = page;
        *out = page;
        return TL_OK;
    }

    /* Allocate slab */
    size_t slab_size = tl_page_alloc_size(count, false);
    void* slab = tl__malloc(alloc, slab_size);
    if (slab == NULL) return TL_ENOMEM;
    memset(slab, 0, slab_size);

    /* Set up page structure */
    tl_page_t* page = (tl_page_t*)slab;
    page->backing = slab;

    /* Compute array offsets */
    uint8_t* base = (uint8_t*)slab;
    size_t offset = TL_ALIGN_UP(sizeof(tl_page_t), 8);

    page->ts = (tl_ts_t*)(base + offset);
    offset += count * sizeof(tl_ts_t);

    page->h = (tl_handle_t*)(base + offset);

    /* Copy data (interleaved to SoA) */
    for (uint32_t i = 0; i < count; i++) {
        page->ts[i] = records[i].ts;
        page->h[i] = records[i].handle;
    }

    /* Set metadata */
    page->count = count;
    page->min_ts = page->ts[0];
    page->max_ts = page->ts[count - 1];
    page->flags = TL_PAGE_FULLY_LIVE;
    page->row_del = NULL;
    page->row_del_kind = TL_ROWDEL_NONE;

    *out = page;
    return TL_OK;
}

tl_status_t tl_page_create_soa(const tl_allocator_t* alloc,
                               const tl_ts_t* ts,
                               const tl_handle_t* h,
                               uint32_t count,
                               tl_page_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    if (count > 0 && (ts == NULL || h == NULL)) return TL_EINVAL;

    /* Handle empty page */
    if (count == 0) {
        tl_page_t* page = tl__calloc(alloc, 1, sizeof(tl_page_t));
        if (page == NULL) return TL_ENOMEM;
        page->flags = TL_PAGE_FULLY_LIVE;
        page->backing = page;
        *out = page;
        return TL_OK;
    }

    /* Allocate slab */
    size_t slab_size = tl_page_alloc_size(count, false);
    void* slab = tl__malloc(alloc, slab_size);
    if (slab == NULL) return TL_ENOMEM;
    memset(slab, 0, slab_size);

    /* Set up page structure */
    tl_page_t* page = (tl_page_t*)slab;
    page->backing = slab;

    /* Compute array offsets */
    uint8_t* base = (uint8_t*)slab;
    size_t offset = TL_ALIGN_UP(sizeof(tl_page_t), 8);

    page->ts = (tl_ts_t*)(base + offset);
    offset += count * sizeof(tl_ts_t);

    page->h = (tl_handle_t*)(base + offset);

    /* Copy data directly */
    memcpy(page->ts, ts, count * sizeof(tl_ts_t));
    memcpy(page->h, h, count * sizeof(tl_handle_t));

    /* Set metadata */
    page->count = count;
    page->min_ts = page->ts[0];
    page->max_ts = page->ts[count - 1];
    page->flags = TL_PAGE_FULLY_LIVE;
    page->row_del = NULL;
    page->row_del_kind = TL_ROWDEL_NONE;

    *out = page;
    return TL_OK;
}

void tl_page_destroy(const tl_allocator_t* alloc, tl_page_t* page) {
    if (page == NULL) return;

    if (page->backing != NULL) {
        tl__free(alloc, page->backing);
    } else {
        /* Separate allocations (future use) */
        if (page->row_del != NULL) {
            tl__free(alloc, page->row_del);
        }
        tl__free(alloc, page);
    }
}

uint32_t tl_page_lower_bound(const tl_page_t* page, tl_ts_t ts) {
    if (page == NULL || page->count == 0) return 0;

    uint32_t lo = 0;
    uint32_t hi = page->count;

    while (lo < hi) {
        uint32_t mid = lo + (hi - lo) / 2;
        if (page->ts[mid] < ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

uint32_t tl_page_upper_bound(const tl_page_t* page, tl_ts_t ts) {
    if (page == NULL || page->count == 0) return 0;

    uint32_t lo = 0;
    uint32_t hi = page->count;

    while (lo < hi) {
        uint32_t mid = lo + (hi - lo) / 2;
        if (page->ts[mid] <= ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

bool tl_page_row_deleted(const tl_page_t* page, uint32_t row) {
    if (page == NULL || row >= page->count) return false;

    /* Fast path: fully live or fully deleted */
    if (page->flags == TL_PAGE_FULLY_LIVE) return false;
    if (page->flags & TL_PAGE_FULLY_DELETED) return true;

    /* Check partial delete bitset */
    if ((page->flags & TL_PAGE_PARTIAL_DELETED) &&
        page->row_del_kind == TL_ROWDEL_BITSET &&
        page->row_del != NULL) {
        const tl_rowbitset_t* bs = (const tl_rowbitset_t*)page->row_del;
        uint32_t word_idx = row / 64;
        uint32_t bit_idx = row % 64;
        if (word_idx < bs->nwords) {
            return (bs->words[word_idx] & (1ULL << bit_idx)) != 0;
        }
    }

    return false;
}

tl_status_t tl_page_validate(const tl_page_t* page) {
    if (page == NULL) return TL_OK;

    /* Empty page is valid */
    if (page->count == 0) return TL_OK;

    /* Check min/max correctness */
    if (page->min_ts != page->ts[0]) return TL_EINTERNAL;
    if (page->max_ts != page->ts[page->count - 1]) return TL_EINTERNAL;

    /* Check sortedness */
    for (uint32_t i = 1; i < page->count; i++) {
        if (page->ts[i] < page->ts[i - 1]) return TL_EINTERNAL;
    }

    /* Check min <= max */
    if (page->min_ts > page->max_ts) return TL_EINTERNAL;

    return TL_OK;
}

/*===========================================================================
 * Page Catalog Functions
 *===========================================================================*/

void tl_page_catalog_init(tl_page_catalog_t* cat) {
    if (cat == NULL) return;
    cat->n_pages = 0;
    cat->pages = NULL;
}

void tl_page_catalog_destroy(const tl_allocator_t* alloc, tl_page_catalog_t* cat) {
    if (cat == NULL) return;

    if (cat->pages != NULL) {
        tl__free(alloc, cat->pages);
    }
    cat->pages = NULL;
    cat->n_pages = 0;
}

uint32_t tl_page_catalog_find_first(const tl_page_catalog_t* cat, tl_ts_t t1) {
    if (cat == NULL || cat->n_pages == 0) return 0;

    /*
     * Binary search for first page with max_ts >= t1.
     * This page might contain records with ts >= t1.
     */
    uint32_t lo = 0;
    uint32_t hi = cat->n_pages;

    while (lo < hi) {
        uint32_t mid = lo + (hi - lo) / 2;
        if (cat->pages[mid].max_ts < t1) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

uint32_t tl_page_catalog_find_last(const tl_page_catalog_t* cat, tl_ts_t t2) {
    if (cat == NULL || cat->n_pages == 0) return 0;

    /*
     * Binary search for first page with min_ts >= t2.
     * All pages before this might contain records with ts < t2.
     */
    uint32_t lo = 0;
    uint32_t hi = cat->n_pages;

    while (lo < hi) {
        uint32_t mid = lo + (hi - lo) / 2;
        if (cat->pages[mid].min_ts < t2) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

/*===========================================================================
 * Page Builder Functions
 *===========================================================================*/

tl_status_t tl_page_builder_init(tl_page_builder_t* builder,
                                  const tl_allocator_t* alloc,
                                  uint32_t capacity) {
    if (builder == NULL || capacity == 0) return TL_EINVAL;

    builder->alloc = alloc;
    builder->capacity = capacity;
    builder->count = 0;

    builder->records = tl__malloc(alloc, capacity * sizeof(tl_record_t));
    if (builder->records == NULL) return TL_ENOMEM;

    return TL_OK;
}

void tl_page_builder_destroy(tl_page_builder_t* builder) {
    if (builder == NULL) return;

    if (builder->records != NULL) {
        tl__free(builder->alloc, builder->records);
    }
    builder->records = NULL;
    builder->count = 0;
    builder->capacity = 0;
}

void tl_page_builder_reset(tl_page_builder_t* builder) {
    if (builder == NULL) return;
    builder->count = 0;
}

tl_status_t tl_page_builder_add(tl_page_builder_t* builder,
                                 tl_ts_t ts,
                                 tl_handle_t handle) {
    if (builder == NULL) return TL_EINVAL;
    if (builder->count >= builder->capacity) return TL_EBUSY;

    builder->records[builder->count].ts = ts;
    builder->records[builder->count].handle = handle;
    builder->count++;

    return TL_OK;
}

tl_status_t tl_page_builder_finish(tl_page_builder_t* builder, tl_page_t** out) {
    if (builder == NULL || out == NULL) return TL_EINVAL;
    *out = NULL;

    if (builder->count == 0) return TL_EOF;

    /* Create page from accumulated records */
    tl_status_t st = tl_page_create(builder->alloc, builder->records,
                                     builder->count, out);
    if (st != TL_OK) return st;

    /* Reset builder for reuse */
    builder->count = 0;

    return TL_OK;
}
