#include "../internal/tl_segment.h"
#include <string.h>

/*===========================================================================
 * Segment Functions
 *===========================================================================*/

/*
 * Internal: destroy segment resources.
 */
static void segment_destroy(tl_segment_t* seg) {
    if (seg == NULL) return;

    const tl_allocator_t* alloc = seg->alloc;

    /* Destroy all pages */
    for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
        if (seg->catalog.pages[i].page != NULL) {
            tl_page_destroy(alloc, seg->catalog.pages[i].page);
        }
    }

    /* Destroy catalog */
    tl_page_catalog_destroy(alloc, &seg->catalog);

    /* Destroy tombstones */
    if (seg->tombstones != NULL) {
        tl_tombstones_destroy(alloc, seg->tombstones);
    }

    /* Free segment itself */
    tl__free(alloc, seg);
}

tl_status_t tl_segment_create(const tl_allocator_t* alloc,
                               tl_page_t** pages,
                               uint32_t n_pages,
                               tl_tombstones_t* tombstones,
                               tl_segment_kind_t kind,
                               uint32_t generation,
                               tl_segment_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    /* Must have either pages or tombstones */
    if (n_pages == 0 && tl_tombstones_empty(tombstones)) {
        return TL_EINVAL;
    }

    /* Allocate segment */
    tl_segment_t* seg = tl__calloc(alloc, 1, sizeof(tl_segment_t));
    if (seg == NULL) return TL_ENOMEM;

    seg->alloc = alloc;
    seg->kind = kind;
    seg->generation = generation;
    tl_atomic_u32_store(&seg->refcnt, 1);

    /* Build page catalog */
    if (n_pages > 0) {
        seg->catalog.pages = tl__malloc(alloc, n_pages * sizeof(tl_page_meta_t));
        if (seg->catalog.pages == NULL) {
            tl__free(alloc, seg);
            return TL_ENOMEM;
        }

        uint64_t total_records = 0;
        for (uint32_t i = 0; i < n_pages; i++) {
            tl_page_t* p = pages[i];
            seg->catalog.pages[i].min_ts = p->min_ts;
            seg->catalog.pages[i].max_ts = p->max_ts;
            seg->catalog.pages[i].count = p->count;
            seg->catalog.pages[i].flags = p->flags;
            seg->catalog.pages[i].page = p;
            total_records += p->count;
        }

        seg->catalog.n_pages = n_pages;
        seg->page_count = n_pages;
        seg->record_count = total_records;

        /* Derive min/max from pages */
        seg->min_ts = seg->catalog.pages[0].min_ts;
        seg->max_ts = seg->catalog.pages[n_pages - 1].max_ts;
    } else {
        /* Tombstone-only segment */
        tl_page_catalog_init(&seg->catalog);
        seg->page_count = 0;
        seg->record_count = 0;
    }

    /* Attach tombstones */
    seg->tombstones = tombstones;

    /* For tombstone-only segments, derive min/max from tombstones */
    if (n_pages == 0 && tombstones != NULL) {
        seg->min_ts = tl_tombstones_min_ts(tombstones);
        seg->max_ts = tl_tombstones_max_ts(tombstones);
    }

    /* Extend min/max to cover tombstones if both present */
    if (n_pages > 0 && !tl_tombstones_empty(tombstones)) {
        tl_ts_t tomb_min = tl_tombstones_min_ts(tombstones);
        tl_ts_t tomb_max = tl_tombstones_max_ts(tombstones);
        if (tomb_min < seg->min_ts) seg->min_ts = tomb_min;
        if (tomb_max > seg->max_ts) seg->max_ts = tomb_max;
    }

    *out = seg;
    return TL_OK;
}

tl_status_t tl_segment_create_tombstone_only(const tl_allocator_t* alloc,
                                              tl_tombstones_t* tombstones,
                                              tl_segment_kind_t kind,
                                              uint32_t generation,
                                              tl_segment_t** out) {
    if (tl_tombstones_empty(tombstones)) {
        return TL_EINVAL;
    }
    return tl_segment_create(alloc, NULL, 0, tombstones, kind, generation, out);
}

uint32_t tl_segment_acquire(tl_segment_t* seg) {
    if (seg == NULL) return 0;
    return tl_atomic_u32_fetch_add(&seg->refcnt, 1) + 1;
}

uint32_t tl_segment_release(tl_segment_t* seg) {
    if (seg == NULL) return 0;

    uint32_t old = tl_atomic_u32_fetch_sub(&seg->refcnt, 1);
    if (old == 1) {
        /* Last reference: destroy segment */
        segment_destroy(seg);
        return 0;
    }
    return old - 1;
}

tl_status_t tl_segment_validate(const tl_segment_t* seg) {
    if (seg == NULL) return TL_OK;

    /* Validate page catalog ordering (S4) */
    for (uint32_t i = 1; i < seg->catalog.n_pages; i++) {
        /* Pages should be sorted by min_ts */
        if (seg->catalog.pages[i].min_ts < seg->catalog.pages[i - 1].min_ts) {
            return TL_EINTERNAL;
        }
    }

    /* Validate each page (S2, S3) */
    for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
        tl_status_t st = tl_page_validate(seg->catalog.pages[i].page);
        if (st != TL_OK) return st;
    }

    /* Validate segment min/max bounds (S5)
     *
     * The segment bounds may be extended beyond page bounds when tombstones
     * are present. The invariants are:
     * - seg->min_ts <= pages[0].min_ts (tombstones can extend lower)
     * - seg->max_ts >= pages[n-1].max_ts (tombstones can extend higher)
     *
     * For tombstone-only segments (page_count == 0), bounds come from tombstones.
     */
    if (seg->page_count > 0) {
        /* min_ts can be extended lower by tombstones */
        if (seg->min_ts > seg->catalog.pages[0].min_ts) {
            return TL_EINTERNAL;  /* Segment min_ts must cover first page */
        }
        /* max_ts can be extended higher by tombstones */
        if (seg->max_ts < seg->catalog.pages[seg->page_count - 1].max_ts) {
            return TL_EINTERNAL;  /* Segment max_ts must cover last page */
        }

        /* When no tombstones, bounds should match exactly */
        if (seg->tombstones == NULL || seg->tombstones->n == 0) {
            if (seg->min_ts != seg->catalog.pages[0].min_ts) {
                return TL_EINTERNAL;  /* No tombstones but min_ts mismatch */
            }
            if (seg->max_ts != seg->catalog.pages[seg->page_count - 1].max_ts) {
                return TL_EINTERNAL;  /* No tombstones but max_ts mismatch */
            }
        }
    }

    return TL_OK;
}

/*===========================================================================
 * Segment Builder Functions
 *===========================================================================*/

#define TL_SEGMENT_BUILDER_INITIAL_PAGES 4

tl_status_t tl_segment_builder_init(tl_segment_builder_t* builder,
                                     const tl_allocator_t* alloc,
                                     uint32_t page_capacity,
                                     tl_segment_kind_t kind,
                                     uint32_t generation) {
    if (builder == NULL || page_capacity == 0) return TL_EINVAL;

    memset(builder, 0, sizeof(*builder));
    builder->alloc = alloc;
    builder->kind = kind;
    builder->generation = generation;
    builder->page_capacity = page_capacity;

    /* Initialize page builder */
    tl_status_t st = tl_page_builder_init(&builder->page_builder, alloc, page_capacity);
    if (st != TL_OK) return st;

    /* Allocate initial pages array */
    builder->pages = tl__malloc(alloc, TL_SEGMENT_BUILDER_INITIAL_PAGES * sizeof(tl_page_t*));
    if (builder->pages == NULL) {
        tl_page_builder_destroy(&builder->page_builder);
        return TL_ENOMEM;
    }
    builder->pages_cap = TL_SEGMENT_BUILDER_INITIAL_PAGES;
    builder->n_pages = 0;

    return TL_OK;
}

void tl_segment_builder_destroy(tl_segment_builder_t* builder) {
    if (builder == NULL) return;

    /* Destroy page builder */
    tl_page_builder_destroy(&builder->page_builder);

    /* Destroy accumulated pages */
    for (uint32_t i = 0; i < builder->n_pages; i++) {
        if (builder->pages[i] != NULL) {
            tl_page_destroy(builder->alloc, builder->pages[i]);
        }
    }
    if (builder->pages != NULL) {
        tl__free(builder->alloc, builder->pages);
    }

    /* Destroy tombstones if not yet transferred */
    if (builder->tombstones != NULL) {
        tl_tombstones_destroy(builder->alloc, builder->tombstones);
    }

    memset(builder, 0, sizeof(*builder));
}

/*
 * Helper: grow pages array if needed.
 */
static tl_status_t builder_ensure_pages_cap(tl_segment_builder_t* builder) {
    if (builder->n_pages < builder->pages_cap) return TL_OK;

    uint32_t new_cap = builder->pages_cap * 2;
    tl_page_t** new_pages = tl__realloc(builder->alloc, builder->pages,
                                         new_cap * sizeof(tl_page_t*));
    if (new_pages == NULL) return TL_ENOMEM;

    builder->pages = new_pages;
    builder->pages_cap = new_cap;
    return TL_OK;
}

/*
 * Helper: finalize current page and add to pages list.
 */
static tl_status_t builder_finish_page(tl_segment_builder_t* builder) {
    if (tl_page_builder_empty(&builder->page_builder)) return TL_OK;

    /* Ensure room in pages array */
    tl_status_t st = builder_ensure_pages_cap(builder);
    if (st != TL_OK) return st;

    /* Finish page */
    tl_page_t* page = NULL;
    st = tl_page_builder_finish(&builder->page_builder, &page);
    if (st != TL_OK) return st;

    builder->pages[builder->n_pages++] = page;
    return TL_OK;
}

tl_status_t tl_segment_builder_add(tl_segment_builder_t* builder,
                                    tl_ts_t ts,
                                    tl_handle_t handle) {
    if (builder == NULL) return TL_EINVAL;

    /* If page is full, finish it and start new one */
    if (!tl_page_builder_has_room(&builder->page_builder)) {
        tl_status_t st = builder_finish_page(builder);
        if (st != TL_OK) return st;
    }

    return tl_page_builder_add(&builder->page_builder, ts, handle);
}

void tl_segment_builder_set_tombstones(tl_segment_builder_t* builder,
                                        tl_tombstones_t* tombstones) {
    if (builder == NULL) return;

    /* Free any existing tombstones */
    if (builder->tombstones != NULL) {
        tl_tombstones_destroy(builder->alloc, builder->tombstones);
    }
    builder->tombstones = tombstones;
}

tl_status_t tl_segment_builder_finish(tl_segment_builder_t* builder,
                                       tl_segment_t** out) {
    if (builder == NULL || out == NULL) return TL_EINVAL;
    *out = NULL;

    /* Finish any in-progress page */
    tl_status_t st = builder_finish_page(builder);
    if (st != TL_OK) return st;

    /* Must have either pages or tombstones */
    if (builder->n_pages == 0 && tl_tombstones_empty(builder->tombstones)) {
        return TL_EOF;
    }

    /* Transfer tombstones ownership */
    tl_tombstones_t* tombstones = builder->tombstones;
    builder->tombstones = NULL;

    /* Create segment (transfers page ownership) */
    st = tl_segment_create(builder->alloc,
                           builder->pages,
                           builder->n_pages,
                           tombstones,
                           builder->kind,
                           builder->generation,
                           out);

    if (st == TL_OK) {
        /* Pages transferred to segment; clear builder's list */
        builder->n_pages = 0;
    } else {
        /* Failed: restore tombstones ownership for cleanup */
        builder->tombstones = tombstones;
    }

    return st;
}
