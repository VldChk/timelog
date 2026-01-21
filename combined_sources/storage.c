/*
============================================================================

   COMBINED SOURCE FILE: storage.c

   Generated from: core/src/storage/
   Generated at:   2026-01-20 23:27:38

   This file combines all .c files from the storage/ subfolder.

   Files included:
 *   - tl_manifest.c
 *   - tl_page.c
 *   - tl_segment.c
 *   - tl_window.c

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: tl_manifest.c
/*   FROM: storage/
/*
/******************************************************************************/
#include "tl_manifest.h"
#include <stdlib.h>  /* qsort */

/*===========================================================================
 * Internal: Destroy Manifest (called when refcnt hits 0)
 *===========================================================================*/

static void manifest_destroy(tl_manifest_t* m) {
    TL_ASSERT(m != NULL);
    tl_alloc_ctx_t* alloc = m->alloc;

    /* Release all L0 segment references */
    for (uint32_t i = 0; i < m->n_l0; i++) {
        tl_segment_release(m->l0[i]);
    }

    /* Release all L1 segment references */
    for (uint32_t i = 0; i < m->n_l1; i++) {
        tl_segment_release(m->l1[i]);
    }

    /* Free arrays */
    if (m->l0 != NULL) {
        TL_FREE(alloc, m->l0);
    }
    if (m->l1 != NULL) {
        TL_FREE(alloc, m->l1);
    }

    /* Free manifest */
    TL_FREE(alloc, m);
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_manifest_create(tl_alloc_ctx_t* alloc, tl_manifest_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    tl_manifest_t* m = TL_NEW(alloc, tl_manifest_t);
    if (m == NULL) {
        return TL_ENOMEM;
    }

    m->version = 1;
    m->l0 = NULL;
    m->n_l0 = 0;
    m->cap_l0 = 0;
    m->l1 = NULL;
    m->n_l1 = 0;
    m->cap_l1 = 0;
    m->has_bounds = false;
    m->min_ts = 0;
    m->max_ts = 0;
    m->alloc = alloc;
    tl_atomic_init_u32(&m->refcnt, 1);

    *out = m;
    return TL_OK;
}

/*===========================================================================
 * Reference Counting
 *===========================================================================*/

tl_manifest_t* tl_manifest_acquire(tl_manifest_t* m) {
    if (m == NULL) {
        return NULL;
    }
    tl_atomic_fetch_add_u32(&m->refcnt, 1, TL_MO_RELAXED);
    return m;
}

void tl_manifest_release(tl_manifest_t* m) {
    if (m == NULL) {
        return;
    }

    uint32_t old = tl_atomic_fetch_sub_u32(&m->refcnt, 1, TL_MO_RELEASE);
    TL_ASSERT(old >= 1);

    if (old == 1) {
        tl_atomic_fence(TL_MO_ACQUIRE);
        manifest_destroy(m);
    }
}

/*===========================================================================
 * Navigation
 *===========================================================================*/

size_t tl_manifest_l1_find_first_overlap(const tl_manifest_t* m, tl_ts_t t1) {
    TL_ASSERT(m != NULL);

    if (m->n_l1 == 0) {
        return 0;
    }

    /*
     * Binary search for first L1 segment where max_ts >= t1.
     * L1 segments are sorted by window_start, and since they are
     * non-overlapping, max_ts is also monotonically non-decreasing.
     */
    size_t lo = 0;
    size_t hi = m->n_l1;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (m->l1[mid]->max_ts < t1) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

/*===========================================================================
 * Builder: Lifecycle
 *
 * Ownership semantics:
 * - Builder does NOT own segments in add/remove arrays (just stores pointers)
 * - Segments must remain valid until build() completes or builder is destroyed
 * - On build() success: new manifest acquires refs; caller may release originals
 * - On build() failure: caller still owns segments, must handle cleanup
 * - destroy() frees internal arrays only, does NOT release segments
 *
 * Rollback safety:
 * - All array allocations happen before segment acquisitions in build()
 * - If allocation fails, no segment refs have been modified
 * - Caller can retry build() or destroy builder and handle segments
 *===========================================================================*/

void tl_manifest_builder_init(tl_manifest_builder_t* mb,
                               tl_alloc_ctx_t* alloc,
                               tl_manifest_t* base) {
    TL_ASSERT(mb != NULL);
    TL_ASSERT(alloc != NULL);

    mb->alloc = alloc;
    mb->base = base;

    mb->add_l0 = NULL;
    mb->add_l0_len = 0;
    mb->add_l0_cap = 0;

    mb->add_l1 = NULL;
    mb->add_l1_len = 0;
    mb->add_l1_cap = 0;

    mb->remove_l0 = NULL;
    mb->remove_l0_len = 0;
    mb->remove_l0_cap = 0;

    mb->remove_l1 = NULL;
    mb->remove_l1_len = 0;
    mb->remove_l1_cap = 0;
}

void tl_manifest_builder_destroy(tl_manifest_builder_t* mb) {
    if (mb == NULL) {
        return;
    }

    if (mb->add_l0 != NULL) {
        TL_FREE(mb->alloc, mb->add_l0);
    }
    if (mb->add_l1 != NULL) {
        TL_FREE(mb->alloc, mb->add_l1);
    }
    if (mb->remove_l0 != NULL) {
        TL_FREE(mb->alloc, mb->remove_l0);
    }
    if (mb->remove_l1 != NULL) {
        TL_FREE(mb->alloc, mb->remove_l1);
    }

    mb->add_l0 = NULL;
    mb->add_l1 = NULL;
    mb->remove_l0 = NULL;
    mb->remove_l1 = NULL;
}

/*===========================================================================
 * Builder: Internal Helpers
 *===========================================================================*/

static tl_status_t ensure_capacity(tl_alloc_ctx_t* alloc,
                                    tl_segment_t*** arr,
                                    size_t* len,
                                    size_t* cap) {
    if (*len < *cap) {
        return TL_OK;
    }

    size_t new_cap = (*cap == 0) ? 8 : *cap * 2;
    tl_segment_t** new_arr = tl__realloc(alloc, *arr,
                                          new_cap * sizeof(tl_segment_t*));
    if (new_arr == NULL) {
        return TL_ENOMEM;
    }

    *arr = new_arr;
    *cap = new_cap;
    return TL_OK;
}

static bool is_in_removal_set(tl_segment_t* seg,
                               tl_segment_t** remove_arr,
                               size_t remove_len) {
    for (size_t i = 0; i < remove_len; i++) {
        if (remove_arr[i] == seg) {
            return true;
        }
    }
    return false;
}

/*===========================================================================
 * Builder: Add/Remove Operations
 *===========================================================================*/

tl_status_t tl_manifest_builder_add_l0(tl_manifest_builder_t* mb,
                                        tl_segment_t* seg) {
    TL_ASSERT(mb != NULL);
    TL_ASSERT(seg != NULL);

    tl_status_t st = ensure_capacity(mb->alloc, &mb->add_l0,
                                      &mb->add_l0_len, &mb->add_l0_cap);
    if (st != TL_OK) {
        return st;
    }

    mb->add_l0[mb->add_l0_len++] = seg;
    return TL_OK;
}

tl_status_t tl_manifest_builder_add_l1(tl_manifest_builder_t* mb,
                                        tl_segment_t* seg) {
    TL_ASSERT(mb != NULL);
    TL_ASSERT(seg != NULL);

    tl_status_t st = ensure_capacity(mb->alloc, &mb->add_l1,
                                      &mb->add_l1_len, &mb->add_l1_cap);
    if (st != TL_OK) {
        return st;
    }

    mb->add_l1[mb->add_l1_len++] = seg;
    return TL_OK;
}

tl_status_t tl_manifest_builder_remove_l0(tl_manifest_builder_t* mb,
                                           tl_segment_t* seg) {
    TL_ASSERT(mb != NULL);
    TL_ASSERT(seg != NULL);

    tl_status_t st = ensure_capacity(mb->alloc, &mb->remove_l0,
                                      &mb->remove_l0_len, &mb->remove_l0_cap);
    if (st != TL_OK) {
        return st;
    }

    mb->remove_l0[mb->remove_l0_len++] = seg;
    return TL_OK;
}

tl_status_t tl_manifest_builder_remove_l1(tl_manifest_builder_t* mb,
                                           tl_segment_t* seg) {
    TL_ASSERT(mb != NULL);
    TL_ASSERT(seg != NULL);

    tl_status_t st = ensure_capacity(mb->alloc, &mb->remove_l1,
                                      &mb->remove_l1_len, &mb->remove_l1_cap);
    if (st != TL_OK) {
        return st;
    }

    mb->remove_l1[mb->remove_l1_len++] = seg;
    return TL_OK;
}

/*===========================================================================
 * Builder: Comparator for L1 Sorting
 *===========================================================================*/

static int compare_l1_by_window_start(const void* a, const void* b) {
    const tl_segment_t* sa = *(const tl_segment_t**)a;
    const tl_segment_t* sb = *(const tl_segment_t**)b;

    if (sa->window_start < sb->window_start) return -1;
    if (sa->window_start > sb->window_start) return 1;
    return 0;
}

/*===========================================================================
 * Builder: Validate Removal Lists
 *
 * Returns TL_EINVAL if:
 * - Any removal target doesn't exist in base
 * - Removal list contains duplicates
 *===========================================================================*/

static tl_status_t validate_removals(tl_segment_t** base_arr, uint32_t base_len,
                                      tl_segment_t** remove_arr, size_t remove_len) {
    /* Check each removal exists in base exactly once */
    for (size_t i = 0; i < remove_len; i++) {
        const tl_segment_t* target = remove_arr[i];

        /* Check for duplicates in removal list */
        for (size_t j = 0; j < i; j++) {
            if (remove_arr[j] == target) {
                return TL_EINVAL; /* Duplicate removal */
            }
        }

        /* Check target exists in base */
        bool found = false;
        for (uint32_t k = 0; k < base_len; k++) {
            if (base_arr[k] == target) {
                found = true;
                break;
            }
        }
        if (!found) {
            return TL_EINVAL; /* Removing segment not in base */
        }
    }

    return TL_OK;
}

/*
 * Count how many segments from base survive removal.
 * Caller must have already validated that removals are a valid subset.
 */
static size_t count_kept(tl_segment_t** base_arr, uint32_t base_len,
                          tl_segment_t** remove_arr, size_t remove_len) {
    size_t kept = 0;
    for (uint32_t i = 0; i < base_len; i++) {
        if (!is_in_removal_set(base_arr[i], remove_arr, remove_len)) {
            kept++;
        }
    }
    return kept;
}

/*===========================================================================
 * Builder: Build
 *===========================================================================*/

tl_status_t tl_manifest_builder_build(tl_manifest_builder_t* mb,
                                       tl_manifest_t** out) {
    TL_ASSERT(mb != NULL);
    TL_ASSERT(out != NULL);

    tl_alloc_ctx_t* alloc = mb->alloc;

    /*
     * Validate removal lists.
     * Each removal must exist in base exactly once, with no duplicates.
     * This prevents memory corruption from incorrect size calculations.
     */
    if (mb->base != NULL) {
        tl_status_t st = validate_removals(mb->base->l0, mb->base->n_l0,
                                            mb->remove_l0, mb->remove_l0_len);
        if (st != TL_OK) {
            return st;
        }
        st = validate_removals(mb->base->l1, mb->base->n_l1,
                                mb->remove_l1, mb->remove_l1_len);
        if (st != TL_OK) {
            return st;
        }
    } else {
        /* No base: removal lists must be empty */
        if (mb->remove_l0_len > 0 || mb->remove_l1_len > 0) {
            return TL_EINVAL;
        }
    }

    /*
     * Compute actual kept counts by scanning.
     * This is safe because we validated the removal lists above.
     */
    size_t kept_l0 = 0, kept_l1 = 0;
    if (mb->base != NULL) {
        kept_l0 = count_kept(mb->base->l0, mb->base->n_l0,
                              mb->remove_l0, mb->remove_l0_len);
        kept_l1 = count_kept(mb->base->l1, mb->base->n_l1,
                              mb->remove_l1, mb->remove_l1_len);
    }

    size_t new_l0_count = kept_l0 + mb->add_l0_len;
    size_t new_l1_count = kept_l1 + mb->add_l1_len;

    /* Check for uint32_t overflow */
    if (new_l0_count > UINT32_MAX || new_l1_count > UINT32_MAX) {
        return TL_EOVERFLOW;
    }

    /* Allocate new manifest */
    tl_manifest_t* m = TL_NEW(alloc, tl_manifest_t);
    if (m == NULL) {
        return TL_ENOMEM;
    }

    m->alloc = alloc;
    m->version = (mb->base != NULL) ? mb->base->version + 1 : 1;
    tl_atomic_init_u32(&m->refcnt, 1);

    /* Allocate L0 array */
    if (new_l0_count > 0) {
        m->l0 = TL_NEW_ARRAY(alloc, tl_segment_t*, new_l0_count);
        if (m->l0 == NULL) {
            TL_FREE(alloc, m);
            return TL_ENOMEM;
        }
        m->cap_l0 = (uint32_t)new_l0_count;
    } else {
        m->l0 = NULL;
        m->cap_l0 = 0;
    }
    m->n_l0 = 0;

    /* Allocate L1 array */
    if (new_l1_count > 0) {
        m->l1 = TL_NEW_ARRAY(alloc, tl_segment_t*, new_l1_count);
        if (m->l1 == NULL) {
            if (m->l0 != NULL) TL_FREE(alloc, m->l0);
            TL_FREE(alloc, m);
            return TL_ENOMEM;
        }
        m->cap_l1 = (uint32_t)new_l1_count;
    } else {
        m->l1 = NULL;
        m->cap_l1 = 0;
    }
    m->n_l1 = 0;

    /* Copy L0 from base (excluding removals), then add new */
    if (new_l0_count > 0) {
        if (mb->base != NULL) {
            for (uint32_t i = 0; i < mb->base->n_l0; i++) {
                tl_segment_t* seg = mb->base->l0[i];
                if (!is_in_removal_set(seg, mb->remove_l0, mb->remove_l0_len)) {
                    m->l0[m->n_l0++] = tl_segment_acquire(seg);
                }
            }
        }
        for (size_t i = 0; i < mb->add_l0_len; i++) {
            m->l0[m->n_l0++] = tl_segment_acquire(mb->add_l0[i]);
        }
    } else {
        TL_ASSERT(mb->add_l0_len == 0);
    }

    /* Copy L1 from base (excluding removals), then add new */
    if (new_l1_count > 0) {
        if (mb->base != NULL) {
            for (uint32_t i = 0; i < mb->base->n_l1; i++) {
                tl_segment_t* seg = mb->base->l1[i];
                if (!is_in_removal_set(seg, mb->remove_l1, mb->remove_l1_len)) {
                    m->l1[m->n_l1++] = tl_segment_acquire(seg);
                }
            }
        }
        for (size_t i = 0; i < mb->add_l1_len; i++) {
            m->l1[m->n_l1++] = tl_segment_acquire(mb->add_l1[i]);
        }
    } else {
        TL_ASSERT(mb->add_l1_len == 0);
    }

    /* Sort L1 by window_start */
    if (m->n_l1 > 1) {
        qsort(m->l1, m->n_l1, sizeof(tl_segment_t*), compare_l1_by_window_start);
    }

    /* Compute cached bounds */
    m->has_bounds = false;
    if (m->n_l0 > 0 || m->n_l1 > 0) {
        tl_ts_t global_min = TL_TS_MAX;
        tl_ts_t global_max = TL_TS_MIN;

        for (uint32_t i = 0; i < m->n_l0; i++) {
            if (m->l0[i]->min_ts < global_min) global_min = m->l0[i]->min_ts;
            if (m->l0[i]->max_ts > global_max) global_max = m->l0[i]->max_ts;
        }
        for (uint32_t i = 0; i < m->n_l1; i++) {
            if (m->l1[i]->min_ts < global_min) global_min = m->l1[i]->min_ts;
            if (m->l1[i]->max_ts > global_max) global_max = m->l1[i]->max_ts;
        }

        if (global_min <= global_max) {
            m->has_bounds = true;
            m->min_ts = global_min;
            m->max_ts = global_max;
        }
    }

    *out = m;
    return TL_OK;
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/**
 * Validate manifest invariants.
 *
 * Invariants:
 * 1. All L0 segment pointers non-NULL
 * 2. All L0 segments have level == TL_SEG_L0
 * 3. All L1 segment pointers non-NULL
 * 4. All L1 segments have level == TL_SEG_L1
 * 5. L1 segments sorted by window_start
 * 6. L1 windows non-overlapping (prev.window_end <= curr.window_start)
 * 7. Unbounded window (window_end == TL_TS_MAX) must be LAST
 * 8. Each segment validates via tl_segment_validate()
 * 9. Cached bounds match computed bounds (if has_bounds)
 */
bool tl_manifest_validate(const tl_manifest_t* m) {
    if (m == NULL) {
        return false;
    }

    /*=========================================================================
     * L0 Segment Validation
     *=========================================================================*/
    for (uint32_t i = 0; i < m->n_l0; i++) {
        /* Pointer non-NULL */
        if (m->l0[i] == NULL) {
            return false;
        }

        /* Level check */
        if (m->l0[i]->level != TL_SEG_L0) {
            return false;
        }

        /* Each segment validates */
        if (!tl_segment_validate(m->l0[i])) {
            return false;
        }
    }

    /*=========================================================================
     * L1 Segment Validation
     *=========================================================================*/
    tl_ts_t prev_window_end = TL_TS_MIN;
    bool prev_window_unbounded = false;

    for (uint32_t i = 0; i < m->n_l1; i++) {
        /* Pointer non-NULL */
        if (m->l1[i] == NULL) {
            return false;
        }

        /* Level check */
        if (m->l1[i]->level != TL_SEG_L1) {
            return false;
        }

        /*
         * CRITICAL: Unbounded window guard
         *
         * If the previous window was unbounded, there MUST NOT be any more
         * segments after it. An unbounded window covers all future timestamps,
         * so any subsequent segment is invalid.
         */
        if (prev_window_unbounded) {
            return false;  /* Unbounded window must be last */
        }

        /* Sorted by window_start */
        if (i > 0) {
            if (m->l1[i]->window_start < m->l1[i - 1]->window_start) {
                return false;
            }
        }

        /* Non-overlapping windows (prev.window_end <= curr.window_start) */
        if (m->l1[i]->window_start < prev_window_end) {
            return false;
        }

        /* Each segment validates */
        if (!tl_segment_validate(m->l1[i])) {
            return false;
        }

        prev_window_end = m->l1[i]->window_end;
        prev_window_unbounded = m->l1[i]->window_end_unbounded;
    }

    /*=========================================================================
     * Cached Bounds Validation
     *=========================================================================*/
    if (m->has_bounds && (m->n_l0 > 0 || m->n_l1 > 0)) {
        tl_ts_t computed_min = TL_TS_MAX;
        tl_ts_t computed_max = TL_TS_MIN;

        for (uint32_t i = 0; i < m->n_l0; i++) {
            if (m->l0[i]->min_ts < computed_min) computed_min = m->l0[i]->min_ts;
            if (m->l0[i]->max_ts > computed_max) computed_max = m->l0[i]->max_ts;
        }
        for (uint32_t i = 0; i < m->n_l1; i++) {
            if (m->l1[i]->min_ts < computed_min) computed_min = m->l1[i]->min_ts;
            if (m->l1[i]->max_ts > computed_max) computed_max = m->l1[i]->max_ts;
        }

        if (m->min_ts != computed_min || m->max_ts != computed_max) {
            return false;
        }
    }

    return true;
}

#endif /* TL_DEBUG */

/------------------------------------------------------------------------------/
/*   END OF: tl_manifest.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_page.c
/*   FROM: storage/
/*
/******************************************************************************/
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

/------------------------------------------------------------------------------/
/*   END OF: tl_page.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_segment.c
/*   FROM: storage/
/*
/******************************************************************************/
#include "tl_segment.h"
#include <string.h>  /* memcpy */

/*===========================================================================
 * Internal: Compute Tombstone Bounds
 *
 * For tombstone-only segments, we derive min_ts/max_ts from tombstones.
 *
 * Rules:
 * - min_ts = min(tombstones[i].start)
 * - max_ts = max(tombstones[i].end - 1) for bounded intervals
 *          = TL_TS_MAX for unbounded intervals [start, +inf)
 *
 * IMPORTANT: Never read tombstones[i].end when end_unbounded is true.
 *===========================================================================*/

static void compute_tombstone_bounds(const tl_interval_t* tombstones, size_t n,
                                      tl_ts_t* out_min, tl_ts_t* out_max) {
    TL_ASSERT(n > 0);
    TL_ASSERT(tombstones != NULL);

    tl_ts_t min_ts = tombstones[0].start;
    tl_ts_t max_ts;

    /* Check if any interval is unbounded */
    bool has_unbounded = false;
    for (size_t i = 0; i < n; i++) {
        if (tombstones[i].end_unbounded) {
            has_unbounded = true;
            break;
        }
    }

    if (has_unbounded) {
        max_ts = TL_TS_MAX;
    } else {
        /* All bounded: find max(end - 1) */
        max_ts = tombstones[0].end - 1;
        for (size_t i = 1; i < n; i++) {
            if (tombstones[i].start < min_ts) {
                min_ts = tombstones[i].start;
            }
            tl_ts_t end_inclusive = tombstones[i].end - 1;
            if (end_inclusive > max_ts) {
                max_ts = end_inclusive;
            }
        }
    }

    /* Also check remaining intervals for min_ts */
    for (size_t i = 1; i < n; i++) {
        if (tombstones[i].start < min_ts) {
            min_ts = tombstones[i].start;
        }
    }

    *out_min = min_ts;
    *out_max = max_ts;
}

/*===========================================================================
 * Internal: Allocate and Copy Tombstones
 *===========================================================================*/

static tl_status_t create_tombstones(tl_alloc_ctx_t* alloc,
                                      const tl_interval_t* src, size_t n,
                                      tl_tombstones_t** out) {
    if (n == 0) {
        *out = NULL;
        return TL_OK;
    }

    tl_tombstones_t* ts = TL_NEW(alloc, tl_tombstones_t);
    if (ts == NULL) {
        return TL_ENOMEM;
    }

    ts->v = TL_NEW_ARRAY(alloc, tl_interval_t, n);
    if (ts->v == NULL) {
        TL_FREE(alloc, ts);
        return TL_ENOMEM;
    }

    memcpy(ts->v, src, n * sizeof(tl_interval_t));
    ts->n = (uint32_t)n;

    *out = ts;
    return TL_OK;
}

static void destroy_tombstones(tl_tombstones_t* ts, tl_alloc_ctx_t* alloc) {
    if (ts == NULL) {
        return;
    }
    if (ts->v != NULL) {
        TL_FREE(alloc, ts->v);
    }
    TL_FREE(alloc, ts);
}

/*===========================================================================
 * Internal: Destroy Segment (called when refcnt hits 0)
 *===========================================================================*/

static void segment_destroy(tl_segment_t* seg) {
    TL_ASSERT(seg != NULL);
    tl_alloc_ctx_t* alloc = seg->alloc;

    /* Destroy all pages */
    for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
        tl_page_t* page = seg->catalog.pages[i].page;
        tl_page_destroy(page, alloc);
    }

    /* Destroy catalog (frees metadata array, not pages) */
    tl_page_catalog_destroy(&seg->catalog);

    /* Destroy tombstones */
    destroy_tombstones(seg->tombstones, alloc);

    /* Free segment itself */
    TL_FREE(alloc, seg);
}

/*===========================================================================
 * Internal: Build Pages from Record Stream
 *
 * Partitions records into pages and populates the catalog.
 * On error, all pages already built are destroyed (rollback).
 *===========================================================================*/

static tl_status_t build_pages(tl_segment_t* seg,
                                const tl_record_t* records, size_t record_count,
                                size_t target_page_bytes) {
    tl_alloc_ctx_t* alloc = seg->alloc;
    tl_page_builder_t pb;
    tl_page_builder_init(&pb, alloc, target_page_bytes);

    size_t cap = pb.records_per_page;
    size_t n_pages = (record_count + cap - 1) / cap;

    /* Reserve catalog space */
    tl_status_t st = tl_page_catalog_reserve(&seg->catalog, n_pages);
    if (st != TL_OK) {
        return st;
    }

    /* Build pages */
    size_t offset = 0;
    while (offset < record_count) {
        size_t chunk = record_count - offset;
        if (chunk > cap) {
            chunk = cap;
        }

        tl_page_t* page = NULL;
        st = tl_page_builder_build(&pb, &records[offset], chunk, &page);
        if (st != TL_OK) {
            goto rollback;
        }

        st = tl_page_catalog_push(&seg->catalog, page);
        if (st != TL_OK) {
            tl_page_destroy(page, alloc);
            goto rollback;
        }

        offset += chunk;
    }

    return TL_OK;

rollback:
    /*
     * Destroy all pages built so far. They're stored in the catalog
     * which the caller will destroy, but the catalog doesn't own pages.
     */
    for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
        tl_page_destroy(seg->catalog.pages[i].page, alloc);
    }
    seg->catalog.n_pages = 0;
    return st;
}

/*===========================================================================
 * L0 Segment Builder
 *===========================================================================*/

tl_status_t tl_segment_build_l0(tl_alloc_ctx_t* alloc,
                                 const tl_record_t* records, size_t record_count,
                                 const tl_interval_t* tombstones, size_t tombstones_len,
                                 size_t target_page_bytes,
                                 uint32_t generation,
                                 tl_segment_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    /* Must have either records or tombstones */
    if (record_count == 0 && tombstones_len == 0) {
        return TL_EINVAL;
    }

    /* Check tombstones_len overflow */
    if (tombstones_len > UINT32_MAX) {
        return TL_EINVAL;
    }

    /* Allocate segment */
    tl_segment_t* seg = TL_NEW(alloc, tl_segment_t);
    if (seg == NULL) {
        return TL_ENOMEM;
    }

    seg->alloc = alloc;
    seg->level = TL_SEG_L0;
    seg->generation = generation;
    seg->window_start = 0;
    seg->window_end = 0;
    seg->window_end_unbounded = false;  /* L0 doesn't use windows */
    tl_atomic_init_u32(&seg->refcnt, 1);

    /* Initialize catalog */
    tl_page_catalog_init(&seg->catalog, alloc);

    /* Create tombstones (copies the array) */
    tl_status_t st = create_tombstones(alloc, tombstones, tombstones_len, &seg->tombstones);
    if (st != TL_OK) {
        /*
         * Cleanup: destroy catalog for consistency with build_pages error path.
         * Note: catalog.pages is NULL at this point (no reserve called yet),
         * so destroy is a no-op. However, calling it maintains consistent
         * cleanup patterns and is defensive against future changes.
         */
        tl_page_catalog_destroy(&seg->catalog);
        TL_FREE(alloc, seg);
        return st;
    }

    /* Build pages if we have records */
    if (record_count > 0) {
        TL_ASSERT(records != NULL);
        st = build_pages(seg, records, record_count, target_page_bytes);
        if (st != TL_OK) {
            destroy_tombstones(seg->tombstones, alloc);
            tl_page_catalog_destroy(&seg->catalog);
            TL_FREE(alloc, seg);
            return st;
        }
    }

    /* Set counts */
    seg->record_count = (uint64_t)record_count;
    seg->page_count = seg->catalog.n_pages;

    /*
     * Compute bounds.
     *
     * L0 segment bounds must cover BOTH records AND tombstones.
     * This is required for correct query planning and compaction selection.
     * A read in range [A, B) must consider any L0 segment whose bounds
     * overlap [A, B), and tombstones affect what data is visible.
     */
    if (record_count > 0 && tombstones_len > 0) {
        /* Both records and tombstones: union of bounds */
        tl_ts_t rec_min = seg->catalog.pages[0].min_ts;
        tl_ts_t rec_max = seg->catalog.pages[seg->catalog.n_pages - 1].max_ts;

        tl_ts_t tomb_min, tomb_max;
        compute_tombstone_bounds(tombstones, tombstones_len, &tomb_min, &tomb_max);

        seg->min_ts = TL_MIN(rec_min, tomb_min);
        seg->max_ts = TL_MAX(rec_max, tomb_max);
    } else if (record_count > 0) {
        /* Records only: bounds from pages */
        seg->min_ts = seg->catalog.pages[0].min_ts;
        seg->max_ts = seg->catalog.pages[seg->catalog.n_pages - 1].max_ts;
    } else {
        /* Tombstone-only: bounds from tombstones */
        TL_ASSERT(tombstones_len > 0);
        compute_tombstone_bounds(tombstones, tombstones_len, &seg->min_ts, &seg->max_ts);
    }

    *out = seg;
    return TL_OK;
}

/*===========================================================================
 * L1 Segment Builder
 *===========================================================================*/

tl_status_t tl_segment_build_l1(tl_alloc_ctx_t* alloc,
                                 const tl_record_t* records, size_t record_count,
                                 size_t target_page_bytes,
                                 tl_ts_t window_start, tl_ts_t window_end,
                                 bool window_end_unbounded,
                                 uint32_t generation,
                                 tl_segment_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);
    /* Invariant: unbounded implies window_end == TL_TS_MAX */
    TL_ASSERT(!window_end_unbounded || window_end == TL_TS_MAX);

    /* L1 must have records */
    if (record_count == 0 || records == NULL) {
        return TL_EINVAL;
    }

    /* Allocate segment */
    tl_segment_t* seg = TL_NEW(alloc, tl_segment_t);
    if (seg == NULL) {
        return TL_ENOMEM;
    }

    seg->alloc = alloc;
    seg->level = TL_SEG_L1;
    seg->generation = generation;
    seg->window_start = window_start;
    seg->window_end = window_end;
    seg->window_end_unbounded = window_end_unbounded;
    seg->tombstones = NULL;  /* L1 never has tombstones */
    tl_atomic_init_u32(&seg->refcnt, 1);

    /* Initialize catalog */
    tl_page_catalog_init(&seg->catalog, alloc);

    /* Build pages */
    tl_status_t st = build_pages(seg, records, record_count, target_page_bytes);
    if (st != TL_OK) {
        tl_page_catalog_destroy(&seg->catalog);
        TL_FREE(alloc, seg);
        return st;
    }

    /* Set counts */
    seg->record_count = (uint64_t)record_count;
    seg->page_count = seg->catalog.n_pages;

    /* Bounds from pages */
    seg->min_ts = seg->catalog.pages[0].min_ts;
    seg->max_ts = seg->catalog.pages[seg->catalog.n_pages - 1].max_ts;

    *out = seg;
    return TL_OK;
}

/*===========================================================================
 * Reference Counting
 *===========================================================================*/

tl_segment_t* tl_segment_acquire(tl_segment_t* seg) {
    if (seg == NULL) {
        return NULL;
    }
    /* Relaxed is sufficient for increment: we already have a reference */
    tl_atomic_fetch_add_u32(&seg->refcnt, 1, TL_MO_RELAXED);
    return seg;
}

void tl_segment_release(tl_segment_t* seg) {
    if (seg == NULL) {
        return;
    }

    /*
     * Release ordering ensures all prior writes to segment data are visible
     * to the thread that will destroy the segment.
     */
    uint32_t old = tl_atomic_fetch_sub_u32(&seg->refcnt, 1, TL_MO_RELEASE);
    TL_ASSERT(old >= 1);

    if (old == 1) {
        /*
         * We're the last owner. Acquire fence synchronizes with all prior
         * releasers to ensure we see all their writes before destruction.
         */
        tl_atomic_fence(TL_MO_ACQUIRE);
        segment_destroy(seg);
    }
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/* Include for tl_intervals_arr_validate */
#include "../internal/tl_intervals.h"

/**
 * Validate segment invariants.
 *
 * L0 Invariants:
 * 1. window_start == window_end == 0
 * 2. Tombstones allowed (validated via shared validator)
 * 3. Bounds COVER both page bounds AND tombstone bounds
 *
 * L1 Invariants:
 * 1. tombstones MUST be NULL (not just n==0)
 * 2. window_start < window_end OR window_end == TL_TS_MAX (unbounded)
 * 3. Records within window: min_ts >= window_start, max_ts < window_end
 *    (except for unbounded window_end == TL_TS_MAX)
 * 4. Bounds EQUAL page bounds (no tombstones to widen)
 *
 * Common Invariants:
 * 1. Valid level (L0 or L1)
 * 2. min_ts <= max_ts
 * 3. Page catalog validates
 * 4. Record count matches sum of page counts
 * 5. page_count == catalog.n_pages
 */
bool tl_segment_validate(const tl_segment_t* seg) {
    if (seg == NULL) {
        return false;
    }

    /* Common: Check level is valid */
    if (seg->level != TL_SEG_L0 && seg->level != TL_SEG_L1) {
        return false;
    }

    /*
     * CRITICAL: Validate page_count == catalog.n_pages BEFORE any indexing.
     *
     * If a segment is corrupted with page_count > 0 but catalog.n_pages == 0,
     * we must detect this before attempting to access catalog.pages[0].
     * Validation should return false, not crash.
     */
    if (seg->page_count != seg->catalog.n_pages) {
        return false;
    }

    /*=========================================================================
     * L0-Specific Validation
     *=========================================================================*/
    if (seg->level == TL_SEG_L0) {
        /* L0: window bounds must be 0 */
        if (seg->window_start != 0 || seg->window_end != 0) {
            return false;
        }

        /* L0: validate tombstones if present (using shared validator) */
        if (seg->tombstones != NULL && seg->tombstones->n > 0) {
            if (!tl_intervals_arr_validate(seg->tombstones->v, seg->tombstones->n)) {
                return false;
            }
        }

        /*
         * L0: Compute required coverage bounds from BOTH pages AND tombstones.
         *
         * The segment's min_ts/max_ts must COVER all content - i.e., they must
         * be <= the minimum and >= the maximum of all pages and tombstones.
         *
         * IMPORTANT: We use an explicit has_content flag rather than sentinel
         * checks like (required_min != TL_TS_MAX) because TL_TS_MAX is a valid
         * timestamp. A segment with a single record at TL_TS_MAX must still
         * have its bounds validated.
         */
        bool has_content = false;
        tl_ts_t required_min = TL_TS_MAX;
        tl_ts_t required_max = TL_TS_MIN;

        /* Page bounds contribute to required coverage */
        if (seg->catalog.n_pages > 0) {
            const tl_page_meta_t* first = &seg->catalog.pages[0];
            const tl_page_meta_t* last = &seg->catalog.pages[seg->catalog.n_pages - 1];
            required_min = first->min_ts;
            required_max = last->max_ts;
            has_content = true;
        }

        /* Tombstone bounds ALSO contribute to required coverage */
        if (seg->tombstones != NULL && seg->tombstones->n > 0) {
            /* Minimum: first tombstone's start (tombstones are sorted) */
            tl_ts_t tomb_min = seg->tombstones->v[0].start;
            if (!has_content || tomb_min < required_min) {
                required_min = tomb_min;
            }

            /* Maximum: last tombstone's end (or TL_TS_MAX if unbounded) */
            const tl_interval_t* last_tomb = &seg->tombstones->v[seg->tombstones->n - 1];
            tl_ts_t tomb_max;
            if (last_tomb->end_unbounded) {
                tomb_max = TL_TS_MAX;
            } else {
                /* end is exclusive, max is inclusive: max_ts = end - 1 */
                tomb_max = last_tomb->end - 1;
            }
            if (!has_content || tomb_max > required_max) {
                required_max = tomb_max;
            }
            has_content = true;
        }

        /* L0: segment bounds must COVER all content */
        if (has_content) {
            if (seg->min_ts > required_min) {
                return false;  /* Segment min doesn't cover content min */
            }
            if (seg->max_ts < required_max) {
                return false;  /* Segment max doesn't cover content max */
            }
        }

        /* L0 tombstone-only: must have tombstones if no pages/records */
        if (seg->catalog.n_pages == 0 && seg->record_count == 0) {
            if (seg->tombstones == NULL || seg->tombstones->n == 0) {
                return false;
            }
        }
    }

    /*=========================================================================
     * L1-Specific Validation
     *=========================================================================*/
    else if (seg->level == TL_SEG_L1) {
        /*
         * L1: tombstones MUST be NULL (not just n==0)
         *
         * This is a strict invariant. L1 segments have tombstones folded
         * during compaction - the pointer itself should be NULL.
         */
        if (seg->tombstones != NULL) {
            return false;
        }

        /* L1: must have records */
        if (seg->record_count == 0) {
            return false;
        }

        /*
         * L1: window bounds validation
         *
         * Normal case: window_start < window_end
         * Unbounded-end: window_end_unbounded == true (covers all future timestamps)
         *
         * Invariant: window_end_unbounded implies window_end == TL_TS_MAX
         */
        if (seg->window_end_unbounded) {
            if (seg->window_end != TL_TS_MAX) {
                return false;  /* Invariant violation */
            }
        } else {
            if (seg->window_start >= seg->window_end) {
                return false;  /* Bounded window must have start < end */
            }
        }

        /* L1: records within window and bounds must EQUAL page bounds */
        if (seg->catalog.n_pages > 0) {
            /* min_ts must be >= window_start */
            if (seg->min_ts < seg->window_start) {
                return false;
            }

            /*
             * For bounded windows: max_ts must be < window_end (half-open interval)
             * For unbounded windows: no upper bound check needed
             */
            if (!seg->window_end_unbounded) {
                if (seg->max_ts >= seg->window_end) {
                    return false;
                }
            }

            /* L1: bounds must EQUAL page bounds (no tombstones to widen) */
            const tl_page_meta_t* first = &seg->catalog.pages[0];
            const tl_page_meta_t* last = &seg->catalog.pages[seg->catalog.n_pages - 1];

            if (seg->min_ts != first->min_ts) {
                return false;
            }
            if (seg->max_ts != last->max_ts) {
                return false;
            }
        }
    }

    /*=========================================================================
     * Common Validation
     *=========================================================================*/

    /* Common: min_ts <= max_ts */
    if (seg->min_ts > seg->max_ts) {
        return false;
    }

    /* page_count == catalog.n_pages already validated at function entry */

    /* Common: record count matches sum of page counts */
    uint64_t computed_records = 0;
    for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
        computed_records += seg->catalog.pages[i].count;
    }
    if (seg->record_count != computed_records) {
        return false;
    }

    /* Common: page catalog validates */
    if (!tl_page_catalog_validate(&seg->catalog)) {
        return false;
    }

    return true;
}

#endif /* TL_DEBUG */

/------------------------------------------------------------------------------/
/*   END OF: tl_segment.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_window.c
/*   FROM: storage/
/*
/******************************************************************************/
#include "tl_window.h"

/*===========================================================================
 * Default Window Size
 *===========================================================================*/

tl_ts_t tl_window_default_size(tl_time_unit_t unit) {
    tl_ts_t size = TL_WINDOW_1H_S; /* Default fallback */

    switch (unit) {
    case TL_TIME_S:  size = TL_WINDOW_1H_S;  break;
    case TL_TIME_MS: size = TL_WINDOW_1H_MS; break;
    case TL_TIME_US: size = TL_WINDOW_1H_US; break;
    case TL_TIME_NS: size = TL_WINDOW_1H_NS; break;
    default:
        TL_ASSERT(0 && "unknown time unit");
        break;
    }

    return size;
}

/*===========================================================================
 * Overflow-Safe Multiplication
 *
 * For window_start = window_origin + window_id * window_size, we need
 * to detect overflow in the multiplication and addition.
 *===========================================================================*/

/*
 * Overflow-safe signed multiplication.
 * Returns true if multiplication would overflow, false otherwise.
 * On success, stores result in *out.
 */
static bool mul_overflow_i64(int64_t a, int64_t b, int64_t* out) {
    /*
     * INT64_MIN = -9223372036854775808
     * INT64_MAX =  9223372036854775807
     *
     * Overflow cases:
     * 1. a > 0 && b > 0 && a > INT64_MAX / b
     * 2. a > 0 && b < 0 && b < INT64_MIN / a
     * 3. a < 0 && b > 0 && a < INT64_MIN / b
     * 4. a < 0 && b < 0 && a < INT64_MAX / b (both negative, result positive)
     * 5. Special case: INT64_MIN * -1 overflows (result would be INT64_MAX + 1)
     */

    /* Handle zero cases first (no overflow possible) */
    if (a == 0 || b == 0) {
        *out = 0;
        return false;
    }

    /* a > 0 */
    if (a > 0) {
        if (b > 0) {
            /* Both positive: check a * b > INT64_MAX */
            if (a > INT64_MAX / b) {
                return true; /* Overflow */
            }
        } else {
            /* a > 0, b < 0: check a * b < INT64_MIN */
            if (b < INT64_MIN / a) {
                return true; /* Underflow */
            }
        }
    } else {
        /* a < 0 */
        if (b > 0) {
            /* a < 0, b > 0: check a * b < INT64_MIN */
            if (a < INT64_MIN / b) {
                return true; /* Underflow */
            }
        } else {
            /* Both negative: check a * b > INT64_MAX */
            /* Special case: INT64_MIN / -1 would overflow */
            if (a == INT64_MIN || b == INT64_MIN) {
                /* INT64_MIN * anything < -1 overflows */
                if (a == INT64_MIN && b < -1) return true;
                if (b == INT64_MIN && a < -1) return true;
            }
            if (a < INT64_MAX / b) {
                return true; /* Overflow (result would be too large positive) */
            }
        }
    }

    *out = a * b;
    return false;
}

/*
 * Overflow-safe signed addition.
 * Returns true if addition would overflow, false otherwise.
 * On success, stores result in *out.
 */
static bool add_overflow_i64(int64_t a, int64_t b, int64_t* out) {
    /*
     * Overflow cases:
     * 1. a > 0 && b > 0 && a > INT64_MAX - b (positive overflow)
     * 2. a < 0 && b < 0 && a < INT64_MIN - b (negative overflow)
     */
    if (b > 0 && a > INT64_MAX - b) {
        return true; /* Positive overflow */
    }
    if (b < 0 && a < INT64_MIN - b) {
        return true; /* Negative overflow */
    }

    *out = a + b;
    return false;
}

/*===========================================================================
 * Window ID Computation
 *===========================================================================*/

tl_status_t tl_window_id_for_ts(tl_ts_t ts, tl_ts_t window_size,
                                 tl_ts_t window_origin, int64_t* out_id) {
    TL_ASSERT(window_size > 0);
    TL_ASSERT(out_id != NULL);

    /*
     * Use floor division for correct behavior with negative numerators.
     * But first, compute ts - window_origin with overflow checking.
     *
     * Example with window_size=10, window_origin=0:
     *   ts = 9  => floor(9/10) = 0
     *   ts = 10 => floor(10/10) = 1
     *   ts = -1 => floor(-1/10) = -1 (C gives 0, wrong)
     *   ts = -10 => floor(-10/10) = -1 (C gives -1, correct)
     *   ts = -11 => floor(-11/10) = -2 (C gives -1, wrong)
     */
    int64_t diff;
    if (tl_sub_overflow_i64(ts, window_origin, &diff)) {
        /* Overflow in subtraction - this is an edge case with extreme values */
        return TL_EOVERFLOW;
    }

    *out_id = tl_floor_div_i64(diff, window_size);
    return TL_OK;
}

/*===========================================================================
 * Window Bounds Computation
 *===========================================================================*/

void tl_window_bounds(int64_t window_id, tl_ts_t window_size, tl_ts_t window_origin,
                      tl_ts_t* out_start, tl_ts_t* out_end, bool* end_unbounded) {
    TL_ASSERT(window_size > 0);
    TL_ASSERT(out_start != NULL);
    TL_ASSERT(out_end != NULL);
    TL_ASSERT(end_unbounded != NULL);

    /*
     * window_start = window_origin + window_id * window_size
     * window_end   = window_start + window_size
     *
     * We need to handle overflow at each step.
     * If window_end overflows, we mark it as unbounded.
     */

    int64_t product;
    int64_t start;
    int64_t end;

    /* Step 1: window_id * window_size */
    if (mul_overflow_i64(window_id, window_size, &product)) {
        /* Overflow in multiplication */
        if (window_id > 0) {
            /* Large positive window_id: saturate to max */
            *out_start = TL_TS_MAX;
            *out_end = TL_TS_MAX;
            *end_unbounded = true;
        } else {
            /* Large negative window_id: saturate to min */
            *out_start = TL_TS_MIN;
            *out_end = TL_TS_MIN;
            *end_unbounded = false;
        }
        return;
    }

    /* Step 2: window_origin + product */
    if (add_overflow_i64(window_origin, product, &start)) {
        /* Overflow in addition */
        if (product > 0) {
            *out_start = TL_TS_MAX;
            *out_end = TL_TS_MAX;
            *end_unbounded = true;
        } else {
            *out_start = TL_TS_MIN;
            *out_end = TL_TS_MIN;
            *end_unbounded = false;
        }
        return;
    }

    /* Step 3: start + window_size */
    if (add_overflow_i64(start, window_size, &end)) {
        /*
         * window_end would overflow - this is the "last window" case.
         * The window is [start, +infinity) conceptually.
         * We represent this with end = TL_TS_MAX and end_unbounded = true.
         */
        *out_start = start;
        *out_end = TL_TS_MAX;
        *end_unbounded = true;
        return;
    }

    *out_start = start;
    *out_end = end;
    *end_unbounded = false;
}

/*===========================================================================
 * Window Bounds for Timestamp
 *===========================================================================*/

tl_status_t tl_window_bounds_for_ts(tl_ts_t ts, tl_ts_t window_size,
                                     tl_ts_t window_origin,
                                     tl_ts_t* out_start, tl_ts_t* out_end,
                                     bool* end_unbounded) {
    int64_t wid;
    tl_status_t status = tl_window_id_for_ts(ts, window_size, window_origin, &wid);
    if (status != TL_OK) {
        return status;
    }
    tl_window_bounds(wid, window_size, window_origin, out_start, out_end, end_unbounded);
    return TL_OK;
}

/------------------------------------------------------------------------------/
/*   END OF: tl_window.c
/------------------------------------------------------------------------------/
