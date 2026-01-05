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
        tl_segment_t* target = remove_arr[i];

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

    /* Copy L1 from base (excluding removals), then add new */
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
         * If the previous window was unbounded (window_end == TL_TS_MAX),
         * there MUST NOT be any more segments after it. An unbounded window
         * covers all future timestamps, so any subsequent segment is invalid.
         */
        if (prev_window_end == TL_TS_MAX) {
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
