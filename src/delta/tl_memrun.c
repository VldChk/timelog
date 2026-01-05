#include "tl_memrun.h"

/*===========================================================================
 * Internal: Bounds Computation
 *
 * CRITICAL: Bounds MUST include tombstones, not just records.
 * This ensures tombstones outside record bounds are NOT pruned during
 * read-path overlap checks (which would cause missed deletes).
 *===========================================================================*/

static void compute_bounds(tl_memrun_t* mr) {
    /* Start with invalid bounds */
    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;

    /* Record bounds from run (sorted, so first/last are min/max) */
    if (mr->run_len > 0) {
        min_ts = TL_MIN(min_ts, mr->run[0].ts);
        max_ts = TL_MAX(max_ts, mr->run[mr->run_len - 1].ts);
    }

    /* Record bounds from ooo (sorted, so first/last are min/max) */
    if (mr->ooo_len > 0) {
        min_ts = TL_MIN(min_ts, mr->ooo[0].ts);
        max_ts = TL_MAX(max_ts, mr->ooo[mr->ooo_len - 1].ts);
    }

    /* Tombstone bounds (CRITICAL for read-path correctness) */
    for (size_t i = 0; i < mr->tombs_len; i++) {
        const tl_interval_t* tomb = &mr->tombs[i];
        min_ts = TL_MIN(min_ts, tomb->start);

        if (tomb->end_unbounded) {
            /* Unbounded tombstone [start, +inf) => max_ts = TL_TS_MAX */
            max_ts = TL_TS_MAX;
        } else {
            /* Bounded tombstone [start, end) => max covered ts is end-1 */
            max_ts = TL_MAX(max_ts, tomb->end - 1);
        }
    }

    mr->min_ts = min_ts;
    mr->max_ts = max_ts;
}

/*===========================================================================
 * Creation
 *===========================================================================*/

/**
 * Initialize a pre-allocated memrun in-place.
 *
 * Takes ownership of the provided arrays (run, ooo, tombs).
 * Caller must ensure at least one array is non-empty.
 * Sets refcnt to 1.
 */
static void memrun_init_inplace(tl_memrun_t* mr,
                                 tl_alloc_ctx_t* alloc,
                                 tl_record_t* run, size_t run_len,
                                 tl_record_t* ooo, size_t ooo_len,
                                 tl_interval_t* tombs, size_t tombs_len) {
    TL_ASSERT(mr != NULL);
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(run_len > 0 || ooo_len > 0 || tombs_len > 0);

    /* Null-check arrays when length is non-zero */
    TL_ASSERT(run_len == 0 || run != NULL);
    TL_ASSERT(ooo_len == 0 || ooo != NULL);
    TL_ASSERT(tombs_len == 0 || tombs != NULL);

    /* Take ownership of arrays */
    mr->run = run;
    mr->run_len = run_len;
    mr->ooo = ooo;
    mr->ooo_len = ooo_len;
    mr->tombs = tombs;
    mr->tombs_len = tombs_len;

    /* Store allocator */
    mr->alloc = alloc;

    /* Initialize reference count to 1 (caller owns) */
    tl_atomic_init_u32(&mr->refcnt, 1);

    /* Compute bounds (includes tombstones) */
    compute_bounds(mr);
}

tl_status_t tl_memrun_create(tl_alloc_ctx_t* alloc,
                              tl_record_t* run, size_t run_len,
                              tl_record_t* ooo, size_t ooo_len,
                              tl_interval_t* tombs, size_t tombs_len,
                              tl_memrun_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    /* All empty is invalid */
    if (run_len == 0 && ooo_len == 0 && tombs_len == 0) {
        return TL_EINVAL;
    }

    /* Allocate memrun struct */
    tl_memrun_t* mr = TL_NEW(alloc, tl_memrun_t);
    if (mr == NULL) {
        /* Arrays NOT freed - caller retains ownership */
        return TL_ENOMEM;
    }

    /* Initialize in-place */
    memrun_init_inplace(mr, alloc, run, run_len, ooo, ooo_len, tombs, tombs_len);

    *out = mr;
    return TL_OK;
}

/*===========================================================================
 * Reference Counting
 *===========================================================================*/

tl_memrun_t* tl_memrun_acquire(tl_memrun_t* mr) {
    if (mr == NULL) {
        return NULL;
    }

    /* Relaxed: we already have a reference, so no ordering needed for increment */
    tl_atomic_fetch_add_u32(&mr->refcnt, 1, TL_MO_RELAXED);
    return mr;
}

void tl_memrun_release(tl_memrun_t* mr) {
    if (mr == NULL) {
        return;
    }

    /* Release ordering: ensure all prior writes are visible before potential destruction */
    uint32_t old = tl_atomic_fetch_sub_u32(&mr->refcnt, 1, TL_MO_RELEASE);

    if (old == 1) {
        /* Acquire fence: synchronize with all releasers before destruction */
        tl_atomic_fence(TL_MO_ACQUIRE);

        /* Free owned arrays */
        if (mr->run != NULL) {
            tl__free(mr->alloc, mr->run);
        }
        if (mr->ooo != NULL) {
            tl__free(mr->alloc, mr->ooo);
        }
        if (mr->tombs != NULL) {
            tl__free(mr->alloc, mr->tombs);
        }

        /* Free memrun struct */
        tl__free(mr->alloc, mr);
    }
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/**
 * Check if record array is sorted by timestamp (non-decreasing).
 */
static bool is_records_sorted(const tl_record_t* arr, size_t len) {
    if (len <= 1) {
        return true;
    }
    for (size_t i = 0; i < len - 1; i++) {
        if (arr[i].ts > arr[i + 1].ts) {
            return false;
        }
    }
    return true;
}

/**
 * Check if tombstone array is sorted, non-overlapping, and coalesced.
 */
static bool is_tombs_valid(const tl_interval_t* arr, size_t len) {
    if (len <= 1) {
        return true;
    }
    for (size_t i = 0; i < len - 1; i++) {
        const tl_interval_t* curr = &arr[i];
        const tl_interval_t* next = &arr[i + 1];

        /* Must be sorted by start */
        if (curr->start > next->start) {
            return false;
        }

        /* If current is unbounded, nothing should follow */
        if (curr->end_unbounded) {
            return false;
        }

        /* Must not overlap: curr->end <= next->start */
        if (curr->end > next->start) {
            return false;
        }

        /* Must not be adjacent (should be coalesced): curr->end < next->start */
        if (curr->end == next->start) {
            return false;
        }
    }
    return true;
}

bool tl_memrun_validate(const tl_memrun_t* mr) {
    if (mr == NULL) {
        return false;
    }

    /* Reference count must be positive */
    if (tl_memrun_refcnt(mr) == 0) {
        return false;
    }

    /* At least one component must be non-empty */
    if (mr->run_len == 0 && mr->ooo_len == 0 && mr->tombs_len == 0) {
        return false;
    }

    /* Check run sorted */
    if (!is_records_sorted(mr->run, mr->run_len)) {
        return false;
    }

    /* Check ooo sorted */
    if (!is_records_sorted(mr->ooo, mr->ooo_len)) {
        return false;
    }

    /* Check tombs valid */
    if (!is_tombs_valid(mr->tombs, mr->tombs_len)) {
        return false;
    }

    /* Verify min_ts */
    tl_ts_t expected_min = TL_TS_MAX;
    if (mr->run_len > 0) {
        expected_min = TL_MIN(expected_min, mr->run[0].ts);
    }
    if (mr->ooo_len > 0) {
        expected_min = TL_MIN(expected_min, mr->ooo[0].ts);
    }
    for (size_t i = 0; i < mr->tombs_len; i++) {
        expected_min = TL_MIN(expected_min, mr->tombs[i].start);
    }
    if (mr->min_ts != expected_min) {
        return false;
    }

    /* Verify max_ts */
    tl_ts_t expected_max = TL_TS_MIN;
    if (mr->run_len > 0) {
        expected_max = TL_MAX(expected_max, mr->run[mr->run_len - 1].ts);
    }
    if (mr->ooo_len > 0) {
        expected_max = TL_MAX(expected_max, mr->ooo[mr->ooo_len - 1].ts);
    }
    for (size_t i = 0; i < mr->tombs_len; i++) {
        const tl_interval_t* tomb = &mr->tombs[i];
        if (tomb->end_unbounded) {
            expected_max = TL_TS_MAX;
        } else {
            expected_max = TL_MAX(expected_max, tomb->end - 1);
        }
    }
    if (mr->max_ts != expected_max) {
        return false;
    }

    return true;
}

#endif /* TL_DEBUG */
