#include "tl_memrun.h"

/*===========================================================================
 * Bounds Computation (M-11: Public for reuse)
 *
 * CRITICAL: Bounds MUST include tombstones, not just records.
 * This ensures tombstones outside record bounds are NOT pruned during
 * read-path overlap checks (which would cause missed deletes).
 *===========================================================================*/

void tl__memrun_compute_bounds(tl_memrun_t* mr) {
    /* Start with invalid bounds */
    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;

    /* Record bounds from run (sorted, so first/last are min/max) */
    if (mr->run_len > 0) {
        min_ts = TL_MIN(min_ts, mr->run[0].ts);
        max_ts = TL_MAX(max_ts, mr->run[mr->run_len - 1].ts);
    }

    /* Record bounds from OOO runs (precomputed min/max) */
    if (mr->ooo_total_len > 0) {
        min_ts = TL_MIN(min_ts, mr->ooo_min_ts);
        max_ts = TL_MAX(max_ts, mr->ooo_max_ts);
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
tl_status_t tl_memrun_init(tl_memrun_t* mr,
                            tl_alloc_ctx_t* alloc,
                            tl_record_t* run, size_t run_len,
                            tl_ooorunset_t* ooo_runs,
                            tl_interval_t* tombs, size_t tombs_len,
                            tl_seq_t applied_seq) {
    if (mr == NULL || alloc == NULL) {
        return TL_EINVAL;
    }
    if (run_len == 0 && ooo_runs == NULL && tombs_len == 0) {
        return TL_EINVAL;
    }
    if (run_len > 0 && run == NULL) {
        return TL_EINVAL;
    }
    if (ooo_runs != NULL && ooo_runs->count == 0) {
        return TL_EINVAL;
    }
    if (tombs_len > 0 && tombs == NULL) {
        return TL_EINVAL;
    }

    /* Take ownership of arrays */
    mr->run = run;
    mr->run_len = run_len;
    mr->ooo_runs = ooo_runs;
    mr->ooo_total_len = (ooo_runs == NULL) ? 0 : ooo_runs->total_len;
    mr->ooo_run_count = (ooo_runs == NULL) ? 0 : ooo_runs->count;
    mr->ooo_min_ts = TL_TS_MAX;
    mr->ooo_max_ts = TL_TS_MIN;
    mr->tombs = tombs;
    mr->tombs_len = tombs_len;
    mr->applied_seq = applied_seq;

    /* Store allocator */
    mr->alloc = alloc;

    /* Initialize reference count to 1 (caller owns) */
    tl_atomic_init_u32(&mr->refcnt, 1);

    if (mr->ooo_total_len > 0) {
        for (size_t i = 0; i < mr->ooo_run_count; i++) {
            const tl_ooorun_t* run_ptr = mr->ooo_runs->runs[i];
            mr->ooo_min_ts = TL_MIN(mr->ooo_min_ts, run_ptr->min_ts);
            mr->ooo_max_ts = TL_MAX(mr->ooo_max_ts, run_ptr->max_ts);
        }
    }

    /* Compute bounds (includes tombstones) */
    tl__memrun_compute_bounds(mr);
    return TL_OK;
}

tl_status_t tl_memrun_create(tl_alloc_ctx_t* alloc,
                              tl_record_t* run, size_t run_len,
                              tl_ooorunset_t* ooo_runs,
                              tl_interval_t* tombs, size_t tombs_len,
                              tl_seq_t applied_seq,
                              tl_memrun_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    /* All empty is invalid */
    if (run_len == 0 && ooo_runs == NULL && tombs_len == 0) {
        return TL_EINVAL;
    }
    if (run_len > 0 && run == NULL) {
        return TL_EINVAL;
    }
    if (ooo_runs != NULL && ooo_runs->count == 0) {
        return TL_EINVAL;
    }
    if (tombs_len > 0 && tombs == NULL) {
        return TL_EINVAL;
    }

    tl_memrun_t* mr = NULL;
    tl_status_t st = tl_memrun_alloc(alloc, &mr);
    if (st != TL_OK) {
        return st;
    }

    st = tl_memrun_init(mr, alloc, run, run_len, ooo_runs, tombs, tombs_len,
                        applied_seq);
    if (st != TL_OK) {
        tl__free(alloc, mr);
        return st;
    }

    *out = mr;
    return TL_OK;
}

tl_status_t tl_memrun_alloc(tl_alloc_ctx_t* alloc, tl_memrun_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    tl_memrun_t* mr = TL_NEW(alloc, tl_memrun_t);
    if (mr == NULL) {
        return TL_ENOMEM;
    }

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
        if (mr->ooo_runs != NULL) {
            tl_ooorunset_release(mr->ooo_runs);
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
static bool is_records_sorted_ts(const tl_record_t* arr, size_t len) {
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

static bool is_records_sorted_ts_handle(const tl_record_t* arr, size_t len) {
    if (len <= 1) {
        return true;
    }
    for (size_t i = 0; i < len - 1; i++) {
        if (arr[i].ts > arr[i + 1].ts) {
            return false;
        }
        if (arr[i].ts == arr[i + 1].ts &&
            arr[i].handle > arr[i + 1].handle) {
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

        /* Must not be adjacent with same max_seq (should be coalesced) */
        if (curr->end == next->start && curr->max_seq == next->max_seq) {
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
    if (mr->run_len == 0 && mr->ooo_total_len == 0 && mr->tombs_len == 0) {
        return false;
    }

    /* Check run sorted by ts (handle order is unspecified for in-order path) */
    if (!is_records_sorted_ts(mr->run, mr->run_len)) {
        return false;
    }

    /* Check OOO runset */
    if (mr->ooo_total_len > 0) {
        if (mr->ooo_runs == NULL || mr->ooo_run_count == 0) {
            return false;
        }
        if (mr->ooo_run_count != mr->ooo_runs->count) {
            return false;
        }
        size_t total = 0;
        uint64_t last_gen = 0;
        bool have_gen = false;
        tl_ts_t min_ts = TL_TS_MAX;
        tl_ts_t max_ts = TL_TS_MIN;

        for (size_t i = 0; i < mr->ooo_run_count; i++) {
            const tl_ooorun_t* run = mr->ooo_runs->runs[i];
            if (run == NULL) {
                return false;
            }
            if (!is_records_sorted_ts_handle(run->records, run->len)) {
                return false;
            }
            if (have_gen && run->gen < last_gen) {
                return false;
            }
            have_gen = true;
            last_gen = run->gen;

            if (run->len > SIZE_MAX - total) {
                return false;
            }
            total += run->len;

            min_ts = TL_MIN(min_ts, run->min_ts);
            max_ts = TL_MAX(max_ts, run->max_ts);
        }

        if (total != mr->ooo_total_len) {
            return false;
        }
        if (min_ts != mr->ooo_min_ts || max_ts != mr->ooo_max_ts) {
            return false;
        }
    } else if (mr->ooo_runs != NULL || mr->ooo_run_count != 0) {
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
    if (mr->ooo_total_len > 0) {
        expected_min = TL_MIN(expected_min, mr->ooo_min_ts);
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
    if (mr->ooo_total_len > 0) {
        expected_max = TL_MAX(expected_max, mr->ooo_max_ts);
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
