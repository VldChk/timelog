#include "tl_memview.h"
#include "../internal/tl_range.h"
#include "../internal/tl_locks.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Update bounds with a record array.
 * Assumes records are sorted by timestamp.
 */
static void update_bounds_from_records(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                        bool* has_data,
                                        const tl_record_t* data, size_t len) {
    if (len == 0) {
        return;
    }

    tl_ts_t rec_min = data[0].ts;
    tl_ts_t rec_max = data[len - 1].ts;

    if (!*has_data) {
        *min_ts = rec_min;
        *max_ts = rec_max;
        *has_data = true;
    } else {
        if (rec_min < *min_ts) *min_ts = rec_min;
        if (rec_max > *max_ts) *max_ts = rec_max;
    }
}

/**
 * Update bounds with tombstone intervals.
 * Tombstones contribute to bounds per read-path overlap rules.
 */
static void update_bounds_from_tombs(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                      bool* has_data,
                                      const tl_interval_t* data, size_t len) {
    if (len == 0) {
        return;
    }

    /* Min is first interval's start (intervals are sorted by start) */
    tl_ts_t tomb_min = data[0].start;

    /* Max is determined by last interval's end (or TL_TS_MAX if unbounded) */
    const tl_interval_t* last = &data[len - 1];
    tl_ts_t tomb_max;
    if (last->end_unbounded) {
        tomb_max = TL_TS_MAX;
    } else {
        /*
         * Tombstone [start, end) covers timestamps up to end-1.
         * For overlap checking, we use end-1 as the max bound.
         * However, we must be careful: if end == TL_TS_MIN (impossible
         * for a valid interval), subtracting would underflow.
         * Valid intervals have start < end, so end > TL_TS_MIN.
         */
        tomb_max = last->end - 1;
    }

    if (!*has_data) {
        *min_ts = tomb_min;
        *max_ts = tomb_max;
        *has_data = true;
    } else {
        if (tomb_min < *min_ts) *min_ts = tomb_min;
        if (tomb_max > *max_ts) *max_ts = tomb_max;
    }
}

/**
 * Update bounds from a memrun.
 */
static void update_bounds_from_memrun(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                       bool* has_data,
                                       const tl_memrun_t* mr) {
    /*
     * Memrun has precomputed bounds that already include tombstones.
     * However, we need to check if it has data first.
     */
    bool mr_has_records = tl_memrun_has_records(mr);
    bool mr_has_tombs = tl_memrun_has_tombstones(mr);

    if (!mr_has_records && !mr_has_tombs) {
        return;
    }

    tl_ts_t mr_min = tl_memrun_min_ts(mr);
    tl_ts_t mr_max = tl_memrun_max_ts(mr);

    if (!*has_data) {
        *min_ts = mr_min;
        *max_ts = mr_max;
        *has_data = true;
    } else {
        if (mr_min < *min_ts) *min_ts = mr_min;
        if (mr_max > *max_ts) *max_ts = mr_max;
    }
}

/**
 * Deep-copy a record array.
 * Returns NULL on allocation failure or if len == 0.
 */
static tl_record_t* copy_records(tl_alloc_ctx_t* alloc,
                                  const tl_record_t* src, size_t len) {
    if (len == 0 || src == NULL) {
        return NULL;
    }

    size_t bytes = len * sizeof(tl_record_t);
    tl_record_t* dst = tl__malloc(alloc, bytes);
    if (dst == NULL) {
        return NULL;
    }

    memcpy(dst, src, bytes);
    return dst;
}

/**
 * Deep-copy an interval array.
 * Returns NULL on allocation failure or if len == 0.
 */
static tl_interval_t* copy_intervals(tl_alloc_ctx_t* alloc,
                                      const tl_interval_t* src, size_t len) {
    if (len == 0 || src == NULL) {
        return NULL;
    }

    size_t bytes = len * sizeof(tl_interval_t);
    tl_interval_t* dst = tl__malloc(alloc, bytes);
    if (dst == NULL) {
        return NULL;
    }

    memcpy(dst, src, bytes);
    return dst;
}

/**
 * Allocate and populate sealed memrun array.
 * Acquires references to each memrun.
 * On failure, releases any already-acquired references.
 */
static tl_status_t copy_sealed_memruns(tl_memview_t* mv,
                                        tl_memtable_t* mt,
                                        tl_mutex_t* memtable_mu) {
    /*
     * Lock memtable_mu to safely access the sealed queue.
     * We need to:
     * 1. Read sealed_len
     * 2. Allocate array
     * 3. Acquire each memrun
     * All under the lock to ensure the queue doesn't change.
     *
     * Use TL_LOCK for debug-mode lock ordering validation.
     */
    TL_LOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);

    size_t len = mt->sealed_len;
    if (len == 0) {
        mv->sealed = NULL;
        mv->sealed_len = 0;
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        return TL_OK;
    }

    /* Allocate array */
    mv->sealed = tl__malloc(mv->alloc, len * sizeof(tl_memrun_t*));
    if (mv->sealed == NULL) {
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        return TL_ENOMEM;
    }

    /* Copy pointers and acquire each memrun */
    for (size_t i = 0; i < len; i++) {
        mv->sealed[i] = tl_memrun_acquire(mt->sealed[i]);
    }
    mv->sealed_len = len;

    TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
    return TL_OK;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_memview_capture(tl_memview_t* mv,
                                tl_memtable_t* mt,
                                tl_mutex_t* memtable_mu,
                                tl_alloc_ctx_t* alloc) {
    TL_ASSERT(mv != NULL);
    TL_ASSERT(mt != NULL);
    TL_ASSERT(memtable_mu != NULL);
    TL_ASSERT(alloc != NULL);

    /* Initialize to empty state */
    memset(mv, 0, sizeof(*mv));
    mv->alloc = alloc;
    mv->has_data = false;

    tl_status_t status;

    /*
     * Step 1: Copy active buffers.
     * Caller holds writer_mu which protects active state.
     */

    /* Copy active_run */
    size_t run_len = tl_memtable_run_len(mt);
    if (run_len > 0) {
        mv->active_run = copy_records(alloc, tl_memtable_run_data(mt), run_len);
        if (mv->active_run == NULL) {
            status = TL_ENOMEM;
            goto fail;
        }
        mv->active_run_len = run_len;
    }

    /* Copy active_ooo */
    size_t ooo_len = tl_memtable_ooo_len(mt);
    if (ooo_len > 0) {
        mv->active_ooo = copy_records(alloc, tl_memtable_ooo_data(mt), ooo_len);
        if (mv->active_ooo == NULL) {
            status = TL_ENOMEM;
            goto fail;
        }
        mv->active_ooo_len = ooo_len;
    }

    /* Copy active_tombs */
    tl_intervals_imm_t tombs_imm = tl_memtable_tombs_imm(mt);
    if (tombs_imm.len > 0) {
        mv->active_tombs = copy_intervals(alloc, tombs_imm.data, tombs_imm.len);
        if (mv->active_tombs == NULL) {
            status = TL_ENOMEM;
            goto fail;
        }
        mv->active_tombs_len = tombs_imm.len;
    }

    /*
     * Step 2: Pin sealed memruns.
     * This function locks memtable_mu internally.
     */
    status = copy_sealed_memruns(mv, mt, memtable_mu);
    if (status != TL_OK) {
        goto fail;
    }

    /*
     * Step 3: Compute bounds.
     * Include records AND tombstones per read-path overlap rules.
     */
    update_bounds_from_records(&mv->min_ts, &mv->max_ts, &mv->has_data,
                               mv->active_run, mv->active_run_len);
    update_bounds_from_records(&mv->min_ts, &mv->max_ts, &mv->has_data,
                               mv->active_ooo, mv->active_ooo_len);
    update_bounds_from_tombs(&mv->min_ts, &mv->max_ts, &mv->has_data,
                             mv->active_tombs, mv->active_tombs_len);

    for (size_t i = 0; i < mv->sealed_len; i++) {
        update_bounds_from_memrun(&mv->min_ts, &mv->max_ts, &mv->has_data,
                                  mv->sealed[i]);
    }

    return TL_OK;

fail:
    tl_memview_destroy(mv);
    return status;
}

void tl_memview_destroy(tl_memview_t* mv) {
    if (mv == NULL) {
        return;
    }

    /* Free copied active buffers */
    if (mv->active_run != NULL) {
        tl__free(mv->alloc, mv->active_run);
        mv->active_run = NULL;
    }
    mv->active_run_len = 0;

    if (mv->active_ooo != NULL) {
        tl__free(mv->alloc, mv->active_ooo);
        mv->active_ooo = NULL;
    }
    mv->active_ooo_len = 0;

    if (mv->active_tombs != NULL) {
        tl__free(mv->alloc, mv->active_tombs);
        mv->active_tombs = NULL;
    }
    mv->active_tombs_len = 0;

    /* Release pinned sealed memruns */
    if (mv->sealed != NULL) {
        for (size_t i = 0; i < mv->sealed_len; i++) {
            if (mv->sealed[i] != NULL) {
                tl_memrun_release(mv->sealed[i]);
            }
        }
        tl__free(mv->alloc, mv->sealed);
        mv->sealed = NULL;
    }
    mv->sealed_len = 0;

    /* Reset bounds */
    mv->min_ts = 0;
    mv->max_ts = 0;
    mv->has_data = false;
}

/*===========================================================================
 * Shared Memview (Snapshot Cache)
 *===========================================================================*/

tl_status_t tl_memview_shared_capture(tl_memview_shared_t** out,
                                       tl_memtable_t* mt,
                                       tl_mutex_t* memtable_mu,
                                       tl_alloc_ctx_t* alloc,
                                       uint64_t epoch) {
    TL_ASSERT(out != NULL);
    TL_ASSERT(mt != NULL);
    TL_ASSERT(memtable_mu != NULL);
    TL_ASSERT(alloc != NULL);

    *out = NULL;

    tl_memview_shared_t* mv = TL_NEW(alloc, tl_memview_shared_t);
    if (mv == NULL) {
        return TL_ENOMEM;
    }

    memset(mv, 0, sizeof(*mv));
    mv->epoch = epoch;
    tl_atomic_init_u32(&mv->refcnt, 1);

    tl_status_t st = tl_memview_capture(&mv->view, mt, memtable_mu, alloc);
    if (st != TL_OK) {
        tl__free(alloc, mv);
        return st;
    }

    *out = mv;
    return TL_OK;
}

tl_memview_shared_t* tl_memview_shared_acquire(tl_memview_shared_t* mv) {
    if (mv == NULL) {
        return NULL;
    }

    tl_atomic_fetch_add_u32(&mv->refcnt, 1, TL_MO_RELAXED);
    return mv;
}

void tl_memview_shared_release(tl_memview_shared_t* mv) {
    if (mv == NULL) {
        return;
    }

    uint32_t old = tl_atomic_fetch_sub_u32(&mv->refcnt, 1, TL_MO_RELEASE);
    TL_ASSERT(old >= 1);

    if (old == 1) {
        tl_atomic_fence(TL_MO_ACQUIRE);
        tl_memview_destroy(&mv->view);
        tl__free(mv->view.alloc, mv);
    }
}

/*===========================================================================
 * Query Support
 *===========================================================================*/

bool tl_memview_overlaps(const tl_memview_t* mv, tl_ts_t t1, tl_ts_t t2,
                         bool t2_unbounded) {
    TL_ASSERT(mv != NULL);

    if (!mv->has_data) {
        return false;
    }

    /*
     * Use tl_range_overlaps from tl_range.h.
     * Memview bounds are [min_ts, max_ts] (inclusive).
     * Query range is [t1, t2) or [t1, +inf).
     */
    return tl_range_overlaps(mv->min_ts, mv->max_ts, t1, t2, t2_unbounded);
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/* Include for tl_intervals_arr_validate */
#include "../internal/tl_intervals.h"

/**
 * Validate memview invariants.
 *
 * Invariants:
 * 1. active_run is sorted (non-decreasing timestamps)
 * 2. active_ooo is sorted (non-decreasing timestamps)
 * 3. active_tombs is valid (sorted, non-overlapping, coalesced)
 * 4. sealed memrun pointers non-NULL
 * 5. has_data consistent with actual content
 */
bool tl_memview_validate(const tl_memview_t* mv) {
    if (mv == NULL) {
        return false;
    }

    /*
     * Invariant 1: active_run is sorted (non-decreasing timestamps)
     *
     * Use accessor functions for encapsulation.
     */
    const tl_record_t* run = tl_memview_run_data(mv);
    size_t run_len = tl_memview_run_len(mv);
    for (size_t i = 1; i < run_len; i++) {
        if (run[i].ts < run[i - 1].ts) {
            return false;
        }
    }

    /*
     * Invariant 2: active_ooo is sorted (non-decreasing timestamps)
     */
    const tl_record_t* ooo = tl_memview_ooo_data(mv);
    size_t ooo_len = tl_memview_ooo_len(mv);
    for (size_t i = 1; i < ooo_len; i++) {
        if (ooo[i].ts < ooo[i - 1].ts) {
            return false;
        }
    }

    /*
     * Invariant 3: active_tombs is valid
     *
     * Uses the shared tl_intervals_arr_validate() function.
     */
    const tl_interval_t* tombs = tl_memview_tomb_data(mv);
    size_t tombs_len = tl_memview_tomb_len(mv);
    if (!tl_intervals_arr_validate(tombs, tombs_len)) {
        return false;
    }

    /*
     * Invariant 4: sealed memrun pointers non-NULL
     */
    size_t sealed_len = tl_memview_sealed_len(mv);
    for (size_t i = 0; i < sealed_len; i++) {
        if (tl_memview_sealed_get(mv, i) == NULL) {
            return false;
        }
    }

    /*
     * Invariant 5: has_data consistency
     *
     * If has_data is true, there must be some content.
     * Content can be: records in run, records in ooo, tombstones, or sealed memruns.
     */
    if (tl_memview_has_data(mv)) {
        bool has_content = (run_len > 0 || ooo_len > 0 ||
                           tombs_len > 0 || sealed_len > 0);
        if (!has_content) {
            return false;  /* has_data true but no content */
        }
    }

    return true;
}

#endif /* TL_DEBUG */
