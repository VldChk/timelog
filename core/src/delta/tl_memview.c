#include "tl_memview.h"
#include "../internal/tl_refcount.h"
#include "../internal/tl_range.h"
#include "../internal/tl_locks.h"
#include "../internal/tl_records.h"
#include "../internal/tl_recvec.h"
#include <stdlib.h>  /* qsort */
#include <string.h>

/* Test hooks let unit tests force the capture path into its retry/fallback
 * branches that are otherwise hard to reach under normal scheduling. */
#ifdef TL_TEST_HOOKS
volatile int tl_test_memview_force_retry_count = 0;
volatile int tl_test_memview_used_fallback = 0;
#endif

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

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

static void update_bounds_from_records_unsorted(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                                 bool* has_data,
                                                 const tl_record_t* data, size_t len) {
    if (len == 0) {
        return;
    }

    tl_ts_t rec_min = data[0].ts;
    tl_ts_t rec_max = rec_min;
    for (size_t i = 1; i < len; i++) {
        rec_min = TL_MIN(rec_min, data[i].ts);
        rec_max = TL_MAX(rec_max, data[i].ts);
    }

    if (!*has_data) {
        *min_ts = rec_min;
        *max_ts = rec_max;
        *has_data = true;
    } else {
        if (rec_min < *min_ts) *min_ts = rec_min;
        if (rec_max > *max_ts) *max_ts = rec_max;
    }
}

static void update_bounds_from_runs(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                     bool* has_data,
                                     const tl_ooorunset_t* runs) {
    if (runs == NULL || runs->total_len == 0) {
        return;
    }

    tl_ts_t rec_min = TL_TS_MAX;
    tl_ts_t rec_max = TL_TS_MIN;
    for (size_t i = 0; i < runs->count; i++) {
        const tl_ooorun_t* run = runs->runs[i];
        rec_min = TL_MIN(rec_min, run->min_ts);
        rec_max = TL_MAX(rec_max, run->max_ts);
    }

    if (!*has_data) {
        *min_ts = rec_min;
        *max_ts = rec_max;
        *has_data = true;
    } else {
        if (rec_min < *min_ts) *min_ts = rec_min;
        if (rec_max > *max_ts) *max_ts = rec_max;
    }
}

static void update_bounds_from_tombs(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                      bool* has_data,
                                      const tl_interval_t* data, size_t len) {
    if (len == 0) {
        return;
    }

    tl_ts_t tomb_min = data[0].start;
    const tl_interval_t* last = &data[len - 1];
    tl_ts_t tomb_max;
    if (last->end_unbounded) {
        tomb_max = TL_TS_MAX;
    } else {
        /* Half-open [start, end) covers up to end-1; valid intervals always
         * satisfy end > start so the subtraction cannot underflow. */
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

static void update_bounds_from_memrun(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                       bool* has_data,
                                       const tl_memrun_t* mr) {
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

static tl_status_t copy_intervals(tl_alloc_ctx_t* alloc,
                                   const tl_interval_t* src, size_t len,
                                   tl_interval_t** out) {
    *out = NULL;

    if (len == 0) {
        return TL_OK;
    }

    if (src == NULL) {
        return TL_EINVAL;
    }

    if (tl__alloc_would_overflow(len, sizeof(tl_interval_t))) {
        return TL_EOVERFLOW;
    }

    size_t bytes = len * sizeof(tl_interval_t);
    tl_interval_t* dst = tl__malloc(alloc, bytes);
    if (dst == NULL) {
        return TL_ENOMEM;
    }

    memcpy(dst, src, bytes);
    *out = dst;
    return TL_OK;
}

static tl_status_t copy_seqs(tl_alloc_ctx_t* alloc,
                              const tl_seq_t* src, size_t len,
                              tl_seq_t** out) {
    *out = NULL;

    if (len == 0) {
        return TL_OK;
    }

    if (src == NULL) {
        return TL_EINVAL;
    }

    if (tl__alloc_would_overflow(len, sizeof(tl_seq_t))) {
        return TL_EOVERFLOW;
    }

    size_t bytes = len * sizeof(tl_seq_t);
    tl_seq_t* dst = tl__malloc(alloc, bytes);
    if (dst == NULL) {
        return TL_ENOMEM;
    }

    memcpy(dst, src, bytes);
    *out = dst;
    return TL_OK;
}

/*
 * Copy and pin the sealed memrun array using an epoch-validated two-phase
 * approach: snapshot the queue metadata under the lock, drop the lock to
 * allocate, then re-acquire and verify the queue is unchanged before pinning.
 * If the queue mutated under us we retry; after a handful of failed attempts
 * we fall back to doing both the allocation and the pin under the lock, which
 * is always correct but holds the lock longer.
 */
static tl_status_t copy_sealed_memruns(tl_memview_t* mv,
                                        const tl_memtable_t* mt,
                                        tl_mutex_t* memtable_mu) {
    const int max_retries = 3;

    for (int attempt = 0; attempt < max_retries; attempt++) {
        size_t len = 0;
        size_t head = 0;
        uint64_t epoch = 0;

        TL_LOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        len = mt->sealed_len;
        head = mt->sealed_head;
        epoch = mt->sealed_epoch;
        if (len == 0) {
            mv->sealed = NULL;
            mv->sealed_len = 0;
            TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
            return TL_OK;
        }
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);

        if (tl__alloc_would_overflow(len, sizeof(tl_memrun_t*))) {
            return TL_EOVERFLOW;
        }

        tl_memrun_t** sealed = (tl_memrun_t**)tl__malloc(mv->alloc,
                                                          len * sizeof(tl_memrun_t*));
        if (sealed == NULL) {
            return TL_ENOMEM;
        }

        /* Validate the snapshot is still current. Any change to length, head,
         * or epoch means a seal/pop happened while the lock was released and
         * the pointers we are about to read could now be stale. */
        TL_LOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        if (mt->sealed_len != len ||
            mt->sealed_head != head ||
            mt->sealed_epoch != epoch) {
            TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
            tl__free(mv->alloc, (void*)sealed);
            continue;
        }

#ifdef TL_TEST_HOOKS
        if (tl_test_memview_force_retry_count > 0) {
            tl_test_memview_force_retry_count--;
            TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
            tl__free(mv->alloc, sealed);
            continue;
        }
#endif

        for (size_t i = 0; i < len; i++) {
            tl_memrun_t* mr = tl_memtable_sealed_at(mt, i);
            sealed[i] = tl_memrun_acquire(mr);
        }
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);

        mv->sealed = sealed;
        mv->sealed_len = len;
        return TL_OK;
    }

    /* Fallback: do allocation + pinning entirely under the lock. Always
     * correct, immune to livelock from a thrashing producer. */
#ifdef TL_TEST_HOOKS
    tl_test_memview_used_fallback = 1;
#endif
    TL_LOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);

    size_t len = mt->sealed_len;
    if (len == 0) {
        mv->sealed = NULL;
        mv->sealed_len = 0;
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        return TL_OK;
    }

    if (tl__alloc_would_overflow(len, sizeof(tl_memrun_t*))) {
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        return TL_EOVERFLOW;
    }

    tl_memrun_t** sealed = (tl_memrun_t**)tl__malloc(mv->alloc,
                                                      len * sizeof(tl_memrun_t*));
    if (sealed == NULL) {
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        return TL_ENOMEM;
    }

    for (size_t i = 0; i < len; i++) {
        tl_memrun_t* mr = tl_memtable_sealed_at(mt, i);
        sealed[i] = tl_memrun_acquire(mr);
    }

    mv->sealed = sealed;
    mv->sealed_len = len;
    TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
    return TL_OK;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_memview_capture(tl_memview_t* mv,
                                const tl_memtable_t* mt,
                                tl_mutex_t* memtable_mu,
                                tl_alloc_ctx_t* alloc) {
    TL_ASSERT(mv != NULL);
    TL_ASSERT(mt != NULL);
    TL_ASSERT(memtable_mu != NULL);
    TL_ASSERT(alloc != NULL);

    memset(mv, 0, sizeof(*mv));
    mv->alloc = alloc;
    mv->has_data = false;

    tl_status_t status;

    /* Caller holds writer_mu, so the active buffers cannot mutate while we
     * deep-copy them into the memview. */
    size_t run_len = tl_memtable_run_len(mt);
    status = tl_records_copy(alloc, tl_memtable_run_data(mt), run_len, &mv->active_run);
    if (status != TL_OK) {
        goto fail;
    }
    mv->active_run_len = run_len;
    status = copy_seqs(alloc, tl_memtable_run_seqs(mt), run_len, &mv->active_run_seqs);
    if (status != TL_OK) {
        goto fail;
    }

    size_t ooo_head_len = tl_memtable_ooo_head_len(mt);
    status = tl_records_copy(alloc, tl_memtable_ooo_head_data(mt), ooo_head_len,
                              &mv->active_ooo_head);
    if (status != TL_OK) {
        goto fail;
    }
    mv->active_ooo_head_len = ooo_head_len;
    mv->active_ooo_head_sorted = mt->ooo_head_sorted;
    status = copy_seqs(alloc, tl_memtable_ooo_head_seqs(mt), ooo_head_len,
                       &mv->active_ooo_head_seqs);
    if (status != TL_OK) {
        goto fail;
    }

    mv->active_ooo_runs = tl_ooorunset_acquire(
                            (tl_ooorunset_t*)tl_memtable_ooo_runs(mt));
    mv->active_ooo_total_len = ooo_head_len +
                               tl_ooorunset_total_len(mv->active_ooo_runs);

    tl_intervals_imm_t tombs_imm = tl_memtable_tombs_imm(mt);
    status = copy_intervals(alloc, tombs_imm.data, tombs_imm.len, &mv->active_tombs);
    if (status != TL_OK) {
        goto fail;
    }
    mv->active_tombs_len = tombs_imm.len;

    /* Sealed memruns live behind memtable_mu; the helper acquires it as part
     * of its epoch-validated capture protocol. */
    status = copy_sealed_memruns(mv, mt, memtable_mu);
    if (status != TL_OK) {
        goto fail;
    }

    /* The bounds must include every component that the read path consults so
     * that overlap pruning never excludes a memview that still carries
     * relevant tombstones. */
    update_bounds_from_records(&mv->min_ts, &mv->max_ts, &mv->has_data,
                               mv->active_run, mv->active_run_len);
    update_bounds_from_records_unsorted(&mv->min_ts, &mv->max_ts, &mv->has_data,
                                        mv->active_ooo_head, mv->active_ooo_head_len);
    update_bounds_from_runs(&mv->min_ts, &mv->max_ts, &mv->has_data,
                            mv->active_ooo_runs);
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

tl_status_t tl_memview_sort_head(tl_memview_t* mv) {
    if (mv == NULL) {
        return TL_OK;
    }

    if (mv->active_ooo_head_sorted) {
        return TL_OK;
    }

    if (mv->active_ooo_head_len > 1) {
        if (mv->active_ooo_head_seqs == NULL) {
            return TL_EINVAL;
        }
        tl_recvec_t tmp = {
            .data = mv->active_ooo_head,
            .len = mv->active_ooo_head_len,
            .cap = mv->active_ooo_head_len,
            .alloc = mv->alloc
        };
        tl_status_t st = tl_recvec_sort_with_seqs(&tmp, mv->active_ooo_head_seqs);
        if (st != TL_OK) {
            return st;
        }
    }

    mv->active_ooo_head_sorted = true;
    return TL_OK;
}

void tl_memview_destroy(tl_memview_t* mv) {
    if (mv == NULL) {
        return;
    }

    tl__free(mv->alloc, mv->active_run);
    tl__free(mv->alloc, mv->active_run_seqs);
    tl__free(mv->alloc, mv->active_ooo_head);
    tl__free(mv->alloc, mv->active_ooo_head_seqs);
    tl__free(mv->alloc, mv->active_tombs);

    if (mv->active_ooo_runs != NULL) {
        tl_ooorunset_release(mv->active_ooo_runs);
    }

    if (mv->sealed != NULL) {
        for (size_t i = 0; i < mv->sealed_len; i++) {
            if (mv->sealed[i] != NULL) {
                tl_memrun_release(mv->sealed[i]);
            }
        }
        tl__free(mv->alloc, (void*)mv->sealed);
    }

    memset(mv, 0, sizeof(*mv));
}

/*===========================================================================
 * Shared Memview (Snapshot Cache)
 *===========================================================================*/

tl_status_t tl_memview_shared_capture(tl_memview_shared_t** out,
                                       const tl_memtable_t* mt,
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

    TL_REFCOUNT_ACQUIRE(&mv->refcnt,
                        "memview acquire after final release",
                        "memview refcount overflow");
    return mv;
}

void tl_memview_shared_release(tl_memview_shared_t* mv) {
    if (mv == NULL) {
        return;
    }

    TL_REFCOUNT_RELEASE(&mv->refcnt, {
        tl_memview_destroy(&mv->view);
        tl__free(mv->view.alloc, mv);
    }, "memview double-release: refcnt was 0 before decrement");
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

    /* Memview bounds are inclusive [min_ts, max_ts]; query range is half-open
     * [t1, t2) or [t1, +inf). tl_range_overlaps encodes that asymmetry. */
    return tl_range_overlaps(mv->min_ts, mv->max_ts, t1, t2, t2_unbounded);
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

#include "../internal/tl_intervals.h"
#include "../internal/tl_recvec.h"

bool tl_memview_validate(const tl_memview_t* mv) {
    if (mv == NULL) {
        return false;
    }

    const tl_record_t* run = tl_memview_run_data(mv);
    size_t run_len = tl_memview_run_len(mv);
    if (run_len > 0 && mv->active_run_seqs == NULL) {
        return false;
    }
    for (size_t i = 1; i < run_len; i++) {
        if (run[i].ts < run[i - 1].ts) {
            return false;
        }
    }
    if (!tl_records_validate_bounds(run, run_len, mv->min_ts, mv->max_ts)) {
        return false;
    }

    /* OOO head sortedness is conditional: capture may copy the head while it
     * is still unsorted; tl_memview_sort_head sets the flag once sorted. */
    const tl_record_t* ooo_head = tl_memview_ooo_head_data(mv);
    size_t ooo_head_len = tl_memview_ooo_head_len(mv);
    if (ooo_head_len > 0 && mv->active_ooo_head_seqs == NULL) {
        return false;
    }
    if (mv->active_ooo_head_sorted) {
        for (size_t i = 1; i < ooo_head_len; i++) {
            if (ooo_head[i].ts < ooo_head[i - 1].ts) {
                return false;
            }
            if (ooo_head[i].ts == ooo_head[i - 1].ts &&
                ooo_head[i].handle < ooo_head[i - 1].handle) {
                return false;
            }
        }
    }
    if (!tl_records_validate_bounds(ooo_head, ooo_head_len, mv->min_ts, mv->max_ts)) {
        return false;
    }

    const tl_ooorunset_t* runs = tl_memview_ooo_runs(mv);
    if (runs != NULL) {
        size_t total = 0;
        uint64_t last_gen = 0;
        bool have_gen = false;
        for (size_t i = 0; i < runs->count; i++) {
            const tl_ooorun_t* run_ptr = runs->runs[i];
            if (run_ptr == NULL) {
                return false;
            }
            for (size_t j = 1; j < run_ptr->len; j++) {
                if (run_ptr->records[j].ts < run_ptr->records[j - 1].ts) {
                    return false;
                }
                if (run_ptr->records[j].ts == run_ptr->records[j - 1].ts &&
                    run_ptr->records[j].handle < run_ptr->records[j - 1].handle) {
                    return false;
                }
            }
            if (have_gen && run_ptr->gen < last_gen) {
                return false;
            }
            have_gen = true;
            last_gen = run_ptr->gen;
            if (run_ptr->len > SIZE_MAX - total) {
                return false;
            }
            total += run_ptr->len;
            if (!tl_records_validate_bounds(run_ptr->records, run_ptr->len,
                                            mv->min_ts, mv->max_ts)) {
                return false;
            }
        }
        if (total + ooo_head_len != mv->active_ooo_total_len) {
            return false;
        }
    } else if (ooo_head_len != mv->active_ooo_total_len) {
        return false;
    }

    const tl_interval_t* tombs = tl_memview_tomb_data(mv);
    size_t tombs_len = tl_memview_tomb_len(mv);
    if (!tl_intervals_arr_validate(tombs, tombs_len)) {
        return false;
    }

    size_t sealed_len = tl_memview_sealed_len(mv);
    for (size_t i = 0; i < sealed_len; i++) {
        if (tl_memview_sealed_get(mv, i) == NULL) {
            return false;
        }
    }

    /* has_data is the read path's signal that bounds are valid; it must not
     * be true unless there is something to consult. */
    if (tl_memview_has_data(mv)) {
        bool has_content = (run_len > 0 || mv->active_ooo_total_len > 0 ||
                           tombs_len > 0 || sealed_len > 0);
        if (!has_content) {
            return false;
        }
    }

    return true;
}

#endif /* TL_DEBUG */
