#include "tl_ooorun.h"
#include "../internal/tl_refcount.h"

/*===========================================================================
 * Run Lifecycle
 *===========================================================================*/

tl_status_t tl_ooorun_create(tl_alloc_ctx_t* alloc,
                              tl_record_t* records, size_t len,
                              tl_seq_t applied_seq,
                              uint64_t gen,
                              tl_ooorun_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    if (len == 0 || records == NULL) {
        return TL_EINVAL;
    }

#ifdef TL_DEBUG
    /* Verify records are sorted by (ts, handle) */
    for (size_t i = 1; i < len; i++) {
        TL_ASSERT(records[i - 1].ts < records[i].ts ||
                  (records[i - 1].ts == records[i].ts &&
                   records[i - 1].handle <= records[i].handle));
    }
#endif

    tl_ooorun_t* run = TL_NEW(alloc, tl_ooorun_t);
    if (run == NULL) {
        return TL_ENOMEM;
    }

    run->alloc = alloc;
    run->records = records;
    run->len = len;
    run->applied_seq = applied_seq;
    run->gen = gen;

    run->min_ts = records[0].ts;
    run->max_ts = records[len - 1].ts;

    tl_atomic_init_u32(&run->refcnt, 1);

    *out = run;
    return TL_OK;
}

tl_ooorun_t* tl_ooorun_acquire(tl_ooorun_t* run) {
    if (run == NULL) {
        return NULL;
    }

    tl_atomic_fetch_add_u32(&run->refcnt, 1, TL_MO_RELAXED);
    return run;
}

void tl_ooorun_release(tl_ooorun_t* run) {
    if (run == NULL) {
        return;
    }

    TL_REFCOUNT_RELEASE(&run->refcnt, {
        tl__free(run->alloc, run->records);
        tl__free(run->alloc, run);
    }, "ooorun double-release: refcnt was 0 before decrement");
}

/*===========================================================================
 * Runset Lifecycle
 *===========================================================================*/

tl_status_t tl_ooorunset_create(tl_alloc_ctx_t* alloc,
                                 tl_ooorun_t* const* runs,
                                 size_t count,
                                 tl_ooorunset_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    if (count == 0 || runs == NULL) {
        return TL_EINVAL;
    }

    if (count > (SIZE_MAX - sizeof(tl_ooorunset_t)) / sizeof(tl_ooorun_t*)) {
        return TL_EOVERFLOW;
    }

    size_t bytes = sizeof(tl_ooorunset_t) + count * sizeof(tl_ooorun_t*);
    tl_ooorunset_t* set = tl__malloc(alloc, bytes);
    if (set == NULL) {
        return TL_ENOMEM;
    }

    tl_atomic_init_u32(&set->refcnt, 1);
    set->alloc = alloc;
    set->count = count;
    set->total_len = 0;

    for (size_t i = 0; i < count; i++) {
        if (runs[i] == NULL) {
            /* NULL run in array - unwind and fail */
            for (size_t j = 0; j < i; j++) {
                tl_ooorun_release(set->runs[j]);
            }
            tl__free(alloc, set);
            return TL_EINVAL;
        }
        set->runs[i] = tl_ooorun_acquire(runs[i]);
        if (runs[i]->len > SIZE_MAX - set->total_len) {
            /* Overflow - unwind */
            for (size_t j = 0; j <= i; j++) {
                tl_ooorun_release(set->runs[j]);
            }
            tl__free(alloc, set);
            return TL_EOVERFLOW;
        }
        set->total_len += runs[i]->len;
    }

    *out = set;
    return TL_OK;
}

tl_status_t tl_ooorunset_append(tl_alloc_ctx_t* alloc,
                                 tl_ooorunset_t* old_set,
                                 tl_ooorun_t* run,
                                 tl_ooorunset_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(run != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    size_t old_count = (old_set == NULL) ? 0 : old_set->count;
    size_t new_count = old_count + 1;

    if (new_count > (SIZE_MAX - sizeof(tl_ooorunset_t)) / sizeof(tl_ooorun_t*)) {
        return TL_EOVERFLOW;
    }

    size_t bytes = sizeof(tl_ooorunset_t) + new_count * sizeof(tl_ooorun_t*);
    tl_ooorunset_t* set = tl__malloc(alloc, bytes);
    if (set == NULL) {
        return TL_ENOMEM;
    }

    tl_atomic_init_u32(&set->refcnt, 1);
    set->alloc = alloc;
    set->count = new_count;
    set->total_len = 0;

    for (size_t i = 0; i < old_count; i++) {
        TL_ASSERT(old_set->runs[i] != NULL);  /* Invariant: valid runsets have no NULL runs */
        set->runs[i] = tl_ooorun_acquire(old_set->runs[i]);
        if (old_set->runs[i]->len > SIZE_MAX - set->total_len) {
            for (size_t j = 0; j <= i; j++) {
                tl_ooorun_release(set->runs[j]);
            }
            tl__free(alloc, set);
            return TL_EOVERFLOW;
        }
        set->total_len += old_set->runs[i]->len;
    }

    set->runs[old_count] = tl_ooorun_acquire(run);
    if (run->len > SIZE_MAX - set->total_len) {
        for (size_t j = 0; j < new_count; j++) {
            tl_ooorun_release(set->runs[j]);
        }
        tl__free(alloc, set);
        return TL_EOVERFLOW;
    }
    set->total_len += run->len;

    *out = set;
    return TL_OK;
}

tl_ooorunset_t* tl_ooorunset_acquire(tl_ooorunset_t* set) {
    if (set == NULL) {
        return NULL;
    }

    tl_atomic_fetch_add_u32(&set->refcnt, 1, TL_MO_RELAXED);
    return set;
}

void tl_ooorunset_release(tl_ooorunset_t* set) {
    if (set == NULL) {
        return;
    }

    TL_REFCOUNT_RELEASE(&set->refcnt, {
        for (size_t i = 0; i < set->count; i++) {
            tl_ooorun_release(set->runs[i]);
        }
        tl__free(set->alloc, set);
    }, "ooorunset double-release: refcnt was 0 before decrement");
}
