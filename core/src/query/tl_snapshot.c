#include "tl_snapshot.h"
#include "../internal/tl_timelog_internal.h"
#include "../internal/tl_locks.h"
#include "../internal/tl_seqlock.h"
#include "../internal/tl_range.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Compute global bounds from manifest and memview.
 */
static void snap_compute_bounds(tl_snapshot_t* snap) {
    snap->has_data = false;
    snap->min_ts = 0;
    snap->max_ts = 0;

    /* Bounds from manifest */
    const tl_manifest_t* m = snap->manifest;
    if (m->has_bounds) {
        snap->min_ts = m->min_ts;
        snap->max_ts = m->max_ts;
        snap->has_data = true;
    }

    /* Bounds from memview */
    const tl_memview_t* mv = tl_memview_shared_view(snap->memview);
    if (mv != NULL && mv->has_data) {
        if (!snap->has_data) {
            snap->min_ts = mv->min_ts;
            snap->max_ts = mv->max_ts;
            snap->has_data = true;
        } else {
            if (mv->min_ts < snap->min_ts) {
                snap->min_ts = mv->min_ts;
            }
            if (mv->max_ts > snap->max_ts) {
                snap->max_ts = mv->max_ts;
            }
        }
    }
}

/*===========================================================================
 * Debug Iterator Tracking
 *===========================================================================*/

#ifdef TL_DEBUG
void tl_snapshot_iter_created(tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    snap->iter_count++;
}

void tl_snapshot_iter_destroyed(tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(snap->iter_count > 0);
    snap->iter_count--;
}
#endif

/*===========================================================================
 * Snapshot Acquisition
 *===========================================================================*/

tl_status_t tl_snapshot_acquire_internal(struct tl_timelog* tl,
                                          tl_alloc_ctx_t* alloc,
                                          tl_snapshot_t** out) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    /* Allocate snapshot structure */
    tl_snapshot_t* snap = TL_NEW(alloc, tl_snapshot_t);
    if (snap == NULL) {
        return TL_ENOMEM;
    }

    /* Zero-initialize all fields for defensive safety */
    memset(snap, 0, sizeof(*snap));
    snap->alloc = alloc;

    /*
     * Seqlock retry loop for snapshot consistency.
     *
     * Protocol (from Software Design Spec Section 4.2):
     * 1. Lock writer_mu
     * 2. Read seqlock seq1 (must be even)
     * 3. Acquire manifest reference
     * 4. Capture memview (locks memtable_mu internally)
     * 5. Read seqlock seq2
     * 6. Unlock writer_mu
     * 7. If seq1 != seq2 OR seq1 is odd: retry
     */
    for (;;) {
        tl_manifest_t* manifest = NULL;
        tl_memview_shared_t* mv = NULL;
        bool used_cache = false;

        TL_LOCK_WRITER(tl);

        /* Step 1: Read seqlock (must be even = no publish in progress) */
        uint64_t seq1 = tl_seqlock_read(&tl->view_seq);
        if (!tl_seqlock_is_even(seq1)) {
            /* Publish in progress - unlock and retry */
            TL_UNLOCK_WRITER(tl);
            continue;
        }

        /* Step 2: Acquire manifest reference */
        manifest = tl_manifest_acquire(tl->manifest);

        /* Step 3: Capture or reuse memview (locks memtable_mu internally) */
        uint64_t epoch = tl_memtable_epoch(&tl->memtable);
        if (tl->memview_cache != NULL && tl->memview_cache_epoch == epoch) {
            mv = tl_memview_shared_acquire(tl->memview_cache);
            used_cache = true;
        } else {
            tl_status_t st = tl_memview_shared_capture(&mv,
                                                        &tl->memtable,
                                                        &tl->memtable_mu,
                                                        alloc,
                                                        epoch);
            if (st != TL_OK) {
                tl_manifest_release(manifest);
                TL_UNLOCK_WRITER(tl);
                tl__free(alloc, snap);
                return st;
            }
        }

        /* Step 4: Read seqlock again and validate */
        uint64_t seq2 = tl_seqlock_read(&tl->view_seq);
        bool ok = tl_seqlock_validate(seq1, seq2);

        if (ok) {
            TL_UNLOCK_WRITER(tl);

            /* Sort OOO head off writer_mu for fresh captures. */
            if (!used_cache) {
                tl_memview_sort_head(&mv->view);

                /* Update cache if epoch unchanged (two-phase capture). */
                TL_LOCK_WRITER(tl);
                if (tl_memtable_epoch(&tl->memtable) == epoch) {
                    if (tl->memview_cache == NULL ||
                        tl->memview_cache_epoch != epoch) {
                        if (tl->memview_cache != NULL) {
                            tl_memview_shared_release(tl->memview_cache);
                        }
                        tl->memview_cache = tl_memview_shared_acquire(mv);
                        tl->memview_cache_epoch = epoch;
                    }
                }
                TL_UNLOCK_WRITER(tl);
            }

            snap->manifest = manifest;
            snap->memview = mv;
            break;  /* Success - consistent snapshot */
        }

        TL_UNLOCK_WRITER(tl);

        /* Inconsistent - release captured state and retry */
        tl_manifest_release(manifest);
        tl_memview_shared_release(mv);
    }

    /* Compute global bounds from manifest + memview */
    snap_compute_bounds(snap);

    snap->parent = tl;

#ifdef TL_DEBUG
    snap->iter_count = 0;
    /* Increment outstanding snapshot count for leak detection at close */
    tl_atomic_fetch_add_u32(&tl->snapshot_count, 1, TL_MO_RELAXED);
#endif

    *out = snap;
    return TL_OK;
}

void tl_snapshot_release_internal(tl_snapshot_t* snap) {
    if (snap == NULL) {
        return;
    }

#ifdef TL_DEBUG
    TL_ASSERT(snap->iter_count == 0 && "Outstanding iterators on snapshot release");
    /* Decrement outstanding snapshot count (cast away const for atomic update) */
    if (snap->parent != NULL) {
        tl_atomic_fetch_sub_u32(&((struct tl_timelog*)snap->parent)->snapshot_count, 1, TL_MO_RELAXED);
    }
#endif

    /* Release memview (shared, refcounted) */
    tl_memview_shared_release(snap->memview);

    /* Release manifest reference */
    if (snap->manifest != NULL) {
        tl_manifest_release(snap->manifest);
    }

    /* Free snapshot structure */
    tl__free(snap->alloc, snap);
}
