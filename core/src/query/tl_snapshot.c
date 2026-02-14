#include "tl_snapshot.h"
#include "../internal/tl_timelog_internal.h"
#include "../internal/tl_locks.h"
#include "../internal/tl_intervals.h"
#include "../internal/tl_range.h"
#include "../internal/tl_tombstone_utils.h"
#include "../storage/tl_segment.h"
#include "tl_plan.h"
#include "tl_merge_iter.h"
#include "tl_filter.h"
#include "tl_count.h"
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
     * Snapshot consistency is guaranteed by writer_mu:
     * - Writers hold writer_mu during publish (manifest swap + memtable pop)
     * - Snapshots hold writer_mu during capture
     * Therefore, we do not need a seqlock retry loop here.
     */
    tl_manifest_t* manifest = NULL;
    tl_memview_shared_t* mv = NULL;
    bool used_cache = false;

    TL_LOCK_WRITER(tl);

    /* Acquire manifest reference under writer_mu to prevent UAF */
    manifest = tl_manifest_acquire(tl->manifest);

    /* Capture or reuse memview (locks memtable_mu internally) */
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

    /* Capture op_seq under writer_mu for tombstone watermarks */
    snap->op_seq = tl->op_seq;

    TL_UNLOCK_WRITER(tl);

    /* Sort OOO head off writer_mu for fresh captures. */
    if (!used_cache) {
        tl_status_t sort_st = tl_memview_sort_head(&mv->view);
        if (sort_st != TL_OK) {
            tl_memview_shared_release(mv);
            tl_manifest_release(manifest);
            tl__free(alloc, snap);
            return sort_st;
        }

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

/*===========================================================================
 * Tombstone Collection
 *===========================================================================*/

tl_status_t tl_snapshot_collect_tombstones(const tl_snapshot_t* snap,
                                           tl_intervals_t* out,
                                           tl_ts_t t1, tl_ts_t t2,
                                           bool t2_unbounded) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(out != NULL);

    tl_intervals_clear(out);

    const tl_manifest_t* manifest = snap->manifest;
    const tl_memview_t* mv = tl_snapshot_memview(snap);

    tl_status_t st;

    /* Active memview tombstones */
    st = tl_tombstones_add_intervals(out, tl_memview_tombs_imm(mv),
                                     t1, t2, t2_unbounded);
    if (st != TL_OK) {
        return st;
    }

    /* Sealed memrun tombstones */
    for (size_t i = 0; i < tl_memview_sealed_len(mv); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(mv, i);

        if (!tl_range_overlaps(tl_memrun_min_ts(mr), tl_memrun_max_ts(mr),
                               t1, t2, t2_unbounded)) {
            continue;
        }

        st = tl_tombstones_add_intervals(out, tl_memrun_tombs_imm(mr),
                                         t1, t2, t2_unbounded);
        if (st != TL_OK) {
            return st;
        }
    }

    /* L0 segment tombstones */
    for (size_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);

        bool overlaps = false;
        if (tl_segment_has_tombstones(seg)) {
            overlaps = tl_range_overlaps(seg->tomb_min_ts, seg->tomb_max_ts,
                                         t1, t2, t2_unbounded);
        }
        if (!overlaps) {
            continue;
        }

        st = tl_tombstones_add_intervals(out, tl_segment_tombstones_imm(seg),
                                         t1, t2, t2_unbounded);
        if (st != TL_OK) {
            return st;
        }
    }

    /* Defensive: L1 tombstones if present (should be empty in V1) */
    for (size_t i = 0; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);

        bool overlaps = false;
        if (tl_segment_has_tombstones(seg)) {
            overlaps = tl_range_overlaps(seg->tomb_min_ts, seg->tomb_max_ts,
                                         t1, t2, t2_unbounded);
        }
        if (!overlaps) {
            continue;
        }

        st = tl_tombstones_add_intervals(out, tl_segment_tombstones_imm(seg),
                                         t1, t2, t2_unbounded);
        if (st != TL_OK) {
            return st;
        }
    }

    return TL_OK;
}


/*===========================================================================
 * Snapshot Count API
 *===========================================================================*/

tl_status_t tl_snapshot_count_range_internal(const tl_snapshot_t* snap,
                                              tl_ts_t t1, tl_ts_t t2,
                                              bool t2_unbounded,
                                              uint64_t* out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    *out = 0;

    /* Short-circuit for empty bounded ranges */
    if (!t2_unbounded && t1 >= t2) {
        return TL_OK;
    }

    /* Collect tombstone skyline for query range */
    tl_intervals_t skyline;
    tl_intervals_init(&skyline, snap->alloc);
    tl_status_t st = tl_snapshot_collect_tombstones(snap, &skyline,
                                                     t1, t2, t2_unbounded);
    if (st != TL_OK) {
        tl_intervals_destroy(&skyline);
        return st;
    }

    tl_intervals_imm_t sky_imm = tl_intervals_as_imm(&skyline);
    const tl_interval_t* sky_data = sky_imm.data;
    size_t sky_len = sky_imm.len;

    const tl_manifest_t* manifest = tl_snapshot_manifest(snap);
    const tl_memview_t* memview = tl_snapshot_memview(snap);

    uint64_t total = 0;

    /* L0 segments */
    for (uint32_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);
        total += tl__visible_records_in_segment_range(seg, sky_data, sky_len,
                                                       t1, t2, t2_unbounded);
    }

    /* L1 segments */
    for (uint32_t i = 0; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);
        total += tl__visible_records_in_segment_range(seg, sky_data, sky_len,
                                                       t1, t2, t2_unbounded);
    }

    /* Sealed memruns */
    for (size_t i = 0; i < tl_memview_sealed_len(memview); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(memview, i);
        total += tl__visible_records_in_memrun_range(mr, sky_data, sky_len,
                                                      t1, t2, t2_unbounded);
    }

    /* Active buffers (per-record watermark filtering) */
    total += tl__count_active_visible_range(memview, sky_imm,
                                             t1, t2, t2_unbounded);

    tl_intervals_destroy(&skyline);
    *out = total;
    return TL_OK;
}
