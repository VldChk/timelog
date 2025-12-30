#include "../internal/tl_snapshot.h"

/*
 * Access timelog internals (defined in tl_timelog.c)
 * These functions provide controlled access to timelog state.
 */
extern uint64_t tl_timelog_view_seq_load(const struct tl_timelog* tl);
extern tl_manifest_t* tl_timelog_manifest_acquire(struct tl_timelog* tl);
extern tl_status_t tl_timelog_memview_capture(struct tl_timelog* tl,
                                               tl_memview_t** out);
extern const tl_allocator_t* tl_timelog_allocator(const struct tl_timelog* tl);

/*
 * Maximum retry attempts before giving up (prevents infinite loop on bug)
 */
#define TL_SNAPSHOT_MAX_RETRIES 1000

tl_status_t tl_snapshot_acquire_internal(struct tl_timelog* tl,
                                          tl_snapshot_t** out) {
    if (tl == NULL || out == NULL) return TL_EINVAL;
    *out = NULL;

    const tl_allocator_t* alloc = tl_timelog_allocator(tl);

    /* Allocate snapshot */
    tl_snapshot_t* snap = tl__calloc(alloc, 1, sizeof(tl_snapshot_t));
    if (snap == NULL) return TL_ENOMEM;

    snap->alloc = alloc;
    snap->tl = tl;

    /*
     * Seqlock acquisition protocol:
     *
     * The view_seq counter uses even/odd signaling:
     * - Even: stable state, safe to read
     * - Odd: publication in progress, must wait
     *
     * Algorithm:
     * 1. Load v1 = view_seq; if odd, retry
     * 2. Acquire manifest reference
     * 3. Capture memview snapshot
     * 4. Load v2 = view_seq
     * 5. If v1 == v2 and even: success
     * 6. Else: release, retry
     */
    int retries = 0;
    while (retries < TL_SNAPSHOT_MAX_RETRIES) {
        /* Step 1: Load view_seq and check stability */
        uint64_t v1 = tl_timelog_view_seq_load(tl);

        if ((v1 & 1) != 0) {
            /* Odd: publication in progress, spin briefly */
            retries++;
            continue;
        }

        /* Step 2: Acquire manifest reference */
        tl_manifest_t* manifest = tl_timelog_manifest_acquire(tl);

        /* Step 3: Capture memview */
        tl_memview_t* memview = NULL;
        tl_status_t st = tl_timelog_memview_capture(tl, &memview);
        if (st != TL_OK) {
            if (manifest != NULL) {
                tl_manifest_release(manifest);
            }
            tl__free(alloc, snap);
            return st;
        }

        /* Step 4: Load view_seq again */
        uint64_t v2 = tl_timelog_view_seq_load(tl);

        /* Step 5: Verify consistency */
        if (v1 == v2) {
            /* Success: snapshot is consistent */
            snap->manifest = manifest;
            snap->memview = memview;

            /* Compute bounds */
            tl_ts_t min_ts = TL_TS_MAX;
            tl_ts_t max_ts = TL_TS_MIN;

            /* Manifest bounds */
            if (manifest != NULL && manifest->has_bounds) {
                if (manifest->min_ts < min_ts) min_ts = manifest->min_ts;
                if (manifest->max_ts > max_ts) max_ts = manifest->max_ts;
            }

            /* Memview bounds */
            if (memview != NULL) {
                if (memview->min_ts < min_ts) min_ts = memview->min_ts;
                if (memview->max_ts > max_ts) max_ts = memview->max_ts;
            }

            if (min_ts <= max_ts) {
                snap->has_bounds = true;
                snap->min_ts = min_ts;
                snap->max_ts = max_ts;
            } else {
                snap->has_bounds = false;
            }

            *out = snap;
            return TL_OK;
        }

        /* Step 6: view_seq changed, retry */
        if (memview != NULL) {
            tl_memview_release(memview);
        }
        if (manifest != NULL) {
            tl_manifest_release(manifest);
        }
        retries++;
    }

    /* Too many retries (should not happen in correct implementation) */
    tl__free(alloc, snap);
    return TL_EBUSY;
}

void tl_snapshot_release_internal(tl_snapshot_t* snap) {
    if (snap == NULL) return;

    const tl_allocator_t* alloc = snap->alloc;

    /* Release memview (we own it) */
    if (snap->memview != NULL) {
        tl_memview_release(snap->memview);
    }

    /* Release manifest reference */
    if (snap->manifest != NULL) {
        tl_manifest_release(snap->manifest);
    }

    tl__free(alloc, snap);
}

bool tl_snapshot_empty(const tl_snapshot_t* snap) {
    if (snap == NULL) return true;

    /* Check manifest */
    if (snap->manifest != NULL) {
        for (uint32_t i = 0; i < snap->manifest->n_main; i++) {
            if (snap->manifest->main[i]->record_count > 0) {
                return false;
            }
        }
        for (uint32_t i = 0; i < snap->manifest->n_delta; i++) {
            if (snap->manifest->delta[i]->record_count > 0) {
                return false;
            }
        }
    }

    /* Check memview */
    if (snap->memview != NULL && !tl_memview_empty(snap->memview)) {
        return false;
    }

    return true;
}

tl_ts_t tl_snapshot_min_ts(const tl_snapshot_t* snap) {
    if (snap == NULL || !snap->has_bounds) return TL_TS_MAX;
    return snap->min_ts;
}

tl_ts_t tl_snapshot_max_ts(const tl_snapshot_t* snap) {
    if (snap == NULL || !snap->has_bounds) return TL_TS_MIN;
    return snap->max_ts;
}
