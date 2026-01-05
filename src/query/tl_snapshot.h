#ifndef TL_SNAPSHOT_H
#define TL_SNAPSHOT_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../storage/tl_manifest.h"
#include "../delta/tl_memview.h"

/*===========================================================================
 * Snapshot: Complete Point-in-Time View
 *
 * A snapshot captures a consistent view of the timelog at a point in time.
 * It contains:
 * - Manifest (pinned via acquire, released on destroy)
 * - Memview (owned, captured at acquisition time)
 *
 * The snapshot is completely immutable after acquisition and can be used
 * for queries without holding any locks.
 *
 * Acquisition Protocol (from Software Design Spec Section 4.2):
 * 1. Lock writer_mu
 * 2. Read seqlock (must be even)
 * 3. Acquire manifest reference
 * 4. Capture memview (locks memtable_mu internally)
 * 5. Read seqlock again
 * 6. Unlock writer_mu
 * 7. If seq1 != seq2 OR seq1 is odd: retry
 *
 * Thread Safety:
 * - Acquisition requires internal locking (handled automatically)
 * - After acquisition, fully immutable - no synchronization needed
 * - Release is thread-safe (reference counting)
 *
 * Reference: Read Path LLD Section 1, Software Design Spec Section 4.2
 *===========================================================================*/

/*
 * Forward declaration of tl_timelog_t.
 * We cannot include tl_timelog.c's struct definition, so we use opaque pointer.
 */
struct tl_timelog;

struct tl_snapshot {
    /*-----------------------------------------------------------------------
     * Manifest (pinned via acquire, released on destroy)
     *-----------------------------------------------------------------------*/
    tl_manifest_t*  manifest;

    /*-----------------------------------------------------------------------
     * Memview (owned, captured at acquisition time)
     *-----------------------------------------------------------------------*/
    tl_memview_t    memview;

    /*-----------------------------------------------------------------------
     * Cached Bounds (computed at acquisition time)
     *-----------------------------------------------------------------------*/
    tl_ts_t         min_ts;          /* Global min across manifest + memview */
    tl_ts_t         max_ts;          /* Global max across manifest + memview */
    bool            has_data;        /* True if any visible data exists */

    /*-----------------------------------------------------------------------
     * Parent Reference (for debug state checks)
     *-----------------------------------------------------------------------*/
    const struct tl_timelog* parent;

    /*-----------------------------------------------------------------------
     * Lifecycle
     *-----------------------------------------------------------------------*/
    tl_alloc_ctx_t* alloc;           /* Allocator (borrowed) */

#ifdef TL_DEBUG
    uint32_t        iter_count;      /* Outstanding iterator count (debug) */
#endif
};

/*===========================================================================
 * Internal API (for query components)
 *===========================================================================*/

/**
 * Get manifest from snapshot.
 */
TL_INLINE const tl_manifest_t* tl_snapshot_manifest(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return snap->manifest;
}

/**
 * Get memview from snapshot.
 */
TL_INLINE const tl_memview_t* tl_snapshot_memview(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return &snap->memview;
}

/**
 * Get allocator from snapshot.
 */
TL_INLINE tl_alloc_ctx_t* tl_snapshot_alloc(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return snap->alloc;
}

/**
 * Check if snapshot has any data.
 */
TL_INLINE bool tl_snapshot_has_data(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return snap->has_data;
}

/**
 * Get minimum timestamp in snapshot.
 * Only valid if has_data is true.
 */
TL_INLINE tl_ts_t tl_snapshot_min_ts(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(snap->has_data);
    return snap->min_ts;
}

/**
 * Get maximum timestamp in snapshot.
 * Only valid if has_data is true.
 */
TL_INLINE tl_ts_t tl_snapshot_max_ts(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(snap->has_data);
    return snap->max_ts;
}

#ifdef TL_DEBUG
/**
 * Track iterator creation (debug only).
 * Must be called when creating an iterator from this snapshot.
 */
void tl_snapshot_iter_created(tl_snapshot_t* snap);

/**
 * Track iterator destruction (debug only).
 * Must be called when destroying an iterator from this snapshot.
 */
void tl_snapshot_iter_destroyed(tl_snapshot_t* snap);
#endif

/*===========================================================================
 * Internal Acquisition (called from tl_timelog.c)
 *
 * The public API (tl_snapshot_acquire, tl_snapshot_release) is declared in
 * timelog.h. The implementation is in tl_snapshot.c but is called from
 * tl_timelog.c wrapper functions.
 *===========================================================================*/

/**
 * Internal snapshot acquisition.
 * Called from tl_snapshot_acquire in tl_timelog.c.
 *
 * This function implements the seqlock protocol for snapshot consistency.
 * The caller (tl_snapshot_acquire in timelog.h) validates tl != NULL and
 * tl->is_open.
 *
 * @param tl    Timelog instance (cast to non-const internally for locking)
 * @param alloc Allocator context
 * @param out   Output snapshot pointer
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_snapshot_acquire_internal(struct tl_timelog* tl,
                                          tl_alloc_ctx_t* alloc,
                                          tl_snapshot_t** out);

/**
 * Internal snapshot release.
 * Called from tl_snapshot_release in tl_timelog.c.
 *
 * @param snap  Snapshot to release (may be NULL)
 */
void tl_snapshot_release_internal(tl_snapshot_t* snap);

#endif /* TL_SNAPSHOT_H */
