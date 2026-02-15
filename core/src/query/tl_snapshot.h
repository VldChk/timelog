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
 * Acquisition Protocol:
 * 1. Lock writer_mu
 * 2. Acquire manifest reference
 * 3. Capture or reuse memview snapshot (captures under memtable_mu as needed)
 * 4. Capture op_seq watermark
 * 5. Unlock writer_mu
 * 6. Sort fresh OOO head outside writer_mu, then cache if epoch still matches
 *
 * Consistency model:
 * - writer_mu serializes publish and snapshot capture
 * - no seqlock retry loop is required in the current implementation
 *
 * Thread Safety:
 * - Acquisition requires internal locking (handled automatically)
 * - After acquisition, fully immutable - no synchronization needed
 * - Release is thread-safe (reference counting)
 *===========================================================================*/

/* Forward declaration (opaque). */
struct tl_timelog;

struct tl_snapshot {
    tl_manifest_t*  manifest;        /* Pinned via acquire */
    tl_memview_shared_t* memview;    /* Shared, captured at acquisition */

    tl_seq_t        op_seq;          /* Tombstone watermark at capture time */

    /* Cached bounds (computed at acquisition) */
    tl_ts_t         min_ts;          /* Global min across manifest + memview */
    tl_ts_t         max_ts;          /* Global max across manifest + memview */
    bool            has_data;        /* True if any visible data exists */

    const struct tl_timelog* parent;  /* For debug state checks */
    tl_alloc_ctx_t* alloc;           /* Allocator (borrowed) */

#ifdef TL_DEBUG
    uint32_t        iter_count;      /* Outstanding iterator count (debug) */
#endif
};

/*===========================================================================
 * Internal API (for query components)
 *===========================================================================*/

/** Get manifest from snapshot. */
TL_INLINE const tl_manifest_t* tl_snapshot_manifest(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return snap->manifest;
}

/** Get memview from snapshot. */
TL_INLINE const tl_memview_t* tl_snapshot_memview(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(snap->memview != NULL);
    return tl_memview_shared_view(snap->memview);
}

/** Get allocator from snapshot. */
TL_INLINE tl_alloc_ctx_t* tl_snapshot_alloc(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return snap->alloc;
}

/** Get op_seq watermark captured with the snapshot. */
TL_INLINE tl_seq_t tl_snapshot_seq(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return snap->op_seq;
}

/** Check if snapshot has any data. */
TL_INLINE bool tl_snapshot_has_data(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return snap->has_data;
}

/** Get minimum timestamp. Only valid if has_data is true. */
TL_INLINE tl_ts_t tl_snapshot_min_ts(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(snap->has_data);
    return snap->min_ts;
}

/** Get maximum timestamp. Only valid if has_data is true. */
TL_INLINE tl_ts_t tl_snapshot_max_ts(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(snap->has_data);
    return snap->max_ts;
}

#ifdef TL_DEBUG
/** Track iterator creation (debug only). */
void tl_snapshot_iter_created(tl_snapshot_t* snap);

/** Track iterator destruction (debug only). */
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
 * Acquire a snapshot under writer_mu.
 * Caller validates tl != NULL and tl->is_open.
 */
tl_status_t tl_snapshot_acquire_internal(struct tl_timelog* tl,
                                          tl_alloc_ctx_t* alloc,
                                          tl_snapshot_t** out);

/** Release snapshot. Safe to call on NULL. */
void tl_snapshot_release_internal(tl_snapshot_t* snap);

/**
 * Collect tombstones from snapshot into a mutable interval set.
 *
 * Builds a piecewise-max tombstone map across:
 * - Active memview tombstones
 * - Sealed memruns in the memview
 * - Manifest L0/L1 segments (if present)
 *
 * Intervals are filtered to those overlapping [t1, t2) or [t1, +inf).
 * The output set is cleared before insertions.
 *
 * @param snap         Snapshot (must remain valid)
 * @param out          Output interval set (initialized by caller)
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY used if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf)
 * @return TL_OK on success, TL_ENOMEM/TL_EOVERFLOW on failure
 */
tl_status_t tl_snapshot_collect_tombstones(const tl_snapshot_t* snap,
                                            tl_intervals_t* out,
                                            tl_ts_t t1, tl_ts_t t2,
                                            bool t2_unbounded);


/**
 * Count visible records in a snapshot range [t1, t2) or [t1, +inf).
 *
 * Semantics are identical to read-path filtering:
 * - half-open range bounds [t1, t2)
 * - record dropped only when tomb_seq(ts) > row_watermark
 *
 * @param snap         Snapshot to query
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY used if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf)
 * @param out          Output count
 * @return TL_OK on success, TL_EINVAL for invalid args, other errors on
 *         allocation/iterator init failures
 */
tl_status_t tl_snapshot_count_range_internal(const tl_snapshot_t* snap,
                                              tl_ts_t t1, tl_ts_t t2,
                                              bool t2_unbounded,
                                              uint64_t* out);

#endif /* TL_SNAPSHOT_H */
