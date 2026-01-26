#ifndef TL_MEMVIEW_H
#define TL_MEMVIEW_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_intervals.h"
#include "../internal/tl_sync.h"
#include "../internal/tl_atomic.h"
#include "tl_memtable.h"
#include "tl_memrun.h"

/*===========================================================================
 * Memview: Immutable Snapshot of Memtable State
 *
 * A memview captures the complete delta state at a point in time:
 * - Active buffers (deep copied, since memtable is mutable)
 * - Sealed memruns (pinned via acquire, released on destroy)
 *
 * Used by the read path to provide snapshot isolation. After capture,
 * the memview is completely immutable and can be used for queries
 * without holding any locks.
 *
 * Thread Safety:
 * - Capture requires writer_mu to be held externally (for active state)
 * - Capture acquires memtable_mu internally (for sealed queue)
 * - After capture, fully immutable - no synchronization needed
 *
 * Lock Ordering: writer_mu -> memtable_mu (per Phase 4 lock hierarchy)
 *
 * Reference: Read Path LLD Section 5.1, Engineering Plan Section 5.1
 *===========================================================================*/

struct tl_memview {
    /*-----------------------------------------------------------------------
     * Active Buffers (copied from memtable - immutable after capture)
     *-----------------------------------------------------------------------*/
    tl_record_t*    active_run;      /* Copy of active_run data (sorted) */
    size_t          active_run_len;

    tl_record_t*    active_ooo_head; /* Copy of OOO head data (sorted after capture) */
    size_t          active_ooo_head_len;
    bool            active_ooo_head_sorted;

    tl_ooorunset_t* active_ooo_runs; /* Pinned OOO runset */
    size_t          active_ooo_total_len;

    tl_interval_t*  active_tombs;    /* Copy of active_tombs data */
    size_t          active_tombs_len;

    /*-----------------------------------------------------------------------
     * Sealed Memruns (pinned via acquire, released on destroy)
     *-----------------------------------------------------------------------*/
    tl_memrun_t**   sealed;          /* Array of pinned memrun pointers */
    size_t          sealed_len;

    /*-----------------------------------------------------------------------
     * Bounds (computed at capture time)
     *-----------------------------------------------------------------------*/
    tl_ts_t         min_ts;          /* Min of all components */
    tl_ts_t         max_ts;          /* Max of all components */
    bool            has_data;        /* True if any records/tombstones exist */

    /*-----------------------------------------------------------------------
     * Lifecycle
     *-----------------------------------------------------------------------*/
    tl_alloc_ctx_t* alloc;           /* Allocator (borrowed) */
};

/*===========================================================================
 * Shared Memview (Snapshot Cache)
 *
 * Shared, refcounted wrapper used to reuse memviews across snapshots when the
 * memtable epoch has not changed. This avoids repeated deep copies on frequent
 * snapshot acquisition under read-heavy workloads.
 *===========================================================================*/

typedef struct tl_memview_shared {
    tl_memview_t   view;             /* Immutable memview */
    tl_atomic_u32  refcnt;           /* Reference count */
    uint64_t       epoch;            /* Memtable epoch at capture time */
} tl_memview_shared_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Capture memview from memtable.
 *
 * LOCKING: Caller must hold writer_mu (for seqlock validation and active
 * state access). This function acquires memtable_mu internally for sealed
 * queue access.
 *
 * Lock ordering: writer_mu -> memtable_mu (Phase 4 lock hierarchy)
 *
 * Copies active buffers (run, OOO head, tombs) and pins sealed memruns via
 * tl_memrun_acquire. The OOO head may be sorted later via tl_memview_sort_head
 * (off-lock). The memview is then immutable and can be used for queries
 * without holding any locks.
 *
 * @param mv          Output memview (caller-allocated, zero-initialized)
 * @param mt          Memtable to capture from
 * @param memtable_mu Mutex protecting sealed queue (from tl_timelog)
 * @param alloc       Allocator for copies
 * @return TL_OK on success, TL_ENOMEM/TL_EOVERFLOW/TL_EINVAL on failure
 *
 * On failure, memview is left in a valid but empty state (safe to destroy).
 */
tl_status_t tl_memview_capture(tl_memview_t* mv,
                                const tl_memtable_t* mt,
                                tl_mutex_t* memtable_mu,
                                tl_alloc_ctx_t* alloc);

/**
 * Sort the copied OOO head in-place (off-lock).
 * Safe to call multiple times.
 */
void tl_memview_sort_head(tl_memview_t* mv);

/**
 * Destroy memview and release all resources.
 *
 * Frees copied active buffers and releases all pinned memruns.
 * Safe to call on zero-initialized or partially initialized memview.
 * Idempotent: safe to call multiple times.
 *
 * After this call, mv is in a zero-initialized state.
 */
void tl_memview_destroy(tl_memview_t* mv);

/*===========================================================================
 * Shared Memview Lifecycle (Snapshot Cache)
 *===========================================================================*/

/**
 * Capture a shared memview for snapshot caching.
 *
 * @param out          Output: new shared memview (refcnt=1)
 * @param mt           Memtable to capture
 * @param memtable_mu  Mutex protecting sealed queue
 * @param alloc        Allocator for memview and shared wrapper
 * @param epoch        Memtable epoch at capture time
 * @return TL_OK on success, TL_ENOMEM/TL_EOVERFLOW/TL_EINVAL on failure
 */
tl_status_t tl_memview_shared_capture(tl_memview_shared_t** out,
                                       const tl_memtable_t* mt,
                                       tl_mutex_t* memtable_mu,
                                       tl_alloc_ctx_t* alloc,
                                       uint64_t epoch);

/**
 * Acquire a reference to a shared memview.
 */
tl_memview_shared_t* tl_memview_shared_acquire(tl_memview_shared_t* mv);

/**
 * Release a reference to a shared memview.
 * Destroys the memview and frees the wrapper when refcnt reaches 0.
 */
void tl_memview_shared_release(tl_memview_shared_t* mv);

/*===========================================================================
 * Query Support
 *===========================================================================*/

/**
 * Check if memview overlaps with range [t1, t2) or [t1, +inf).
 *
 * UNBOUNDED QUERIES:
 * - If t2_unbounded == true, checks overlap with [t1, +inf)
 * - When t2_unbounded is true, t2 is ignored (pass 0 for clarity)
 *
 * Uses the computed min_ts/max_ts bounds for fast pruning.
 *
 * @param mv           Memview to check
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY used if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @return true if any component's bounds overlap the range, false otherwise
 *         Always returns false if !has_data
 */
bool tl_memview_overlaps(const tl_memview_t* mv, tl_ts_t t1, tl_ts_t t2,
                         bool t2_unbounded);

/*===========================================================================
 * Accessors
 *===========================================================================*/

/**
 * Get immutable view of active tombstones (for read path tombstone collection).
 */
TL_INLINE tl_intervals_imm_t tl_memview_tombs_imm(const tl_memview_t* mv) {
    tl_intervals_imm_t imm;
    imm.data = mv->active_tombs;
    imm.len = mv->active_tombs_len;
    return imm;
}

/*===========================================================================
 * Shared Memview Accessors
 *===========================================================================*/

TL_INLINE const tl_memview_t* tl_memview_shared_view(const tl_memview_shared_t* mv) {
    return mv != NULL ? &mv->view : NULL;
}

TL_INLINE uint64_t tl_memview_shared_epoch(const tl_memview_shared_t* mv) {
    return mv != NULL ? mv->epoch : 0;
}

/**
 * Check if memview has any data (records or tombstones).
 */
TL_INLINE bool tl_memview_has_data(const tl_memview_t* mv) {
    return mv->has_data;
}

/**
 * Get minimum timestamp across all components.
 * Only valid if has_data is true.
 */
TL_INLINE tl_ts_t tl_memview_min_ts(const tl_memview_t* mv) {
    TL_ASSERT(mv->has_data);
    return mv->min_ts;
}

/**
 * Get maximum timestamp across all components.
 * Only valid if has_data is true.
 */
TL_INLINE tl_ts_t tl_memview_max_ts(const tl_memview_t* mv) {
    TL_ASSERT(mv->has_data);
    return mv->max_ts;
}

/**
 * Get count of sealed memruns.
 */
TL_INLINE size_t tl_memview_sealed_len(const tl_memview_t* mv) {
    return mv->sealed_len;
}

/**
 * Get a sealed memrun by index.
 * @param idx Index in [0, sealed_len)
 * @return Pinned memrun pointer (do NOT release - memview owns reference)
 */
TL_INLINE tl_memrun_t* tl_memview_sealed_get(const tl_memview_t* mv, size_t idx) {
    TL_ASSERT(idx < mv->sealed_len);
    return mv->sealed[idx];
}

/**
 * Get active run data.
 */
TL_INLINE const tl_record_t* tl_memview_run_data(const tl_memview_t* mv) {
    return mv->active_run;
}

TL_INLINE size_t tl_memview_run_len(const tl_memview_t* mv) {
    return mv->active_run_len;
}

/**
 * Get active OOO head data (sorted).
 */
TL_INLINE const tl_record_t* tl_memview_ooo_head_data(const tl_memview_t* mv) {
    return mv->active_ooo_head;
}

TL_INLINE size_t tl_memview_ooo_head_len(const tl_memview_t* mv) {
    return mv->active_ooo_head_len;
}

TL_INLINE const tl_ooorunset_t* tl_memview_ooo_runs(const tl_memview_t* mv) {
    return mv->active_ooo_runs;
}

TL_INLINE size_t tl_memview_ooo_total_len(const tl_memview_t* mv) {
    return mv->active_ooo_total_len;
}

/**
 * Get active tombstones data.
 */
TL_INLINE const tl_interval_t* tl_memview_tomb_data(const tl_memview_t* mv) {
    return mv->active_tombs;
}

TL_INLINE size_t tl_memview_tomb_len(const tl_memview_t* mv) {
    return mv->active_tombs_len;
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG
/**
 * Validate memview invariants.
 *
 * Invariants:
 * 1. active_run is sorted (non-decreasing timestamps)
 * 2. active_ooo_head is sorted (by ts, handle)
 * 3. active_ooo_runs (if any) are valid and sorted
 * 4. active_tombs is valid (sorted, non-overlapping, coalesced)
 * 5. sealed memrun pointers non-NULL
 * 6. has_data consistent with actual content
 *
 * Uses accessor functions for field access.
 *
 * @return true if valid, false if any invariant violated
 */
bool tl_memview_validate(const tl_memview_t* mv);
#endif

#endif /* TL_MEMVIEW_H */
