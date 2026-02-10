#ifndef TL_MEMRUN_H
#define TL_MEMRUN_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_atomic.h"
#include "../internal/tl_intervals.h"
#include "tl_ooorun.h"

/*===========================================================================
 * Memrun: Sealed Immutable Memtable Snapshot
 *
 * A memrun is the sealed, immutable result of a memtable seal operation.
 * It contains:
 * - run: sorted append-only records (from active_run)
 * - ooo_runs: immutable sorted OOO runs (sorted by ts+handle, created from head)
 * - tombs: coalesced tombstone intervals (from active_tombs)
 *
 * Reference Counting:
 * - Sealed queue owns one reference
 * - Flush pins (acquires) while building L0 segment
 * - Memview (snapshot) pins if needed for reads
 * - Released when refcnt hits 0
 *
 * Thread Safety:
 * - Immutable after creation (no synchronization needed for reads)
 * - refcnt uses atomic operations
 *
 * Bounds Computation (CRITICAL for read-path correctness):
 * - min_ts = min(run[0].ts, ooo_min_ts, tombs[0].start)
 * - max_ts = max(run[N-1].ts, ooo_max_ts, max_tomb_end)
 * - max_tomb_end = TL_TS_MAX if any unbounded, else max(tombs[i].end - 1)
 *
 * This ensures tombstones outside record bounds are NOT pruned during
 * read-path overlap checks.
 *
 * Reference: Write Path LLD Section 3.5
 *===========================================================================*/

struct tl_memrun {
    /*-----------------------------------------------------------------------
     * Record Arrays (owned, allocated from alloc)
     *-----------------------------------------------------------------------*/
    tl_record_t*    run;         /* Sorted in-order records */
    size_t          run_len;     /* Count of in-order records */

    tl_ooorunset_t* ooo_runs;    /* Immutable OOO runs (pinned) */
    size_t          ooo_total_len; /* Total OOO records across runs */
    size_t          ooo_run_count; /* Number of OOO runs */
    tl_ts_t         ooo_min_ts;  /* Min timestamp across OOO runs */
    tl_ts_t         ooo_max_ts;  /* Max timestamp across OOO runs */

    /*-----------------------------------------------------------------------
     * Tombstones (owned, allocated from alloc)
     *-----------------------------------------------------------------------*/
    tl_interval_t*  tombs;       /* Coalesced intervals */
    size_t          tombs_len;   /* Count of intervals */

    /*-----------------------------------------------------------------------
     * Bounds (computed at seal time - includes records AND tombstones)
     *-----------------------------------------------------------------------*/
    tl_ts_t         min_ts;      /* Min of records AND tombstone starts */
    tl_ts_t         max_ts;      /* Max of records AND tombstone ends */

    /*-----------------------------------------------------------------------
     * Lifecycle
     *-----------------------------------------------------------------------*/
    tl_atomic_u32   refcnt;      /* Reference count */
    tl_alloc_ctx_t* alloc;       /* Allocator (borrowed) */

    /*-----------------------------------------------------------------------
     * Tombstone watermark
     *-----------------------------------------------------------------------*/
    tl_seq_t        applied_seq; /* Tombstones <= applied_seq already applied */
};

/*===========================================================================
 * Creation
 *===========================================================================*/

/**
 * Create a memrun by taking ownership of arrays.
 *
 * The caller must NOT free the arrays after this call succeeds.
 * On failure, the arrays are NOT freed - caller retains ownership for rollback.
 *
 * @param alloc     Allocator context (borrowed)
 * @param run       Sorted in-order records (ownership transferred on success)
 * @param run_len   Count of in-order records
 * @param ooo_runs  OOO runset (ownership transferred on success)
 * @param tombs     Tombstone intervals (ownership transferred on success)
 * @param tombs_len Count of intervals
 * @param out       Output: created memrun
 * @return TL_OK on success,
 *         TL_EINVAL if all inputs are empty (run_len=0 AND ooo_total_len=0 AND tombs_len=0),
 *         TL_ENOMEM on allocation failure (arrays NOT freed, caller retains ownership)
 *
 * Bounds computation includes tombstones:
 * - min_ts = min(run[0].ts, ooo_min_ts, tombs[0].start) where applicable
 * - max_ts = max(run[N-1].ts, ooo_max_ts, max_tomb_end) where applicable
 * - For unbounded tombstones, max_ts = TL_TS_MAX
 *
 * Returned memrun has refcnt = 1 (caller owns reference).
 */
tl_status_t tl_memrun_create(tl_alloc_ctx_t* alloc,
                              tl_record_t* run, size_t run_len,
                              tl_ooorunset_t* ooo_runs,
                              tl_interval_t* tombs, size_t tombs_len,
                              tl_seq_t applied_seq,
                              tl_memrun_t** out);

/**
 * Allocate a memrun struct (zeroed).
 * Arrays are NOT owned until tl_memrun_init() succeeds.
 */
tl_status_t tl_memrun_alloc(tl_alloc_ctx_t* alloc, tl_memrun_t** out);

/**
 * Initialize a pre-allocated memrun in-place.
 * Takes ownership of arrays on success.
 */
tl_status_t tl_memrun_init(tl_memrun_t* mr,
                            tl_alloc_ctx_t* alloc,
                            tl_record_t* run, size_t run_len,
                            tl_ooorunset_t* ooo_runs,
                            tl_interval_t* tombs, size_t tombs_len,
                            tl_seq_t applied_seq);

/*===========================================================================
 * Reference Counting
 *
 * Memory ordering:
 * - Acquire (increment): relaxed is sufficient (already have a reference)
 * - Release (decrement): release ordering, acquire fence before destruction
 *
 * Pattern for release:
 *   uint32_t old = tl_atomic_fetch_sub_u32(&refcnt, 1, TL_MO_RELEASE);
 *   if (old == 1) {
 *       tl_atomic_fence(TL_MO_ACQUIRE);
 *       destroy(obj);
 *   }
 *===========================================================================*/

/**
 * Acquire a reference (increment refcnt).
 * Returns the memrun for chaining.
 */
tl_memrun_t* tl_memrun_acquire(tl_memrun_t* mr);

/**
 * Release a reference.
 * Destroys when refcnt reaches 0.
 * Frees run, ooo, tombs arrays and the memrun struct itself.
 */
void tl_memrun_release(tl_memrun_t* mr);

/**
 * Get current reference count (for debugging).
 */
TL_INLINE uint32_t tl_memrun_refcnt(const tl_memrun_t* mr) {
    return tl_atomic_load_relaxed_u32(&mr->refcnt);
}

/*===========================================================================
 * Internal Helpers (M-11: Exposed for reuse by tl_memtable.c)
 *===========================================================================*/

/**
 * Compute bounds for memrun (includes records AND tombstones).
 *
 * CRITICAL: Bounds MUST include tombstones, not just records.
 * This ensures tombstones outside record bounds are NOT pruned during
 * read-path overlap checks (which would cause missed deletes).
 *
 * Assumes ooo_min_ts/ooo_max_ts are already set if OOO runs exist.
 */
void tl__memrun_compute_bounds(tl_memrun_t* mr);

/*===========================================================================
 * Accessors
 *===========================================================================*/

TL_INLINE size_t tl_memrun_run_len(const tl_memrun_t* mr) {
    return mr->run_len;
}

TL_INLINE size_t tl_memrun_ooo_len(const tl_memrun_t* mr) {
    return mr->ooo_total_len;
}

TL_INLINE size_t tl_memrun_tombs_len(const tl_memrun_t* mr) {
    return mr->tombs_len;
}

TL_INLINE bool tl_memrun_has_records(const tl_memrun_t* mr) {
    return mr->run_len > 0 || mr->ooo_total_len > 0;
}

TL_INLINE bool tl_memrun_has_tombstones(const tl_memrun_t* mr) {
    return mr->tombs_len > 0;
}

TL_INLINE bool tl_memrun_is_empty(const tl_memrun_t* mr) {
    return mr->run_len == 0 && mr->ooo_total_len == 0 && mr->tombs_len == 0;
}

TL_INLINE tl_ts_t tl_memrun_min_ts(const tl_memrun_t* mr) {
    return mr->min_ts;
}

TL_INLINE tl_ts_t tl_memrun_max_ts(const tl_memrun_t* mr) {
    return mr->max_ts;
}

TL_INLINE const tl_record_t* tl_memrun_run_data(const tl_memrun_t* mr) {
    return mr->run;
}

TL_INLINE size_t tl_memrun_ooo_run_count(const tl_memrun_t* mr) {
    return mr->ooo_run_count;
}

TL_INLINE const tl_ooorunset_t* tl_memrun_ooo_runs(const tl_memrun_t* mr) {
    return mr->ooo_runs;
}

TL_INLINE const tl_ooorun_t* tl_memrun_ooo_run_at(const tl_memrun_t* mr, size_t idx) {
    TL_ASSERT(mr->ooo_runs != NULL);
    return mr->ooo_runs->runs[idx];
}

TL_INLINE const tl_interval_t* tl_memrun_tombs_data(const tl_memrun_t* mr) {
    return mr->tombs;
}

TL_INLINE tl_seq_t tl_memrun_applied_seq(const tl_memrun_t* mr) {
    return mr->applied_seq;
}

/**
 * Get immutable view of tombstones (for read path).
 */
TL_INLINE tl_intervals_imm_t tl_memrun_tombs_imm(const tl_memrun_t* mr) {
    tl_intervals_imm_t imm;
    imm.data = mr->tombs;
    imm.len = mr->tombs_len;
    return imm;
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG
/**
 * Validate memrun invariants.
 * @return true if valid, false if invariants violated
 *
 * Checks:
 * - run[] is sorted by timestamp (non-decreasing)
 * - OOO runs are sorted by (ts, handle)
 * - tombs[] is sorted by start (non-decreasing)
 * - tombs[] is non-overlapping and coalesced
 * - min_ts/max_ts are correct (include tombstones)
 * - refcnt > 0
 */
bool tl_memrun_validate(const tl_memrun_t* mr);
#endif

#endif /* TL_MEMRUN_H */
