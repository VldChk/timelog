/*
============================================================================

   COMBINED HEADER FILE: delta.h

   Generated from: core\src\delta
   Generated at:   2026-01-30 00:27:14

   This file combines all .h files from the delta/ subfolder.

   Files included:
 *   - tl_flush.h
 *   - tl_memrun.h
 *   - tl_memtable.h
 *   - tl_memview.h
 *   - tl_ooorun.h

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: tl_flush.h
/*   FROM: delta/
/*
/******************************************************************************/
#ifndef TL_FLUSH_H
#define TL_FLUSH_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../storage/tl_segment.h"
#include "tl_memrun.h"

/*===========================================================================
 * Flush Builder
 *
 * Builds L0 segments from sealed memruns. Serialized by flush_mu in tl_timelog.
 *
 * The flush builder:
 * 1. Merges run + OOO runs into a single sorted stream (K-way merge)
 * 2. Passes merged records + tombstones to tl_segment_build_l0
 * 3. Returns the built L0 segment
 *
 * Reference: Write Path LLD Section 4.3
 *===========================================================================*/

/*===========================================================================
 * Flush Context
 *
 * Stack-allocated by caller. Contains configuration for flush build.
 *===========================================================================*/

typedef struct tl_flush_ctx {
    tl_alloc_ctx_t* alloc;              /* Allocator */
    size_t          target_page_bytes;  /* Page size target */
    uint32_t        generation;         /* Generation for L0 segment */
} tl_flush_ctx_t;

/*===========================================================================
 * Two-Way Merge Iterator
 *
 * Produces records in timestamp order from two sorted inputs.
 * Stable merge: if timestamps are equal, prefers first input.
 *
 * Usage:
 *   tl_merge_iter_t it;
 *   tl_merge_iter_init(&it, run, run_len, ooo, ooo_len);
 *   while (!tl_merge_iter_done(&it)) {
 *       const tl_record_t* rec = tl_merge_iter_next(&it);
 *       // Process rec
 *   }
 *
 * Thread Safety:
 * - Not thread-safe. Each thread should use its own iterator.
 *===========================================================================*/

typedef struct tl_merge_iter {
    const tl_record_t* a;       /* First input array (e.g., run) */
    size_t             a_len;   /* Length of first array */
    size_t             a_pos;   /* Current position in first array */

    const tl_record_t* b;       /* Second input array (e.g., ooo) */
    size_t             b_len;   /* Length of second array */
    size_t             b_pos;   /* Current position in second array */
} tl_merge_iter_t;

/*===========================================================================
 * Merge Iterator API
 *===========================================================================*/

/**
 * Initialize a merge iterator.
 *
 * @param it    Iterator to initialize
 * @param a     First sorted array (may be NULL if a_len == 0)
 * @param a_len Length of first array
 * @param b     Second sorted array (may be NULL if b_len == 0)
 * @param b_len Length of second array
 */
void tl_merge_iter_init(tl_merge_iter_t* it,
                         const tl_record_t* a, size_t a_len,
                         const tl_record_t* b, size_t b_len);

/**
 * Peek at the next record without advancing.
 *
 * Stable merge: If both inputs have equal timestamps, peeks from 'a' first.
 *
 * @param it  Iterator
 * @return Pointer to next record, or NULL if exhausted
 */
const tl_record_t* tl_merge_iter_peek(const tl_merge_iter_t* it);

/**
 * Get the next record from the merge.
 *
 * Stable merge: If both inputs have equal timestamps, returns from 'a' first.
 *
 * @param it  Iterator
 * @return Pointer to next record, or NULL if exhausted
 */
const tl_record_t* tl_merge_iter_next(tl_merge_iter_t* it);

/**
 * Check if iterator is exhausted.
 */
TL_INLINE bool tl_merge_iter_done(const tl_merge_iter_t* it) {
    return it->a_pos >= it->a_len && it->b_pos >= it->b_len;
}

/**
 * Get count of remaining records (test/diagnostic helper).
 */
TL_INLINE size_t tl_merge_iter_remaining(const tl_merge_iter_t* it) {
    return (it->a_len - it->a_pos) + (it->b_len - it->b_pos);
}

/*===========================================================================
 * Flush Build API
 *===========================================================================*/

/**
 * Build an L0 segment from a memrun.
 *
 * Algorithm:
 * 1. Check for addition overflow: run_len + ooo_total_len
 * 2. If both run and OOO empty but tombs non-empty: build tombstone-only segment
 * 3. Check for multiplication overflow: total_records * sizeof(tl_record_t)
 * 4. Allocate merged[] buffer
 * 5. Merge run + OOO runs into merged[] using K-way merge
 * 6. Call tl_segment_build_l0(merged, tombstones)
 * 7. Free merged[] buffer
 *
 * @param ctx      Flush context with configuration
 * @param mr       Pinned memrun (caller holds reference)
 * @param out_seg  Output: built L0 segment (caller takes ownership, refcnt = 1)
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EOVERFLOW if total_records * sizeof overflows,
 *         TL_EINVAL if memrun is completely empty (no records, no tombstones)
 */
tl_status_t tl_flush_build(const tl_flush_ctx_t* ctx,
                            const tl_memrun_t* mr,
                            tl_segment_t** out_seg);

#endif /* TL_FLUSH_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_flush.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memrun.h
/*   FROM: delta/
/*
/******************************************************************************/
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
                            tl_interval_t* tombs, size_t tombs_len);

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

/------------------------------------------------------------------------------/
/*   END OF: tl_memrun.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memtable.h
/*   FROM: delta/
/*
/******************************************************************************/
#ifndef TL_MEMTABLE_H
#define TL_MEMTABLE_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_recvec.h"
#include "../internal/tl_intervals.h"
#include "../internal/tl_sync.h"
#include "tl_memrun.h"

/*===========================================================================
 * Memtable: Mutable Write Buffer
 *
 * The memtable accepts writes (inserts and tombstones) and periodically
 * seals them into immutable memruns for flushing to L0 segments.
 *
 * Thread Safety:
 * - Writer operations (insert, delete, seal) require external writer_mu
 * - Sealed queue operations require tl_timelog.memtable_mu (external)
 * - The memtable does NOT own its lock; tl_timelog_t provides it
 *
 * Lock Ordering (from HLD):
 * - maint_mu -> flush_mu -> writer_mu -> memtable_mu
 *
 * CRITICAL: sealed[] is preallocated to sealed_max_runs at init.
 * This eliminates realloc on the seal hot path and simplifies failure handling.
 *
 * Reference: Write Path LLD Section 3.2
 *===========================================================================*/

struct tl_memtable {
    /*-----------------------------------------------------------------------
     * Active State (single-writer, protected by writer_mu externally)
     *-----------------------------------------------------------------------*/
    tl_recvec_t     active_run;       /* Append-only sorted records */
    tl_recvec_t     ooo_head;         /* Mutable OOO head (append-only) */
    tl_intervals_t  active_tombs;     /* Coalesced tombstone intervals */

    tl_ooorunset_t* ooo_runs;         /* Immutable OOO runs (pinned) */

    bool            ooo_head_sorted;  /* Head sorted by (ts, handle) */
    tl_ts_t         ooo_head_last_ts; /* Last ts appended to head */
    tl_handle_t     ooo_head_last_handle; /* Last handle appended to head */
    uint64_t        ooo_next_gen;     /* Monotonic run generation */

    tl_ts_t         last_inorder_ts;  /* Last timestamp appended to active_run */
    size_t          active_bytes_est; /* Estimated bytes (run + ooo + tombs) */

    /*-----------------------------------------------------------------------
     * Sealed Queue (protected by tl_timelog.memtable_mu externally)
     *
     * IMPORTANT: sealed[] is preallocated to sealed_max_runs at init.
     * No realloc ever occurs on the seal path.
     *-----------------------------------------------------------------------*/
    tl_memrun_t**   sealed;           /* FIFO queue (fixed capacity) */
    size_t          sealed_head;      /* Ring buffer head (oldest index) */
    size_t          sealed_len;       /* Current queue length */
    size_t          sealed_max_runs;  /* Fixed capacity (from config) */
    /*
     * M-09: sealed_epoch is protected by memtable_mu only.
     * Updated atomically when sealed queue changes (seal, pop).
     * Used for flush synchronization and memview cache invalidation.
     */
    uint64_t        sealed_epoch;     /* Monotonic counter for queue changes */

    /*-----------------------------------------------------------------------
     * Configuration (immutable after init)
     *-----------------------------------------------------------------------*/
    size_t          memtable_max_bytes; /* Threshold for sealing */
    size_t          ooo_budget_bytes;   /* OOO budget before early seal */
    size_t          ooo_chunk_records;  /* OOO head flush threshold */
    size_t          ooo_run_limit;      /* Max OOO runs before backpressure */

    /*-----------------------------------------------------------------------
     * Metadata
     *-----------------------------------------------------------------------*/
    /*
     * M-09: epoch is protected by writer_mu only.
     * Incremented on every write operation (insert, tombstone).
     * Used for memview cache invalidation - snapshot caching checks if
     * epoch changed to determine if cached memview is still valid.
     */
    uint64_t        epoch;            /* Monotonic counter, increments on memtable changes */

    /*-----------------------------------------------------------------------
     * Allocator (borrowed)
     *-----------------------------------------------------------------------*/
    tl_alloc_ctx_t* alloc;
};

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Initialize a memtable.
 *
 * Preallocates sealed[] to sealed_max_runs capacity. This ensures seal
 * operations never need to realloc.
 *
 * @param mt                 Memtable to initialize
 * @param alloc              Allocator context (borrowed)
 * @param memtable_max_bytes Maximum active bytes before seal
 * @param ooo_budget_bytes   Maximum OOO bytes before early seal
 * @param sealed_max_runs    Fixed sealed queue capacity
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_memtable_init(tl_memtable_t* mt,
                              tl_alloc_ctx_t* alloc,
                              size_t memtable_max_bytes,
                              size_t ooo_budget_bytes,
                              size_t sealed_max_runs);

/**
 * Destroy a memtable.
 * Releases all memruns in the sealed queue and frees active buffers.
 * Does NOT destroy the external lock (caller's responsibility).
 */
void tl_memtable_destroy(tl_memtable_t* mt);

/*===========================================================================
 * Insert Operations (require external writer_mu)
 *
 * IMPORTANT: All insert operations:
 * - Increment epoch on success (for snapshot caching)
 * - Update active_bytes_est (for seal threshold)
 *===========================================================================*/

/**
 * Insert a single record.
 *
 * Algorithm (Write Path LLD Section 3.6, updated for OOO head):
 * - If ts >= last_inorder_ts: append to active_run (fast path)
 * - Else: append to ooo_head (unsorted, sorted on flush/seal)
 *
 * OOO head append is O(1). Sorting is deferred to head flush or seal,
 * giving O(n log n) total instead of O(n?).
 *
 * Updates: epoch++, active_bytes_est += sizeof(tl_record_t)
 *
 * @return TL_OK on success, TL_ENOMEM (no insert), or TL_EBUSY (inserted but
 *         head flush failed; do not retry)
 */
tl_status_t tl_memtable_insert(tl_memtable_t* mt, tl_ts_t ts, tl_handle_t handle);

/**
 * Insert a batch of records.
 *
 * Flag semantics (from timelog.h):
 * - TL_APPEND_HINT_MOSTLY_IN_ORDER: hint that batch is likely sorted.
 *   This is NOT a guarantee. Implementation MUST verify sortedness
 *   before using fast path.
 *
 * Fast path (bulk append to active_run):
 * - Enabled if batch is verified sorted AND records[0].ts >= last_inorder_ts
 * - Verification: FULL check of records[i].ts <= records[i+1].ts for ALL i.
 *   NO SAMPLING.
 *
 * Slow path (per-record insert):
 * - Used when batch is not sorted or starts before last_inorder_ts
 *
 * Updates: epoch++ and active_bytes_est updated ONCE at end for inserted count.
 * All-or-nothing: on failure, no records are inserted and metadata is unchanged.
 *
 * @param records  Array of records
 * @param n        Count of records (0 is a no-op returning TL_OK)
 * @param flags    TL_APPEND_HINT_MOSTLY_IN_ORDER or 0
 * @return TL_OK on success, TL_ENOMEM/TL_EOVERFLOW on failure (no records inserted),
 *         or TL_EBUSY if all records inserted but head flush failed
 */
tl_status_t tl_memtable_insert_batch(tl_memtable_t* mt,
                                      const tl_record_t* records, size_t n,
                                      uint32_t flags);

/**
 * Insert a tombstone interval [t1, t2).
 *
 * Semantics (Write Path LLD Section 3.8):
 * - t1 > t2:  Returns TL_EINVAL (invalid interval)
 * - t1 == t2: Returns TL_OK (no-op, empty interval)
 * - t1 < t2:  Inserts and coalesces
 *
 * Updates on success: epoch++, active_bytes_est += sizeof(tl_interval_t)
 *
 * @return TL_OK, TL_EINVAL (if t1 > t2), TL_ENOMEM
 */
tl_status_t tl_memtable_insert_tombstone(tl_memtable_t* mt, tl_ts_t t1, tl_ts_t t2);

/**
 * Insert an unbounded tombstone [t1, +inf).
 *
 * Updates on success: epoch++, active_bytes_est += sizeof(tl_interval_t)
 *
 * @return TL_OK, TL_ENOMEM
 */
tl_status_t tl_memtable_insert_tombstone_unbounded(tl_memtable_t* mt, tl_ts_t t1);

/*===========================================================================
 * Seal Operations
 *
 * Lock requirements:
 * - Caller MUST hold writer_mu externally (protects active state)
 * - memtable_mu is acquired INTERNALLY by tl_memtable_seal for queue operations
 *
 * CRITICAL INVARIANT: On TL_ENOMEM or TL_EBUSY, active state is PRESERVED.
 * Caller can retry later without data loss.
 *===========================================================================*/

/**
 * Check if memtable should be sealed.
 *
 * Returns true if any of:
 * - active_bytes_est >= memtable_max_bytes
 * - OOO bytes >= ooo_budget_bytes
 *
 * OOO bytes computation:
 *   ooo_bytes = (ooo_head.len + ooo_runs.total_len) * sizeof(tl_record_t)
 *
 * Does NOT require memtable_mu (reads active state under writer_mu only).
 */
bool tl_memtable_should_seal(const tl_memtable_t* mt);

/**
 * Check if OOO budget is exceeded (used for instrumentation).
 *
 * Returns true if:
 * - ooo_budget_bytes > 0 AND
 * - OOO bytes >= ooo_budget_bytes
 *
 * Does NOT require memtable_mu (reads active state under writer_mu only).
 */
bool tl_memtable_ooo_budget_exceeded(const tl_memtable_t* mt);

/**
 * Seal active state into a memrun and push to sealed queue.
 *
 * CRITICAL: This function PRESERVES active state on failure.
 *
 * Algorithm (failure-safe):
 * 1. If active empty: return TL_OK (no-op)
 * 2. Check queue capacity (under memtable_mu): if full, return TL_EBUSY
 * 3. Allocate memrun struct: if fails, return TL_ENOMEM (active preserved)
 * 4. Take ownership of active arrays (tl_recvec_take, tl_intervals_take)
 * 5. Initialize memrun fields, compute bounds (including tombstones)
 * 6. Push to sealed queue (under memtable_mu)
 * 7. Reset active metadata (last_inorder_ts, active_bytes_est)
 *
 * Requires: writer_mu held externally, memtable_mu acquired internally
 *
 * @param mt   Memtable
 * @param mu   Pointer to memtable_mu in tl_timelog (for queue operations)
 * @param cond Pointer to condvar for signaling (may be NULL)
 * @return TL_OK, TL_EBUSY (queue full), TL_ENOMEM (active state PRESERVED)
 */
tl_status_t tl_memtable_seal(tl_memtable_t* mt, tl_mutex_t* mu, tl_cond_t* cond);

/**
 * Check if active state is empty (no records, no tombstones).
 */
bool tl_memtable_is_active_empty(const tl_memtable_t* mt);

/*===========================================================================
 * Sealed Queue Operations (require external memtable_mu)
 *===========================================================================*/

/**
 * Check if sealed queue has memruns awaiting flush.
 */
bool tl_memtable_has_sealed(const tl_memtable_t* mt);

/**
 * Check if sealed queue is full.
 */
bool tl_memtable_is_sealed_full(const tl_memtable_t* mt);

/**
 * Peek and pin the oldest sealed memrun (for flush).
 *
 * Increments refcnt of the returned memrun. Caller MUST call
 * tl_memrun_release when done.
 *
 * @param out  Output: pinned memrun, or NULL if queue empty
 * @return TL_OK (out may be NULL if empty)
 */
tl_status_t tl_memtable_peek_oldest(const tl_memtable_t* mt, tl_memrun_t** out);

/**
 * Pop the oldest sealed memrun (after successful flush).
 *
 * CRITICAL: This function RELEASES the queue's reference to the memrun.
 * The memrun is removed from the queue and tl_memrun_release is called.
 * Caller still holds their pin from peek_oldest and must release it separately.
 *
 * After pop, signals condvar if provided (for backpressure waiters).
 *
 * NOTE: Increments epoch because the sealed queue has changed.
 *
 * @param mt   Memtable
 * @param cond Condvar to signal (may be NULL)
 */
void tl_memtable_pop_oldest(tl_memtable_t* mt, tl_cond_t* cond);

/**
 * Get current sealed queue length.
 */
size_t tl_memtable_sealed_len(const tl_memtable_t* mt);

/**
 * Map logical sealed index [0..sealed_len) to physical array index.
 * Overflow-safe (avoids head+offset wrap before modulo).
 */
TL_INLINE size_t tl_memtable_sealed_index(const tl_memtable_t* mt, size_t offset) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(mt->sealed_max_runs > 0);

    size_t cap = mt->sealed_max_runs;
    size_t head = mt->sealed_head;

    if (cap == 0) {
        return 0;
    }

    if (offset >= cap) {
        offset %= cap;
    }

    /* If head + offset would reach cap, wrap with subtraction */
    if (head >= cap - offset) {
        return head - (cap - offset);
    }
    return head + offset;
}

/**
 * Get sealed memrun at logical index (0 = oldest).
 */
TL_INLINE tl_memrun_t* tl_memtable_sealed_at(const tl_memtable_t* mt, size_t idx) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(idx < mt->sealed_len);
    size_t pos = tl_memtable_sealed_index(mt, idx);
    return mt->sealed[pos];
}

/*===========================================================================
 * Backpressure (Write Path LLD Section 6.1)
 *===========================================================================*/

/**
 * Wait for sealed queue to have space (bounded wait).
 *
 * Requires: memtable_mu held on entry, released during wait, reacquired on return.
 *
 * Implementation uses a loop to handle spurious wakeups:
 *   while (sealed_len >= sealed_max_runs && !timed_out) {
 *       tl_cond_timedwait(cond, mu, remaining_ms);
 *   }
 *
 * @param mt         Memtable
 * @param mu         Memtable mutex (held by caller)
 * @param cond       Condvar to wait on
 * @param timeout_ms Maximum wait time in milliseconds
 * @return true if space available, false if timeout (queue still full)
 */
bool tl_memtable_wait_for_space(const tl_memtable_t* mt, tl_mutex_t* mu,
                                 tl_cond_t* cond, uint32_t timeout_ms);

/*===========================================================================
 * Epoch (for snapshot caching)
 *===========================================================================*/

/**
 * Get current epoch (monotonic write counter).
 */
TL_INLINE uint64_t tl_memtable_epoch(const tl_memtable_t* mt) {
    return mt->epoch;
}

/*===========================================================================
 * Accessors
 *===========================================================================*/

/**
 * Get immutable view of active run (for snapshot).
 */
TL_INLINE const tl_record_t* tl_memtable_run_data(const tl_memtable_t* mt) {
    return tl_recvec_data(&mt->active_run);
}

TL_INLINE size_t tl_memtable_run_len(const tl_memtable_t* mt) {
    return tl_recvec_len(&mt->active_run);
}

/**
 * Get immutable view of OOO head (for snapshot).
 */
TL_INLINE const tl_record_t* tl_memtable_ooo_head_data(const tl_memtable_t* mt) {
    return tl_recvec_data(&mt->ooo_head);
}

TL_INLINE size_t tl_memtable_ooo_head_len(const tl_memtable_t* mt) {
    return tl_recvec_len(&mt->ooo_head);
}

TL_INLINE const tl_ooorunset_t* tl_memtable_ooo_runs(const tl_memtable_t* mt) {
    return mt->ooo_runs;
}

TL_INLINE size_t tl_memtable_ooo_total_len(const tl_memtable_t* mt) {
    size_t head_len = tl_recvec_len(&mt->ooo_head);
    size_t run_len = tl_ooorunset_total_len(mt->ooo_runs);
    if (head_len > SIZE_MAX - run_len) {
        return SIZE_MAX;
    }
    return head_len + run_len;
}

/**
 * Get immutable view of active tombstones (for snapshot).
 */
TL_INLINE tl_intervals_imm_t tl_memtable_tombs_imm(const tl_memtable_t* mt) {
    return tl_intervals_as_imm(&mt->active_tombs);
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG
/**
 * Validate memtable invariants.
 * @return true if valid, false if invariants violated
 *
 * Checks:
 * - active_run is sorted (non-decreasing timestamps)
 * - ooo_head: NO sortedness check (sorted on flush/seal or at capture)
 * - active_tombs is valid (sorted, non-overlapping, coalesced)
 * - sealed[] entries are non-NULL
 * - sealed_len <= sealed_max_runs
 */
bool tl_memtable_validate(const tl_memtable_t* mt);
#endif

#endif /* TL_MEMTABLE_H */


/------------------------------------------------------------------------------/
/*   END OF: tl_memtable.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memview.h
/*   FROM: delta/
/*
/******************************************************************************/
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

/------------------------------------------------------------------------------/
/*   END OF: tl_memview.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_ooorun.h
/*   FROM: delta/
/*
/******************************************************************************/
#ifndef TL_OOORUN_H
#define TL_OOORUN_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_atomic.h"

/*===========================================================================
 * OOO Run: Immutable Sorted Records
 *
 * Represents a sorted run of out-of-order records. Immutable after creation.
 * Reference counted so runs can be pinned by memviews and memruns.
 *===========================================================================*/

typedef struct tl_ooorun {
    tl_atomic_u32   refcnt;     /* Reference count */
    tl_alloc_ctx_t* alloc;      /* Allocator (borrowed) */

    tl_record_t*    records;    /* Sorted by (ts, handle) */
    size_t          len;        /* Record count */

    tl_ts_t         min_ts;     /* records[0].ts */
    tl_ts_t         max_ts;     /* records[len - 1].ts */

    uint64_t        gen;        /* Monotonic generation for tie-breaks */
} tl_ooorun_t;

/*===========================================================================
 * OOO Runset: Immutable Array of Runs
 *
 * Holds a stable array of run pointers. Immutable after creation.
 *===========================================================================*/

typedef struct tl_ooorunset {
    tl_atomic_u32   refcnt;     /* Reference count */
    tl_alloc_ctx_t* alloc;      /* Allocator (borrowed) */

    size_t          count;      /* Number of runs */
    size_t          total_len;  /* Sum of run lengths */

    tl_ooorun_t*    runs[];     /* Flexible array of run pointers */
} tl_ooorunset_t;

/*===========================================================================
 * Run Lifecycle
 *===========================================================================*/

tl_status_t tl_ooorun_create(tl_alloc_ctx_t* alloc,
                              tl_record_t* records, size_t len,
                              uint64_t gen,
                              tl_ooorun_t** out);

tl_ooorun_t* tl_ooorun_acquire(tl_ooorun_t* run);
void tl_ooorun_release(tl_ooorun_t* run);

/*===========================================================================
 * Runset Lifecycle
 *===========================================================================*/

tl_status_t tl_ooorunset_create(tl_alloc_ctx_t* alloc,
                                 tl_ooorun_t* const* runs,
                                 size_t count,
                                 tl_ooorunset_t** out);

tl_status_t tl_ooorunset_append(tl_alloc_ctx_t* alloc,
                                 tl_ooorunset_t* old_set,
                                 tl_ooorun_t* run,
                                 tl_ooorunset_t** out);

tl_ooorunset_t* tl_ooorunset_acquire(tl_ooorunset_t* set);
void tl_ooorunset_release(tl_ooorunset_t* set);

/*===========================================================================
 * Accessors
 *===========================================================================*/

TL_INLINE size_t tl_ooorun_len(const tl_ooorun_t* run) {
    return run->len;
}

TL_INLINE const tl_record_t* tl_ooorun_records(const tl_ooorun_t* run) {
    return run->records;
}

TL_INLINE tl_ts_t tl_ooorun_min_ts(const tl_ooorun_t* run) {
    return run->min_ts;
}

TL_INLINE tl_ts_t tl_ooorun_max_ts(const tl_ooorun_t* run) {
    return run->max_ts;
}

TL_INLINE uint64_t tl_ooorun_gen(const tl_ooorun_t* run) {
    return run->gen;
}

TL_INLINE size_t tl_ooorunset_count(const tl_ooorunset_t* set) {
    return (set == NULL) ? 0 : set->count;
}

TL_INLINE size_t tl_ooorunset_total_len(const tl_ooorunset_t* set) {
    return (set == NULL) ? 0 : set->total_len;
}

TL_INLINE tl_ooorun_t* tl_ooorunset_run_at(const tl_ooorunset_t* set, size_t idx) {
    return set->runs[idx];
}

#endif /* TL_OOORUN_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_ooorun.h
/------------------------------------------------------------------------------/
