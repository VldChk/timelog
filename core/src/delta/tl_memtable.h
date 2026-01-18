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
    tl_recvec_t     active_ooo;       /* Sorted OOO records */
    tl_intervals_t  active_tombs;     /* Coalesced tombstone intervals */

    tl_ts_t         last_inorder_ts;  /* Last timestamp appended to active_run */
    size_t          active_bytes_est; /* Estimated bytes (run + ooo + tombs) */

    /*-----------------------------------------------------------------------
     * Sealed Queue (protected by tl_timelog.memtable_mu externally)
     *
     * IMPORTANT: sealed[] is preallocated to sealed_max_runs at init.
     * No realloc ever occurs on the seal path.
     *-----------------------------------------------------------------------*/
    tl_memrun_t**   sealed;           /* FIFO queue (fixed capacity) */
    size_t          sealed_len;       /* Current queue length */
    size_t          sealed_max_runs;  /* Fixed capacity (from config) */

    /*-----------------------------------------------------------------------
     * Configuration (immutable after init)
     *-----------------------------------------------------------------------*/
    size_t          memtable_max_bytes; /* Threshold for sealing */
    size_t          ooo_budget_bytes;   /* OOO budget before early seal */

    /*-----------------------------------------------------------------------
     * Metadata
     *-----------------------------------------------------------------------*/
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
 * Algorithm (Write Path LLD Section 3.6):
 * - If ts >= last_inorder_ts: append to active_run (fast path)
 * - Else: insert into active_ooo (sorted insert, slow path)
 *
 * Updates: epoch++, active_bytes_est += sizeof(tl_record_t)
 *
 * @return TL_OK on success, TL_ENOMEM (active state preserved on failure)
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
 * On partial failure, only the successfully inserted count is added.
 *
 * @param records  Array of records
 * @param n        Count of records (0 is a no-op returning TL_OK)
 * @param flags    TL_APPEND_HINT_MOSTLY_IN_ORDER or 0
 * @return TL_OK on success, TL_ENOMEM (on partial failure, inserted records remain)
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
 *   ooo_bytes = active_ooo.len * sizeof(tl_record_t)
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
tl_status_t tl_memtable_peek_oldest(tl_memtable_t* mt, tl_memrun_t** out);

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
bool tl_memtable_wait_for_space(tl_memtable_t* mt, tl_mutex_t* mu,
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
 * Get immutable view of active ooo (for snapshot).
 */
TL_INLINE const tl_record_t* tl_memtable_ooo_data(const tl_memtable_t* mt) {
    return tl_recvec_data(&mt->active_ooo);
}

TL_INLINE size_t tl_memtable_ooo_len(const tl_memtable_t* mt) {
    return tl_recvec_len(&mt->active_ooo);
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
 * - active_run is sorted
 * - active_ooo is sorted
 * - active_tombs is valid (sorted, non-overlapping, coalesced)
 * - sealed[] entries are non-NULL
 * - sealed_len <= sealed_max_runs
 */
bool tl_memtable_validate(const tl_memtable_t* mt);
#endif

#endif /* TL_MEMTABLE_H */
