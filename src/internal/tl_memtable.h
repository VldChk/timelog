#ifndef TL_MEMTABLE_H
#define TL_MEMTABLE_H

#include "tl_defs.h"
#include "tl_alloc.h"
#include "tl_atomic.h"
#include "tl_thread.h"
#include "tl_recvec.h"
#include "tl_intervals.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Forward declarations */
typedef struct tl_memrun   tl_memrun_t;
typedef struct tl_memtable tl_memtable_t;
typedef struct tl_memview  tl_memview_t;

/*===========================================================================
 * Memrun (sealed immutable run)
 *===========================================================================*/

/**
 * Sealed immutable memrun.
 *
 * Created by sealing active memtable buffers. Contains:
 * - In-order records (already sorted by timestamp)
 * - Out-of-order records (sorted at seal time)
 * - Tombstones captured at seal time
 *
 * Immutable after creation. Pinnable by snapshots until flushed/published.
 */
struct tl_memrun {
    /* In-order part (already sorted by ts at insert time) */
    tl_record_t*     run;
    size_t           run_len;

    /* Out-of-order part (sorted at seal time) */
    tl_record_t*     ooo;
    size_t           ooo_len;

    /* Tombstones captured at seal time (disjoint sorted intervals) */
    tl_interval_t*   tombs;
    size_t           tombs_len;

    /* Cached bounds for fast pruning */
    tl_ts_t          min_ts;
    tl_ts_t          max_ts;

    /* OOO bounds tracked during insert (for cheap min/max at seal) */
    tl_ts_t          ooo_min_ts;
    tl_ts_t          ooo_max_ts;

    /* Allocator used */
    const tl_allocator_t* alloc;

    /* Lifetime: reference count for snapshot pinning */
    tl_atomic_u32_t  refcnt;

    /* Publication state: true once flushed and published */
    bool             is_published;
};

uint32_t tl_memrun_acquire(tl_memrun_t* mr);
uint32_t tl_memrun_release(tl_memrun_t* mr);

TL_INLINE size_t tl_memrun_record_count(const tl_memrun_t* mr) {
    return mr ? (mr->run_len + mr->ooo_len) : 0;
}

TL_INLINE bool tl_memrun_empty(const tl_memrun_t* mr) {
    return mr == NULL ||
           (mr->run_len == 0 && mr->ooo_len == 0 && mr->tombs_len == 0);
}

/*===========================================================================
 * Memtable (delta manager)
 *===========================================================================*/

/**
 * Internal backpressure constants.
 */
#define TL_SEALED_MAX_RUNS     4   /* Max sealed memruns before backpressure */
#define TL_OOO_BUDGET_PERCENT  5   /* Max OOO as % of memtable size before early seal */

/**
 * Memtable: manages active delta buffers and sealed memrun queue.
 *
 * Threading model:
 * - Single external writer (enforced by tl_timelog writer_mu)
 * - Internal mutex protects sealed queue for concurrent flush/snapshot access
 * - Active buffers accessed only by writer thread
 */
struct tl_memtable {
    /* Allocator */
    const tl_allocator_t* alloc;

    /* Active mutable buffers (single-writer, no lock needed for these) */
    tl_recvec_t      active_run;      /* Append-only, sorted by ts */
    tl_recvec_t      active_ooo;      /* Append-only, unsorted */
    tl_intervals_t   active_tombs;    /* Disjoint sorted intervals [t1,t2) */

    /* OOO tracking for cheap min/max at seal */
    tl_ts_t          active_ooo_min;
    tl_ts_t          active_ooo_max;
    bool             active_ooo_has_data;

    /* Last in-order timestamp (for in-order/OOO classification) */
    tl_ts_t          active_last_inorder_ts;
    bool             active_has_inorder;

    /* Sealed immutable runs waiting to flush/publish */
    tl_memrun_t**    sealed;          /* Array of pointers */
    size_t           sealed_len;
    size_t           sealed_cap;

    /* Internal mutex protecting sealed queue */
    tl_mutex_t       mu;

    /* Configuration thresholds */
    size_t           memtable_max_bytes;
    size_t           target_page_bytes;

    /* Accounting */
    size_t           active_bytes_est;   /* Approximate memory footprint */
    uint64_t         write_count;        /* Monotonic counter (debug/stats) */
    uint64_t         seal_count;         /* Number of seals performed */
};

/**
 * Create a new memtable.
 *
 * @param alloc             Allocator to use
 * @param memtable_max_bytes Threshold for sealing
 * @param target_page_bytes  Page size for flush estimation
 * @param out               Output pointer
 * @return TL_OK on success
 */
tl_status_t tl_memtable_create(const tl_allocator_t* alloc,
                                size_t memtable_max_bytes,
                                size_t target_page_bytes,
                                tl_memtable_t** out);

/**
 * Destroy memtable and all resources.
 *
 * WARNING: Caller must ensure no snapshots reference sealed memruns.
 */
void tl_memtable_destroy(tl_memtable_t* mt);

/*===========================================================================
 * Ingestion API
 *===========================================================================*/

/**
 * Insert a single record.
 *
 * Records go to active_run if in-order, active_ooo otherwise.
 *
 * @param mt     Memtable
 * @param ts     Timestamp
 * @param handle Handle
 * @return TL_OK on success, TL_ENOMEM if allocation fails
 */
tl_status_t tl_memtable_insert(tl_memtable_t* mt, tl_ts_t ts, tl_handle_t handle);

/**
 * Insert a batch of records.
 *
 * @param mt      Memtable
 * @param records Records to insert
 * @param n       Number of records
 * @param flags   Hint flags (TL_APPEND_HINT_MOSTLY_ORDER)
 * @return TL_OK on success
 */
tl_status_t tl_memtable_insert_batch(tl_memtable_t* mt,
                                      const tl_record_t* records,
                                      size_t n,
                                      uint32_t flags);

/**
 * Add a tombstone interval [t1, t2).
 *
 * Coalesces with existing intervals.
 *
 * @param mt Memtable
 * @param t1 Start (inclusive)
 * @param t2 End (exclusive)
 * @return TL_OK on success, TL_EINVAL if t1 > t2
 */
tl_status_t tl_memtable_add_tombstone(tl_memtable_t* mt, tl_ts_t t1, tl_ts_t t2);

/*===========================================================================
 * Sealing API
 *===========================================================================*/

/**
 * Check if memtable needs sealing based on thresholds.
 *
 * Conditions:
 * - active_bytes_est >= memtable_max_bytes
 * - OOO buffer exceeds budget
 */
bool tl_memtable_should_seal(const tl_memtable_t* mt);

/**
 * Check if sealed queue has room (backpressure check).
 */
bool tl_memtable_can_seal(const tl_memtable_t* mt);

/**
 * Seal active buffers into an immutable memrun.
 *
 * @param mt Memtable
 * @return TL_OK if sealed, TL_EOF if active is empty, TL_EBUSY if backpressure
 */
tl_status_t tl_memtable_seal_active(tl_memtable_t* mt);

/**
 * Get count of sealed memruns.
 */
size_t tl_memtable_sealed_count(const tl_memtable_t* mt);

/**
 * Get the oldest sealed memrun (for FIFO flush).
 *
 * Does NOT remove from queue or transfer ownership.
 *
 * @return Oldest memrun, or NULL if none
 */
tl_memrun_t* tl_memtable_peek_oldest_sealed(tl_memtable_t* mt);

/**
 * Remove the oldest sealed memrun after successful publish.
 *
 * Called after flush + manifest publish completes.
 * Marks memrun as published and removes from queue.
 *
 * @param mt Memtable
 * @return The removed memrun (caller should release when safe)
 */
tl_memrun_t* tl_memtable_pop_oldest_sealed(tl_memtable_t* mt);

/*===========================================================================
 * Memview (Snapshot View)
 *===========================================================================*/

/**
 * Snapshot view of memtable for read queries.
 *
 * Captures:
 * - Pinned references to all non-published sealed memruns
 * - Snapshot of active buffers at capture time
 *
 * Immutable after creation. Must be released when done.
 */
struct tl_memview {
    /* Pinned sealed memruns (non-published only) */
    tl_memrun_t**    sealed;
    size_t           sealed_len;

    /* Snapshot of active state (copied at capture time) */
    tl_record_t*     active_run;
    size_t           active_run_len;
    tl_record_t*     active_ooo;
    size_t           active_ooo_len;
    tl_interval_t*   active_tombs;
    size_t           active_tombs_len;

    /* Bounds */
    tl_ts_t          min_ts;
    tl_ts_t          max_ts;

    /* Allocator */
    const tl_allocator_t* alloc;
};

/**
 * Capture a consistent memview snapshot.
 *
 * Called during snapshot acquisition under view_seq protection.
 *
 * @param mt  Memtable
 * @param out Output pointer
 * @return TL_OK on success
 */
tl_status_t tl_memtable_snapshot(tl_memtable_t* mt, tl_memview_t** out);

/**
 * Release a memview and unpin all referenced memruns.
 */
void tl_memview_release(tl_memview_t* mv);

/**
 * Check if memview is empty (no records, no tombstones).
 */
bool tl_memview_empty(const tl_memview_t* mv);

/**
 * Get total record count in memview.
 */
size_t tl_memview_record_count(const tl_memview_t* mv);

#ifdef __cplusplus
}
#endif

#endif /* TL_MEMTABLE_H */
