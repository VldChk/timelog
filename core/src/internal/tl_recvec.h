#ifndef TL_RECVEC_H
#define TL_RECVEC_H

#include "tl_defs.h"
#include "tl_alloc.h"

/*===========================================================================
 * Record Vector
 *
 * A dynamic array of tl_record_t that provides:
 * - Amortized O(1) append for sorted and unsorted insertions
 * - Binary search helpers (lower_bound, upper_bound) for range queries
 * - Reserve/clear/destroy lifecycle
 *
 * Used by:
 * - tl_memtable_t.active_run (append-only sorted records)
 * - tl_memtable_t.ooo_head (append-only OOO head; may be unsorted)
 * - tl_memrun_t.run (sealed array, always sorted)
 * - OOO runs (sorted arrays created from head flush)
 * - Page builder (sorted record stream)
 *
 * Thread Safety:
 * - Not thread-safe. Caller must provide synchronization.
 *===========================================================================*/

/**
 * Dynamic array of records.
 *
 * Design notes:
 * - The allocator pointer is borrowed; the caller owns the allocator lifetime.
 * - Capacity growth uses 2x strategy (amortized O(1) append).
 * - Zero-length vectors have data == NULL, len == 0, cap == 0.
 */
typedef struct tl_recvec {
    tl_record_t*    data;     /* Array of records */
    size_t          len;      /* Current number of records */
    size_t          cap;      /* Allocated capacity */
    tl_alloc_ctx_t* alloc;    /* Allocator context (borrowed, not owned) */
} tl_recvec_t;

/*---------------------------------------------------------------------------
 * Lifecycle
 *---------------------------------------------------------------------------*/

/**
 * Initialize an empty record vector.
 * @param rv    Vector to initialize
 * @param alloc Allocator context (must outlive the vector)
 */
void tl_recvec_init(tl_recvec_t* rv, tl_alloc_ctx_t* alloc);

/**
 * Destroy a record vector and free memory.
 * Idempotent: safe to call on already-destroyed or zero-initialized vectors.
 * After this call, rv is in a valid empty state (can be destroyed again or reused).
 */
void tl_recvec_destroy(tl_recvec_t* rv);

/**
 * Clear the vector (set len = 0) without freeing memory.
 * Useful for reuse without reallocation.
 */
void tl_recvec_clear(tl_recvec_t* rv);

/*---------------------------------------------------------------------------
 * Capacity Management
 *---------------------------------------------------------------------------*/

/**
 * Ensure capacity for at least min_cap records.
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_recvec_reserve(tl_recvec_t* rv, size_t min_cap);

/**
 * Shrink capacity to exactly fit current length.
 * If len == 0: frees backing storage and sets data=NULL, cap=0.
 * If len == cap: no-op.
 * Otherwise: realloc to len.
 * @return TL_OK on success, TL_ENOMEM if realloc fails (capacity unchanged)
 */
tl_status_t tl_recvec_shrink_to_fit(tl_recvec_t* rv);

/*---------------------------------------------------------------------------
 * Insertion
 *---------------------------------------------------------------------------*/

/**
 * Append a single record to the end.
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_recvec_push(tl_recvec_t* rv, tl_ts_t ts, tl_handle_t handle);

/**
 * Append multiple records to the end.
 * @param records Array of records to append
 * @param n       Number of records
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_recvec_push_n(tl_recvec_t* rv, const tl_record_t* records, size_t n);

/**
 * Insert a record at a specific index, shifting subsequent records.
 * @param idx Index to insert at (0 <= idx <= len)
 * @return TL_OK on success, TL_ENOMEM on allocation failure, TL_EINVAL if idx > len
 */
tl_status_t tl_recvec_insert(tl_recvec_t* rv, size_t idx, tl_ts_t ts, tl_handle_t handle);

/*---------------------------------------------------------------------------
 * Sorting
 *---------------------------------------------------------------------------*/

/**
 * Sort the record vector by (ts, handle) (non-decreasing).
 * Uses stdlib qsort. O(n log n) complexity.
 *
 * C-14 fix: Supports deferred sort strategy where OOO records are
 * appended unsorted during insertion and sorted once at seal/capture time.
 * This gives O(n) + O(n log n) total vs O(n^2) for sorted insert.
 *
 * @param rv Vector to sort (modified in place)
 */
void tl_recvec_sort(tl_recvec_t* rv);

/*---------------------------------------------------------------------------
 * Binary Search (for sorted vectors)
 *---------------------------------------------------------------------------*/

/**
 * Find the first index where rv->data[i].ts >= ts.
 * Returns rv->len if all records have ts < target.
 *
 * Precondition: rv is sorted by ts (non-decreasing).
 */
size_t tl_recvec_lower_bound(const tl_recvec_t* rv, tl_ts_t ts);

/**
 * Find the first index where rv->data[i].ts > ts.
 * Returns rv->len if all records have ts <= target.
 *
 * Precondition: rv is sorted by ts (non-decreasing).
 */
size_t tl_recvec_upper_bound(const tl_recvec_t* rv, tl_ts_t ts);

/**
 * Find the range [lo, hi) of indices where rv->data[i].ts is in [t1, t2).
 * @param lo Output: first index with ts >= t1
 * @param hi Output: first index with ts >= t2
 *
 * Precondition: rv is sorted by ts (non-decreasing).
 */
void tl_recvec_range_bounds(const tl_recvec_t* rv, tl_ts_t t1, tl_ts_t t2,
                            size_t* lo, size_t* hi);

/*---------------------------------------------------------------------------
 * Validation Helpers (Debug)
 *---------------------------------------------------------------------------*/

/**
 * Validate that all records are within [min_ts, max_ts] (inclusive).
 * Returns true if bounds are satisfied or len == 0.
 */
TL_INLINE bool tl_records_validate_bounds(const tl_record_t* records, size_t len,
                                          tl_ts_t min_ts, tl_ts_t max_ts) {
    if (len == 0) {
        return true;
    }
    TL_ASSERT(records != NULL);
    for (size_t i = 0; i < len; i++) {
        if (records[i].ts < min_ts || records[i].ts > max_ts) {
            return false;
        }
    }
    return true;
}

/*---------------------------------------------------------------------------
 * Accessors
 *---------------------------------------------------------------------------*/

/**
 * Get pointer to record at index (no bounds check in release).
 */
TL_INLINE const tl_record_t* tl_recvec_get(const tl_recvec_t* rv, size_t idx) {
    TL_ASSERT(idx < rv->len);
    return &rv->data[idx];
}

/**
 * Get mutable pointer to record at index.
 */
TL_INLINE tl_record_t* tl_recvec_get_mut(tl_recvec_t* rv, size_t idx) {
    TL_ASSERT(idx < rv->len);
    return &rv->data[idx];
}

TL_INLINE size_t tl_recvec_len(const tl_recvec_t* rv) {
    return rv->len;
}

TL_INLINE bool tl_recvec_is_empty(const tl_recvec_t* rv) {
    return rv->len == 0;
}

/**
 * Get raw data pointer (for bulk operations).
 * May be NULL if len == 0.
 */
TL_INLINE const tl_record_t* tl_recvec_data(const tl_recvec_t* rv) {
    return rv->data;
}

/**
 * Take ownership of the internal array and reset vector to empty.
 * Caller is responsible for freeing the returned array via tl__free().
 * @param out_len Output: length of returned array
 * @return Array pointer (may be NULL if empty)
 */
tl_record_t* tl_recvec_take(tl_recvec_t* rv, size_t* out_len);

#endif /* TL_RECVEC_H */
