#ifndef TL_RECVEC_H
#define TL_RECVEC_H

#include "tl_defs.h"
#include "tl_alloc.h"

/*===========================================================================
 * Record Vector
 *
 * Dynamic array of tl_record_t with the operations the engine needs in one
 * place: amortised O(1) append (geometric growth), in-place sort, and
 * lower_bound/upper_bound for half-open range queries.
 *
 * The vector backs every contiguous record container in the engine — the
 * memtable's active run and OOO head, sealed memruns, OOO runs flushed
 * from the head, and the page builder's input stream. Some callers keep
 * the vector sorted on every insert; others (notably the OOO head) append
 * without sorting and call tl_recvec_sort() at seal time.
 *
 * Not thread-safe; callers serialise access externally.
 *===========================================================================*/

/**
 * Dynamic record array. The allocator is borrowed and must outlive the
 * vector. A vector that has never received an allocation has data == NULL,
 * len == 0, cap == 0 — this is the canonical "empty" state used by both
 * fresh init and post-destroy.
 */
typedef struct tl_recvec {
    tl_record_t*    data;
    size_t          len;
    size_t          cap;
    tl_alloc_ctx_t* alloc;
} tl_recvec_t;

/*---------------------------------------------------------------------------
 * Lifecycle
 *---------------------------------------------------------------------------*/

/** @param alloc Borrowed allocator; must outlive the vector. */
void tl_recvec_init(tl_recvec_t* rv, tl_alloc_ctx_t* alloc);

/**
 * Release storage and reset to the canonical empty state. Idempotent on
 * already-destroyed or zero-initialised vectors so cleanup paths need not
 * track initialisation progress.
 */
void tl_recvec_destroy(tl_recvec_t* rv);

/** Reset length to zero without releasing the backing storage. */
void tl_recvec_clear(tl_recvec_t* rv);

/*---------------------------------------------------------------------------
 * Capacity Management
 *---------------------------------------------------------------------------*/

/** @return TL_OK on success, TL_ENOMEM on allocation failure. */
tl_status_t tl_recvec_reserve(tl_recvec_t* rv, size_t min_cap);

/**
 * Shrink the allocation to match the current length. An empty vector is
 * fully released back to the canonical zero state. On failure the existing
 * allocation is preserved and capacity is unchanged.
 */
tl_status_t tl_recvec_shrink_to_fit(tl_recvec_t* rv);

/*---------------------------------------------------------------------------
 * Insertion
 *---------------------------------------------------------------------------*/

tl_status_t tl_recvec_push(tl_recvec_t* rv, tl_ts_t ts, tl_handle_t handle);

tl_status_t tl_recvec_push_n(tl_recvec_t* rv, const tl_record_t* records, size_t n);

/**
 * Insert at position idx (0 <= idx <= len), shifting the tail. O(len-idx).
 * @return TL_OK, TL_ENOMEM on allocation failure, TL_EINVAL if idx > len.
 */
tl_status_t tl_recvec_insert(tl_recvec_t* rv, size_t idx, tl_ts_t ts, tl_handle_t handle);

/*---------------------------------------------------------------------------
 * Sorting
 *---------------------------------------------------------------------------*/

/**
 * Stable-ish in-place sort by (ts, handle) ascending, via qsort.
 *
 * Enables the deferred-sort strategy used by the OOO head: callers may
 * append unsorted records in O(1) and pay the O(n log n) sort cost once
 * at seal time, instead of paying O(n) per insertion (O(n^2) total).
 */
void tl_recvec_sort(tl_recvec_t* rv);

/**
 * Sort by (ts, handle) and permute a parallel sequence array in lockstep,
 * so that seqs[i] still pertains to the record that ends up at index i.
 * Allocates a small temporary buffer to keep the pairing intact during the
 * underlying qsort.
 *
 * @param seqs Parallel array; must have rv->len entries.
 * @return TL_OK on success, TL_ENOMEM on allocation failure.
 */
tl_status_t tl_recvec_sort_with_seqs(tl_recvec_t* rv, tl_seq_t* seqs);

/*---------------------------------------------------------------------------
 * Binary Search (for sorted vectors)
 *---------------------------------------------------------------------------*/

/**
 * First index i such that rv->data[i].ts >= ts; rv->len if no such index.
 * Precondition: rv is sorted by ts non-decreasing.
 */
size_t tl_recvec_lower_bound(const tl_recvec_t* rv, tl_ts_t ts);

/**
 * First index i such that rv->data[i].ts > ts; rv->len if no such index.
 * Precondition: rv is sorted by ts non-decreasing.
 */
size_t tl_recvec_upper_bound(const tl_recvec_t* rv, tl_ts_t ts);

/**
 * Compute the [lo, hi) index range matching the half-open timestamp
 * window [t1, t2). Precondition: rv is sorted by ts non-decreasing.
 */
void tl_recvec_range_bounds(const tl_recvec_t* rv, tl_ts_t t1, tl_ts_t t2,
                            size_t* lo, size_t* hi);

/*---------------------------------------------------------------------------
 * Validation Helpers (Debug)
 *---------------------------------------------------------------------------*/

/** True if every record's ts lies inside the closed interval [min_ts, max_ts]. */
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

/** Bounds-checked in debug builds only. */
TL_INLINE const tl_record_t* tl_recvec_get(const tl_recvec_t* rv, size_t idx) {
    TL_ASSERT(idx < rv->len);
    return &rv->data[idx];
}

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

/** Raw data pointer for bulk operations. May be NULL when len == 0. */
TL_INLINE const tl_record_t* tl_recvec_data(const tl_recvec_t* rv) {
    return rv->data;
}

/**
 * Detach the backing array. The vector resets to the canonical empty
 * state; the caller becomes responsible for freeing the buffer via
 * tl__free() against the same allocator used to construct the vector.
 *
 * @return Array pointer (NULL when the vector was empty).
 */
tl_record_t* tl_recvec_take(tl_recvec_t* rv, size_t* out_len);

#endif /* TL_RECVEC_H */
