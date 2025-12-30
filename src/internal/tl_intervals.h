#ifndef TL_INTERVALS_H
#define TL_INTERVALS_H

#include "tl_defs.h"
#include "tl_status.h"
#include "tl_alloc.h"
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * A half-open time interval [start, end) (end may be TL_TS_UNBOUNDED).
 *
 * Invariant: start < end (empty intervals are not stored)
 */
typedef struct tl_interval {
    tl_ts_t start;  /* Inclusive */
    tl_ts_t end;    /* Exclusive */
} tl_interval_t;

/**
 * Disjoint sorted interval set.
 *
 * Invariants:
 * 1. intervals[i].start < intervals[i].end for all i
 * 2. intervals[i].end <= intervals[i+1].start for all i (strictly disjoint)
 * 3. intervals are sorted by start
 * 4. Adjacent intervals are coalesced (no i where intervals[i].end == intervals[i+1].start)
 *
 * Design choices:
 * - Dynamic array (not tree) since tombstone lists are typically small
 * - Insert coalesces immediately to keep list minimal
 * - Supports efficient "is timestamp deleted?" queries
 */
typedef struct tl_intervals {
    tl_interval_t*        data;
    size_t                len;
    size_t                cap;
    const tl_allocator_t* alloc;
} tl_intervals_t;

/**
 * Initialize an empty interval set.
 */
void tl_intervals_init(tl_intervals_t* iset, const tl_allocator_t* alloc);

/**
 * Initialize with pre-allocated capacity.
 */
tl_status_t tl_intervals_init_cap(tl_intervals_t* iset, const tl_allocator_t* alloc,
                                   size_t init_cap);

/**
 * Destroy interval set and free memory.
 */
void tl_intervals_destroy(tl_intervals_t* iset);

/**
 * Clear interval set without freeing memory.
 */
void tl_intervals_clear(tl_intervals_t* iset);

/**
 * Insert an interval with coalescing.
 *
 * @param start Inclusive start (must be < end)
 * @param end   Exclusive end
 * @return TL_OK on success, TL_EINVAL if start >= end, TL_ENOMEM on allocation failure
 *
 * Behavior:
 * - If [start, end) overlaps or touches existing intervals, they are merged
 * - Result is always a minimal disjoint set
 */
tl_status_t tl_intervals_insert(tl_intervals_t* iset, tl_ts_t start, tl_ts_t end);

/**
 * Check if a timestamp is covered by any interval.
 *
 * @param ts Timestamp to check
 * @return true if ts is in some interval [a, b) (i.e., a <= ts < b)
 */
bool tl_intervals_contains(const tl_intervals_t* iset, tl_ts_t ts);

/**
 * Find the interval containing or immediately after a timestamp.
 *
 * @param ts  Timestamp to search for
 * @param out Output interval (if found)
 * @return Index of interval where start <= ts < end,
 *         or first interval with start > ts,
 *         or iset->len if no such interval exists
 */
size_t tl_intervals_find(const tl_intervals_t* iset, tl_ts_t ts);

/**
 * Clip intervals to a range [clip_start, clip_end).
 * Modifies in place: removes intervals outside range, trims boundary intervals.
 *
 * @return TL_OK on success
 */
tl_status_t tl_intervals_clip(tl_intervals_t* iset, tl_ts_t clip_start, tl_ts_t clip_end);

/**
 * Compute union of two interval sets into dst.
 * dst is cleared first; src1 and src2 are not modified.
 *
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_intervals_union(tl_intervals_t* dst,
                                const tl_intervals_t* src1,
                                const tl_intervals_t* src2);

/**
 * Copy interval set.
 */
tl_status_t tl_intervals_copy(tl_intervals_t* dst, const tl_intervals_t* src);

/**
 * Move ownership from src to dst.
 */
void tl_intervals_move(tl_intervals_t* dst, tl_intervals_t* src);

/*
 * Inline accessors
 */
TL_INLINE size_t tl_intervals_len(const tl_intervals_t* iset) {
    return iset ? iset->len : 0;
}

TL_INLINE bool tl_intervals_empty(const tl_intervals_t* iset) {
    return iset == NULL || iset->len == 0;
}

TL_INLINE const tl_interval_t* tl_intervals_data(const tl_intervals_t* iset) {
    return iset ? iset->data : NULL;
}

TL_INLINE const tl_interval_t* tl_intervals_at(const tl_intervals_t* iset, size_t i) {
    return (iset && i < iset->len) ? &iset->data[i] : NULL;
}

/**
 * Validate invariants (for testing/debugging).
 *
 * @return TL_OK if valid, TL_EINTERNAL if invariants violated
 */
tl_status_t tl_intervals_validate(const tl_intervals_t* iset);

#ifdef __cplusplus
}
#endif

#endif /* TL_INTERVALS_H */
