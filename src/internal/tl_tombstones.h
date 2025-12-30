#ifndef TL_TOMBSTONES_H
#define TL_TOMBSTONES_H

#include "tl_defs.h"
#include "tl_alloc.h"
#include "tl_intervals.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Immutable tombstone set for segments.
 *
 * This is a frozen snapshot of a tl_intervals_t, optimized for read-only access.
 * Unlike tl_intervals_t, this cannot be modified after creation.
 *
 * Properties:
 * - Intervals are sorted by t1 (start)
 * - Intervals are non-overlapping and non-adjacent (coalesced)
 * - Half-open semantics: [t1, t2) means t1 <= deleted_ts < t2
 */
typedef struct tl_tombstones {
    uint32_t         n;       /* Number of intervals */
    tl_interval_t*   v;       /* Sorted, coalesced intervals (immutable after creation) */
    void*            backing; /* Allocation backing (if single slab) */
} tl_tombstones_t;

/**
 * Create an immutable tombstone set by copying from tl_intervals_t.
 *
 * @param alloc Allocator to use
 * @param src   Source interval set (may be NULL for empty)
 * @param out   Output pointer for new tombstone set
 * @return TL_OK on success
 */
tl_status_t tl_tombstones_create(const tl_allocator_t* alloc,
                                  const tl_intervals_t* src,
                                  tl_tombstones_t** out);

/**
 * Create an immutable tombstone set by moving ownership from tl_intervals_t.
 *
 * After this call, src is cleared (data moved to new tombstone set).
 *
 * @param alloc Allocator to use
 * @param src   Source interval set (ownership transferred)
 * @param out   Output pointer for new tombstone set
 * @return TL_OK on success
 */
tl_status_t tl_tombstones_create_move(const tl_allocator_t* alloc,
                                       tl_intervals_t* src,
                                       tl_tombstones_t** out);

/**
 * Destroy a tombstone set.
 */
void tl_tombstones_destroy(const tl_allocator_t* alloc, tl_tombstones_t* ts);

/**
 * Check if a timestamp is covered by any tombstone.
 *
 * @param ts  Tombstone set
 * @param t   Timestamp to check
 * @return true if t is covered by any [t1, t2)
 */
bool tl_tombstones_contains(const tl_tombstones_t* ts, tl_ts_t t);

/**
 * Get minimum timestamp covered by tombstones.
 *
 * @param ts Tombstone set
 * @return Minimum t1, or TL_TS_MAX if empty
 */
tl_ts_t tl_tombstones_min_ts(const tl_tombstones_t* ts);

/**
 * Get maximum timestamp covered by tombstones.
 *
 * Note: Returns max(t2) which is exclusive upper bound.
 *
 * @param ts Tombstone set
 * @return Maximum t2, or TL_TS_MIN if empty
 */
tl_ts_t tl_tombstones_max_ts(const tl_tombstones_t* ts);

/**
 * Check if tombstone set is empty.
 */
TL_INLINE bool tl_tombstones_empty(const tl_tombstones_t* ts) {
    return ts == NULL || ts->n == 0;
}

/**
 * Get number of intervals in tombstone set.
 */
TL_INLINE uint32_t tl_tombstones_len(const tl_tombstones_t* ts) {
    return ts ? ts->n : 0;
}

/**
 * Get interval at index.
 */
TL_INLINE const tl_interval_t* tl_tombstones_at(const tl_tombstones_t* ts, uint32_t i) {
    return (ts && i < ts->n) ? &ts->v[i] : NULL;
}

#ifdef __cplusplus
}
#endif

#endif /* TL_TOMBSTONES_H */
