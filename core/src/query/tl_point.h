#ifndef TL_POINT_H
#define TL_POINT_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "tl_snapshot.h"

/*===========================================================================
 * Point Lookup Fast Path
 *
 * Dedicated single-timestamp lookup that skips the K-way merge by
 * binary-searching each component directly for the exact timestamp.
 *
 * Algorithm:
 * 1. Compute tomb_seq(ts) across all sources; a row is dropped iff
 *    tomb_seq(ts) > row_watermark.
 * 2. L1: binary-search the window catalog, then the page catalog,
 *    then within the page.
 * 3. L0: same, repeated for each overlapping segment.
 * 4. Memview: binary-search the active sorted run, the OOO head, each
 *    OOO run, and each sealed memrun.
 * 5. Concatenate results. Duplicates are preserved; order is unspecified.
 *
 * Complexity is O(log S1) for the L1 window lookup plus O(log P) per
 * segment page catalog and O(log rows) within a page; for a single
 * timestamp this is dramatically cheaper than building the full merge.
 *
 * Thread Safety:
 * - Snapshot must remain valid for the lifetime of the result.
 * - The result array is owned by the caller.
 *===========================================================================*/

/**
 * Result of point lookup.
 * Contains array of matching records (caller must free).
 */
typedef struct tl_point_result {
    tl_record_t*    records;    /* Array of matching records (owned) */
    size_t          count;      /* Number of records */
    size_t          capacity;   /* Allocated capacity */
    tl_alloc_ctx_t* alloc;      /* Allocator for cleanup */
} tl_point_result_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Find every visible record at exactly `ts` in the snapshot.
 *
 * Watermark semantics: a row is treated as deleted only when
 * tomb_seq(ts) > row_watermark.
 *
 * @param result  Output result (caller-allocated, zero-initialised)
 * @param snap    Snapshot to search
 * @param ts      Timestamp to find
 * @param alloc   Allocator for result records
 * @return TL_OK on success (even when no records match),
 *         TL_ENOMEM on allocation failure
 */
tl_status_t tl_point_lookup(tl_point_result_t* result,
                             const tl_snapshot_t* snap,
                             tl_ts_t ts,
                             tl_alloc_ctx_t* alloc);

/**
 * Destroy point result and free records array.
 * Safe to call on zero-initialized or empty result.
 * After this call, result is in a zero-initialized state.
 */
void tl_point_result_destroy(tl_point_result_t* result);

/*===========================================================================
 * Accessors
 *===========================================================================*/

/** Check if result is empty. */
TL_INLINE bool tl_point_result_empty(const tl_point_result_t* result) {
    return result->count == 0;
}

/** Get record by index. */
TL_INLINE const tl_record_t* tl_point_result_get(const tl_point_result_t* result,
                                                  size_t idx) {
    TL_ASSERT(idx < result->count);
    return &result->records[idx];
}

#endif /* TL_POINT_H */
