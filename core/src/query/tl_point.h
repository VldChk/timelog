#ifndef TL_POINT_H
#define TL_POINT_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "tl_snapshot.h"

/*===========================================================================
 * Point Lookup Fast Path
 *
 * Dedicated single-timestamp lookup that bypasses the full K-way merge.
 * Uses direct binary search on each component to find all records with
 * the exact timestamp.
 *
 * Algorithm (Read Path LLD Section 8):
 * 1. Tombstone check: if any tombstone covers ts, return empty immediately
 * 2. L1 lookup: binary search window, catalog, page for ts
 * 3. L0 lookup: scan overlapping segments with binary search
 * 4. Memview lookup: binary search active_run, active_ooo, sealed memruns
 * 5. Concatenate results (duplicates preserved, order unspecified)
 *
 * Complexity:
 * - O(log S1) to find L1 window
 * - O(log P) per segment page catalog
 * - O(log rows) per page binary search
 * - Much cheaper than full K-way merge for single-timestamp queries
 *
 * Thread Safety:
 * - Snapshot must remain valid for the lifetime of the result
 * - Result array is owned by caller
 *
 * Reference: Read Path LLD Section 8, timelog_v1_c_software_design_spec.md
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
 * Perform point lookup for exact timestamp.
 *
 * Finds all visible records with record.ts == ts in the snapshot.
 * Uses direct binary search on each component (no K-way merge).
 *
 * If any tombstone covers ts, returns empty result (not an error).
 * This is correct: the timestamp is deleted.
 *
 * @param result  Output result (caller-allocated, zero-initialized)
 * @param snap    Snapshot to search
 * @param ts      Timestamp to find
 * @param alloc   Allocator for result records
 * @return TL_OK on success (even if no records found),
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

/**
 * Check if result is empty.
 */
TL_INLINE bool tl_point_result_empty(const tl_point_result_t* result) {
    return result->count == 0;
}

/**
 * Get record by index.
 */
TL_INLINE const tl_record_t* tl_point_result_get(const tl_point_result_t* result,
                                                  size_t idx) {
    TL_ASSERT(idx < result->count);
    return &result->records[idx];
}

#endif /* TL_POINT_H */
