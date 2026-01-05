#ifndef TL_FILTER_H
#define TL_FILTER_H

#include "../internal/tl_defs.h"
#include "../internal/tl_intervals.h"
#include "tl_merge_iter.h"

/*===========================================================================
 * Filtered Iterator
 *
 * Wraps a K-way merge iterator and filters out records covered by tombstones.
 * Uses a cursor-based approach for efficient filtering with amortized O(1)
 * per-record cost.
 *
 * Algorithm (Read Path LLD Section 7):
 * 1. Get next record from merge iterator
 * 2. Check if record's timestamp is deleted using tombstone cursor
 * 3. If deleted, skip and repeat
 * 4. If not deleted, return the record
 *
 * The tombstone cursor takes advantage of the fact that both the merge iterator
 * output and the tombstone intervals are sorted. The cursor advances forward
 * only, never backwards, achieving amortized O(1) per record.
 *
 * Thread Safety:
 * - Not thread-safe (each thread needs its own iterator)
 * - Underlying merge iterator must remain valid
 *
 * Reference: Read Path LLD Section 7
 *===========================================================================*/

typedef struct tl_filter_iter {
    /* Underlying K-way merge iterator (borrowed, must remain valid) */
    tl_kmerge_iter_t*     merge;

    /* Tombstone cursor for efficient deletion checking */
    tl_intervals_cursor_t tomb_cursor;

    /* State */
    bool                  done;
} tl_filter_iter_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Initialize filtered iterator.
 *
 * @param it      Iterator to initialize
 * @param merge   Underlying K-way merge iterator (must remain valid)
 * @param tombs   Tombstone intervals (sorted, non-overlapping)
 */
void tl_filter_iter_init(tl_filter_iter_t* it,
                          tl_kmerge_iter_t* merge,
                          tl_intervals_imm_t tombs);

/*===========================================================================
 * Iteration
 *===========================================================================*/

/**
 * Get next visible record.
 *
 * Skips records that are covered by tombstones.
 * Returns records in non-decreasing timestamp order.
 *
 * @param it   Iterator
 * @param out  Output record
 * @return TL_OK if record available, TL_EOF if exhausted
 */
tl_status_t tl_filter_iter_next(tl_filter_iter_t* it, tl_record_t* out);

/*===========================================================================
 * State Queries
 *===========================================================================*/

/**
 * Check if iterator is exhausted.
 */
TL_INLINE bool tl_filter_iter_done(const tl_filter_iter_t* it) {
    TL_ASSERT(it != NULL);
    return it->done;
}

#endif /* TL_FILTER_H */
