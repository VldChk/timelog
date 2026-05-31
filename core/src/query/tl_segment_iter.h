#ifndef TL_SEGMENT_ITER_H
#define TL_SEGMENT_ITER_H

#include "../internal/tl_defs.h"
#include "../storage/tl_segment.h"

/*===========================================================================
 * Segment Iterator
 *
 * Walks the records of a segment that fall in [t1, t2) or [t1, +inf).
 * The page catalog prunes to the relevant page range, then a binary
 * search inside each page positions the cursor at the first matching
 * row.
 *
 * API contract:
 * - Pull-based: next() is the only way to advance.
 * - No persistent "current row" and no peek; callers that need
 *   non-advancing inspection must cache the last returned record.
 *
 * Range semantics:
 * - t2_unbounded == true means [t1, +inf); the t2 field is ignored.
 *   All comparisons MUST check t2_unbounded before reading t2.
 *
 * Thread Safety:
 * - Not thread-safe (each thread needs its own iterator).
 * - Segment must remain valid for the lifetime of the iterator.
 *===========================================================================*/

typedef struct tl_segment_iter {
    const tl_segment_t* seg;

    /* Range bounds */
    tl_ts_t         t1;
    tl_ts_t         t2;              /* ONLY valid if !t2_unbounded */
    bool            t2_unbounded;

    /* Current page */
    size_t          page_idx;        /* Current page index */
    size_t          page_end;        /* Last page index (exclusive) */

    /* Current position within page */
    size_t          row_idx;         /* Current row within page */
    size_t          row_end;         /* End row within page (exclusive) */

    /* State */
    bool            done;
} tl_segment_iter_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Initialise the iterator for range [t1, t2) or [t1, +inf).
 *
 * After init, call tl_segment_iter_next() to fetch the first record.
 * If the segment does not overlap the requested range, the iterator
 * starts already exhausted.
 *
 * @param it           Iterator to initialise
 * @param seg          Segment to iterate (must remain valid)
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive); ignored when t2_unbounded
 * @param t2_unbounded When true, range is [t1, +inf)
 */
void tl_segment_iter_init(tl_segment_iter_t* it,
                           const tl_segment_t* seg,
                           tl_ts_t t1, tl_ts_t t2,
                           bool t2_unbounded);

/*===========================================================================
 * Iteration
 *===========================================================================*/

/**
 * Advance to next record.
 *
 * @param it   Iterator
 * @param out  Output record (may be NULL if only checking for existence)
 * @return TL_OK if record available, TL_EOF if exhausted
 *
 * The iterator advances only through this function.
 */
tl_status_t tl_segment_iter_next(tl_segment_iter_t* it, tl_record_t* out);

/**
 * Seek to first record with ts >= target.
 *
 * Used for skip-ahead optimization in merge iteration.
 * If target is before current position, does nothing (no backwards seek).
 * If target is past the range end, iterator becomes exhausted.
 *
 * After seek, call tl_segment_iter_next() to get the record at the new position.
 *
 * @param it     Iterator
 * @param target Target timestamp to seek to
 */
void tl_segment_iter_seek(tl_segment_iter_t* it, tl_ts_t target);

/*===========================================================================
 * State Queries
 *===========================================================================*/

/** Check if iterator is exhausted. */
TL_INLINE bool tl_segment_iter_done(const tl_segment_iter_t* it) {
    TL_ASSERT(it != NULL);
    return it->done;
}

#endif /* TL_SEGMENT_ITER_H */
