#include "tl_filter.h"

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_filter_iter_init(tl_filter_iter_t* it,
                          tl_kmerge_iter_t* merge,
                          tl_intervals_imm_t tombs) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(merge != NULL);

    it->merge = merge;
    tl_intervals_cursor_init(&it->tomb_cursor, tombs);
    it->done = tl_kmerge_iter_done(merge);
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_filter_iter_next(tl_filter_iter_t* it, tl_record_t* out) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(out != NULL);

    if (it->done) {
        return TL_EOF;
    }

    /* Loop until we find a visible record or exhaust the merge iterator */
    for (;;) {
        tl_record_t rec;
        tl_status_t st = tl_kmerge_iter_next(it->merge, &rec);

        if (st == TL_EOF) {
            it->done = true;
            return TL_EOF;
        }

        if (st != TL_OK) {
            /* Propagate any error */
            it->done = true;
            return st;
        }

        /* Check if this record is deleted by a tombstone.
         *
         * The cursor is efficient because both the merge output and
         * tombstone intervals are sorted. The cursor advances forward
         * monotonically, giving amortized O(1) per record.
         *
         * Edge cases handled by cursor:
         * - Empty tombstone set: pos >= len, returns false (not deleted)
         * - Single tombstone [a,b): deleted iff a <= ts < b
         * - Unbounded tombstone [a, +inf): deleted iff ts >= a
         * - Gaps between tombstones: correctly returns false in gaps
         * - Boundary values: half-open [start, end) semantics
         *
         * IMPORTANT: cursor_is_deleted assumes monotonically increasing ts.
         * Out-of-order timestamps would require cursor reset (not supported).
         * The k-way merge guarantees sorted output, so this is safe.
         */
        if (tl_intervals_cursor_is_deleted(&it->tomb_cursor, rec.ts)) {
            /* Record is deleted - skip it */
            continue;
        }

        /* Record is visible - return it */
        *out = rec;
        return TL_OK;
    }
}
