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
        /* Fetch next record from merge iterator */
        tl_record_t rec;
        tl_seq_t watermark = 0;
        tl_status_t st = tl_kmerge_iter_next(it->merge, &rec, &watermark);

        if (st == TL_EOF) {
            it->done = true;
            return TL_EOF;
        }

        if (st != TL_OK) {
            /* Propagate any error */
            it->done = true;
            return st;
        }

        /*
         * Compute max tombstone seq at this timestamp and compare against
         * the record's watermark (rec_seq for mutable, applied_seq for immutable).
         * Drop if tomb_seq > watermark.
         */
        tl_seq_t tomb_seq = tl_intervals_cursor_max_seq(&it->tomb_cursor, rec.ts);
        if (tomb_seq > watermark) {
            if (tl_kmerge_iter_can_skip(it->merge, tomb_seq)) {
                tl_ts_t next_ts = rec.ts;
                if (!tl_intervals_cursor_skip_to(&it->tomb_cursor, rec.ts, &next_ts)) {
                    it->done = true;
                    return TL_EOF;
                }
                if (next_ts > rec.ts) {
                    tl_kmerge_iter_seek(it->merge, next_ts);
                }
            }
            continue;
        }

        /* Record is visible - return it */
        *out = rec;
        return TL_OK;
    }
}
