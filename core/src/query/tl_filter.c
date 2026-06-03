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

    if (it->tomb_cursor.len == 0) {
        tl_seq_t watermark = 0;
        tl_status_t st = tl_kmerge_iter_next(it->merge, out, &watermark);
        if (st == TL_EOF) {
            it->done = true;
        } else if (st != TL_OK) {
            it->done = true;
        }
        return st;
    }

    for (;;) {
        tl_record_t rec;
        tl_seq_t watermark = 0;
        tl_status_t st = tl_kmerge_iter_next(it->merge, &rec, &watermark);

        if (st == TL_EOF) {
            it->done = true;
            return TL_EOF;
        }

        if (st != TL_OK) {
            it->done = true;
            return st;
        }

        /* A record is deleted iff the strongest tombstone covering its
         * timestamp was applied after the record itself. The watermark
         * here is rec_seq for mutable sources and applied_seq for
         * immutable ones. */
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

        *out = rec;
        return TL_OK;
    }
}
