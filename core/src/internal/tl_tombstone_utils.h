#ifndef TL_TOMBSTONE_UTILS_H
#define TL_TOMBSTONE_UTILS_H

#include "tl_intervals.h"
#include "tl_range.h"

/*
 * Shared tombstone collection helper.
 *
 * Adds tombstone intervals that overlap the query range [t1, t2)
 * into the accumulator, preserving per-interval max_seq.
 */
static inline tl_status_t
tl_tombstones_add_intervals(tl_intervals_t* accum,
                            tl_intervals_imm_t tombs,
                            tl_ts_t t1, tl_ts_t t2,
                            bool t2_unbounded) {
    if (tombs.len == 0) {
        return TL_OK;
    }

    for (size_t i = 0; i < tombs.len; i++) {
        const tl_interval_t* interval = &tombs.data[i];

        /* Skip if interval doesn't overlap query range */
        tl_ts_t int_max = interval->end_unbounded ? TL_TS_MAX : interval->end - 1;
        if (!tl_range_overlaps(interval->start, int_max,
                               t1, t2, t2_unbounded)) {
            continue;
        }

        tl_status_t st;
        if (interval->end_unbounded) {
            st = tl_intervals_insert_unbounded(accum, interval->start,
                                               interval->max_seq);
        } else {
            st = tl_intervals_insert(accum, interval->start, interval->end,
                                     interval->max_seq);
        }

        if (st != TL_OK) {
            return st;
        }
    }

    return TL_OK;
}

#endif /* TL_TOMBSTONE_UTILS_H */
