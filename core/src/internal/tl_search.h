/*===========================================================================
 * Search Helpers (Records)
 *===========================================================================*/

#ifndef TL_SEARCH_H
#define TL_SEARCH_H

#include "tl_defs.h"

/**
 * Binary search: first index where data[i].ts >= target.
 * Returns len if all records have ts < target.
 */
TL_INLINE size_t tl_record_lower_bound(const tl_record_t* data,
                                        size_t len,
                                        tl_ts_t target) {
    size_t lo = 0;
    size_t hi = len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (data[mid].ts < target) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

#endif /* TL_SEARCH_H */
