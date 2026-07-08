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
    /* Branchless (cmov) power-of-two-step search for page/memtable-sized arrays;
     * branchy fallback above the size gate where branch speculation wins on huge
     * arrays (see TL_LOWER_BOUND_BRANCHLESS_MAX). Both forms return the identical
     * first index i in [0,len] with data[i].ts >= target. */
    if (len <= TL_LOWER_BOUND_BRANCHLESS_MAX) {
        size_t base = 0;
        size_t length = len;
        while (length > 0) {
            size_t half = length / 2;
            base += (size_t)(data[base + half].ts < target) * (length - half);
            length = half;
        }
        return base;
    }

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

/**
 * Binary search: first index where ts[i] >= target (flat timestamp array).
 * Returns len if all timestamps < target.
 *
 * Same dual-mode algorithm as tl_record_lower_bound above (branchless cmov
 * below the gate, branchy fallback above it); the AoS/SoA layouts prevent
 * sharing one body, so keep the two in sync.
 */
TL_INLINE size_t tl_ts_lower_bound(const tl_ts_t* ts,
                                    size_t len,
                                    tl_ts_t target) {
    if (len <= TL_LOWER_BOUND_BRANCHLESS_MAX) {
        size_t base = 0;
        size_t length = len;
        while (length > 0) {
            size_t half = length / 2;
            base += (size_t)(ts[base + half] < target) * (length - half);
            length = half;
        }
        return base;
    }

    size_t lo = 0;
    size_t hi = len;
    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (ts[mid] < target) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    return lo;
}

#endif /* TL_SEARCH_H */
