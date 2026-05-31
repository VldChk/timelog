#include "tl_window.h"

/*===========================================================================
 * Default Window Size
 *===========================================================================*/

tl_ts_t tl_window_default_size(tl_time_unit_t unit) {
    /* Unknown values fall through to 1 hour in seconds so that a misconfigured
     * time unit cannot return 0 and trigger division-by-zero downstream. */
    switch (unit) {
    case TL_TIME_S:  return TL_WINDOW_1H_S;
    case TL_TIME_MS: return TL_WINDOW_1H_MS;
    case TL_TIME_US: return TL_WINDOW_1H_US;
    case TL_TIME_NS: return TL_WINDOW_1H_NS;
    default:
        return TL_WINDOW_1H_S;
    }
}

/*===========================================================================
 * Window ID Computation
 *===========================================================================*/

tl_status_t tl_window_id_for_ts(tl_ts_t ts, tl_ts_t window_size,
                                 tl_ts_t window_origin, int64_t* out_id) {
    TL_ASSERT(out_id != NULL);

    /* Reject non-positive window sizes in release builds; the floor division
     * would otherwise hit UB. */
    if (window_size <= 0) {
        return TL_EINVAL;
    }

    int64_t diff;
    if (tl_sub_overflow_i64(ts, window_origin, &diff)) {
        return TL_EOVERFLOW;
    }

    /* tl_floor_div_i64 rounds toward -infinity so windows align consistently
     * for timestamps on both sides of window_origin. */
    *out_id = tl_floor_div_i64(diff, window_size);
    return TL_OK;
}

/*===========================================================================
 * Window Bounds Computation
 *===========================================================================*/

void tl_window_bounds(int64_t window_id, tl_ts_t window_size, tl_ts_t window_origin,
                      tl_ts_t* out_start, tl_ts_t* out_end, bool* end_unbounded) {
    TL_ASSERT(out_start != NULL);
    TL_ASSERT(out_end != NULL);
    TL_ASSERT(end_unbounded != NULL);

    /* A non-positive window size cannot describe a real window; collapse to
     * an empty range at the origin instead of taking division-by-zero UB. */
    if (window_size <= 0) {
        *out_start = window_origin;
        *out_end = window_origin;
        *end_unbounded = false;
        return;
    }

    /* start = origin + id*size, end = start + size. Every step is overflow-
     * checked; on overflow we either saturate to TL_TS_MAX/MIN or, if only
     * end overflows, mark the window as unbounded so callers know the window
     * has no finite upper bound. */
    int64_t product;
    int64_t start;
    int64_t end;

    if (tl_mul_overflow_i64(window_id, window_size, &product)) {
        if (window_id > 0) {
            *out_start = TL_TS_MAX;
            *out_end = TL_TS_MAX;
            *end_unbounded = true;
        } else {
            *out_start = TL_TS_MIN;
            *out_end = TL_TS_MIN;
            *end_unbounded = false;
        }
        return;
    }

    if (tl_add_overflow_i64(window_origin, product, &start)) {
        if (product > 0) {
            *out_start = TL_TS_MAX;
            *out_end = TL_TS_MAX;
            *end_unbounded = true;
        } else {
            *out_start = TL_TS_MIN;
            *out_end = TL_TS_MIN;
            *end_unbounded = false;
        }
        return;
    }

    /* Only the end overflows: this is the trailing window that extends to
     * +infinity. Encode it as (start, TL_TS_MAX, end_unbounded=true). */
    if (tl_add_overflow_i64(start, window_size, &end)) {
        *out_start = start;
        *out_end = TL_TS_MAX;
        *end_unbounded = true;
        return;
    }

    *out_start = start;
    *out_end = end;
    *end_unbounded = false;
}

/*===========================================================================
 * Window Bounds for Timestamp
 *===========================================================================*/

tl_status_t tl_window_bounds_for_ts(tl_ts_t ts, tl_ts_t window_size,
                                     tl_ts_t window_origin,
                                     tl_ts_t* out_start, tl_ts_t* out_end,
                                     bool* end_unbounded) {
    int64_t wid;
    tl_status_t status = tl_window_id_for_ts(ts, window_size, window_origin, &wid);
    if (status != TL_OK) {
        return status;
    }
    tl_window_bounds(wid, window_size, window_origin, out_start, out_end, end_unbounded);
    return TL_OK;
}
