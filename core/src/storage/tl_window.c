#include "tl_window.h"

/*===========================================================================
 * Default Window Size
 *===========================================================================*/

tl_ts_t tl_window_default_size(tl_time_unit_t unit) {
    /*
     * M-06 fix: Use switch with fallthrough to default instead of TL_ASSERT.
     * Unknown enum values are user errors, not programmer bugs.
     * Return safe default (1 hour in seconds) for robustness.
     */
    switch (unit) {
    case TL_TIME_S:  return TL_WINDOW_1H_S;
    case TL_TIME_MS: return TL_WINDOW_1H_MS;
    case TL_TIME_US: return TL_WINDOW_1H_US;
    case TL_TIME_NS: return TL_WINDOW_1H_NS;
    default:
        /* Unknown unit: return safe default (1 hour in seconds).
         * This is defensive - the config validator should catch invalid units
         * before reaching here, but we don't crash on unknown values. */
        return TL_WINDOW_1H_S;
    }
}

/*===========================================================================
 * Overflow-Safe Arithmetic
 *
 * For window_start = window_origin + window_id * window_size, we need
 * overflow-safe multiplication and addition. These are provided by
 * tl_math.h (tl_mul_overflow_i64 / tl_add_overflow_i64).
 *===========================================================================*/

/*===========================================================================
 * Window ID Computation
 *===========================================================================*/

tl_status_t tl_window_id_for_ts(tl_ts_t ts, tl_ts_t window_size,
                                 tl_ts_t window_origin, int64_t* out_id) {
    TL_ASSERT(out_id != NULL);

    /* C-06 fix: Runtime check for window_size.
     * TL_ASSERT becomes UB in release builds. This defensive check
     * prevents division by zero on invalid config or overflow corruption. */
    if (window_size <= 0) {
        return TL_EINVAL;
    }

    /*
     * Use floor division for correct behavior with negative numerators.
     * But first, compute ts - window_origin with overflow checking.
     *
     * Example with window_size=10, window_origin=0:
     *   ts = 9  => floor(9/10) = 0
     *   ts = 10 => floor(10/10) = 1
     *   ts = -1 => floor(-1/10) = -1 (C gives 0, wrong)
     *   ts = -10 => floor(-10/10) = -1 (C gives -1, correct)
     *   ts = -11 => floor(-11/10) = -2 (C gives -1, wrong)
     */
    int64_t diff;
    if (tl_sub_overflow_i64(ts, window_origin, &diff)) {
        /* Overflow in subtraction - this is an edge case with extreme values */
        return TL_EOVERFLOW;
    }

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

    /* C-06 fix: Runtime guard for window_size.
     * TL_ASSERT becomes UB in release builds. This defensive check
     * prevents UB on invalid config or overflow corruption.
     * Returns degenerate empty window [origin, origin) on invalid input. */
    if (window_size <= 0) {
        *out_start = window_origin;
        *out_end = window_origin;
        *end_unbounded = false;
        return;
    }

    /*
     * window_start = window_origin + window_id * window_size
     * window_end   = window_start + window_size
     *
     * We need to handle overflow at each step.
     * If window_end overflows, we mark it as unbounded.
     */

    int64_t product;
    int64_t start;
    int64_t end;

    /* Step 1: window_id * window_size */
    if (tl_mul_overflow_i64(window_id, window_size, &product)) {
        /* Overflow in multiplication */
        if (window_id > 0) {
            /* Large positive window_id: saturate to max */
            *out_start = TL_TS_MAX;
            *out_end = TL_TS_MAX;
            *end_unbounded = true;
        } else {
            /* Large negative window_id: saturate to min */
            *out_start = TL_TS_MIN;
            *out_end = TL_TS_MIN;
            *end_unbounded = false;
        }
        return;
    }

    /* Step 2: window_origin + product */
    if (tl_add_overflow_i64(window_origin, product, &start)) {
        /* Overflow in addition */
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

    /* Step 3: start + window_size */
    if (tl_add_overflow_i64(start, window_size, &end)) {
        /*
         * window_end would overflow - this is the "last window" case.
         * The window is [start, +infinity) conceptually.
         * We represent this with end = TL_TS_MAX and end_unbounded = true.
         */
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
