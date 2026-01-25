#ifndef TL_WINDOW_H
#define TL_WINDOW_H

#include "../internal/tl_defs.h"

/*===========================================================================
 * Window Mapping
 *
 * Computes window boundaries for L1 time partitioning.
 * All L1 segments align to window boundaries.
 *
 * Window ID formula (mathematical floor):
 *   window_id = floor((ts - window_origin) / window_size)
 *
 * Window bounds:
 *   window_start = window_origin + window_id * window_size
 *   window_end   = window_start + window_size  (may be unbounded)
 *
 * IMPORTANT: C integer division truncates toward zero, NOT floor.
 * For negative numerators, we must use floor division.
 *
 * The last window containing TL_TS_MAX has an unbounded end because
 * window_start + window_size would exceed int64_t range. This is
 * represented by end_unbounded=true, similar to unbounded tombstones.
 *
 * Reference: Storage LLD Section 6.1, HLD Section 9.2
 *===========================================================================*/

/*---------------------------------------------------------------------------
 * Overflow-Safe Arithmetic Helpers
 *
 * These return true on overflow, false on success.
 * On success, result is stored in *out.
 *---------------------------------------------------------------------------*/

/*
 * Overflow-safe subtraction: computes a - b.
 * Returns true if overflow would occur, false otherwise.
 */
TL_INLINE bool tl_sub_overflow_i64(int64_t a, int64_t b, int64_t* out) {
    /*
     * Overflow cases:
     * 1. b > 0 && a < INT64_MIN + b  (a - b would underflow)
     * 2. b < 0 && a > INT64_MAX + b  (a - b would overflow)
     *
     * Note: INT64_MAX + b when b < 0 is safe (result < INT64_MAX)
     *       INT64_MIN + b when b > 0 is safe (result > INT64_MIN)
     */
    if (b > 0 && a < INT64_MIN + b) {
        return true; /* Underflow */
    }
    if (b < 0 && a > INT64_MAX + b) {
        return true; /* Overflow */
    }
    *out = a - b;
    return false;
}

/*---------------------------------------------------------------------------
 * Floor Division for Signed Integers
 *
 * C's / operator truncates toward zero. For correct window mapping,
 * we need mathematical floor(a / b), which always rounds toward -infinity.
 *
 * Examples:
 *   tl_floor_div_i64(-1, 10)  = -1   (C gives 0)
 *   tl_floor_div_i64(-10, 10) = -1   (C gives -1, same)
 *   tl_floor_div_i64(-11, 10) = -2   (C gives -1)
 *   tl_floor_div_i64(9, 10)   = 0    (C gives 0, same)
 *   tl_floor_div_i64(10, 10)  = 1    (C gives 1, same)
 *
 * If b <= 0, returns 0 as defensive fallback to prevent UB.
 * Callers should validate b > 0 before calling.
 *---------------------------------------------------------------------------*/

TL_INLINE int64_t tl_floor_div_i64(int64_t a, int64_t b) {
    /* C-06 fix: Runtime guard against division by zero.
     * TL_ASSERT becomes UB in release builds. Return 0 as safe fallback. */
    if (b <= 0) {
        return 0;
    }
    int64_t q = a / b;
    int64_t r = a % b;
    /* Adjust if remainder is non-zero and numerator is negative */
    if (r != 0 && a < 0) {
        q -= 1;
    }
    return q;
}

/*---------------------------------------------------------------------------
 * Default Window Size
 *
 * Returns 1 hour in the specified time unit.
 * Uses constants from tl_defs.h.
 *---------------------------------------------------------------------------*/

tl_ts_t tl_window_default_size(tl_time_unit_t unit);

/*---------------------------------------------------------------------------
 * Window ID Computation
 *
 * Computes the window ID for a given timestamp.
 * Uses floor division for correctness with negative timestamps.
 *
 * @param ts            Timestamp
 * @param window_size   Window width (must be > 0)
 * @param window_origin Origin for window alignment
 * @param out_id        Output: window ID (may be negative)
 * @return TL_OK on success,
 *         TL_EINVAL if window_size <= 0,
 *         TL_EOVERFLOW if ts - origin overflows
 *---------------------------------------------------------------------------*/

tl_status_t tl_window_id_for_ts(tl_ts_t ts, tl_ts_t window_size,
                                 tl_ts_t window_origin, int64_t* out_id);

/*---------------------------------------------------------------------------
 * Window Bounds Computation
 *
 * Computes the start and end boundaries for a given window ID.
 * Uses overflow-safe arithmetic.
 *
 * When window_end would exceed INT64_MAX, end_unbounded is set to true
 * and out_end is set to TL_TS_MAX. Callers must check end_unbounded
 * when comparing timestamps against window_end.
 *
 * If window_size <= 0, returns degenerate empty window [origin, origin)
 * with end_unbounded = false. Callers should validate window_size > 0
 * before calling; this defensive behavior prevents UB on bad input.
 *
 * @param window_id      Window ID
 * @param window_size    Window width (must be > 0; returns degenerate if not)
 * @param window_origin  Origin for window alignment
 * @param out_start      Output: window start (inclusive)
 * @param out_end        Output: window end (exclusive), or TL_TS_MAX if unbounded
 * @param end_unbounded  Output: true if end extends to +infinity
 *---------------------------------------------------------------------------*/

void tl_window_bounds(int64_t window_id, tl_ts_t window_size, tl_ts_t window_origin,
                      tl_ts_t* out_start, tl_ts_t* out_end, bool* end_unbounded);

/*---------------------------------------------------------------------------
 * Window Bounds for Timestamp (Convenience)
 *
 * Computes window boundaries containing a given timestamp.
 * Combines window_id_for_ts and window_bounds.
 *
 * @param ts             Timestamp
 * @param window_size    Window width (must be > 0)
 * @param window_origin  Origin for window alignment
 * @param out_start      Output: window start (inclusive)
 * @param out_end        Output: window end (exclusive), or TL_TS_MAX if unbounded
 * @param end_unbounded  Output: true if end extends to +infinity
 * @return TL_OK on success,
 *         TL_EINVAL if window_size <= 0,
 *         TL_EOVERFLOW if computation overflows
 *---------------------------------------------------------------------------*/

tl_status_t tl_window_bounds_for_ts(tl_ts_t ts, tl_ts_t window_size,
                                     tl_ts_t window_origin,
                                     tl_ts_t* out_start, tl_ts_t* out_end,
                                     bool* end_unbounded);

/*---------------------------------------------------------------------------
 * Window Containment Check
 *
 * Checks if a timestamp falls within a window [window_start, window_end).
 * Handles unbounded windows correctly.
 *---------------------------------------------------------------------------*/

TL_INLINE bool tl_window_contains(tl_ts_t window_start, tl_ts_t window_end,
                                   bool end_unbounded, tl_ts_t ts) {
    if (ts < window_start) {
        return false;
    }
    if (end_unbounded) {
        return true; /* ts >= start and no upper bound */
    }
    return ts < window_end;
}

/*---------------------------------------------------------------------------
 * Window Containment Check (Simple)
 *
 * For windows known to be bounded (e.g., internal use where overflow
 * is not possible). Caller must ensure window_end is valid.
 *---------------------------------------------------------------------------*/

TL_INLINE bool tl_window_contains_bounded(tl_ts_t window_start,
                                           tl_ts_t window_end,
                                           tl_ts_t ts) {
    return ts >= window_start && ts < window_end;
}

#endif /* TL_WINDOW_H */
