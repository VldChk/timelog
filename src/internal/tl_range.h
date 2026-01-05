#ifndef TL_RANGE_H
#define TL_RANGE_H

#include "tl_defs.h"

/*===========================================================================
 * Unbounded Range Helpers
 *
 * These helpers ensure correct handling of unbounded ranges [t1, +inf).
 *
 * DESIGN PRINCIPLE:
 * Unbounded queries use a boolean flag (t2_unbounded) as the SOLE indicator
 * of infinity. INT64_MAX/TL_TS_MAX is a valid timestamp, NOT a sentinel.
 * When t2_unbounded is true:
 * - The t2 field is ignored (callers should pass 0 for clarity)
 * - All comparisons must check t2_unbounded FIRST before accessing t2
 *
 * Usage pattern:
 *   if (tl_ts_before_end(ts, t2, t2_unbounded)) { ... }
 *   if (tl_range_overlaps(min, max, t1, t2, t2_unbounded)) { ... }
 *
 * Reference: plan_phase5.md Section 5.0
 *===========================================================================*/

/**
 * Check if timestamp is before the end bound.
 *
 * Returns true if ts < t2 (bounded) or always true (unbounded).
 * This is the fundamental predicate for "is ts in range [t1, t2)?".
 *
 * @param ts           Timestamp to check
 * @param t2           End bound (ONLY read if !t2_unbounded)
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @return true if ts is before the end bound
 */
TL_INLINE bool tl_ts_before_end(tl_ts_t ts, tl_ts_t t2, bool t2_unbounded) {
    return t2_unbounded || ts < t2;
}

/**
 * Check if timestamp is at or after the end bound.
 *
 * Returns true if ts >= t2 (bounded) or always false (unbounded).
 * Useful for "stop iteration" checks.
 *
 * @param ts           Timestamp to check
 * @param t2           End bound (ONLY read if !t2_unbounded)
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @return true if ts is at or past the end bound
 */
TL_INLINE bool tl_ts_at_or_past_end(tl_ts_t ts, tl_ts_t t2, bool t2_unbounded) {
    return !t2_unbounded && ts >= t2;
}

/**
 * Check if interval [min_ts, max_ts] overlaps with range [t1, t2) or [t1, +inf).
 *
 * An interval [min_ts, max_ts] (inclusive bounds) overlaps a half-open range
 * [t1, t2) (or unbounded [t1, +inf)) when:
 * - max_ts >= t1 (interval ends at or after range start), AND
 * - min_ts < t2 (interval starts before range end) OR t2_unbounded
 *
 * Used for pruning segments and pages during query planning.
 *
 * @param min_ts       Interval minimum (inclusive)
 * @param max_ts       Interval maximum (inclusive)
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY read if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @return true if the interval overlaps the range
 */
TL_INLINE bool tl_range_overlaps(tl_ts_t min_ts, tl_ts_t max_ts,
                                  tl_ts_t t1, tl_ts_t t2,
                                  bool t2_unbounded) {
    return (max_ts >= t1) && (t2_unbounded || min_ts < t2);
}

/**
 * Check if range [t1, t2) or [t1, +inf) is empty.
 *
 * A bounded range is empty if t1 >= t2.
 * An unbounded range is never empty (assuming t1 is valid).
 *
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY read if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @return true if the range is empty
 */
TL_INLINE bool tl_range_is_empty(tl_ts_t t1, tl_ts_t t2, bool t2_unbounded) {
    return !t2_unbounded && t1 >= t2;
}

/**
 * Compute the overlap start between interval [min_ts, max_ts] and range [t1, t2).
 *
 * Returns max(min_ts, t1) - the first timestamp in the overlap.
 * Caller must first verify that an overlap exists using tl_range_overlaps().
 *
 * @param min_ts  Interval minimum (inclusive)
 * @param t1      Range start (inclusive)
 * @return Start of the overlap region
 */
TL_INLINE tl_ts_t tl_range_overlap_start(tl_ts_t min_ts, tl_ts_t t1) {
    return (min_ts > t1) ? min_ts : t1;
}

#endif /* TL_RANGE_H */
