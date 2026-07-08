#ifndef TL_RANGE_H
#define TL_RANGE_H

#include "tl_defs.h"

/*===========================================================================
 * Range Predicates
 *
 * Helpers for half-open ranges [t1, t2) with explicit support for the
 * unbounded form [t1, +inf).
 *
 * Infinity is encoded by a separate boolean flag (t2_unbounded) rather than
 * a sentinel value: INT64_MAX / TL_TS_MAX are legal timestamps, not magic
 * numbers. When the flag is true the t2 field carries no meaning and must
 * not be read — every predicate below checks t2_unbounded first.
 *===========================================================================*/

/**
 * True if the closed interval [min_ts, max_ts] overlaps the half-open range
 * [t1, t2) (or [t1, +inf) when unbounded). Used by query planning to prune
 * segments and pages whose bounds cannot intersect the query range.
 */
TL_INLINE bool tl_range_overlaps(tl_ts_t min_ts, tl_ts_t max_ts,
                                  tl_ts_t t1, tl_ts_t t2,
                                  bool t2_unbounded) {
    return (max_ts >= t1) && (t2_unbounded || min_ts < t2);
}

/**
 * A bounded range is empty when t1 >= t2. Unbounded ranges are never empty.
 */
TL_INLINE bool tl_range_is_empty(tl_ts_t t1, tl_ts_t t2, bool t2_unbounded) {
    return !t2_unbounded && t1 >= t2;
}

#endif /* TL_RANGE_H */
