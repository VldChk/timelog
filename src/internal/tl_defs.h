#ifndef TL_DEFS_H
#define TL_DEFS_H

/*
 * Internal definitions header.
 * Re-exports fundamental types from public header and adds internal macros.
 */
#include "../../include/timelog/timelog.h"
#include <stdbool.h>
#include <limits.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Timestamp bounds
 */
#define TL_TS_MIN INT64_MIN
#define TL_TS_MAX INT64_MAX
#define TL_TS_UNBOUNDED TL_TS_MAX  /* Range end sentinel: treated as unbounded */

/*
 * Cache line size for alignment
 */
#ifndef TL_CACHE_LINE
#define TL_CACHE_LINE 64
#endif

/*
 * Compiler hints
 */
#if defined(__GNUC__) || defined(__clang__)
#define TL_LIKELY(x)   __builtin_expect(!!(x), 1)
#define TL_UNLIKELY(x) __builtin_expect(!!(x), 0)
#define TL_INLINE      static inline __attribute__((always_inline))
#define TL_NOINLINE    __attribute__((noinline))
#define TL_UNUSED      __attribute__((unused))
#else
#define TL_LIKELY(x)   (x)
#define TL_UNLIKELY(x) (x)
#define TL_INLINE      static inline
#define TL_NOINLINE
#define TL_UNUSED
#endif

TL_INLINE bool tl_ts_is_unbounded(tl_ts_t ts) {
    return ts == TL_TS_UNBOUNDED;
}

TL_INLINE bool tl_ts_before_end(tl_ts_t ts, tl_ts_t end) {
    return tl_ts_is_unbounded(end) || ts < end;
}

TL_INLINE bool tl_ts_range_empty(tl_ts_t t1, tl_ts_t t2) {
    return !tl_ts_is_unbounded(t2) && t1 >= t2;
}

#ifdef __cplusplus
}
#endif

#endif /* TL_DEFS_H */
