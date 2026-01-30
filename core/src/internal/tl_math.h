#ifndef TL_MATH_H
#define TL_MATH_H

#include "tl_defs.h"

#include <stdint.h>
#include <stdbool.h>

/*===========================================================================
 * Overflow-Safe int64 Arithmetic
 *
 * These helpers return true if the operation would overflow, false otherwise.
 * On success, the result is stored in *out.
 *===========================================================================*/

/* Overflow-safe addition: computes a + b. */
TL_INLINE bool tl_add_overflow_i64(int64_t a, int64_t b, int64_t* out) {
    /*
     * Overflow cases:
     * 1. b > 0 && a > INT64_MAX - b  (positive overflow)
     * 2. b < 0 && a < INT64_MIN - b  (negative overflow)
     */
    if (b > 0 && a > INT64_MAX - b) {
        return true;
    }
    if (b < 0 && a < INT64_MIN - b) {
        return true;
    }
    *out = a + b;
    return false;
}

/* Overflow-safe subtraction: computes a - b. */
TL_INLINE bool tl_sub_overflow_i64(int64_t a, int64_t b, int64_t* out) {
    /*
     * Overflow cases:
     * 1. b > 0 && a < INT64_MIN + b  (a - b would underflow)
     * 2. b < 0 && a > INT64_MAX + b  (a - b would overflow)
     */
    if (b > 0 && a < INT64_MIN + b) {
        return true;
    }
    if (b < 0 && a > INT64_MAX + b) {
        return true;
    }
    *out = a - b;
    return false;
}

/* Overflow-safe multiplication: computes a * b. */
TL_INLINE bool tl_mul_overflow_i64(int64_t a, int64_t b, int64_t* out) {
    /*
     * INT64_MIN = -9223372036854775808
     * INT64_MAX =  9223372036854775807
     *
     * Overflow cases:
     * 1. a > 0 && b > 0 && a > INT64_MAX / b
     * 2. a > 0 && b < 0 && b < INT64_MIN / a
     * 3. a < 0 && b > 0 && a < INT64_MIN / b
     * 4. a < 0 && b < 0 && a < INT64_MAX / b
     * 5. Special case: INT64_MIN * -1 overflows
     */

    if (a == 0 || b == 0) {
        *out = 0;
        return false;
    }

    if (a > 0) {
        if (b > 0) {
            if (a > INT64_MAX / b) {
                return true;
            }
        } else {
            if (b < INT64_MIN / a) {
                return true;
            }
        }
    } else {
        if (b > 0) {
            if (a < INT64_MIN / b) {
                return true;
            }
        } else {
            if (a == INT64_MIN || b == INT64_MIN) {
                if (a == INT64_MIN && b < -1) return true;
                if (b == INT64_MIN && a < -1) return true;
            }
            if (a < INT64_MAX / b) {
                return true;
            }
        }
    }

    *out = a * b;
    return false;
}

#endif /* TL_MATH_H */
