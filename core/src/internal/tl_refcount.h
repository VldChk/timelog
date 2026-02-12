#ifndef TL_REFCOUNT_H
#define TL_REFCOUNT_H

#include "tl_defs.h"
#include "tl_atomic.h"

/*
 * Shared release pattern for intrusive refcounted objects:
 * - post-decrement guard via TL_VERIFY (safe in release builds)
 * - acquire fence before final destruction
 */
#define TL_REFCOUNT_RELEASE(refcnt_ptr, on_zero, double_release_msg) \
    do { \
        uint32_t tl_refcount_old__ = tl_atomic_fetch_sub_u32((refcnt_ptr), 1, TL_MO_RELEASE); \
        TL_VERIFY(tl_refcount_old__ >= 1 && (double_release_msg)); \
        if (tl_refcount_old__ == 1) { \
            tl_atomic_fence(TL_MO_ACQUIRE); \
            do { on_zero; } while (0); \
        } \
    } while (0)

#endif /* TL_REFCOUNT_H */

