/*===========================================================================
 * Record Array Helpers
 *===========================================================================*/

#ifndef TL_RECORDS_H
#define TL_RECORDS_H

#include "tl_alloc.h"
#include <string.h>

/**
 * Copy a record array.
 *
 * If len == 0, sets *out to NULL and returns TL_OK.
 * Performs overflow-safe allocation before memcpy.
 */
TL_INLINE tl_status_t tl_records_copy(tl_alloc_ctx_t* alloc,
                                       const tl_record_t* src,
                                       size_t len,
                                       tl_record_t** out) {
    TL_ASSERT(out != NULL);

    *out = NULL;

    if (len == 0) {
        return TL_OK;
    }
    if (src == NULL) {
        return TL_EINVAL;
    }
    if (tl__alloc_would_overflow(len, sizeof(tl_record_t))) {
        return TL_EOVERFLOW;
    }

    tl_record_t* dst = tl__mallocarray(alloc, len, sizeof(tl_record_t));
    if (dst == NULL) {
        return TL_ENOMEM;
    }

    memcpy(dst, src, len * sizeof(tl_record_t));
    *out = dst;
    return TL_OK;
}

#endif /* TL_RECORDS_H */
