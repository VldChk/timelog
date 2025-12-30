#include "internal/tl_status.h"

static const char* const tl_status_strings[] = {
    [TL_OK]        = "success",
    [TL_EOF]       = "end of iteration or not found",
    [TL_EINVAL]    = "invalid argument",
    [TL_ESTATE]    = "invalid state for operation",
    [TL_EBUSY]     = "resource busy or backpressure",
    [TL_ENOMEM]    = "memory allocation failed",
    [TL_EINTERNAL] = "internal error"
};

const char* tl_strerror(tl_status_t s) {
    /* Bounds check for safety */
    if (s >= 0 && s <= TL_EINTERNAL && tl_status_strings[s] != NULL) {
        return tl_status_strings[s];
    }
    return "unknown error";
}
