#include "tl_recvec.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/** Minimum initial capacity for record vector (larger - batches can be big) */
static const size_t RECVEC_MIN_CAPACITY = 16;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_recvec_init(tl_recvec_t* rv, tl_alloc_ctx_t* alloc) {
    TL_ASSERT(rv != NULL);
    TL_ASSERT(alloc != NULL);

    rv->data = NULL;
    rv->len = 0;
    rv->cap = 0;
    rv->alloc = alloc;
}

void tl_recvec_destroy(tl_recvec_t* rv) {
    if (rv == NULL) {
        return;
    }

    if (rv->data != NULL) {
        tl__free(rv->alloc, rv->data);
    }

    /* Leave in valid empty state for idempotent destroy */
    rv->data = NULL;
    rv->len = 0;
    rv->cap = 0;
    /* Note: alloc pointer is borrowed, not cleared */
}

void tl_recvec_clear(tl_recvec_t* rv) {
    TL_ASSERT(rv != NULL);
    rv->len = 0;
}

/*===========================================================================
 * Capacity Management
 *===========================================================================*/

tl_status_t tl_recvec_reserve(tl_recvec_t* rv, size_t min_cap) {
    TL_ASSERT(rv != NULL);

    if (min_cap <= rv->cap) {
        return TL_OK; /* Already have enough capacity */
    }

    size_t new_cap = tl__grow_capacity(rv->cap, min_cap, RECVEC_MIN_CAPACITY);
    if (new_cap == 0 || tl__alloc_would_overflow(new_cap, sizeof(tl_record_t))) {
        return TL_ENOMEM;
    }

    tl_record_t* new_data = tl__realloc(rv->alloc, rv->data,
                                         new_cap * sizeof(tl_record_t));
    if (new_data == NULL) {
        return TL_ENOMEM;
    }

    rv->data = new_data;
    rv->cap = new_cap;
    return TL_OK;
}

tl_status_t tl_recvec_shrink_to_fit(tl_recvec_t* rv) {
    TL_ASSERT(rv != NULL);

    if (rv->len == rv->cap) {
        return TL_OK; /* Already exact fit */
    }

    if (rv->len == 0) {
        /* Free backing storage entirely */
        if (rv->data != NULL) {
            tl__free(rv->alloc, rv->data);
            rv->data = NULL;
        }
        rv->cap = 0;
        return TL_OK;
    }

    /* Reallocate to exact size */
    tl_record_t* new_data = tl__realloc(rv->alloc, rv->data,
                                         rv->len * sizeof(tl_record_t));
    if (new_data == NULL) {
        /* Realloc failed, capacity unchanged (data is still valid) */
        return TL_ENOMEM;
    }

    rv->data = new_data;
    rv->cap = rv->len;
    return TL_OK;
}

/*===========================================================================
 * Insertion
 *===========================================================================*/

tl_status_t tl_recvec_push(tl_recvec_t* rv, tl_ts_t ts, tl_handle_t handle) {
    TL_ASSERT(rv != NULL);

    /* Check for len overflow */
    if (rv->len == SIZE_MAX) {
        return TL_ENOMEM;
    }

    tl_status_t s = tl_recvec_reserve(rv, rv->len + 1);
    if (s != TL_OK) {
        return s;
    }

    rv->data[rv->len].ts = ts;
    rv->data[rv->len].handle = handle;
    rv->len++;
    return TL_OK;
}

tl_status_t tl_recvec_push_n(tl_recvec_t* rv, const tl_record_t* records, size_t n) {
    TL_ASSERT(rv != NULL);

    if (n == 0) {
        return TL_OK; /* No-op for n=0 */
    }

    TL_ASSERT(records != NULL);

    /* Check for len + n overflow */
    if (n > SIZE_MAX - rv->len) {
        return TL_ENOMEM;
    }

    tl_status_t s = tl_recvec_reserve(rv, rv->len + n);
    if (s != TL_OK) {
        return s;
    }

    memcpy(&rv->data[rv->len], records, n * sizeof(tl_record_t));
    rv->len += n;
    return TL_OK;
}

tl_status_t tl_recvec_insert(tl_recvec_t* rv, size_t idx, tl_ts_t ts, tl_handle_t handle) {
    TL_ASSERT(rv != NULL);

    if (idx > rv->len) {
        return TL_EINVAL;
    }

    /* Check for len overflow */
    if (rv->len == SIZE_MAX) {
        return TL_ENOMEM;
    }

    tl_status_t s = tl_recvec_reserve(rv, rv->len + 1);
    if (s != TL_OK) {
        return s;
    }

    /* Shift elements to make room */
    if (idx < rv->len) {
        memmove(&rv->data[idx + 1], &rv->data[idx],
                (rv->len - idx) * sizeof(tl_record_t));
    }

    rv->data[idx].ts = ts;
    rv->data[idx].handle = handle;
    rv->len++;
    return TL_OK;
}

/*===========================================================================
 * Binary Search
 *===========================================================================*/

size_t tl_recvec_lower_bound(const tl_recvec_t* rv, tl_ts_t ts) {
    TL_ASSERT(rv != NULL);

    size_t lo = 0;
    size_t hi = rv->len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (rv->data[mid].ts < ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

size_t tl_recvec_upper_bound(const tl_recvec_t* rv, tl_ts_t ts) {
    TL_ASSERT(rv != NULL);

    size_t lo = 0;
    size_t hi = rv->len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (rv->data[mid].ts <= ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

void tl_recvec_range_bounds(const tl_recvec_t* rv, tl_ts_t t1, tl_ts_t t2,
                            size_t* lo, size_t* hi) {
    TL_ASSERT(rv != NULL);
    TL_ASSERT(lo != NULL);
    TL_ASSERT(hi != NULL);

    *lo = tl_recvec_lower_bound(rv, t1);
    *hi = tl_recvec_lower_bound(rv, t2);
}

/*===========================================================================
 * Ownership Transfer
 *===========================================================================*/

tl_record_t* tl_recvec_take(tl_recvec_t* rv, size_t* out_len) {
    TL_ASSERT(rv != NULL);
    TL_ASSERT(out_len != NULL);

    tl_record_t* data = rv->data;
    *out_len = rv->len;

    /* Reset vector to empty state */
    rv->data = NULL;
    rv->len = 0;
    rv->cap = 0;

    return data;
}
