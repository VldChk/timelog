#include "internal/tl_recvec.h"
#include <string.h>
#include <stdlib.h>

/* Growth factor: 1.5x (good balance of memory efficiency and copy frequency) */
#define TL_RECVEC_GROWTH_NUM 3
#define TL_RECVEC_GROWTH_DEN 2

/* Minimum allocation to avoid tiny reallocs */
#define TL_RECVEC_MIN_CAP 16

static size_t next_capacity(size_t current, size_t needed) {
    /* At least double what we have, or what's needed */
    size_t grow = current * TL_RECVEC_GROWTH_NUM / TL_RECVEC_GROWTH_DEN;
    if (grow < needed) grow = needed;
    if (grow < TL_RECVEC_MIN_CAP) grow = TL_RECVEC_MIN_CAP;
    return grow;
}

void tl_recvec_init(tl_recvec_t* vec, const tl_allocator_t* alloc) {
    if (vec == NULL) return;
    vec->data = NULL;
    vec->len = 0;
    vec->cap = 0;
    vec->alloc = alloc;
    vec->pin_count = 0;
}

tl_status_t tl_recvec_init_cap(tl_recvec_t* vec, const tl_allocator_t* alloc,
                               size_t init_cap) {
    if (vec == NULL) return TL_EINVAL;

    tl_recvec_init(vec, alloc);

    if (init_cap > 0) {
        vec->data = tl__malloc(alloc, init_cap * sizeof(tl_record_t));
        if (vec->data == NULL) {
            return TL_ENOMEM;
        }
        vec->cap = init_cap;
    }

    return TL_OK;
}

void tl_recvec_destroy(tl_recvec_t* vec) {
    if (vec == NULL) return;

    if (vec->data != NULL) {
        tl__free(vec->alloc, vec->data);
    }
    vec->data = NULL;
    vec->len = 0;
    vec->cap = 0;
    vec->pin_count = 0;
}

void tl_recvec_clear(tl_recvec_t* vec) {
    if (vec == NULL) return;
    vec->len = 0;
}

tl_status_t tl_recvec_reserve(tl_recvec_t* vec, size_t needed) {
    if (vec == NULL) return TL_EINVAL;
    if (vec->cap >= needed) return TL_OK;

    size_t new_cap = next_capacity(vec->cap, needed);

    if (vec->pin_count > 0) {
        /*
         * Vector is pinned: cannot realloc in place.
         * Must allocate new buffer; old buffer stays valid for readers.
         *
         * Note: This creates a memory "leak" that must be handled by
         * the snapshot/pin system (retire old buffer when unpinned).
         * For Phase 1, we simply allocate new and leave old in place.
         * This is safe because readers have the old pointer.
         */
        tl_record_t* new_data = tl__malloc(vec->alloc, new_cap * sizeof(tl_record_t));
        if (new_data == NULL) {
            return TL_ENOMEM;
        }

        if (vec->len > 0) {
            memcpy(new_data, vec->data, vec->len * sizeof(tl_record_t));
        }

        /* Old buffer deliberately NOT freed (pinned by readers) */
        /* TODO: Phase 2+ needs proper retire-and-reclaim mechanism */

        vec->data = new_data;
        vec->cap = new_cap;
    } else {
        /* Standard realloc */
        tl_record_t* new_data = tl__realloc(vec->alloc, vec->data,
                                            new_cap * sizeof(tl_record_t));
        if (new_data == NULL) {
            return TL_ENOMEM;
        }
        vec->data = new_data;
        vec->cap = new_cap;
    }

    return TL_OK;
}

tl_status_t tl_recvec_push(tl_recvec_t* vec, tl_ts_t ts, tl_handle_t handle) {
    if (vec == NULL) return TL_EINVAL;

    if (vec->len >= vec->cap) {
        tl_status_t st = tl_recvec_reserve(vec, vec->len + 1);
        if (st != TL_OK) return st;
    }

    vec->data[vec->len].ts = ts;
    vec->data[vec->len].handle = handle;
    vec->len++;

    return TL_OK;
}

tl_status_t tl_recvec_push_n(tl_recvec_t* vec, const tl_record_t* recs, size_t n) {
    if (vec == NULL) return TL_EINVAL;
    if (n == 0) return TL_OK;
    if (recs == NULL) return TL_EINVAL;

    tl_status_t st = tl_recvec_reserve(vec, vec->len + n);
    if (st != TL_OK) return st;

    memcpy(&vec->data[vec->len], recs, n * sizeof(tl_record_t));
    vec->len += n;

    return TL_OK;
}

tl_status_t tl_recvec_shrink_to_fit(tl_recvec_t* vec) {
    if (vec == NULL) return TL_EINVAL;
    if (vec->len == vec->cap) return TL_OK;
    if (vec->pin_count > 0) return TL_EBUSY;

    if (vec->len == 0) {
        tl__free(vec->alloc, vec->data);
        vec->data = NULL;
        vec->cap = 0;
        return TL_OK;
    }

    tl_record_t* new_data = tl__realloc(vec->alloc, vec->data,
                                        vec->len * sizeof(tl_record_t));
    if (new_data == NULL) {
        /* Shrink failed, keep old allocation (not fatal) */
        return TL_ENOMEM;
    }

    vec->data = new_data;
    vec->cap = vec->len;
    return TL_OK;
}

void tl_recvec_move(tl_recvec_t* dst, tl_recvec_t* src) {
    if (dst == NULL || src == NULL || dst == src) return;

    /* Destroy existing dst content */
    tl_recvec_destroy(dst);

    /* Transfer ownership */
    dst->data = src->data;
    dst->len = src->len;
    dst->cap = src->cap;
    dst->alloc = src->alloc;
    dst->pin_count = src->pin_count;

    /* Clear source */
    src->data = NULL;
    src->len = 0;
    src->cap = 0;
    src->pin_count = 0;
}

/*
 * Comparison function for qsort
 * Sorts by timestamp only (tie order unspecified per V1 semantics)
 */
static int cmp_record_ts(const void* a, const void* b) {
    const tl_record_t* ra = (const tl_record_t*)a;
    const tl_record_t* rb = (const tl_record_t*)b;

    if (ra->ts < rb->ts) return -1;
    if (ra->ts > rb->ts) return 1;
    return 0;
}

void tl_recvec_sort_by_ts(tl_recvec_t* vec) {
    if (vec == NULL || vec->len < 2) return;

    qsort(vec->data, vec->len, sizeof(tl_record_t), cmp_record_ts);
}

size_t tl_recvec_lower_bound(const tl_recvec_t* vec, tl_ts_t ts) {
    if (vec == NULL || vec->len == 0) return 0;

    /*
     * Binary search for first element with rec.ts >= ts
     * Standard lower_bound algorithm
     */
    size_t lo = 0;
    size_t hi = vec->len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (vec->data[mid].ts < ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

void tl_recvec_pin(tl_recvec_t* vec) {
    if (vec == NULL) return;
    vec->pin_count++;
}

void tl_recvec_unpin(tl_recvec_t* vec) {
    if (vec == NULL || vec->pin_count == 0) return;
    vec->pin_count--;
}

bool tl_recvec_is_pinned(const tl_recvec_t* vec) {
    return vec != NULL && vec->pin_count > 0;
}
