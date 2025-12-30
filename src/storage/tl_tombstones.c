#include "../internal/tl_tombstones.h"
#include <string.h>

tl_status_t tl_tombstones_create(const tl_allocator_t* alloc,
                                  const tl_intervals_t* src,
                                  tl_tombstones_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    /* Allocate tombstone set */
    tl_tombstones_t* ts = tl__calloc(alloc, 1, sizeof(tl_tombstones_t));
    if (ts == NULL) return TL_ENOMEM;

    if (src == NULL || src->len == 0) {
        /* Empty tombstone set */
        ts->n = 0;
        ts->v = NULL;
        ts->backing = ts;
        *out = ts;
        return TL_OK;
    }

    /* Allocate interval array */
    ts->v = tl__malloc(alloc, src->len * sizeof(tl_interval_t));
    if (ts->v == NULL) {
        tl__free(alloc, ts);
        return TL_ENOMEM;
    }

    /* Copy intervals */
    memcpy(ts->v, src->data, src->len * sizeof(tl_interval_t));
    ts->n = (uint32_t)src->len;
    ts->backing = NULL; /* Separate allocations */

    *out = ts;
    return TL_OK;
}

tl_status_t tl_tombstones_create_move(const tl_allocator_t* alloc,
                                       tl_intervals_t* src,
                                       tl_tombstones_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    /* Allocate tombstone set */
    tl_tombstones_t* ts = tl__calloc(alloc, 1, sizeof(tl_tombstones_t));
    if (ts == NULL) return TL_ENOMEM;

    if (src == NULL || src->len == 0) {
        /* Empty tombstone set */
        ts->n = 0;
        ts->v = NULL;
        ts->backing = ts;
        *out = ts;
        return TL_OK;
    }

    /* Transfer ownership */
    ts->v = src->data;
    ts->n = (uint32_t)src->len;
    ts->backing = NULL;

    /* Clear source */
    src->data = NULL;
    src->len = 0;
    src->cap = 0;

    *out = ts;
    return TL_OK;
}

void tl_tombstones_destroy(const tl_allocator_t* alloc, tl_tombstones_t* ts) {
    if (ts == NULL) return;

    if (ts->v != NULL && ts->backing != ts) {
        tl__free(alloc, ts->v);
    }
    tl__free(alloc, ts);
}

bool tl_tombstones_contains(const tl_tombstones_t* ts, tl_ts_t t) {
    if (ts == NULL || ts->n == 0) return false;

    /* Binary search for interval containing t */
    uint32_t lo = 0;
    uint32_t hi = ts->n;

    while (lo < hi) {
        uint32_t mid = lo + (hi - lo) / 2;
        if (!tl_ts_before_end(t, ts->v[mid].end)) {
            lo = mid + 1;
        } else if (ts->v[mid].start > t) {
            hi = mid;
        } else {
            /* start <= t < end */
            return true;
        }
    }

    return false;
}

tl_ts_t tl_tombstones_min_ts(const tl_tombstones_t* ts) {
    if (ts == NULL || ts->n == 0) return TL_TS_MAX;
    return ts->v[0].start;
}

tl_ts_t tl_tombstones_max_ts(const tl_tombstones_t* ts) {
    if (ts == NULL || ts->n == 0) return TL_TS_MIN;
    return ts->v[ts->n - 1].end;
}
