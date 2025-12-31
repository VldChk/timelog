#include "../internal/tl_filter.h"

void tl_tomb_cursor_init(tl_tomb_cursor_t* cur, const tl_tombstones_t* tombs) {
    if (cur == NULL) return;

    cur->tombs = tombs;
    cur->idx = 0;

    if (tombs != NULL && tombs->n > 0) {
        cur->cur_start = tombs->v[0].start;
        cur->cur_end = tombs->v[0].end;
        cur->cur_end_unbounded = tombs->v[0].end_unbounded;
    } else {
        cur->cur_start = TL_TS_MAX;
        cur->cur_end = TL_TS_MAX;
        cur->cur_end_unbounded = false;
    }
}

bool tl_tomb_cursor_is_deleted(tl_tomb_cursor_t* cur, tl_ts_t ts) {
    if (cur == NULL || cur->tombs == NULL || cur->tombs->n == 0) {
        return false;
    }

    /*
     * Advance cursor while ts >= cur_end.
     * Because timestamps are non-decreasing, we only move forward.
     */
    while (cur->idx < cur->tombs->n &&
           !tl_ts_before_end(ts, cur->cur_end, cur->cur_end_unbounded)) {
        cur->idx++;
        if (cur->idx < cur->tombs->n) {
            cur->cur_start = cur->tombs->v[cur->idx].start;
            cur->cur_end = cur->tombs->v[cur->idx].end;
            cur->cur_end_unbounded = cur->tombs->v[cur->idx].end_unbounded;
        } else {
            cur->cur_start = TL_TS_MAX;
            cur->cur_end = TL_TS_MAX;
            cur->cur_end_unbounded = false;
        }
    }

    /* Check if ts falls within current interval [cur_start, cur_end) */
    return (ts >= cur->cur_start &&
            tl_ts_before_end(ts, cur->cur_end, cur->cur_end_unbounded));
}

/*
 * Advance filtered iterator to next non-deleted record.
 */
static void filtered_iter_advance_to_valid(tl_filtered_iter_t* it) {
    while (tl_merge_iter_state(it->merge) == TL_ITER_READY) {
        const tl_record_t* rec = tl_merge_iter_peek(it->merge);
        if (rec == NULL) {
            it->state = TL_ITER_EOF;
            return;
        }

        /* Check if record is deleted */
        if (!tl_tomb_cursor_is_deleted(&it->cursor, rec->ts)) {
            /* Found non-deleted record */
            it->current = *rec;
            it->state = TL_ITER_READY;
            return;
        }

        /* Record is deleted, advance merge iterator */
        tl_merge_iter_advance(it->merge);
    }

    it->state = TL_ITER_EOF;
}

tl_status_t tl_filtered_iter_create(const tl_allocator_t* alloc,
                                     tl_merge_iter_t* merge,
                                     const tl_tombstones_t* tombs,
                                     tl_filtered_iter_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    tl_filtered_iter_t* it = tl__calloc(alloc, 1, sizeof(tl_filtered_iter_t));
    if (it == NULL) return TL_ENOMEM;

    it->alloc = alloc;
    it->merge = merge;
    it->state = TL_ITER_EOF;

    /* Initialize tombstone cursor */
    tl_tomb_cursor_init(&it->cursor, tombs);

    /* Position to first non-deleted record */
    if (merge != NULL) {
        filtered_iter_advance_to_valid(it);
    }

    *out = it;
    return TL_OK;
}

void tl_filtered_iter_destroy(tl_filtered_iter_t* it) {
    if (it == NULL) return;
    /* Note: we don't own the merge iterator */
    tl__free(it->alloc, it);
}

const tl_record_t* tl_filtered_iter_peek(tl_filtered_iter_t* it) {
    if (it == NULL || it->state != TL_ITER_READY) return NULL;
    return &it->current;
}

tl_status_t tl_filtered_iter_advance(tl_filtered_iter_t* it) {
    if (it == NULL) return TL_EINVAL;
    if (it->state != TL_ITER_READY) return TL_EOF;

    /* Advance underlying merge iterator */
    tl_merge_iter_advance(it->merge);

    /* Find next non-deleted record */
    filtered_iter_advance_to_valid(it);

    return (it->state == TL_ITER_READY) ? TL_OK : TL_EOF;
}

tl_iter_state_t tl_filtered_iter_state(tl_filtered_iter_t* it) {
    return it ? it->state : TL_ITER_EOF;
}
