#include "../internal/tl_iter.h"
#include <string.h>

/*===========================================================================
 * Array Iterator Implementation
 *===========================================================================*/

/*
 * Binary search for lower_bound in sorted record array.
 * Returns index of first record with ts >= target, or len if none.
 */
static size_t array_lower_bound(const tl_record_t* data, size_t len, tl_ts_t ts) {
    size_t lo = 0, hi = len;
    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (data[mid].ts < ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    return lo;
}

static void array_iter_position_to_first(tl_array_iter_t* it) {
    /* Find first record >= t1 */
    it->idx = array_lower_bound(it->data, it->len, it->t1);

    /* Find first valid record in range [t1, t2) */
    if (it->idx < it->len && it->data[it->idx].ts < it->t2) {
        it->current = it->data[it->idx];
        it->state = TL_ITER_READY;
        return;
    }

    it->state = TL_ITER_EOF;
}

tl_status_t tl_array_iter_create(const tl_allocator_t* alloc,
                                  const tl_record_t* data,
                                  size_t len,
                                  tl_ts_t t1,
                                  tl_ts_t t2,
                                  tl_array_iter_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    tl_array_iter_t* it = tl__calloc(alloc, 1, sizeof(tl_array_iter_t));
    if (it == NULL) return TL_ENOMEM;

    it->alloc = alloc;
    it->data = data;
    it->len = len;
    it->t1 = t1;
    it->t2 = t2;

    /* Position to first valid record */
    if (data != NULL && len > 0 && t1 < t2) {
        array_iter_position_to_first(it);
    } else {
        it->state = TL_ITER_EOF;
    }

    *out = it;
    return TL_OK;
}

void tl_array_iter_destroy(tl_array_iter_t* it) {
    if (it == NULL) return;
    tl__free(it->alloc, it);
}

const tl_record_t* tl_array_iter_peek(tl_array_iter_t* it) {
    if (it == NULL || it->state != TL_ITER_READY) return NULL;
    return &it->current;
}

tl_status_t tl_array_iter_advance(tl_array_iter_t* it) {
    if (it == NULL) return TL_EINVAL;
    if (it->state != TL_ITER_READY) return TL_EOF;

    it->idx++;

    /* Find next valid record in range */
    if (it->idx < it->len && it->data[it->idx].ts < it->t2) {
        it->current = it->data[it->idx];
        return TL_OK;
    }

    it->state = TL_ITER_EOF;
    return TL_EOF;
}

tl_status_t tl_array_iter_seek(tl_array_iter_t* it, tl_ts_t ts) {
    if (it == NULL) return TL_EINVAL;

    /* Update lower bound */
    if (ts > it->t1) {
        it->t1 = ts;
    }

    /* Seek to first record >= ts */
    it->idx = array_lower_bound(it->data, it->len, ts);

    /* Check if in range */
    if (it->idx < it->len && it->data[it->idx].ts < it->t2) {
        it->current = it->data[it->idx];
        it->state = TL_ITER_READY;
        return TL_OK;
    }

    it->state = TL_ITER_EOF;
    return TL_EOF;
}

tl_iter_state_t tl_array_iter_state(tl_array_iter_t* it) {
    return it ? it->state : TL_ITER_EOF;
}

/*===========================================================================
 * Segment Iterator Implementation
 *===========================================================================*/

/*
 * Load a page and compute row boundaries.
 */
static void segment_iter_load_page(tl_segment_iter_t* it);
static void segment_iter_advance_to_valid(tl_segment_iter_t* it);

static void segment_iter_load_page(tl_segment_iter_t* it) {
    while (it->page_idx < it->page_end) {
        const tl_page_meta_t* meta = &it->seg->catalog.pages[it->page_idx];

        /* Skip fully deleted pages */
        if (meta->flags & TL_PAGE_FULLY_DELETED) {
            it->page_idx++;
            continue;
        }

        it->current_page = meta->page;

        /* Compute row range within page using binary search */
        it->row_idx = tl_page_lower_bound(it->current_page, it->t1);
        it->row_end = tl_page_lower_bound(it->current_page, it->t2);

        /* Skip to next page if empty range in this page */
        if (it->row_idx >= it->row_end) {
            it->page_idx++;
            continue;
        }

        return;
    }

    /* No more pages */
    it->state = TL_ITER_EOF;
}

/*
 * Advance to next non-deleted row within range.
 */
static void segment_iter_advance_to_valid(tl_segment_iter_t* it) {
    while (it->page_idx < it->page_end) {
        /* Scan rows in current page */
        while (it->row_idx < it->row_end) {
            /* Check row deletion status for partially deleted pages */
            if (it->current_page != NULL &&
                (it->current_page->flags & TL_PAGE_PARTIAL_DELETED) &&
                tl_page_row_deleted(it->current_page, it->row_idx)) {
                it->row_idx++;
                continue;
            }

            /* Found valid row */
            it->current.ts = it->current_page->ts[it->row_idx];
            it->current.handle = it->current_page->h[it->row_idx];
            it->state = TL_ITER_READY;
            return;
        }

        /* Move to next page */
        it->page_idx++;
        if (it->page_idx < it->page_end) {
            segment_iter_load_page(it);
        }
    }

    it->state = TL_ITER_EOF;
}

tl_status_t tl_segment_iter_create(const tl_allocator_t* alloc,
                                    const tl_segment_t* seg,
                                    tl_ts_t t1,
                                    tl_ts_t t2,
                                    tl_segment_iter_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    tl_segment_iter_t* it = tl__calloc(alloc, 1, sizeof(tl_segment_iter_t));
    if (it == NULL) return TL_ENOMEM;

    it->alloc = alloc;
    it->seg = seg;
    it->t1 = t1;
    it->t2 = t2;
    it->state = TL_ITER_EOF;

    /* Empty segment check */
    if (seg == NULL || seg->catalog.n_pages == 0) {
        *out = it;
        return TL_OK;
    }

    /* Invalid range check */
    if (t1 >= t2) {
        *out = it;
        return TL_OK;
    }

    /* Check segment overlap with query range */
    if (!tl_segment_overlaps(seg, t1, t2)) {
        *out = it;
        return TL_OK;
    }

    /* Find candidate pages using catalog (fence pointer navigation) */
    it->page_idx = tl_page_catalog_find_first(&seg->catalog, t1);
    it->page_end = tl_page_catalog_find_last(&seg->catalog, t2);

    /* Load first page and position to first valid record */
    if (it->page_idx < it->page_end) {
        segment_iter_load_page(it);
        /* segment_iter_load_page sets state to EOF only on failure,
         * check current_page to see if load succeeded */
        if (it->current_page != NULL) {
            segment_iter_advance_to_valid(it);
        }
    }

    *out = it;
    return TL_OK;
}

void tl_segment_iter_destroy(tl_segment_iter_t* it) {
    if (it == NULL) return;
    tl__free(it->alloc, it);
}

const tl_record_t* tl_segment_iter_peek(tl_segment_iter_t* it) {
    if (it == NULL || it->state != TL_ITER_READY) return NULL;
    return &it->current;
}

tl_status_t tl_segment_iter_advance(tl_segment_iter_t* it) {
    if (it == NULL) return TL_EINVAL;
    if (it->state != TL_ITER_READY) return TL_EOF;

    it->row_idx++;
    segment_iter_advance_to_valid(it);

    return (it->state == TL_ITER_READY) ? TL_OK : TL_EOF;
}

tl_status_t tl_segment_iter_seek(tl_segment_iter_t* it, tl_ts_t ts) {
    if (it == NULL) return TL_EINVAL;
    if (it->seg == NULL) {
        it->state = TL_ITER_EOF;
        return TL_EOF;
    }

    /* Update lower bound */
    if (ts > it->t1) {
        it->t1 = ts;

        /* May need to skip pages with max_ts < ts */
        while (it->page_idx < it->page_end) {
            const tl_page_meta_t* meta = &it->seg->catalog.pages[it->page_idx];
            if (meta->max_ts >= ts) {
                break;
            }
            it->page_idx++;
        }

        if (it->page_idx < it->page_end) {
            segment_iter_load_page(it);
            if (it->current_page != NULL) {
                /* Re-position within page */
                uint32_t new_row = tl_page_lower_bound(it->current_page, ts);
                if (new_row > it->row_idx) {
                    it->row_idx = new_row;
                }
                segment_iter_advance_to_valid(it);
            }
        } else {
            it->state = TL_ITER_EOF;
        }
    }

    return (it->state == TL_ITER_READY) ? TL_OK : TL_EOF;
}

tl_iter_state_t tl_segment_iter_state(tl_segment_iter_t* it) {
    return it ? it->state : TL_ITER_EOF;
}

/*===========================================================================
 * Two-Way Merge Iterator Implementation
 *===========================================================================*/

static void twoway_iter_pick_next(tl_twoway_iter_t* it) {
    /* Check if both arrays have valid records in range */
    bool run_valid = (it->run != NULL &&
                      it->run_idx < it->run_len &&
                      it->run[it->run_idx].ts >= it->t1 &&
                      it->run[it->run_idx].ts < it->t2);
    bool ooo_valid = (it->ooo != NULL &&
                      it->ooo_idx < it->ooo_len &&
                      it->ooo[it->ooo_idx].ts >= it->t1 &&
                      it->ooo[it->ooo_idx].ts < it->t2);

    if (!run_valid && !ooo_valid) {
        it->state = TL_ITER_EOF;
        return;
    }

    /* Pick smaller timestamp (stable: prefer run on tie) */
    if (!ooo_valid || (run_valid && it->run[it->run_idx].ts <= it->ooo[it->ooo_idx].ts)) {
        it->current = it->run[it->run_idx];
    } else {
        it->current = it->ooo[it->ooo_idx];
    }

    it->state = TL_ITER_READY;
}

static void twoway_iter_position(tl_twoway_iter_t* it) {
    /* Position both arrays to first record >= t1 */
    if (it->run != NULL && it->run_len > 0) {
        it->run_idx = array_lower_bound(it->run, it->run_len, it->t1);
    } else {
        it->run_idx = 0;
    }

    if (it->ooo != NULL && it->ooo_len > 0) {
        it->ooo_idx = array_lower_bound(it->ooo, it->ooo_len, it->t1);
    } else {
        it->ooo_idx = 0;
    }

    twoway_iter_pick_next(it);
}

tl_status_t tl_twoway_iter_create(const tl_allocator_t* alloc,
                                   const tl_record_t* run,
                                   size_t run_len,
                                   const tl_record_t* ooo,
                                   size_t ooo_len,
                                   tl_ts_t t1,
                                   tl_ts_t t2,
                                   tl_twoway_iter_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    tl_twoway_iter_t* it = tl__calloc(alloc, 1, sizeof(tl_twoway_iter_t));
    if (it == NULL) return TL_ENOMEM;

    it->alloc = alloc;
    it->run = run;
    it->run_len = run_len;
    it->ooo = ooo;
    it->ooo_len = ooo_len;
    it->t1 = t1;
    it->t2 = t2;

    if (t1 < t2) {
        twoway_iter_position(it);
    } else {
        it->state = TL_ITER_EOF;
    }

    *out = it;
    return TL_OK;
}

void tl_twoway_iter_destroy(tl_twoway_iter_t* it) {
    if (it == NULL) return;
    tl__free(it->alloc, it);
}

const tl_record_t* tl_twoway_iter_peek(tl_twoway_iter_t* it) {
    if (it == NULL || it->state != TL_ITER_READY) return NULL;
    return &it->current;
}

tl_status_t tl_twoway_iter_advance(tl_twoway_iter_t* it) {
    if (it == NULL) return TL_EINVAL;
    if (it->state != TL_ITER_READY) return TL_EOF;

    /* Advance the array that produced the current record */
    bool run_valid = (it->run != NULL &&
                      it->run_idx < it->run_len &&
                      it->run[it->run_idx].ts < it->t2);
    bool ooo_valid = (it->ooo != NULL &&
                      it->ooo_idx < it->ooo_len &&
                      it->ooo[it->ooo_idx].ts < it->t2);

    /* Determine which array produced current record and advance it */
    if (run_valid && it->current.ts == it->run[it->run_idx].ts &&
        it->current.handle == it->run[it->run_idx].handle) {
        it->run_idx++;
    } else if (ooo_valid && it->current.ts == it->ooo[it->ooo_idx].ts &&
               it->current.handle == it->ooo[it->ooo_idx].handle) {
        it->ooo_idx++;
    } else {
        /* Fallback: advance run if it matches ts, else ooo */
        if (run_valid && it->current.ts == it->run[it->run_idx].ts) {
            it->run_idx++;
        } else if (ooo_valid) {
            it->ooo_idx++;
        }
    }

    twoway_iter_pick_next(it);

    return (it->state == TL_ITER_READY) ? TL_OK : TL_EOF;
}

tl_status_t tl_twoway_iter_seek(tl_twoway_iter_t* it, tl_ts_t ts) {
    if (it == NULL) return TL_EINVAL;

    if (ts > it->t1) {
        it->t1 = ts;
        twoway_iter_position(it);
    }

    return (it->state == TL_ITER_READY) ? TL_OK : TL_EOF;
}

tl_iter_state_t tl_twoway_iter_state(tl_twoway_iter_t* it) {
    return it ? it->state : TL_ITER_EOF;
}
