#include "tl_active_iter.h"
#include "../internal/tl_range.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Binary search: find first index where data[i].ts >= target.
 * Returns len if all records have ts < target.
 */
static size_t lower_bound(const tl_record_t* data, size_t len, tl_ts_t target) {
    size_t lo = 0;
    size_t hi = len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (data[mid].ts < target) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

/**
 * Advance to next valid record using two-way merge.
 *
 * NOTE: No t2 bounds check here because run_end/ooo_end are already
 * computed as lower_bound(data, len, t2) in init, so all records
 * within [run_pos, run_end) and [ooo_pos, ooo_end) satisfy ts < t2.
 */
static void advance_to_next(tl_active_iter_t* it) {
    const tl_record_t* run = tl_memview_run_data(it->mv);
    const tl_record_t* ooo = tl_memview_ooo_data(it->mv);

    bool run_done = (it->run_pos >= it->run_end);
    bool ooo_done = (it->ooo_pos >= it->ooo_end);

    if (run_done && ooo_done) {
        it->done = true;
        it->has_current = false;
        return;
    }

    /* Select smaller timestamp (prefer run on tie for stability) */
    const tl_record_t* next;
    if (run_done) {
        next = &ooo[it->ooo_pos++];
    } else if (ooo_done) {
        next = &run[it->run_pos++];
    } else if (run[it->run_pos].ts <= ooo[it->ooo_pos].ts) {
        next = &run[it->run_pos++];
    } else {
        next = &ooo[it->ooo_pos++];
    }

    it->current = *next;
    it->has_current = true;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_active_iter_init(tl_active_iter_t* it,
                          const tl_memview_t* mv,
                          tl_ts_t t1, tl_ts_t t2,
                          bool t2_unbounded) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(mv != NULL);

    memset(it, 0, sizeof(*it));
    it->mv = mv;
    it->t1 = t1;
    it->t2 = t2;
    it->t2_unbounded = t2_unbounded;
    it->done = false;
    it->has_current = false;

    /* Get active buffer lengths */
    size_t run_len = tl_memview_run_len(mv);
    size_t ooo_len = tl_memview_ooo_len(mv);

    /* Check if there are any active records */
    if (run_len == 0 && ooo_len == 0) {
        it->done = true;
        return;
    }

    /*
     * Find starting positions using binary search.
     */
    const tl_record_t* run = tl_memview_run_data(mv);
    const tl_record_t* ooo = tl_memview_ooo_data(mv);

    it->run_pos = lower_bound(run, run_len, t1);
    it->ooo_pos = lower_bound(ooo, ooo_len, t1);

    /* Set end positions */
    if (t2_unbounded) {
        it->run_end = run_len;
        it->ooo_end = ooo_len;
    } else {
        it->run_end = lower_bound(run, run_len, t2);
        it->ooo_end = lower_bound(ooo, ooo_len, t2);
    }

    /* Check if anything in range */
    if (it->run_pos >= it->run_end && it->ooo_pos >= it->ooo_end) {
        it->done = true;
    }
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_active_iter_next(tl_active_iter_t* it, tl_record_t* out) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return TL_EOF;
    }

    /* Advance to get the next record */
    advance_to_next(it);

    if (it->done) {
        return TL_EOF;
    }

    /* Output the record if requested */
    if (out != NULL) {
        *out = it->current;
    }

    return TL_OK;
}

void tl_active_iter_seek(tl_active_iter_t* it, tl_ts_t target) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return;
    }

    if (target <= it->t1) {
        return;
    }

    if (!it->t2_unbounded && target >= it->t2) {
        it->done = true;
        it->has_current = false;
        return;
    }

    const tl_record_t* run = tl_memview_run_data(it->mv);
    size_t run_len = tl_memview_run_len(it->mv);
    const tl_record_t* ooo = tl_memview_ooo_data(it->mv);
    size_t ooo_len = tl_memview_ooo_len(it->mv);

    size_t new_run_pos = lower_bound(run, run_len, target);
    size_t new_ooo_pos = lower_bound(ooo, ooo_len, target);

    /* Only advance, never go backwards */
    if (new_run_pos > it->run_pos) {
        it->run_pos = new_run_pos;
    }
    if (new_ooo_pos > it->ooo_pos) {
        it->ooo_pos = new_ooo_pos;
    }

    if (it->run_pos >= it->run_end && it->ooo_pos >= it->ooo_end) {
        it->done = true;
        it->has_current = false;
    } else {
        it->has_current = false;
    }
}
