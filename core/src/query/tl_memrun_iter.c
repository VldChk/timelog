#include "tl_memrun_iter.h"
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
 * Merges run[] and ooo[] in timestamp order.
 * On ties, prefers run[] for stability (run records are in-order,
 * ooo records are out-of-order, so run should come first).
 *
 * NOTE: No t2 bounds check here because run_end/ooo_end are already
 * computed as lower_bound(data, len, t2) in init, so all records
 * within [run_pos, run_end) and [ooo_pos, ooo_end) satisfy ts < t2.
 */
static void advance_to_next(tl_memrun_iter_t* it) {
    const tl_record_t* run = tl_memrun_run_data(it->mr);
    const tl_record_t* ooo = tl_memrun_ooo_data(it->mr);

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

void tl_memrun_iter_init(tl_memrun_iter_t* it,
                          const tl_memrun_t* mr,
                          tl_ts_t t1, tl_ts_t t2,
                          bool t2_unbounded) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(mr != NULL);

    memset(it, 0, sizeof(*it));
    it->mr = mr;
    it->t1 = t1;
    it->t2 = t2;
    it->t2_unbounded = t2_unbounded;
    it->done = false;
    it->has_current = false;

    /*
     * Check memrun bounds (pruning).
     * Note: memrun bounds include tombstones, but we only iterate records.
     */
    if (!tl_memrun_has_records(mr)) {
        it->done = true;
        return;
    }

    if (!tl_range_overlaps(tl_memrun_min_ts(mr), tl_memrun_max_ts(mr),
                           t1, t2, t2_unbounded)) {
        it->done = true;
        return;
    }

    /*
     * Find starting positions in run[] and ooo[] using binary search.
     */
    const tl_record_t* run = tl_memrun_run_data(mr);
    size_t run_len = tl_memrun_run_len(mr);
    const tl_record_t* ooo = tl_memrun_ooo_data(mr);
    size_t ooo_len = tl_memrun_ooo_len(mr);

    /* Find first record >= t1 in each array */
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

tl_status_t tl_memrun_iter_next(tl_memrun_iter_t* it, tl_record_t* out) {
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

void tl_memrun_iter_seek(tl_memrun_iter_t* it, tl_ts_t target) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return;
    }

    /*
     * If target is before t1, do nothing.
     */
    if (target <= it->t1) {
        return;
    }

    /*
     * Check if target is past range end.
     */
    if (!it->t2_unbounded && target >= it->t2) {
        it->done = true;
        it->has_current = false;
        return;
    }

    /*
     * Re-compute positions using binary search from target.
     */
    const tl_record_t* run = tl_memrun_run_data(it->mr);
    size_t run_len = tl_memrun_run_len(it->mr);
    const tl_record_t* ooo = tl_memrun_ooo_data(it->mr);
    size_t ooo_len = tl_memrun_ooo_len(it->mr);

    size_t new_run_pos = lower_bound(run, run_len, target);
    size_t new_ooo_pos = lower_bound(ooo, ooo_len, target);

    /* Only advance, never go backwards */
    if (new_run_pos > it->run_pos) {
        it->run_pos = new_run_pos;
    }
    if (new_ooo_pos > it->ooo_pos) {
        it->ooo_pos = new_ooo_pos;
    }

    /* Check if exhausted */
    if (it->run_pos >= it->run_end && it->ooo_pos >= it->ooo_end) {
        it->done = true;
        it->has_current = false;
    } else {
        it->has_current = false;  /* Need to call next() to load record */
    }
}
