#include "tl_segment_iter.h"
#include "../internal/tl_range.h"
#include "tl_segment_range.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Initialize row bounds for current page.
 * Uses binary search to find the range of rows that overlap [t1, t2).
 */
static void init_page_bounds(tl_segment_iter_t* it) {
    const tl_page_catalog_t* cat = tl_segment_catalog(it->seg);
    const tl_page_meta_t* meta = tl_page_catalog_get(cat, it->page_idx);
    const tl_page_t* page = meta->page;

    /* Skip FULLY_DELETED pages (bitmask test for future flag compatibility) */
    if ((meta->flags & TL_PAGE_FULLY_DELETED) != 0) {
        it->row_idx = 0;
        it->row_end = 0;  /* Empty range, will advance to next page */
        return;
    }

    /* Binary search for row boundaries within this page */
    it->row_idx = tl_page_lower_bound(page, it->t1);

    if (it->t2_unbounded) {
        it->row_end = page->count;
    } else {
        it->row_end = tl_page_lower_bound(page, it->t2);
    }
}

/**
 * Advance to next page that has rows in range.
 * Returns true if found a valid page, false if exhausted.
 */
static bool advance_to_next_page(tl_segment_iter_t* it) {
    it->page_idx++;

    while (it->page_idx < it->page_end) {
        init_page_bounds(it);

        /* Check if this page has any rows in range */
        if (it->row_idx < it->row_end) {
            return true;
        }

        /* No rows in range, try next page */
        it->page_idx++;
    }

    /* Exhausted all pages */
    return false;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_segment_iter_init(tl_segment_iter_t* it,
                           const tl_segment_t* seg,
                           tl_ts_t t1, tl_ts_t t2,
                           bool t2_unbounded) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(seg != NULL);

    memset(it, 0, sizeof(*it));
    it->seg = seg;
    it->t1 = t1;
    it->t2 = t2;
    it->t2_unbounded = t2_unbounded;
    it->done = false;

    /*
     * Check segment bounds first (pruning).
     * Use tl_range_overlaps for correct unbounded handling.
     */
    if (!tl_range_overlaps(seg->min_ts, seg->max_ts, t1, t2, t2_unbounded)) {
        it->done = true;
        return;
    }

    /* Handle tombstone-only segments (no pages to iterate) */
    if (seg->page_count == 0) {
        it->done = true;
        return;
    }

    size_t first = 0;
    size_t last = 0;
    if (!tl_segment_page_range(seg, t1, t2, t2_unbounded, &first, &last)) {
        it->done = true;
        return;
    }

    it->page_idx = first;
    it->page_end = last;

    /* Initialize first page bounds */
    init_page_bounds(it);

    /* If first page has no rows in range, advance to next page */
    if (it->row_idx >= it->row_end) {
        if (!advance_to_next_page(it)) {
            it->done = true;
        }
    }
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_segment_iter_next(tl_segment_iter_t* it, tl_record_t* out) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return TL_EOF;
    }

    for (;;) {
        /* Ensure current page bounds are valid */
        if (it->row_idx >= it->row_end) {
            if (!advance_to_next_page(it)) {
                it->done = true;
                return TL_EOF;
            }
        }

        const tl_page_catalog_t* cat = tl_segment_catalog(it->seg);
        const tl_page_meta_t* meta = tl_page_catalog_get(cat, it->page_idx);
        const tl_page_t* page = meta->page;

        /* Skip deleted rows on PARTIAL_DELETED pages */
        if (tl_page_row_is_deleted(page, it->row_idx)) {
            it->row_idx++;
            continue;
        }

        /* Load current record */
        tl_record_t rec;
        tl_page_get_record(page, it->row_idx, &rec);

        /* Output the record if requested */
        if (out != NULL) {
            *out = rec;
        }

        /* Advance to next row */
        it->row_idx++;

        /* Check if we've exhausted the current page */
        if (it->row_idx >= it->row_end) {
            /* Try to advance to next page */
            if (!advance_to_next_page(it)) {
                it->done = true;
            }
        }

        return TL_OK;
    }
}

void tl_segment_iter_seek(tl_segment_iter_t* it, tl_ts_t target) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return;
    }

    /*
     * If target is before or at current position, do nothing.
     * We can only seek forward.
     */
    if (target <= it->t1) {
        return;
    }

    /*
     * Check if target is past the query range end.
     */
    if (!it->t2_unbounded && target >= it->t2) {
        it->done = true;
        return;
    }

    /*
     * Check if target is past the segment's max_ts.
     */
    if (target > it->seg->max_ts) {
        it->done = true;
        return;
    }

    /*
     * Save current position for monotonicity clamping.
     * Seek must NEVER go backwards - this is a critical invariant.
     */
    size_t old_page_idx = it->page_idx;
    size_t old_row_idx = it->row_idx;

    const tl_page_catalog_t* cat = tl_segment_catalog(it->seg);

    /*
     * Find the first page that might contain target.
     * This is the page with max_ts >= target.
     */
    size_t new_page_idx = tl_page_catalog_find_first_ge(cat, target);

    /* Make sure we don't go backwards or past the end */
    if (new_page_idx < it->page_idx) {
        new_page_idx = it->page_idx;
    }

    if (new_page_idx >= it->page_end) {
        it->done = true;
        return;
    }

    /* Update position */
    it->page_idx = new_page_idx;

    /* Reinitialize page bounds with new t1 = target */
    const tl_page_meta_t* meta = tl_page_catalog_get(cat, it->page_idx);
    const tl_page_t* page = meta->page;

    /* Skip FULLY_DELETED pages (bitmask test for future flag compatibility) */
    if ((meta->flags & TL_PAGE_FULLY_DELETED) != 0) {
        it->row_idx = 0;
        it->row_end = 0;
    } else {
        /* Binary search for row >= target */
        size_t new_row_idx = tl_page_lower_bound(page, target);

        /*
         * CRITICAL: Clamp row_idx to maintain monotonicity.
         * When staying on the same page, never go backwards.
         */
        if (it->page_idx == old_page_idx && new_row_idx < old_row_idx) {
            new_row_idx = old_row_idx;
        }

        it->row_idx = new_row_idx;

        if (it->t2_unbounded) {
            it->row_end = page->count;
        } else {
            it->row_end = tl_page_lower_bound(page, it->t2);
        }
    }

    /* If this page has no rows in range, advance to next page */
    if (it->row_idx >= it->row_end) {
        if (!advance_to_next_page(it)) {
            it->done = true;
        }
    }

}
