#ifndef TL_SEGMENT_RANGE_H
#define TL_SEGMENT_RANGE_H

#include "../storage/tl_segment.h"
#include "../storage/tl_page.h"
#include "../internal/tl_search.h"
#include "../internal/tl_range.h"

/**
 * Compute page index range [first, last) overlapping [t1, t2).
 *
 * Returns true if any pages overlap, false otherwise.
 * Does NOT perform segment-level overlap checks; caller should prune first.
 */
TL_INLINE bool tl_segment_page_range(const tl_segment_t* seg,
                                      tl_ts_t t1,
                                      tl_ts_t t2,
                                      bool t2_unbounded,
                                      size_t* out_first,
                                      size_t* out_last) {
    if (seg == NULL || seg->page_count == 0) {
        return false;
    }

    const tl_page_catalog_t* cat = tl_segment_catalog(seg);
    size_t first = tl_page_catalog_find_first_ge(cat, t1);
    size_t last = t2_unbounded ? tl_page_catalog_count(cat)
                               : tl_page_catalog_find_start_ge(cat, t2);

    if (first >= last) {
        return false;
    }

    if (out_first != NULL) {
        *out_first = first;
    }
    if (out_last != NULL) {
        *out_last = last;
    }

    return true;
}


/**
 * Count records in [a, b) for a segment using page-level metadata.
 *
 * Algorithm:
 * - Prune pages via catalog fence searches:
 *     first page with max_ts >= a
 *     first page with min_ts >= b (exclusive end)
 * - Boundary pages use page-local lower_bound to compute partial counts
 * - Interior pages sum via page metadata counts
 *
 * Returns 0 for empty ranges or non-overlapping segments.
 */
TL_INLINE uint64_t tl_count_records_in_segment_range(const tl_segment_t* seg,
                                                      tl_ts_t a,
                                                      tl_ts_t b,
                                                      bool b_unbounded) {
    if (seg == NULL || seg->page_count == 0) {
        return 0;
    }

    if (!b_unbounded && a >= b) {
        return 0;
    }

    if (!tl_range_overlaps(seg->record_min_ts, seg->record_max_ts, a, b, b_unbounded)) {
        return 0;
    }

    const tl_page_catalog_t* cat = tl_segment_catalog(seg);
    size_t first = tl_page_catalog_find_first_ge(cat, a);
    size_t last = b_unbounded ? tl_page_catalog_count(cat)
                              : tl_page_catalog_find_start_ge(cat, b);

    if (first >= last) {
        return 0;
    }

    if (first + 1 >= last) {
        const tl_page_meta_t* meta = tl_page_catalog_get(cat, first);
        const tl_page_t* page = meta->page;
        size_t lo = tl_page_lower_bound(page, a);
        size_t hi = b_unbounded ? page->count : tl_page_lower_bound(page, b);
        if (hi <= lo) {
            return 0;
        }
        return (uint64_t)(hi - lo);
    }

    uint64_t total = 0;

    const tl_page_meta_t* first_meta = tl_page_catalog_get(cat, first);
    size_t first_lo = tl_page_lower_bound(first_meta->page, a);
    if (first_lo < first_meta->count) {
        total += (uint64_t)(first_meta->count - first_lo);
    }

    const tl_page_meta_t* last_meta = tl_page_catalog_get(cat, last - 1);
    size_t last_hi = b_unbounded ? last_meta->count : tl_page_lower_bound(last_meta->page, b);
    if (last_hi > 0) {
        total += (uint64_t)last_hi;
    }

    size_t interior_start = first + 1;
    size_t interior_end = last - 1;
    if (interior_start < interior_end) {
        if (seg->page_prefix_counts != NULL) {
            total += seg->page_prefix_counts[interior_end] - seg->page_prefix_counts[interior_start];
        } else {
            for (size_t i = interior_start; i < interior_end; i++) {
                total += tl_page_catalog_get(cat, i)->count;
            }
        }
    }

    return total;
}

#endif /* TL_SEGMENT_RANGE_H */
