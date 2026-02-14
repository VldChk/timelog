#ifndef TL_SEGMENT_RANGE_H
#define TL_SEGMENT_RANGE_H

#include "../storage/tl_segment.h"
#include "../storage/tl_page.h"

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
 * Count records in segment overlap [a, b) without row scan.
 *
 * Uses page-catalog fences to locate candidate pages, then:
 * - boundary pages: page-local lower_bound arithmetic
 * - interior pages: page metadata count (or optional segment prefix sums)
 */
TL_INLINE uint64_t tl_count_records_in_segment_range(const tl_segment_t* seg,
                                                     tl_ts_t a,
                                                     tl_ts_t b) {
    if (seg == NULL || seg->page_count == 0 || a >= b) {
        return 0;
    }

    const tl_page_catalog_t* cat = tl_segment_catalog(seg);
    size_t first = tl_page_catalog_find_first_ge(cat, a);
    size_t last = tl_page_catalog_find_start_ge(cat, b);

    if (first >= last) {
        return 0;
    }

    if (last - first == 1) {
        const tl_page_meta_t* pm = tl_page_catalog_get(cat, first);
        const tl_page_t* page = pm->page;
        size_t lo = tl_page_lower_bound(page, a);
        size_t hi = tl_page_lower_bound(page, b);
        return (hi > lo) ? (uint64_t)(hi - lo) : 0;
    }

    const tl_page_meta_t* first_meta = tl_page_catalog_get(cat, first);
    const tl_page_t* first_page = first_meta->page;
    size_t first_lo = tl_page_lower_bound(first_page, a);
    uint64_t total = (uint64_t)first_meta->count - (uint64_t)first_lo;

    size_t last_idx = last - 1;
    const tl_page_meta_t* last_meta = tl_page_catalog_get(cat, last_idx);
    const tl_page_t* last_page = last_meta->page;
    size_t last_hi = tl_page_lower_bound(last_page, b);
    total += (uint64_t)last_hi;

    size_t interior_first = first + 1;
    if (interior_first < last_idx) {
        total += tl_segment_page_prefix_sum(seg, interior_first, last_idx);
    }

    return total;
}

TL_INLINE uint64_t tl_count_records_in_segment_since(const tl_segment_t* seg,
                                                     tl_ts_t a) {
    if (seg == NULL || seg->page_count == 0) {
        return 0;
    }

    const tl_page_catalog_t* cat = tl_segment_catalog(seg);
    size_t first = tl_page_catalog_find_first_ge(cat, a);
    size_t last = tl_page_catalog_count(cat);
    if (first >= last) {
        return 0;
    }

    const tl_page_meta_t* first_meta = tl_page_catalog_get(cat, first);
    const tl_page_t* first_page = first_meta->page;
    size_t first_lo = tl_page_lower_bound(first_page, a);
    uint64_t total = (uint64_t)first_meta->count - (uint64_t)first_lo;

    size_t interior_first = first + 1;
    if (interior_first < last) {
        total += tl_segment_page_prefix_sum(seg, interior_first, last);
    }

    return total;
}

#endif /* TL_SEGMENT_RANGE_H */
