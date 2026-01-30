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

#endif /* TL_SEGMENT_RANGE_H */
