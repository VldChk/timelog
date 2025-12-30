#include "internal/tl_intervals.h"
#include <string.h>

#define TL_INTERVALS_MIN_CAP 4

static size_t next_capacity(size_t current, size_t needed) {
    size_t grow = current * 2;
    if (grow < needed) grow = needed;
    if (grow < TL_INTERVALS_MIN_CAP) grow = TL_INTERVALS_MIN_CAP;
    return grow;
}

void tl_intervals_init(tl_intervals_t* iset, const tl_allocator_t* alloc) {
    if (iset == NULL) return;
    iset->data = NULL;
    iset->len = 0;
    iset->cap = 0;
    iset->alloc = alloc;
}

tl_status_t tl_intervals_init_cap(tl_intervals_t* iset, const tl_allocator_t* alloc,
                                   size_t init_cap) {
    if (iset == NULL) return TL_EINVAL;

    tl_intervals_init(iset, alloc);

    if (init_cap > 0) {
        iset->data = tl__malloc(alloc, init_cap * sizeof(tl_interval_t));
        if (iset->data == NULL) {
            return TL_ENOMEM;
        }
        iset->cap = init_cap;
    }

    return TL_OK;
}

void tl_intervals_destroy(tl_intervals_t* iset) {
    if (iset == NULL) return;

    if (iset->data != NULL) {
        tl__free(iset->alloc, iset->data);
    }
    iset->data = NULL;
    iset->len = 0;
    iset->cap = 0;
}

void tl_intervals_clear(tl_intervals_t* iset) {
    if (iset == NULL) return;
    iset->len = 0;
}

static tl_status_t ensure_capacity(tl_intervals_t* iset, size_t needed) {
    if (iset->cap >= needed) return TL_OK;

    size_t new_cap = next_capacity(iset->cap, needed);
    tl_interval_t* new_data = tl__realloc(iset->alloc, iset->data,
                                          new_cap * sizeof(tl_interval_t));
    if (new_data == NULL) {
        return TL_ENOMEM;
    }

    iset->data = new_data;
    iset->cap = new_cap;
    return TL_OK;
}

/*
 * Find index of first interval where end >= start_ts.
 * This includes adjacent intervals (where end == start_ts) for proper coalescing.
 */
static size_t find_overlap_start(const tl_intervals_t* iset, tl_ts_t start_ts) {
    if (iset->len == 0) return 0;

    /* Binary search for first interval with end >= start_ts (includes adjacent) */
    size_t lo = 0;
    size_t hi = iset->len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (iset->data[mid].end < start_ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

tl_status_t tl_intervals_insert(tl_intervals_t* iset, tl_ts_t start, tl_ts_t end) {
    if (iset == NULL) return TL_EINVAL;
    if (start >= end) return TL_EINVAL;  /* Empty interval */

    /*
     * Algorithm:
     * 1. Find first interval that might overlap (end > new_start)
     * 2. Merge all overlapping/adjacent intervals
     * 3. Insert the merged result
     */

    /* Find merge range start */
    size_t merge_start = find_overlap_start(iset, start);

    /* Extend start/end to cover all overlapping intervals */
    tl_ts_t new_start = start;
    tl_ts_t new_end = end;
    size_t merge_end = merge_start;

    while (merge_end < iset->len && iset->data[merge_end].start <= new_end) {
        /* This interval overlaps or touches [new_start, new_end) */
        if (iset->data[merge_end].start < new_start) {
            new_start = iset->data[merge_end].start;
        }
        if (iset->data[merge_end].end > new_end) {
            new_end = iset->data[merge_end].end;
        }
        merge_end++;
    }

    /* Number of intervals being replaced */
    size_t replace_count = merge_end - merge_start;

    if (replace_count == 0) {
        /* No overlap: insert new interval at merge_start */
        tl_status_t st = ensure_capacity(iset, iset->len + 1);
        if (st != TL_OK) return st;

        /* Shift elements to make room */
        if (merge_start < iset->len) {
            memmove(&iset->data[merge_start + 1], &iset->data[merge_start],
                    (iset->len - merge_start) * sizeof(tl_interval_t));
        }

        iset->data[merge_start].start = new_start;
        iset->data[merge_start].end = new_end;
        iset->len++;
    } else if (replace_count == 1) {
        /* Replace exactly one interval */
        iset->data[merge_start].start = new_start;
        iset->data[merge_start].end = new_end;
    } else {
        /* Replace multiple intervals with one merged interval */
        iset->data[merge_start].start = new_start;
        iset->data[merge_start].end = new_end;

        /* Remove excess intervals by shifting */
        size_t remove_count = replace_count - 1;
        if (merge_end < iset->len) {
            memmove(&iset->data[merge_start + 1], &iset->data[merge_end],
                    (iset->len - merge_end) * sizeof(tl_interval_t));
        }
        iset->len -= remove_count;
    }

    return TL_OK;
}

bool tl_intervals_contains(const tl_intervals_t* iset, tl_ts_t ts) {
    if (iset == NULL || iset->len == 0) return false;

    /* Binary search for interval containing ts */
    size_t lo = 0;
    size_t hi = iset->len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (!tl_ts_before_end(ts, iset->data[mid].end)) {
            lo = mid + 1;
        } else if (iset->data[mid].start > ts) {
            hi = mid;
        } else {
            /* start <= ts < end */
            return true;
        }
    }

    return false;
}

size_t tl_intervals_find(const tl_intervals_t* iset, tl_ts_t ts) {
    if (iset == NULL || iset->len == 0) return 0;

    /* Find first interval where start <= ts < end, or first with start > ts */
    size_t lo = 0;
    size_t hi = iset->len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (!tl_ts_before_end(ts, iset->data[mid].end)) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

tl_status_t tl_intervals_clip(tl_intervals_t* iset, tl_ts_t clip_start, tl_ts_t clip_end) {
    if (iset == NULL) return TL_EINVAL;
    if (clip_start >= clip_end) {
        iset->len = 0;
        return TL_OK;
    }

    /* Find first interval that might intersect clip range */
    size_t first = 0;
    while (first < iset->len && iset->data[first].end <= clip_start) {
        first++;
    }

    /* Find last interval that intersects clip range */
    size_t last = iset->len;
    while (last > first && iset->data[last - 1].start >= clip_end) {
        last--;
    }

    if (first >= last) {
        /* No intervals in clip range */
        iset->len = 0;
        return TL_OK;
    }

    /* Shift surviving intervals to front */
    if (first > 0) {
        memmove(&iset->data[0], &iset->data[first],
                (last - first) * sizeof(tl_interval_t));
    }
    iset->len = last - first;

    /* Clip boundary intervals */
    if (iset->len > 0) {
        if (iset->data[0].start < clip_start) {
            iset->data[0].start = clip_start;
        }
        if (iset->data[iset->len - 1].end > clip_end) {
            iset->data[iset->len - 1].end = clip_end;
        }
    }

    return TL_OK;
}

tl_status_t tl_intervals_union(tl_intervals_t* dst,
                                const tl_intervals_t* src1,
                                const tl_intervals_t* src2) {
    if (dst == NULL) return TL_EINVAL;

    tl_intervals_clear(dst);

    /* Handle empty cases */
    if (tl_intervals_empty(src1) && tl_intervals_empty(src2)) {
        return TL_OK;
    }
    if (tl_intervals_empty(src1)) {
        return tl_intervals_copy(dst, src2);
    }
    if (tl_intervals_empty(src2)) {
        return tl_intervals_copy(dst, src1);
    }

    /*
     * Merge-style union: iterate both lists in order, coalescing as we go.
     * This is O(n + m) where n and m are the source list sizes.
     */
    size_t i = 0, j = 0;
    tl_ts_t cur_start = 0, cur_end = 0;
    bool have_current = false;

    while (i < src1->len || j < src2->len) {
        /* Pick next interval from whichever source has smaller start */
        const tl_interval_t* next;
        if (i >= src1->len) {
            next = &src2->data[j++];
        } else if (j >= src2->len) {
            next = &src1->data[i++];
        } else if (src1->data[i].start <= src2->data[j].start) {
            next = &src1->data[i++];
        } else {
            next = &src2->data[j++];
        }

        if (!have_current) {
            cur_start = next->start;
            cur_end = next->end;
            have_current = true;
        } else if (next->start <= cur_end) {
            /* Overlaps or touches: extend */
            if (next->end > cur_end) {
                cur_end = next->end;
            }
        } else {
            /* Gap: output current interval and start new */
            tl_status_t st = ensure_capacity(dst, dst->len + 1);
            if (st != TL_OK) return st;

            dst->data[dst->len].start = cur_start;
            dst->data[dst->len].end = cur_end;
            dst->len++;

            cur_start = next->start;
            cur_end = next->end;
        }
    }

    /* Output final interval */
    if (have_current) {
        tl_status_t st = ensure_capacity(dst, dst->len + 1);
        if (st != TL_OK) return st;

        dst->data[dst->len].start = cur_start;
        dst->data[dst->len].end = cur_end;
        dst->len++;
    }

    return TL_OK;
}

tl_status_t tl_intervals_copy(tl_intervals_t* dst, const tl_intervals_t* src) {
    if (dst == NULL) return TL_EINVAL;

    tl_intervals_clear(dst);

    if (src == NULL || src->len == 0) {
        return TL_OK;
    }

    tl_status_t st = ensure_capacity(dst, src->len);
    if (st != TL_OK) return st;

    memcpy(dst->data, src->data, src->len * sizeof(tl_interval_t));
    dst->len = src->len;

    return TL_OK;
}

void tl_intervals_move(tl_intervals_t* dst, tl_intervals_t* src) {
    if (dst == NULL || src == NULL || dst == src) return;

    tl_intervals_destroy(dst);

    dst->data = src->data;
    dst->len = src->len;
    dst->cap = src->cap;
    dst->alloc = src->alloc;

    src->data = NULL;
    src->len = 0;
    src->cap = 0;
}

tl_status_t tl_intervals_validate(const tl_intervals_t* iset) {
    if (iset == NULL) return TL_OK;

    for (size_t i = 0; i < iset->len; i++) {
        /* Check interval validity */
        if (iset->data[i].start >= iset->data[i].end) {
            return TL_EINTERNAL;
        }

        /* Check ordering and disjointness */
        if (i > 0) {
            if (iset->data[i].start < iset->data[i-1].end) {
                return TL_EINTERNAL;  /* Overlapping */
            }
            if (iset->data[i].start == iset->data[i-1].end) {
                return TL_EINTERNAL;  /* Should have been coalesced */
            }
        }
    }

    return TL_OK;
}
