#include "tl_intervals.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Check if allocation size would overflow.
 */
TL_INLINE bool alloc_would_overflow_iv(size_t count, size_t elem_size) {
    return elem_size != 0 && count > SIZE_MAX / elem_size;
}

/**
 * Compute next capacity >= required using 2x growth.
 */
static size_t next_capacity_iv(size_t current, size_t required) {
    static const size_t MIN_CAPACITY = 8;

    size_t new_cap = (current == 0) ? MIN_CAPACITY : current;

    while (new_cap < required) {
        if (new_cap > SIZE_MAX / 2) {
            return SIZE_MAX;
        }
        new_cap *= 2;
    }

    return new_cap;
}

/**
 * Reserve capacity for interval set.
 */
static tl_status_t intervals_reserve(tl_intervals_t* iv, size_t min_cap) {
    if (min_cap <= iv->cap) {
        return TL_OK;
    }

    size_t new_cap = next_capacity_iv(iv->cap, min_cap);

    if (alloc_would_overflow_iv(new_cap, sizeof(tl_interval_t))) {
        return TL_ENOMEM;
    }

    tl_interval_t* new_data = tl__realloc(iv->alloc, iv->data,
                                           new_cap * sizeof(tl_interval_t));
    if (new_data == NULL) {
        return TL_ENOMEM;
    }

    iv->data = new_data;
    iv->cap = new_cap;
    return TL_OK;
}

/**
 * Check if two intervals overlap or are adjacent (can be merged).
 * Handles unbounded intervals correctly.
 *
 * Precondition: a->start <= b->start (caller ensures sorted order)
 */
static bool intervals_can_merge(const tl_interval_t* a, const tl_interval_t* b) {
    if (a->end_unbounded) {
        return true; /* Unbounded covers everything after */
    }
    return a->end >= b->start; /* Adjacent or overlapping */
}

/**
 * Merge two overlapping/adjacent intervals into result.
 * Precondition: intervals_can_merge(a, b) is true.
 */
static void intervals_merge_into(tl_interval_t* result,
                                  const tl_interval_t* a,
                                  const tl_interval_t* b) {
    result->start = TL_MIN(a->start, b->start);

    /* Unboundedness propagates */
    if (a->end_unbounded || b->end_unbounded) {
        result->end_unbounded = true;
        result->end = 0; /* Undefined, set to 0 for safety */
    } else {
        result->end_unbounded = false;
        result->end = TL_MAX(a->end, b->end);
    }
}

/**
 * Find first interval with start >= ts using binary search.
 * Returns position where interval with this start would be inserted.
 */
static size_t intervals_lower_bound(const tl_intervals_t* iv, tl_ts_t ts) {
    size_t lo = 0;
    size_t hi = iv->len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (iv->data[mid].start < ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

/**
 * Push a single interval to the end (no coalescing).
 */
static tl_status_t intervals_push_interval(tl_intervals_t* iv, const tl_interval_t* interval) {
    if (iv->len == SIZE_MAX) {
        return TL_ENOMEM;
    }

    tl_status_t s = intervals_reserve(iv, iv->len + 1);
    if (s != TL_OK) {
        return s;
    }

    iv->data[iv->len] = *interval;
    iv->len++;
    return TL_OK;
}

/**
 * Replace a range [pos, end) with a single interval.
 * Shifts remaining elements.
 */
static tl_status_t intervals_replace_range(tl_intervals_t* iv, size_t pos, size_t end,
                                            const tl_interval_t* replacement) {
    size_t remove_count = end - pos;
    size_t tail_count = iv->len - end;

    if (remove_count == 0) {
        /* Insert new interval at pos */
        if (iv->len == SIZE_MAX) {
            return TL_ENOMEM;
        }

        tl_status_t s = intervals_reserve(iv, iv->len + 1);
        if (s != TL_OK) {
            return s;
        }

        /* Shift tail right by 1 */
        if (tail_count > 0) {
            memmove(&iv->data[pos + 1], &iv->data[pos],
                    tail_count * sizeof(tl_interval_t));
        }

        iv->data[pos] = *replacement;
        iv->len++;
    } else if (remove_count == 1) {
        /* Replace in place */
        iv->data[pos] = *replacement;
    } else {
        /* Replace first, shift tail left */
        iv->data[pos] = *replacement;

        if (tail_count > 0) {
            memmove(&iv->data[pos + 1], &iv->data[end],
                    tail_count * sizeof(tl_interval_t));
        }

        iv->len -= (remove_count - 1);
    }

    return TL_OK;
}

/**
 * Internal insert with full interval struct.
 * Handles both bounded and unbounded intervals.
 */
static tl_status_t intervals_insert_internal(tl_intervals_t* iv,
                                              const tl_interval_t* new_iv) {
    /* Handle empty case */
    if (iv->len == 0) {
        return intervals_push_interval(iv, new_iv);
    }

    /* Find insertion point */
    size_t pos = intervals_lower_bound(iv, new_iv->start);

    /* Working copy of merged interval */
    tl_interval_t merged = *new_iv;

    /* Check predecessor for merge */
    if (pos > 0) {
        tl_interval_t* prev = &iv->data[pos - 1];
        if (intervals_can_merge(prev, &merged)) {
            pos--;
            intervals_merge_into(&merged, prev, &merged);
        }
    }

    /* Merge with successors */
    size_t merge_end = pos;
    while (merge_end < iv->len && !merged.end_unbounded) {
        tl_interval_t* cur = &iv->data[merge_end];
        if (!intervals_can_merge(&merged, cur)) {
            break; /* No more overlap */
        }
        intervals_merge_into(&merged, &merged, cur);
        merge_end++;
    }

    /* If merged is unbounded, consume ALL remaining intervals */
    if (merged.end_unbounded) {
        merge_end = iv->len;
    }

    /* Replace [pos, merge_end) with single merged interval */
    return intervals_replace_range(iv, pos, merge_end, &merged);
}

/**
 * Append interval to end, coalescing with last if overlapping/adjacent.
 * This is O(1) per call - only compares with the last interval.
 *
 * Precondition: new_iv.start >= last interval's start (inputs arrive sorted).
 */
static tl_status_t intervals_append_coalescing(tl_intervals_t* out,
                                                const tl_interval_t* new_iv) {
    if (out->len == 0) {
        return intervals_push_interval(out, new_iv);
    }

    tl_interval_t* last = &out->data[out->len - 1];

    /* Check if we can merge with last */
    if (intervals_can_merge(last, new_iv)) {
        /* Merge in place - O(1) */
        intervals_merge_into(last, last, new_iv);
        return TL_OK;
    }

    /* No merge - append new interval */
    return intervals_push_interval(out, new_iv);
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_intervals_init(tl_intervals_t* iv, tl_alloc_ctx_t* alloc) {
    TL_ASSERT(iv != NULL);
    TL_ASSERT(alloc != NULL);

    iv->data = NULL;
    iv->len = 0;
    iv->cap = 0;
    iv->alloc = alloc;
}

void tl_intervals_destroy(tl_intervals_t* iv) {
    if (iv == NULL) {
        return;
    }

    if (iv->data != NULL) {
        tl__free(iv->alloc, iv->data);
    }

    iv->data = NULL;
    iv->len = 0;
    iv->cap = 0;
}

void tl_intervals_clear(tl_intervals_t* iv) {
    TL_ASSERT(iv != NULL);
    iv->len = 0;
}

/*===========================================================================
 * Insertion
 *===========================================================================*/

tl_status_t tl_intervals_insert(tl_intervals_t* iv, tl_ts_t t1, tl_ts_t t2) {
    TL_ASSERT(iv != NULL);

    /* Empty interval: no-op (Write Path LLD Section 3.8) */
    if (t1 == t2) {
        return TL_OK;
    }

    /* Invalid interval */
    if (t1 > t2) {
        return TL_EINVAL;
    }

    /* Create the new interval (bounded) */
    tl_interval_t new_iv;
    new_iv.start = t1;
    new_iv.end = t2;
    new_iv.end_unbounded = false;

    return intervals_insert_internal(iv, &new_iv);
}

tl_status_t tl_intervals_insert_unbounded(tl_intervals_t* iv, tl_ts_t t1) {
    TL_ASSERT(iv != NULL);

    tl_interval_t new_iv;
    new_iv.start = t1;
    new_iv.end = 0; /* Undefined for unbounded */
    new_iv.end_unbounded = true;

    return intervals_insert_internal(iv, &new_iv);
}

/*===========================================================================
 * Point Containment
 *===========================================================================*/

/**
 * Internal containment check on raw array.
 */
static bool intervals_contains_internal(const tl_interval_t* data, size_t len, tl_ts_t ts) {
    if (len == 0) {
        return false;
    }

    /* Binary search for first interval with start > ts */
    size_t lo = 0;
    size_t hi = len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (data[mid].start <= ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    /* Check if ts is in the interval before lo */
    if (lo == 0) {
        return false;
    }

    const tl_interval_t* cand = &data[lo - 1];
    return cand->end_unbounded || ts < cand->end;
}

bool tl_intervals_contains(const tl_intervals_t* iv, tl_ts_t ts) {
    TL_ASSERT(iv != NULL);
    return intervals_contains_internal(iv->data, iv->len, ts);
}

bool tl_intervals_imm_contains(tl_intervals_imm_t iv, tl_ts_t ts) {
    return intervals_contains_internal(iv.data, iv.len, ts);
}

/*===========================================================================
 * Set Operations
 *===========================================================================*/

tl_status_t tl_intervals_union(tl_intervals_t* out,
                               const tl_intervals_t* a,
                               const tl_intervals_t* b) {
    TL_ASSERT(out != NULL);
    TL_ASSERT(a != NULL);
    TL_ASSERT(b != NULL);
    /* Aliasing not supported: out must be distinct from inputs */
    TL_ASSERT(out != a && out != b);

    tl_intervals_clear(out);

    /* Check for length addition overflow before reserving */
    if (a->len > SIZE_MAX - b->len) {
        return TL_ENOMEM;
    }

    /* Reserve upfront to avoid reallocations during merge */
    tl_status_t s = intervals_reserve(out, a->len + b->len);
    if (s != TL_OK) {
        return s;
    }

    /* Two-pointer merge */
    size_t i = 0, j = 0;

    while (i < a->len || j < b->len) {
        const tl_interval_t* next;

        if (i >= a->len) {
            next = &b->data[j++];
        } else if (j >= b->len) {
            next = &a->data[i++];
        } else if (a->data[i].start <= b->data[j].start) {
            next = &a->data[i++];
        } else {
            next = &b->data[j++];
        }

        /* Append with coalescing - O(1) per interval */
        s = intervals_append_coalescing(out, next);
        if (s != TL_OK) {
            return s;
        }
    }

    return TL_OK;
}

tl_status_t tl_intervals_union_imm(tl_intervals_t* out,
                                   tl_intervals_imm_t a,
                                   tl_intervals_imm_t b) {
    TL_ASSERT(out != NULL);

    tl_intervals_clear(out);

    /* Check for length addition overflow before reserving */
    if (a.len > SIZE_MAX - b.len) {
        return TL_ENOMEM;
    }

    tl_status_t s = intervals_reserve(out, a.len + b.len);
    if (s != TL_OK) {
        return s;
    }

    size_t i = 0, j = 0;

    while (i < a.len || j < b.len) {
        const tl_interval_t* next;

        if (i >= a.len) {
            next = &b.data[j++];
        } else if (j >= b.len) {
            next = &a.data[i++];
        } else if (a.data[i].start <= b.data[j].start) {
            next = &a.data[i++];
        } else {
            next = &b.data[j++];
        }

        s = intervals_append_coalescing(out, next);
        if (s != TL_OK) {
            return s;
        }
    }

    return TL_OK;
}

void tl_intervals_clip(tl_intervals_t* iv, tl_ts_t t1, tl_ts_t t2) {
    TL_ASSERT(iv != NULL);
    TL_ASSERT(t1 < t2); /* Clip range must be valid */

    size_t write = 0;

    for (size_t read = 0; read < iv->len; read++) {
        tl_interval_t* cur = &iv->data[read];

        /* Compute clipped interval */
        tl_ts_t start = TL_MAX(cur->start, t1);
        tl_ts_t end;

        if (cur->end_unbounded) {
            /* Unbounded becomes bounded when clipped */
            end = t2;
        } else {
            end = TL_MIN(cur->end, t2);
        }

        /* Skip if empty after clipping */
        if (start >= end) {
            continue;
        }

        /* Write clipped interval (always bounded after clip) */
        iv->data[write].start = start;
        iv->data[write].end = end;
        iv->data[write].end_unbounded = false;
        write++;
    }

    iv->len = write;
}

/*===========================================================================
 * Accessors and Ownership
 *===========================================================================*/

tl_interval_t* tl_intervals_take(tl_intervals_t* iv, size_t* out_len) {
    TL_ASSERT(iv != NULL);
    TL_ASSERT(out_len != NULL);

    tl_interval_t* data = iv->data;
    *out_len = iv->len;

    iv->data = NULL;
    iv->len = 0;
    iv->cap = 0;

    return data;
}

tl_ts_t tl_intervals_covered_span(const tl_intervals_t* iv) {
    TL_ASSERT(iv != NULL);

    /*
     * Use unsigned arithmetic to avoid signed overflow UB.
     * For extreme ranges like [INT64_MIN, 0), (end - start) would overflow
     * signed arithmetic but is well-defined for unsigned.
     */
    uint64_t total = 0;

    for (size_t i = 0; i < iv->len; i++) {
        const tl_interval_t* cur = &iv->data[i];

        /* Unbounded => saturate to max */
        if (cur->end_unbounded) {
            return TL_TS_MAX;
        }

        /* Unsigned subtraction: always well-defined */
        uint64_t span = (uint64_t)cur->end - (uint64_t)cur->start;

        /* Saturating addition */
        if (span > UINT64_MAX - total) {
            return TL_TS_MAX;
        }
        total += span;

        /* Clamp to TL_TS_MAX */
        if (total > (uint64_t)TL_TS_MAX) {
            return TL_TS_MAX;
        }
    }

    return (tl_ts_t)total;
}

/*===========================================================================
 * Cursor Operations
 *===========================================================================*/

bool tl_intervals_cursor_is_deleted(tl_intervals_cursor_t* cur, tl_ts_t ts) {
    /* Advance past intervals that end before ts */
    while (cur->pos < cur->len) {
        const tl_interval_t* iv = &cur->data[cur->pos];

        /* Unbounded interval never ends - stay here forever */
        if (iv->end_unbounded) {
            return ts >= iv->start;
        }

        /* If ts < end, this interval might cover ts */
        if (ts < iv->end) {
            break;
        }

        /* ts >= end, advance to next interval */
        cur->pos++;
    }

    /* Check if current interval covers ts */
    if (cur->pos >= cur->len) {
        return false;
    }

    const tl_interval_t* iv = &cur->data[cur->pos];
    return ts >= iv->start && (iv->end_unbounded || ts < iv->end);
}

tl_ts_t tl_intervals_cursor_skip_to(tl_intervals_cursor_t* cur, tl_ts_t ts) {
    /*
     * Advance past intervals that are exhausted (ts >= end).
     * This mirrors cursor_is_deleted's advancement logic.
     */
    while (cur->pos < cur->len) {
        const tl_interval_t* iv = &cur->data[cur->pos];

        /* Unbounded interval never ends */
        if (iv->end_unbounded) {
            if (ts >= iv->start) {
                return TL_TS_MAX; /* Covered by unbounded => skip to max */
            }
            return ts; /* ts < start => not covered yet */
        }

        /* If ts < end, this interval might still be relevant */
        if (ts < iv->end) {
            if (ts >= iv->start) {
                return iv->end; /* Covered => skip to end */
            }
            return ts; /* ts < start => not covered yet */
        }

        /* ts >= end: interval exhausted, advance */
        cur->pos++;
    }

    /* No more intervals */
    return ts;
}

/*===========================================================================
 * Debug Validation
 *===========================================================================*/

#ifdef TL_DEBUG
bool tl_intervals_validate(const tl_intervals_t* iv) {
    if (iv == NULL) {
        return false;
    }

    for (size_t i = 0; i < iv->len; i++) {
        const tl_interval_t* cur = &iv->data[i];

        /* Bounded intervals must have start < end */
        if (!cur->end_unbounded && cur->start >= cur->end) {
            return false;
        }

        /* Unbounded interval must be the last one (covers everything after) */
        if (cur->end_unbounded && i < iv->len - 1) {
            return false;
        }

        /* Check sorted order and no overlap */
        if (i > 0) {
            const tl_interval_t* prev = &iv->data[i - 1];

            /* Must be sorted by start */
            if (cur->start < prev->start) {
                return false;
            }

            /* No overlap allowed (prev can't be unbounded here due to check above) */
            if (!prev->end_unbounded && prev->end > cur->start) {
                return false;
            }

            /* Adjacent intervals should have been coalesced */
            if (!prev->end_unbounded && prev->end == cur->start) {
                return false;
            }
        }
    }

    return true;
}
#endif
