#include "tl_intervals.h"
#include <string.h>

/*===========================================================================*/
/* Internal Helpers */
/*===========================================================================*/

static const size_t INTERVALS_MIN_CAPACITY = 8;

static tl_status_t intervals_reserve(tl_intervals_t* iv, size_t min_cap) {
    if (min_cap <= iv->cap) {
        return TL_OK;
    }

    size_t new_cap = tl__grow_capacity(iv->cap, min_cap, INTERVALS_MIN_CAPACITY);
    if (new_cap == 0 || tl__alloc_would_overflow(new_cap, sizeof(tl_interval_t))) {
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

static tl_status_t intervals_insert_at(tl_intervals_t* iv, size_t pos,
                                       const tl_interval_t* interval) {
    if (iv->len == SIZE_MAX) {
        return TL_ENOMEM;
    }

    tl_status_t st = intervals_reserve(iv, iv->len + 1);
    if (st != TL_OK) {
        return st;
    }

    if (pos < iv->len) {
        memmove(&iv->data[pos + 1], &iv->data[pos],
                (iv->len - pos) * sizeof(tl_interval_t));
    }

    iv->data[pos] = *interval;
    iv->len++;
    return TL_OK;
}

static tl_status_t intervals_split_at(tl_intervals_t* iv, tl_ts_t ts) {
    if (iv->len == 0) {
        return TL_OK;
    }

    size_t idx = intervals_lower_bound(iv, ts);
    if (idx < iv->len && iv->data[idx].start == ts) {
        return TL_OK; /* Already a boundary */
    }
    if (idx == 0) {
        return TL_OK;
    }

    size_t i = idx - 1;
    tl_interval_t* cur = &iv->data[i];

    if (!cur->end_unbounded && ts >= cur->end) {
        return TL_OK;
    }

    tl_interval_t right = *cur;
    right.start = ts;

    if (cur->end_unbounded) {
        cur->end_unbounded = false;
        cur->end = ts;
    } else {
        cur->end = ts;
    }

    return intervals_insert_at(iv, i + 1, &right);
}

static void intervals_coalesce(tl_intervals_t* iv) {
    if (iv->len <= 1) {
        return;
    }

    size_t write = 0;
    for (size_t read = 0; read < iv->len; read++) {
        const tl_interval_t* cur = &iv->data[read];

        if (write == 0) {
            iv->data[write++] = *cur;
            continue;
        }

        tl_interval_t* prev = &iv->data[write - 1];
        if (prev->end_unbounded) {
            if (prev->max_seq == cur->max_seq) {
                continue;
            }
            if (cur->start <= prev->start) {
                iv->data[write - 1] = *cur;
                continue;
            }
            prev->end_unbounded = false;
            prev->end = cur->start;
        }

        if (!prev->end_unbounded &&
            prev->max_seq == cur->max_seq &&
            prev->end >= cur->start) {
            if (cur->end_unbounded) {
                prev->end_unbounded = true;
                prev->end = 0;
            } else if (cur->end > prev->end) {
                prev->end = cur->end;
            }
            continue;
        }

        iv->data[write++] = *cur;
    }

    iv->len = write;
}

/*===========================================================================*/
/* Lifecycle */
/*===========================================================================*/

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

/*===========================================================================*/
/* Insertion */
/*===========================================================================*/

tl_status_t tl_intervals_insert(tl_intervals_t* iv, tl_ts_t t1, tl_ts_t t2, tl_seq_t seq) {
    TL_ASSERT(iv != NULL);

    if (t1 == t2) {
        return TL_OK;
    }
    if (t1 > t2) {
        return TL_EINVAL;
    }
    if (seq == 0) {
        return TL_EINVAL;
    }

    TL_ASSERT(seq > 0);

    if (iv->len == 0) {
        tl_interval_t interval = {
            .start = t1,
            .end = t2,
            .end_unbounded = false,
            .max_seq = seq
        };
        return intervals_insert_at(iv, 0, &interval);
    }

    if (iv->len > SIZE_MAX - 2) {
        return TL_ENOMEM;
    }
    tl_status_t st = intervals_reserve(iv, iv->len + 2);
    if (st != TL_OK) {
        return st;
    }

    st = intervals_split_at(iv, t1);
    if (st != TL_OK) {
        return st;
    }
    st = intervals_split_at(iv, t2);
    if (st != TL_OK) {
        return st;
    }

    size_t i = intervals_lower_bound(iv, t1);
    tl_ts_t cur = t1;

    while (i < iv->len) {
        tl_interval_t* it = &iv->data[i];
        if (it->start >= t2) {
            break;
        }

        if (cur < it->start) {
            tl_interval_t gap = {
                .start = cur,
                .end = it->start,
                .end_unbounded = false,
                .max_seq = seq
            };
            st = intervals_insert_at(iv, i, &gap);
            if (st != TL_OK) {
                return st;
            }
            i++;
            cur = gap.end;
            continue;
        }

        it->max_seq = TL_MAX(it->max_seq, seq);
        TL_ASSERT(!it->end_unbounded);
        cur = it->end;
        i++;

        if (cur >= t2) {
            break;
        }
    }

    if (cur < t2) {
        tl_interval_t tail = {
            .start = cur,
            .end = t2,
            .end_unbounded = false,
            .max_seq = seq
        };
        st = intervals_insert_at(iv, i, &tail);
        if (st != TL_OK) {
            return st;
        }
    }

    intervals_coalesce(iv);
    return TL_OK;
}

tl_status_t tl_intervals_insert_unbounded(tl_intervals_t* iv, tl_ts_t t1, tl_seq_t seq) {
    TL_ASSERT(iv != NULL);
    if (seq == 0) {
        return TL_EINVAL;
    }

    TL_ASSERT(seq > 0);

    if (iv->len == 0) {
        tl_interval_t interval = {
            .start = t1,
            .end = 0,
            .end_unbounded = true,
            .max_seq = seq
        };
        return intervals_insert_at(iv, 0, &interval);
    }

    if (iv->len > SIZE_MAX - 2) {
        return TL_ENOMEM;
    }
    tl_status_t st = intervals_reserve(iv, iv->len + 2);
    if (st != TL_OK) {
        return st;
    }

    st = intervals_split_at(iv, t1);
    if (st != TL_OK) {
        return st;
    }

    size_t i = intervals_lower_bound(iv, t1);
    tl_ts_t cur = t1;

    while (i < iv->len) {
        tl_interval_t* it = &iv->data[i];

        if (cur < it->start) {
            tl_interval_t gap = {
                .start = cur,
                .end = it->start,
                .end_unbounded = false,
                .max_seq = seq
            };
            st = intervals_insert_at(iv, i, &gap);
            if (st != TL_OK) {
                return st;
            }
            i++;
            cur = gap.end;
            continue;
        }

        it->max_seq = TL_MAX(it->max_seq, seq);
        if (it->end_unbounded) {
            intervals_coalesce(iv);
            return TL_OK;
        }

        cur = it->end;
        i++;
    }

    tl_interval_t tail = {
        .start = cur,
        .end = 0,
        .end_unbounded = true,
        .max_seq = seq
    };
    st = intervals_insert_at(iv, iv->len, &tail);
    if (st != TL_OK) {
        return st;
    }

    intervals_coalesce(iv);
    return TL_OK;
}

/*===========================================================================*/
/* Point Containment */
/*===========================================================================*/

static tl_seq_t intervals_max_seq_internal(const tl_interval_t* data, size_t len, tl_ts_t ts) {
    if (len == 0) {
        return 0;
    }

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

    if (lo == 0) {
        return 0;
    }

    const tl_interval_t* cand = &data[lo - 1];
    if (cand->end_unbounded || ts < cand->end) {
        return cand->max_seq;
    }

    return 0;
}

bool tl_intervals_contains(const tl_intervals_t* iv, tl_ts_t ts) {
    TL_ASSERT(iv != NULL);
    return intervals_max_seq_internal(iv->data, iv->len, ts) != 0;
}

bool tl_intervals_imm_contains(tl_intervals_imm_t iv, tl_ts_t ts) {
    return intervals_max_seq_internal(iv.data, iv.len, ts) != 0;
}

tl_seq_t tl_intervals_max_seq(const tl_intervals_t* iv, tl_ts_t ts) {
    TL_ASSERT(iv != NULL);
    return intervals_max_seq_internal(iv->data, iv->len, ts);
}

tl_seq_t tl_intervals_imm_max_seq(tl_intervals_imm_t iv, tl_ts_t ts) {
    return intervals_max_seq_internal(iv.data, iv.len, ts);
}

/*===========================================================================*/
/* Set Operations */
/*===========================================================================*/

static tl_status_t intervals_append(tl_intervals_t* out,
                                    tl_ts_t start,
                                    tl_ts_t end,
                                    bool end_unbounded,
                                    tl_seq_t max_seq) {
    if (max_seq == 0) {
        return TL_OK;
    }
    if (!end_unbounded && start >= end) {
        return TL_OK;
    }

    if (out->len > 0) {
        tl_interval_t* prev = &out->data[out->len - 1];
        if (prev->end_unbounded) {
            return TL_OK;
        }
        if (prev->max_seq == max_seq && prev->end == start) {
            if (end_unbounded) {
                prev->end_unbounded = true;
                prev->end = 0;
            } else {
                prev->end = end;
            }
            return TL_OK;
        }
    }

    if (out->len >= out->cap) {
        tl_status_t st = intervals_reserve(out, out->len + 1);
        if (st != TL_OK) {
            return st;
        }
    }

    out->data[out->len].start = start;
    out->data[out->len].end = end;
    out->data[out->len].end_unbounded = end_unbounded;
    out->data[out->len].max_seq = max_seq;
    out->len++;
    return TL_OK;
}

static tl_status_t intervals_union_impl(tl_intervals_t* out,
                                        const tl_interval_t* a,
                                        size_t a_len,
                                        const tl_interval_t* b,
                                        size_t b_len) {
    tl_intervals_clear(out);

    if (a_len > SIZE_MAX - b_len) {
        return TL_ENOMEM;
    }
    size_t max_len = a_len + b_len;
    if (max_len > 0) {
        tl_status_t st = intervals_reserve(out, max_len);
        if (st != TL_OK) {
            return st;
        }
    }

    size_t ia = 0;
    size_t ib = 0;
    tl_seq_t val_a = 0;
    tl_seq_t val_b = 0;
    tl_ts_t end_a = TL_TS_MAX;
    tl_ts_t end_b = TL_TS_MAX;

    tl_ts_t next_start_a = (ia < a_len) ? a[ia].start : TL_TS_MAX;
    tl_ts_t next_start_b = (ib < b_len) ? b[ib].start : TL_TS_MAX;

    tl_ts_t pos = TL_MIN(next_start_a, next_start_b);
    if (pos == TL_TS_MAX) {
        return TL_OK;
    }

    for (;;) {
        if (ia < a_len && a[ia].start == pos) {
            val_a = a[ia].max_seq;
            end_a = a[ia].end_unbounded ? TL_TS_MAX : a[ia].end;
            ia++;
        }
        if (ib < b_len && b[ib].start == pos) {
            val_b = b[ib].max_seq;
            end_b = b[ib].end_unbounded ? TL_TS_MAX : b[ib].end;
            ib++;
        }

        next_start_a = (ia < a_len) ? a[ia].start : TL_TS_MAX;
        next_start_b = (ib < b_len) ? b[ib].start : TL_TS_MAX;
        tl_ts_t next_end_a = (val_a != 0) ? end_a : TL_TS_MAX;
        tl_ts_t next_end_b = (val_b != 0) ? end_b : TL_TS_MAX;

        tl_ts_t next = TL_MIN(TL_MIN(next_start_a, next_start_b),
                               TL_MIN(next_end_a, next_end_b));

        tl_seq_t max_seq = TL_MAX(val_a, val_b);

        if (next == TL_TS_MAX) {
            if (max_seq > 0) {
                tl_status_t st = intervals_append(out, pos, 0, true, max_seq);
                if (st != TL_OK) {
                    return st;
                }
            }
            break;
        }

        if (max_seq > 0 && pos < next) {
            tl_status_t st = intervals_append(out, pos, next, false, max_seq);
            if (st != TL_OK) {
                return st;
            }
        }

        pos = next;
        if (pos == next_end_a) {
            val_a = 0;
            end_a = TL_TS_MAX;
        }
        if (pos == next_end_b) {
            val_b = 0;
            end_b = TL_TS_MAX;
        }
    }

    return TL_OK;
}

tl_status_t tl_intervals_union(tl_intervals_t* out,
                               const tl_intervals_t* a,
                               const tl_intervals_t* b) {
    TL_ASSERT(out != NULL);
    TL_ASSERT(a != NULL);
    TL_ASSERT(b != NULL);

    if (out == a || out == b) {
        return TL_EINVAL;
    }

    return intervals_union_impl(out, a->data, a->len, b->data, b->len);
}

tl_status_t tl_intervals_union_imm(tl_intervals_t* out,
                                   tl_intervals_imm_t a,
                                   tl_intervals_imm_t b) {
    TL_ASSERT(out != NULL);

    return intervals_union_impl(out, a.data, a.len, b.data, b.len);
}

void tl_intervals_clip(tl_intervals_t* iv, tl_ts_t t1, tl_ts_t t2) {
    TL_ASSERT(iv != NULL);
    TL_ASSERT(t1 < t2);

    size_t write = 0;

    for (size_t read = 0; read < iv->len; read++) {
        tl_interval_t* cur = &iv->data[read];

        tl_ts_t start = TL_MAX(cur->start, t1);
        tl_ts_t end;

        if (cur->end_unbounded) {
            end = t2;
        } else {
            end = TL_MIN(cur->end, t2);
        }

        if (start >= end) {
            continue;
        }

        iv->data[write].start = start;
        iv->data[write].end = end;
        iv->data[write].end_unbounded = false;
        iv->data[write].max_seq = cur->max_seq;
        write++;
    }

    iv->len = write;
    intervals_coalesce(iv);
}

void tl_intervals_clip_lower(tl_intervals_t* iv, tl_ts_t t1) {
    TL_ASSERT(iv != NULL);

    size_t write = 0;

    for (size_t read = 0; read < iv->len; read++) {
        tl_interval_t* cur = &iv->data[read];

        if (cur->end_unbounded) {
            iv->data[write].start = TL_MAX(cur->start, t1);
            iv->data[write].end = 0;
            iv->data[write].end_unbounded = true;
            iv->data[write].max_seq = cur->max_seq;
            write++;
        } else {
            if (cur->end <= t1) {
                continue;
            }
            iv->data[write].start = TL_MAX(cur->start, t1);
            iv->data[write].end = cur->end;
            iv->data[write].end_unbounded = false;
            iv->data[write].max_seq = cur->max_seq;
            write++;
        }
    }

    iv->len = write;
    intervals_coalesce(iv);
}

/*===========================================================================*/
/* Ownership Transfer */
/*===========================================================================*/

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

    uint64_t total = 0;

    for (size_t i = 0; i < iv->len; i++) {
        const tl_interval_t* cur = &iv->data[i];

        if (cur->end_unbounded) {
            return TL_TS_MAX;
        }

        uint64_t span = (uint64_t)cur->end - (uint64_t)cur->start;
        if (span > UINT64_MAX - total) {
            return TL_TS_MAX;
        }
        total += span;
        if (total > (uint64_t)TL_TS_MAX) {
            return TL_TS_MAX;
        }
    }

    return (tl_ts_t)total;
}

/*===========================================================================*/
/* Cursor Operations */
/*===========================================================================*/

tl_seq_t tl_intervals_cursor_max_seq(tl_intervals_cursor_t* cur, tl_ts_t ts) {
    while (cur->pos < cur->len) {
        const tl_interval_t* iv = &cur->data[cur->pos];

        if (iv->end_unbounded) {
            return (ts >= iv->start) ? iv->max_seq : 0;
        }

        if (ts < iv->end) {
            break;
        }

        cur->pos++;
    }

    if (cur->pos >= cur->len) {
        return 0;
    }

    const tl_interval_t* iv = &cur->data[cur->pos];
    if (ts >= iv->start && (iv->end_unbounded || ts < iv->end)) {
        return iv->max_seq;
    }

    return 0;
}

bool tl_intervals_cursor_skip_to(tl_intervals_cursor_t* cur, tl_ts_t ts,
                                 tl_ts_t* out) {
    TL_ASSERT(out != NULL);

    while (cur->pos < cur->len) {
        const tl_interval_t* iv = &cur->data[cur->pos];

        if (iv->end_unbounded) {
            if (ts >= iv->start) {
                return false;
            }
            *out = ts;
            return true;
        }

        if (ts < iv->end) {
            if (ts >= iv->start) {
                *out = iv->end;
                return true;
            }
            *out = ts;
            return true;
        }

        cur->pos++;
    }

    *out = ts;
    return true;
}

/*===========================================================================*/
/* Debug Validation */
/*===========================================================================*/

#ifdef TL_DEBUG

bool tl_intervals_arr_validate(const tl_interval_t* data, size_t len) {
    if (len == 0) {
        return true;
    }

    if (data == NULL) {
        return false;
    }

    for (size_t i = 0; i < len; i++) {
        const tl_interval_t* cur = &data[i];

        if (!cur->end_unbounded && cur->start >= cur->end) {
            return false;
        }
        if (cur->max_seq == 0) {
            return false;
        }
        if (cur->end_unbounded && i < len - 1) {
            return false;
        }

        if (i > 0) {
            const tl_interval_t* prev = &data[i - 1];

            if (cur->start < prev->start) {
                return false;
            }

            if (!prev->end_unbounded && prev->end > cur->start) {
                return false;
            }

            if (!prev->end_unbounded &&
                prev->end == cur->start &&
                prev->max_seq == cur->max_seq) {
                return false;
            }
        }
    }

    return true;
}

bool tl_intervals_validate(const tl_intervals_t* iv) {
    if (iv == NULL) {
        return false;
    }

    return tl_intervals_arr_validate(iv->data, iv->len);
}

#endif /* TL_DEBUG */
