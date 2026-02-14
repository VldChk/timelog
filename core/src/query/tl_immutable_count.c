#include "tl_immutable_count.h"
#include "tl_segment_range.h"
#include "../internal/tl_range.h"
#include "../internal/tl_search.h"

static uint64_t count_sorted_records_in_range(const tl_record_t* data,
                                              size_t len,
                                              tl_ts_t a,
                                              tl_ts_t b,
                                              bool b_unbounded) {
    if (data == NULL || len == 0) {
        return 0;
    }
    size_t lo = tl_record_lower_bound(data, len, a);
    size_t hi = b_unbounded ? len : tl_record_lower_bound(data, len, b);
    if (hi <= lo) {
        return 0;
    }
    return (uint64_t)(hi - lo);
}

static bool overlap_range(tl_ts_t a, tl_ts_t b, bool b_unbounded,
                          tl_ts_t c, tl_ts_t d, bool d_unbounded,
                          tl_ts_t* out_start, tl_ts_t* out_end,
                          bool* out_end_unbounded) {
    if (!b_unbounded && a >= b) {
        return false;
    }
    if (!d_unbounded && c >= d) {
        return false;
    }

    tl_ts_t start = (a > c) ? a : c;
    bool end_unbounded = b_unbounded && d_unbounded;
    tl_ts_t end = 0;

    if (!end_unbounded) {
        if (b_unbounded) {
            end = d;
        } else if (d_unbounded) {
            end = b;
        } else {
            end = (b < d) ? b : d;
        }
        if (start >= end) {
            return false;
        }
    }

    *out_start = start;
    *out_end = end;
    *out_end_unbounded = end_unbounded;
    return true;
}

uint64_t tl_count_records_in_memrun_range(const tl_memrun_t* mr,
                                          tl_ts_t a,
                                          tl_ts_t b,
                                          bool b_unbounded) {
    if (mr == NULL) {
        return 0;
    }
    if (!b_unbounded && a >= b) {
        return 0;
    }
    if (!tl_memrun_has_records(mr)) {
        return 0;
    }
    if (!tl_range_overlaps(tl_memrun_min_ts(mr), tl_memrun_max_ts(mr), a, b, b_unbounded)) {
        return 0;
    }

    uint64_t total = 0;
    total += count_sorted_records_in_range(mr->run, mr->run_len, a, b, b_unbounded);

    const tl_ooorunset_t* runs = tl_memrun_ooo_runs(mr);
    if (runs != NULL) {
        for (size_t i = 0; i < runs->count; i++) {
            const tl_ooorun_t* run = runs->runs[i];
            if (run == NULL || run->len == 0) {
                continue;
            }
            if (!tl_range_overlaps(run->min_ts, run->max_ts, a, b, b_unbounded)) {
                continue;
            }
            total += count_sorted_records_in_range(run->records, run->len, a, b, b_unbounded);
        }
    }

    return total;
}

uint64_t tl_count_visible_records_in_segment_range(const tl_segment_t* seg,
                                                   tl_ts_t a,
                                                   tl_ts_t b,
                                                   bool b_unbounded,
                                                   const tl_interval_t* tombs,
                                                   size_t tomb_count) {
    uint64_t visible = tl_count_records_in_segment_range(seg, a, b, b_unbounded);
    if (visible == 0 || tombs == NULL || tomb_count == 0) {
        return visible;
    }

    tl_seq_t watermark = tl_segment_applied_seq(seg);
    for (size_t i = 0; i < tomb_count; i++) {
        const tl_interval_t* f = &tombs[i];
        if (f->max_seq <= watermark) {
            continue;
        }

        tl_ts_t ov_start, ov_end;
        bool ov_end_unbounded;
        if (!overlap_range(a, b, b_unbounded,
                           f->start, f->end, f->end_unbounded,
                           &ov_start, &ov_end, &ov_end_unbounded)) {
            continue;
        }

        uint64_t sub = tl_count_records_in_segment_range(seg, ov_start, ov_end, ov_end_unbounded);
        visible = (sub > visible) ? 0 : (visible - sub);
    }

    return visible;
}

uint64_t tl_count_visible_records_in_memrun_range(const tl_memrun_t* mr,
                                                  tl_ts_t a,
                                                  tl_ts_t b,
                                                  bool b_unbounded,
                                                  const tl_interval_t* tombs,
                                                  size_t tomb_count) {
    uint64_t visible = tl_count_records_in_memrun_range(mr, a, b, b_unbounded);
    if (visible == 0 || tombs == NULL || tomb_count == 0) {
        return visible;
    }

    tl_seq_t watermark = tl_memrun_applied_seq(mr);
    for (size_t i = 0; i < tomb_count; i++) {
        const tl_interval_t* f = &tombs[i];
        if (f->max_seq <= watermark) {
            continue;
        }

        tl_ts_t ov_start, ov_end;
        bool ov_end_unbounded;
        if (!overlap_range(a, b, b_unbounded,
                           f->start, f->end, f->end_unbounded,
                           &ov_start, &ov_end, &ov_end_unbounded)) {
            continue;
        }

        uint64_t sub = tl_count_records_in_memrun_range(mr, ov_start, ov_end, ov_end_unbounded);
        visible = (sub > visible) ? 0 : (visible - sub);
    }

    return visible;
}
