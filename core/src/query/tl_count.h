#ifndef TL_COUNT_H
#define TL_COUNT_H

#include "../internal/tl_defs.h"
#include "../internal/tl_search.h"
#include "../internal/tl_intervals.h"
#include "../storage/tl_segment.h"
#include "../delta/tl_memrun.h"
#include "../delta/tl_memview.h"
#include "../delta/tl_ooorun.h"
#include "tl_segment_range.h"

/*===========================================================================
 * Count Helpers (Shared between tl_snapshot.c and tl_timelog.c)
 *
 * These provide O(S * T * log P) record counting without row-level scanning.
 * Two flavors:
 *   - Full-extent: counts all visible records in a source (for tl_stats)
 *   - Range-intersected: counts visible records in query/source overlap
 *     (for count API)
 *
 * Tombstone deduction uses watermark-aware semantics:
 *   - tomb_seq > source_watermark    tombstone is newer, deduct records
 *   - tomb_seq <= source_watermark   already applied, skip tombstone
 *
 * Active buffers use per-record watermarks (seqs[]) since they lack a single
 * source-level watermark.
 *===========================================================================*/

/*---------------------------------------------------------------------------
 * Range Overlap
 *---------------------------------------------------------------------------*/

/**
 * Compute intersection of two half-open ranges.
 *
 * Returns true if the intersection is non-empty, storing the result in
 * out_lo / out_hi / out_hi_unbounded.
 *
 * Both ranges can be bounded [a1, a2) or unbounded [a1, +inf).
 */
TL_INLINE bool tl__range_overlap_half_open(tl_ts_t a1,
                                                   tl_ts_t a2,
                                                   bool a2_unbounded,
                                                   tl_ts_t b1,
                                                   tl_ts_t b2,
                                                   bool b2_unbounded,
                                                   tl_ts_t* out_lo,
                                                   tl_ts_t* out_hi,
                                                   bool* out_hi_unbounded) {
    tl_ts_t lo = (a1 > b1) ? a1 : b1;

    bool hi_unbounded = a2_unbounded && b2_unbounded;
    tl_ts_t hi = 0;
    if (!hi_unbounded) {
        hi = a2_unbounded ? b2 : (b2_unbounded ? a2 : TL_MIN(a2, b2));
        if (lo >= hi) {
            return false;
        }
    }

    if (out_lo != NULL) *out_lo = lo;
    if (out_hi != NULL) *out_hi = hi;
    if (out_hi_unbounded != NULL) *out_hi_unbounded = hi_unbounded;
    return true;
}

/*---------------------------------------------------------------------------
 * Sorted-Array Binary Search Count
 *---------------------------------------------------------------------------*/

/**
 * Count records in sorted array within [t1, t2) or [t1, +inf).
 */
TL_INLINE uint64_t tl__count_records_sorted_range(
        const tl_record_t* data,
        size_t len,
        tl_ts_t t1,
        tl_ts_t t2,
        bool t2_unbounded) {
    if (data == NULL || len == 0) {
        return 0;
    }

    size_t lo = tl_record_lower_bound(data, len, t1);
    size_t hi = t2_unbounded ? len : tl_record_lower_bound(data, len, t2);
    if (hi <= lo) {
        return 0;
    }
    return (uint64_t)(hi - lo);
}

/*---------------------------------------------------------------------------
 * Memrun Record Counting
 *---------------------------------------------------------------------------*/

/**
 * Count records in memrun within [t1, t2) or [t1, +inf).
 * Sums across in-order run + all OOO runs.
 */
TL_INLINE uint64_t tl__count_records_in_memrun_range(
        const tl_memrun_t* mr,
        tl_ts_t t1,
        tl_ts_t t2,
        bool t2_unbounded) {
    uint64_t total = 0;
    total += tl__count_records_sorted_range(tl_memrun_run_data(mr),
                                            tl_memrun_run_len(mr),
                                            t1, t2, t2_unbounded);

    size_t run_count = tl_memrun_ooo_run_count(mr);
    for (size_t i = 0; i < run_count; i++) {
        const tl_ooorun_t* run = tl_memrun_ooo_run_at(mr, i);
        total += tl__count_records_sorted_range(tl_ooorun_records(run),
                                                tl_ooorun_len(run),
                                                t1, t2, t2_unbounded);
    }

    return total;
}

/**
 * Compute record bounds (min_ts, max_ts) for a memrun.
 * Returns false if the memrun has no records.
 */
TL_INLINE bool tl__memrun_record_bounds(const tl_memrun_t* mr,
                                                tl_ts_t* out_min,
                                                tl_ts_t* out_max) {
    bool has = false;
    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;

    if (tl_memrun_run_len(mr) > 0) {
        const tl_record_t* run = tl_memrun_run_data(mr);
        min_ts = TL_MIN(min_ts, run[0].ts);
        max_ts = TL_MAX(max_ts, run[tl_memrun_run_len(mr) - 1].ts);
        has = true;
    }

    for (size_t i = 0; i < tl_memrun_ooo_run_count(mr); i++) {
        const tl_ooorun_t* run = tl_memrun_ooo_run_at(mr, i);
        if (tl_ooorun_len(run) == 0) {
            continue;
        }
        min_ts = TL_MIN(min_ts, tl_ooorun_min_ts(run));
        max_ts = TL_MAX(max_ts, tl_ooorun_max_ts(run));
        has = true;
    }

    if (!has) {
        return false;
    }

    *out_min = min_ts;
    *out_max = max_ts;
    return true;
}

/*---------------------------------------------------------------------------
 * Full-Extent Visible Counting (for tl_stats)
 *---------------------------------------------------------------------------*/

/**
 * Count visible records in a segment (full extent).
 *
 * Gross = total records in segment.
 * Deduction = records in overlap of segment and tombstone where
 * tomb_seq > watermark.
 */
TL_INLINE uint64_t tl__visible_records_in_segment(
        const tl_segment_t* seg,
        const tl_interval_t* tombs,
        size_t tomb_count) {
    if (!tl_segment_has_records(seg)) {
        return 0;
    }

    tl_ts_t src_start = tl_segment_record_min_ts(seg);
    tl_ts_t src_end = tl_segment_record_max_ts(seg);
    bool src_end_unbounded = (src_end == TL_TS_MAX);
    tl_ts_t src_end_exclusive = src_end_unbounded ? 0 : (src_end + 1);

    uint64_t gross = src_end_unbounded
        ? tl_count_records_in_segment_since(seg, src_start)
        : tl_count_records_in_segment_range(seg, src_start, src_end_exclusive);

    tl_seq_t watermark = tl_segment_applied_seq(seg);
    for (size_t i = 0; i < tomb_count; i++) {
        const tl_interval_t* f = &tombs[i];
        if (f->max_seq <= watermark) {
            continue;
        }

        tl_ts_t ov_lo = 0, ov_hi = 0;
        bool ov_hi_unbounded = false;
        if (!tl__range_overlap_half_open(src_start, src_end_exclusive, src_end_unbounded,
                                         f->start, f->end, f->end_unbounded,
                                         &ov_lo, &ov_hi, &ov_hi_unbounded)) {
            continue;
        }

        uint64_t dec = ov_hi_unbounded
            ? tl_count_records_in_segment_since(seg, ov_lo)
            : tl_count_records_in_segment_range(seg, ov_lo, ov_hi);
        TL_ASSERT(dec <= gross);
        gross = (dec <= gross) ? (gross - dec) : 0;
    }

    return gross;
}

/**
 * Count visible records in a memrun (full extent).
 */
TL_INLINE uint64_t tl__visible_records_in_memrun(
        const tl_memrun_t* mr,
        const tl_interval_t* tombs,
        size_t tomb_count) {
    tl_ts_t src_min = 0, src_max = 0;
    if (!tl__memrun_record_bounds(mr, &src_min, &src_max)) {
        return 0;
    }

    bool src_end_unbounded = (src_max == TL_TS_MAX);
    tl_ts_t src_end_exclusive = src_end_unbounded ? 0 : (src_max + 1);

    uint64_t gross = tl__count_records_in_memrun_range(mr,
                                                        src_min,
                                                        src_end_exclusive,
                                                        src_end_unbounded);

    tl_seq_t watermark = tl_memrun_applied_seq(mr);
    for (size_t i = 0; i < tomb_count; i++) {
        const tl_interval_t* f = &tombs[i];
        if (f->max_seq <= watermark) {
            continue;
        }

        tl_ts_t ov_lo = 0, ov_hi = 0;
        bool ov_hi_unbounded = false;
        if (!tl__range_overlap_half_open(src_min, src_end_exclusive, src_end_unbounded,
                                         f->start, f->end, f->end_unbounded,
                                         &ov_lo, &ov_hi, &ov_hi_unbounded)) {
            continue;
        }

        uint64_t dec = tl__count_records_in_memrun_range(mr,
                                                         ov_lo,
                                                         ov_hi,
                                                         ov_hi_unbounded);
        TL_ASSERT(dec <= gross);
        gross = (dec <= gross) ? (gross - dec) : 0;
    }

    return gross;
}

/*---------------------------------------------------------------------------
 * Range-Intersected Visible Counting (for count API)
 *---------------------------------------------------------------------------*/

/**
 * Count visible records in segment in [t1, t2) or [t1, +inf).
 *
 * Algorithm:
 * 1. Compute effective range = intersection of query [t1,t2) and source extent
 * 2. Gross = records in effective range (O(log P) via page fences)
 * 3. For each tombstone fragment: deduct records in triple-intersect
 *    (query intersect source intersect tombstone) where tomb_seq > watermark
 */
TL_INLINE uint64_t tl__visible_records_in_segment_range(
        const tl_segment_t* seg,
        const tl_interval_t* tombs,
        size_t tomb_count,
        tl_ts_t t1,
        tl_ts_t t2,
        bool t2_unbounded) {
    if (!tl_segment_has_records(seg)) {
        return 0;
    }

    tl_ts_t src_start = tl_segment_record_min_ts(seg);
    tl_ts_t src_end = tl_segment_record_max_ts(seg);
    bool src_end_unbounded = (src_end == TL_TS_MAX);
    tl_ts_t src_end_exclusive = src_end_unbounded ? 0 : (src_end + 1);

    /* Intersect query range with source extent */
    tl_ts_t eff_lo = 0, eff_hi = 0;
    bool eff_hi_unbounded = false;
    if (!tl__range_overlap_half_open(t1, t2, t2_unbounded,
                                     src_start, src_end_exclusive, src_end_unbounded,
                                     &eff_lo, &eff_hi, &eff_hi_unbounded)) {
        return 0;
    }

    uint64_t gross = eff_hi_unbounded
        ? tl_count_records_in_segment_since(seg, eff_lo)
        : tl_count_records_in_segment_range(seg, eff_lo, eff_hi);

    tl_seq_t watermark = tl_segment_applied_seq(seg);
    for (size_t i = 0; i < tomb_count; i++) {
        const tl_interval_t* f = &tombs[i];
        if (f->max_seq <= watermark) {
            continue;
        }

        /* Triple-intersect: effective range and tombstone */
        tl_ts_t ov_lo = 0, ov_hi = 0;
        bool ov_hi_unbounded = false;
        if (!tl__range_overlap_half_open(eff_lo, eff_hi, eff_hi_unbounded,
                                         f->start, f->end, f->end_unbounded,
                                         &ov_lo, &ov_hi, &ov_hi_unbounded)) {
            continue;
        }

        uint64_t dec = ov_hi_unbounded
            ? tl_count_records_in_segment_since(seg, ov_lo)
            : tl_count_records_in_segment_range(seg, ov_lo, ov_hi);
        TL_ASSERT(dec <= gross);
        gross = (dec <= gross) ? (gross - dec) : 0;
    }

    return gross;
}

/**
 * Count visible records in memrun in [t1, t2) or [t1, +inf).
 *
 * Same triple-intersect algorithm as segments but uses binary-search
 * on sorted record arrays instead of page fences.
 */
TL_INLINE uint64_t tl__visible_records_in_memrun_range(
        const tl_memrun_t* mr,
        const tl_interval_t* tombs,
        size_t tomb_count,
        tl_ts_t t1,
        tl_ts_t t2,
        bool t2_unbounded) {
    tl_ts_t src_min = 0, src_max = 0;
    if (!tl__memrun_record_bounds(mr, &src_min, &src_max)) {
        return 0;
    }

    bool src_end_unbounded = (src_max == TL_TS_MAX);
    tl_ts_t src_end_exclusive = src_end_unbounded ? 0 : (src_max + 1);

    /* Intersect query range with source extent */
    tl_ts_t eff_lo = 0, eff_hi = 0;
    bool eff_hi_unbounded = false;
    if (!tl__range_overlap_half_open(t1, t2, t2_unbounded,
                                     src_min, src_end_exclusive, src_end_unbounded,
                                     &eff_lo, &eff_hi, &eff_hi_unbounded)) {
        return 0;
    }

    uint64_t gross = tl__count_records_in_memrun_range(mr, eff_lo, eff_hi,
                                                        eff_hi_unbounded);

    tl_seq_t watermark = tl_memrun_applied_seq(mr);
    for (size_t i = 0; i < tomb_count; i++) {
        const tl_interval_t* f = &tombs[i];
        if (f->max_seq <= watermark) {
            continue;
        }

        /* Triple-intersect: effective range and tombstone */
        tl_ts_t ov_lo = 0, ov_hi = 0;
        bool ov_hi_unbounded = false;
        if (!tl__range_overlap_half_open(eff_lo, eff_hi, eff_hi_unbounded,
                                         f->start, f->end, f->end_unbounded,
                                         &ov_lo, &ov_hi, &ov_hi_unbounded)) {
            continue;
        }

        uint64_t dec = tl__count_records_in_memrun_range(mr, ov_lo, ov_hi,
                                                          ov_hi_unbounded);
        TL_ASSERT(dec <= gross);
        gross = (dec <= gross) ? (gross - dec) : 0;
    }

    return gross;
}

/*---------------------------------------------------------------------------
 * Active Buffer Visible Counting (per-record watermarks)
 *
 * Active buffers (run, OOO head, OOO runs) have per-record watermarks
 * stored in seqs[]. Each record is individually checked against the
 * tombstone skyline.
 *
 * This is O(R_active * 1) amortized per sorted source since both records
 * and the tombstone cursor advance forward together.
 *---------------------------------------------------------------------------*/

/**
 * Count visible records in a sorted (records, seqs) array within [t1, t2).
 *
 * Uses a locally-initialized tombstone cursor for amortized O(1)
 * per-record checking.
 *
 * @param data      Sorted record array
 * @param seqs      Per-record watermark array (parallel to data)
 * @param len       Array length
 * @param t1        Range start (inclusive)
 * @param t2        Range end (exclusive); ignored if t2_unbounded
 * @param t2_unbounded True => [t1, +inf)
 * @param skyline   Tombstone skyline (immutable)
 * @return Count of visible records in range
 */
TL_INLINE uint64_t tl__count_visible_sorted_range(
        const tl_record_t* data,
        const tl_seq_t* seqs,
        size_t len,
        tl_ts_t t1,
        tl_ts_t t2,
        bool t2_unbounded,
        tl_intervals_imm_t skyline) {
    if (data == NULL || len == 0) {
        return 0;
    }

    size_t lo = tl_record_lower_bound(data, len, t1);
    size_t hi = t2_unbounded ? len : tl_record_lower_bound(data, len, t2);
    if (hi <= lo) {
        return 0;
    }

    /* No tombstones: all records visible */
    if (skyline.len == 0) {
        return (uint64_t)(hi - lo);
    }

    /* Cursor-based tombstone check; records are in sorted order */
    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, skyline);

    uint64_t visible = 0;
    for (size_t i = lo; i < hi; i++) {
        tl_seq_t tomb_seq = tl_intervals_cursor_max_seq(&cur, data[i].ts);
        if (tomb_seq == 0 || tomb_seq <= seqs[i]) {
            visible++;
        }
    }

    return visible;
}

/**
 * Count visible records in active buffers (memview) within [t1, t2).
 *
 * Iterates active_run, active_ooo_head, and active_ooo_runs, checking each
 * record's individual watermark (seqs[i]) against the tombstone skyline.
 *
 * Precondition: active_ooo_head must be sorted (asserted).
 *
 * @param mv          Memview (immutable snapshot of memtable)
 * @param skyline     Tombstone skyline covering the query range
 * @param t1          Range start (inclusive)
 * @param t2          Range end (exclusive); ignored if t2_unbounded
 * @param t2_unbounded True => [t1, +inf)
 * @return Count of visible active records in range
 */
TL_INLINE uint64_t tl__count_active_visible_range(
        const tl_memview_t* mv,
        tl_intervals_imm_t skyline,
        tl_ts_t t1,
        tl_ts_t t2,
        bool t2_unbounded) {
    uint64_t total = 0;

    /* Active run */
    total += tl__count_visible_sorted_range(
        tl_memview_run_data(mv),
        tl_memview_run_seqs(mv),
        tl_memview_run_len(mv),
        t1, t2, t2_unbounded,
        skyline);

    /* Active OOO head (must be sorted for cursor correctness) */
    TL_ASSERT(mv->active_ooo_head_sorted ||
              tl_memview_ooo_head_len(mv) == 0);
    total += tl__count_visible_sorted_range(
        tl_memview_ooo_head_data(mv),
        tl_memview_ooo_head_seqs(mv),
        tl_memview_ooo_head_len(mv),
        t1, t2, t2_unbounded,
        skyline);

    /* Active OOO runs (each run is individually sorted) */
    const tl_ooorunset_t* runset = tl_memview_ooo_runs(mv);
    if (runset != NULL) {
        for (size_t i = 0; i < tl_ooorunset_count(runset); i++) {
            const tl_ooorun_t* run = tl_ooorunset_run_at(runset, i);
            if (tl_ooorun_len(run) == 0) {
                continue;
            }

            /*
             * OOO runs have a source-level watermark, not per-record seqs.
             * For counting, treat each record as having the run's applied_seq.
             * But we do not have a seqs array; use the same watermark-based
             * approach as immutable sources: if all tombstones have
             * tomb_seq <= run.applied_seq, the run is fully visible in range.
             * Otherwise we must scan record-by-record.
             *
             * Potential future optimization: could skip the per-record
             * scan when all tombstones have max_seq <= run_watermark.
             */
            tl_seq_t run_watermark = tl_ooorun_applied_seq(run);
            const tl_record_t* rdata = tl_ooorun_records(run);
            size_t rlen = tl_ooorun_len(run);

            size_t lo = tl_record_lower_bound(rdata, rlen, t1);
            size_t hi = t2_unbounded ? rlen
                                     : tl_record_lower_bound(rdata, rlen, t2);
            if (hi <= lo) {
                continue;
            }

            if (skyline.len == 0) {
                total += (uint64_t)(hi - lo);
                continue;
            }

            /* Cursor-based per-record check using run-level watermark */
            tl_intervals_cursor_t cur;
            tl_intervals_cursor_init(&cur, skyline);

            for (size_t j = lo; j < hi; j++) {
                tl_seq_t tomb_seq = tl_intervals_cursor_max_seq(&cur, rdata[j].ts);
                if (tomb_seq == 0 || tomb_seq <= run_watermark) {
                    total++;
                }
            }
        }
    }

    return total;
}

#endif /* TL_COUNT_H */
