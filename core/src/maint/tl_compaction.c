#include "tl_compaction.h"
#include "tl_adaptive.h"
#include "../internal/tl_timelog_internal.h"
#include "../internal/tl_locks.h"
#include "../internal/tl_seqlock.h"
#include "../internal/tl_heap.h"
#include "../internal/tl_recvec.h"
#include "../internal/tl_tombstone_utils.h"
#include "../query/tl_segment_iter.h"
#include "../query/tl_snapshot.h"
#include "../storage/tl_window.h"
#include <string.h>

/*===========================================================================
 * Test Hooks (Debug/Test Builds Only)
 *
 * TL_TEST_HOOKS enables deterministic failpoints for testing error paths.
 * Defined only for test builds via CMake compile definitions.
 *===========================================================================*/

#ifdef TL_TEST_HOOKS
/* When > 0, tl_compact_publish() decrements this counter and returns
 * TL_EBUSY instead of publishing, simulating manifest races for retry
 * exhaustion tests.
 *
 * volatile: keeps the compiler from caching the value across publish
 * call boundaries even though tests are single-threaded. Modify only
 * from single-threaded test code. */
volatile int tl_test_force_ebusy_count = 0;
#endif

/*===========================================================================
 * Context Lifecycle
 *===========================================================================*/

void tl_compact_ctx_init(tl_compact_ctx_t* ctx,
                          tl_timelog_t* tl,
                          tl_alloc_ctx_t* alloc,
                          tl_ts_t window_size) {
    TL_ASSERT(ctx != NULL);
    TL_ASSERT(tl != NULL);
    TL_ASSERT(alloc != NULL);

    memset(ctx, 0, sizeof(*ctx));
    ctx->tl = tl;
    ctx->alloc = alloc;

    /* Copy config values */
    ctx->window_size = window_size;
    ctx->window_origin = tl->config.window_origin;
    ctx->target_page_bytes = tl->config.target_page_bytes;

    /* Copy callback if configured (matches tl_config_t field names) */
    ctx->on_drop_handle = tl->config.on_drop_handle;
    ctx->on_drop_ctx = tl->config.on_drop_ctx;

    tl_intervals_init(&ctx->tombs, alloc);
    tl_intervals_init(&ctx->tombs_clipped, alloc);
}

void tl_compact_ctx_destroy(tl_compact_ctx_t* ctx) {
    if (ctx == NULL) return;

    /* Release pinned input segments */
    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        if (ctx->input_l0[i] != NULL) {
            tl_segment_release(ctx->input_l0[i]);
        }
    }
    tl__free(ctx->alloc, (void*)ctx->input_l0);
    ctx->input_l0 = NULL;
    ctx->input_l0_len = 0;

    for (size_t i = 0; i < ctx->input_l1_len; i++) {
        if (ctx->input_l1[i] != NULL) {
            tl_segment_release(ctx->input_l1[i]);
        }
    }
    tl__free(ctx->alloc, (void*)ctx->input_l1);
    ctx->input_l1 = NULL;
    ctx->input_l1_len = 0;

    /* Release pinned base manifest */
    if (ctx->base_manifest != NULL) {
        tl_manifest_release(ctx->base_manifest);
        ctx->base_manifest = NULL;
    }

    /* Release pinned snapshot */
    if (ctx->snapshot != NULL) {
        tl_snapshot_release_internal(ctx->snapshot);
        ctx->snapshot = NULL;
    }

    /* Destroy tombstone sets */
    tl_intervals_destroy(&ctx->tombs);
    tl_intervals_destroy(&ctx->tombs_clipped);

    /* Release unpublished output L1 segments */
    for (size_t i = 0; i < ctx->output_l1_len; i++) {
        if (ctx->output_l1[i] != NULL) {
            tl_segment_release(ctx->output_l1[i]);
        }
    }
    tl__free(ctx->alloc, (void*)ctx->output_l1);
    ctx->output_l1 = NULL;
    ctx->output_l1_len = 0;
    ctx->output_l1_cap = 0;

    /* Release residual tombstone segment if not published */
    if (ctx->residual_tomb != NULL) {
        tl_segment_release(ctx->residual_tomb);
        ctx->residual_tomb = NULL;
    }

    /* Free deferred drop records (not fired - compaction failed/retrying) */
    if (ctx->dropped_records != NULL) {
        tl__free(ctx->alloc, ctx->dropped_records);
        ctx->dropped_records = NULL;
    }
    ctx->dropped_len = 0;
    ctx->dropped_cap = 0;
}

/*===========================================================================
 * Debug Validation (Debug/Test Builds Only)
 *===========================================================================*/

#ifndef NDEBUG
/**
 * Assert that L0 segments are ordered by ascending generation.
 *
 * L0 segments are appended in flush order, and merge tie-breaking relies
 * on this ordering to choose the newer record on timestamp ties.
 */
static void tl__validate_l0_generation_order(const tl_manifest_t* m) {
    uint32_t n = tl_manifest_l0_count(m);
    if (n <= 1) {
        return;
    }

    uint32_t prev_gen = tl_manifest_l0_get(m, 0)->generation;
    for (uint32_t i = 1; i < n; i++) {
        uint32_t gen = tl_manifest_l0_get(m, i)->generation;
        TL_ASSERT(gen > prev_gen && "L0 must be ordered by generation");
        prev_gen = gen;
    }
}

/**
 * Assert the L1 non-overlap invariant: L1 segments partition the time
 * domain by window and no two L1 windows intersect.
 *
 * The manifest builder keeps L1 sorted by window_start, so an O(n)
 * adjacent-pair scan is sufficient: an overlap exists iff
 * prev.window_end > curr.window_start.
 */
static void tl__validate_l1_non_overlap(const tl_manifest_t* m) {
    uint32_t n = tl_manifest_l1_count(m);
    if (n <= 1) {
        return;
    }

    for (uint32_t i = 1; i < n; i++) {
        const tl_segment_t* prev = tl_manifest_l1_get(m, i - 1);
        const tl_segment_t* curr = tl_manifest_l1_get(m, i);

        /* An unbounded window can only ever be the last L1 segment. */
        TL_ASSERT(!prev->window_end_unbounded && "Unbounded L1 window must be last");

        TL_ASSERT(prev->window_end <= curr->window_start && "L1 overlap detected");
    }
}
#endif /* NDEBUG */

/*===========================================================================
 * Delete Debt Computation (Internal)
 *===========================================================================*/

/** Compute max delete debt ratio across all windows. */
static double tl__compute_delete_debt(const tl_timelog_t* tl,
                                       const tl_manifest_t* m,
                                       tl_ts_t window_size) {
    tl_intervals_t tombs;
    tl_intervals_init(&tombs, (tl_alloc_ctx_t*)&tl->alloc);

    for (uint32_t i = 0; i < tl_manifest_l0_count(m); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(m, i);
        if (tl_segment_has_tombstones(seg)) {
            tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
            tl_status_t union_st = tl_tombstones_add_intervals(&tombs, seg_tombs,
                                                               TL_TS_MIN, 0, true);
            if (union_st != TL_OK) {
                tl_intervals_destroy(&tombs);
                return 1.0;
            }
        }
    }

    if (tl_intervals_is_empty(&tombs)) {
        tl_intervals_destroy(&tombs);
        return 0.0;
    }

    double max_ratio = 0.0;

    /* Short-circuit on an unbounded tombstone [t, +inf): it implicates
     * every future window, and an honest scan would walk to TL_TS_MAX.
     * Returning maximum debt forces compaction immediately. */
    const tl_interval_t* last_tomb = tl_intervals_get(&tombs, tl_intervals_len(&tombs) - 1);
    if (last_tomb->end_unbounded) {
        tl_intervals_destroy(&tombs);
        return 1.0;
    }

    /* tomb_max = end - 1: half-open [start, end) covers up to end-1 */
    tl_ts_t tomb_min = tl_intervals_get(&tombs, 0)->start;
    tl_ts_t tomb_max = (last_tomb->end > TL_TS_MIN) ? (last_tomb->end - 1) : TL_TS_MIN;

    int64_t min_wid, max_wid;
    tl_status_t st;

    st = tl_window_id_for_ts(tomb_min, window_size, tl->config.window_origin, &min_wid);
    if (st != TL_OK) {
        /* On overflow, conservatively return max debt to trigger compaction */
        tl_intervals_destroy(&tombs);
        return 1.0;
    }

    st = tl_window_id_for_ts(tomb_max, window_size, tl->config.window_origin, &max_wid);
    if (st != TL_OK) {
        tl_intervals_destroy(&tombs);
        return 1.0;
    }

    /* Cap iteration to TL_MAX_DEBT_WINDOWS with overflow-safe subtraction. */
    int64_t debt_span;
    if (tl_sub_overflow_i64(max_wid, min_wid, &debt_span)) {
        /* Overflow - conservatively assume high debt */
        tl_intervals_destroy(&tombs);
        return 1.0;
    }
    if (debt_span < 0 || debt_span > TL_MAX_DEBT_WINDOWS) {
        tl_intervals_destroy(&tombs);
        return 1.0;  /* Assume high debt for large or invalid spans */
    }

    size_t tomb_len = tl_intervals_len(&tombs);
    size_t idx = 0;

    for (int64_t wid = min_wid; wid <= max_wid; wid++) {
        tl_ts_t w_start, w_end;
        bool w_unbounded;
        tl_window_bounds(wid, window_size, tl->config.window_origin,
                          &w_start, &w_end, &w_unbounded);

        /* Skip unbounded windows for delete debt (infinite debt is meaningless) */
        if (w_unbounded) {
            continue;
        }

        uint64_t covered = 0;
        size_t i = idx;

        while (i < tomb_len) {
            const tl_interval_t* t = tl_intervals_get(&tombs, i);

            /* Skip intervals that end before the window */
            if (!t->end_unbounded && t->end <= w_start) {
                i++;
                continue;
            }

            /* If interval starts after window end, we're done for this window */
            if (t->start >= w_end) {
                break;
            }

            tl_ts_t overlap_start = (t->start > w_start) ? t->start : w_start;
            tl_ts_t overlap_end = t->end_unbounded ? w_end :
                                  ((t->end < w_end) ? t->end : w_end);

            if (overlap_end > overlap_start) {
                int64_t diff;
                if (tl_sub_overflow_i64(overlap_end, overlap_start, &diff)) {
                    tl_intervals_destroy(&tombs);
                    return 1.0;
                }
                covered += (uint64_t)diff;
            }

            if (!t->end_unbounded && t->end > w_end) {
                break; /* Interval continues into next window */
            }

            i++;
        }

        idx = i;

        double ratio = (double)covered / (double)window_size;
        if (ratio > max_ratio) {
            max_ratio = ratio;
        }
    }

    tl_intervals_destroy(&tombs);
    return max_ratio;
}

#ifdef TL_TEST_HOOKS
double tl_test_compute_delete_debt(const tl_timelog_t* tl,
                                   const tl_manifest_t* m) {
    tl_timelog_t* tl_mut = (tl_timelog_t*)tl;
    TL_LOCK_MAINT(tl_mut);
    tl_ts_t window_size = tl_mut->effective_window_size;
    TL_UNLOCK_MAINT(tl_mut);
    return tl__compute_delete_debt(tl, m, window_size);
}
#endif

/*===========================================================================
 * Trigger Logic
 *===========================================================================*/

bool tl_compact_needed(const tl_timelog_t* tl) {
    /*
     * Pin the manifest under writer_mu before reading: a concurrent
     * publish could otherwise free the manifest between our load and
     * use. This is an advisory check; the selection phase re-pins for
     * the authoritative decision.
     */
    tl_timelog_t* tl_mut = (tl_timelog_t*)tl;
    TL_LOCK_WRITER(tl_mut);

    /* Pin manifest to prevent UAF */
    tl_manifest_t* m = tl_manifest_acquire(tl_mut->manifest);

    TL_UNLOCK_WRITER(tl_mut);

    /* Now we can safely read from the pinned manifest */
    bool needed = false;
    tl_ts_t window_size;

    TL_LOCK_MAINT(tl_mut);
    window_size = tl_mut->effective_window_size;
    TL_UNLOCK_MAINT(tl_mut);

    if (tl_manifest_l0_count(m) >= tl->config.max_delta_segments) {
        needed = true;
        goto done;
    }

    if (tl->config.delete_debt_threshold > 0.0) {
        if (tl__compute_delete_debt(tl, m, window_size) >=
                tl->config.delete_debt_threshold) {
            needed = true;
            goto done;
        }
    }

done:
    tl_manifest_release(m);
    return needed;
}

/*===========================================================================
 * Selection
 *===========================================================================*/

/**
 * Does an L1 segment's WINDOW intersect the compaction output range?
 *
 * Overlap MUST use window bounds (window_start, window_end), not record
 * bounds (min_ts, max_ts). L1 segments partition the time domain by
 * window, and records within a window may be sparse:
 *
 *   L1 segment for window [0, 3600) holds a single record at ts=0
 *   -> seg->min_ts = seg->max_ts = 0, but seg->window_end = 3600
 *   Incoming L0 data at ts=1000 lives in the same window. A record-bound
 *   test (max_ts(0) >= 1000) would reject the L1 from selection; the
 *   merge would then emit a NEW L1 for [0, 3600), violating L1
 *   non-overlap.
 *
 * @param seg                  L1 segment to test
 * @param output_first_wstart  First output window start
 * @param output_last_wend     Last output window end (TL_TS_MAX if unbounded)
 * @param output_unbounded     True iff the last output window is unbounded
 */
static bool tl__l1_overlaps_window_range(const tl_segment_t* seg,
                                          tl_ts_t output_first_wstart,
                                          tl_ts_t output_last_wend,
                                          bool output_unbounded) {
    /* L1 segment overlaps if its window intersects output window range.
     * Use half-open intervals: seg window is [window_start, window_end).
     * Output range is [output_first_wstart, output_last_wend) unless unbounded. */

    /* Segment ends before output starts - no overlap */
    if (seg->window_end <= output_first_wstart) {
        return false;
    }

    /* If output is unbounded, any segment starting before infinity overlaps */
    if (output_unbounded) {
        return true;
    }

    /* Segment starts at or after output ends - no overlap */
    if (seg->window_start >= output_last_wend) {
        return false;
    }

    return true;
}

/*===========================================================================
 * Selection Helper Functions
 *
 * tl_compact_select() pins the manifest and invokes greedy L0 selection,
 * which in turn calls the L1 helper to pull in any window-overlapping L1
 * segments. L1 overlap MUST use window bounds (not record bounds) to
 * preserve the L1 non-overlap invariant.
 *===========================================================================*/

/**
 * Select L1 segments whose windows overlap the output window range.
 */
static tl_status_t tl__compact_select_l1(tl_compact_ctx_t* ctx,
                                          const tl_manifest_t* m) {
    /* Compute output window bounds */
    tl_ts_t output_first_wstart, output_first_wend;
    bool output_first_unbounded;
    tl_window_bounds(ctx->output_min_wid, ctx->window_size, ctx->window_origin,
                      &output_first_wstart, &output_first_wend, &output_first_unbounded);

    tl_ts_t output_last_wstart, output_last_wend;
    bool output_last_unbounded;
    tl_window_bounds(ctx->output_max_wid, ctx->window_size, ctx->window_origin,
                      &output_last_wstart, &output_last_wend, &output_last_unbounded);

    uint32_t n_l1 = tl_manifest_l1_count(m);
    if (n_l1 == 0) {
        return TL_OK;
    }

    /* One pass: allocate n_l1 pointers upfront (matching the L0 selection
     * style) so each segment's window overlap is evaluated exactly once.
     * The transient over-allocation is 8 bytes per non-overlapping L1
     * segment; ctx_destroy tolerates len < allocation. */
    if (tl__alloc_would_overflow((size_t)n_l1, sizeof(tl_segment_t*))) {
        return TL_EOVERFLOW;
    }

    ctx->input_l1 = (tl_segment_t**)tl__malloc(ctx->alloc,
                                                (size_t)n_l1 * sizeof(tl_segment_t*));
    if (ctx->input_l1 == NULL) {
        return TL_ENOMEM;
    }

    for (uint32_t i = 0; i < n_l1; i++) {
        tl_segment_t* seg = tl_manifest_l1_get(m, i);
        if (tl__l1_overlaps_window_range(seg, output_first_wstart,
                                          output_last_wend, output_last_unbounded)) {
            ctx->input_l1[ctx->input_l1_len++] = tl_segment_acquire(seg);
        }
    }

    return TL_OK;
}

/* Saturating size arithmetic (C17 + MSVC, so no <stdckdint.h>). The estimate
 * feeds only the greedy byte cap in selection, so clamping to SIZE_MAX on
 * overflow is exact enough: the exact saturation point is unobservable. */
static size_t tl__sat_add(size_t a, size_t b) {
    return (a > SIZE_MAX - b) ? SIZE_MAX : a + b;
}

/* uint64_t count input: record_count is uint64_t; the u64 comparison is also
 * correct for the narrower page/tombstone counts on 32-bit size_t hosts. */
static size_t tl__sat_mul_u64(uint64_t count, size_t elem_size) {
    return (count > SIZE_MAX / elem_size) ? SIZE_MAX
                                          : (size_t)count * elem_size;
}

static size_t tl__segment_estimate_bytes(const tl_segment_t* seg) {
    size_t est = tl__sat_mul_u64(seg->record_count, sizeof(tl_record_t));
    est = tl__sat_add(est, tl__sat_mul_u64(seg->page_count,
                                           sizeof(tl_page_meta_t)));
    if (seg->tombstones != NULL) {
        est = tl__sat_add(est, tl__sat_mul_u64(seg->tombstones->n,
                                               sizeof(tl_interval_t)));
        est = tl__sat_add(est, sizeof(tl_tombstones_t));
    }
    return tl__sat_add(est, sizeof(tl_segment_t));
}

/**
 * Greedy L0 selection: accumulate L0 segments until an input/window/byte cap
 * is hit. Caller has already pinned manifest and incremented next_gen.
 */
static tl_status_t tl__compact_select_greedy(tl_compact_ctx_t* ctx,
                                               const tl_manifest_t* m,
                                               size_t max_inputs) {
    tl_timelog_t* tl = ctx->tl;
    tl_status_t st;
    uint32_t n_l0 = tl_manifest_l0_count(m);

    if (n_l0 == 0) {
        return TL_EOF;
    }

    /* Allocate L0 input array */
    size_t l0_count = (size_t)n_l0;
    if (l0_count > SIZE_MAX / sizeof(tl_segment_t*)) {
        return TL_EOVERFLOW;
    }
    ctx->input_l0 = (tl_segment_t**)tl__malloc(ctx->alloc,
                                                l0_count * sizeof(tl_segment_t*));
    if (ctx->input_l0 == NULL) {
        return TL_ENOMEM;
    }

    /* Greedy L0 selection bounded by three caps: maximum input count,
     * maximum compaction window span, and target output bytes. A value
     * of 0 for any cap means unlimited. */
    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;
    size_t est_bytes = 0;

    uint64_t max_windows = (uint64_t)tl->config.max_compaction_windows;
    size_t target_bytes = tl->config.compaction_target_bytes;

    for (uint32_t i = 0; i < n_l0; i++) {
        if (max_inputs > 0 && ctx->input_l0_len >= max_inputs) {
            break;
        }

        tl_segment_t* seg = tl_manifest_l0_get(m, i);

        /* Candidate bounds if we include this segment */
        tl_ts_t cand_min = (ctx->input_l0_len == 0) ? seg->min_ts : TL_MIN(min_ts, seg->min_ts);
        tl_ts_t cand_max = (ctx->input_l0_len == 0) ? seg->max_ts : TL_MAX(max_ts, seg->max_ts);

        int64_t cand_min_wid = 0;
        int64_t cand_max_wid = 0;
        st = tl_window_id_for_ts(cand_min, ctx->window_size,
                                  ctx->window_origin, &cand_min_wid);
        if (st != TL_OK) {
            return st;
        }
        st = tl_window_id_for_ts(cand_max, ctx->window_size,
                                  ctx->window_origin, &cand_max_wid);
        if (st != TL_OK) {
            return st;
        }

        bool windows_exceed = false;
        if (max_windows > 0) {
            /* Direct subtraction can overflow in signed space for
             * extreme window-ID ranges; use the checked helper. */
            int64_t span_diff;
            if (tl_sub_overflow_i64(cand_max_wid, cand_min_wid, &span_diff)) {
                return TL_EOVERFLOW;
            }
            if (span_diff < 0) {
                return TL_EOVERFLOW;
            }
            /* span = span_diff + 1, range [1, 2^63]; uint64_t holds it. */
            uint64_t span = (uint64_t)span_diff + 1;
            windows_exceed = (span > max_windows);
        }

        size_t seg_bytes = 0;
        bool bytes_exceed = false;
        if (target_bytes > 0) {
            seg_bytes = tl__segment_estimate_bytes(seg);

            if (seg_bytes > SIZE_MAX - est_bytes) {
                bytes_exceed = true;
            } else {
                bytes_exceed = ((est_bytes + seg_bytes) > target_bytes);
            }
        }

        /* Caps apply only after at least one segment is selected: this
         * guarantees forward progress if a single segment exceeds a
         * cap on its own. */
        if (ctx->input_l0_len > 0 && (windows_exceed || bytes_exceed)) {
            break;
        }

        ctx->input_l0[ctx->input_l0_len++] = tl_segment_acquire(seg);
        min_ts = cand_min;
        max_ts = cand_max;
        if (target_bytes > 0) {
            if (seg_bytes > SIZE_MAX - est_bytes) {
                est_bytes = SIZE_MAX;
            } else {
                est_bytes += seg_bytes;
            }
        }
    }

    if (ctx->input_l0_len == 0) {
        return TL_EOF;
    }

    ctx->output_min_ts = min_ts;
    ctx->output_max_ts = max_ts;

    /* Compute covered window IDs (for output partitioning) */
    st = tl_window_id_for_ts(min_ts, ctx->window_size,
                              ctx->window_origin, &ctx->output_min_wid);
    if (st != TL_OK) {
        return st;
    }

    st = tl_window_id_for_ts(max_ts, ctx->window_size,
                              ctx->window_origin, &ctx->output_max_wid);
    if (st != TL_OK) {
        return st;
    }

    /* L1 selection using shared helper */
    return tl__compact_select_l1(ctx, m);
}

/*===========================================================================
 * Selection - Entry Point
 *===========================================================================*/

tl_status_t tl_compact_select(tl_compact_ctx_t* ctx) {
    tl_timelog_t* tl = ctx->tl;
    tl_status_t st;

    tl_atomic_inc_u64(&tl->compaction_select_calls);

    /* Snapshot pins a consistent tombstone view and op_seq watermark. */
    st = tl_snapshot_acquire_internal(tl, &tl->alloc, &ctx->snapshot);
    if (st != TL_OK) {
        return st;
    }

    ctx->applied_seq = tl_snapshot_seq(ctx->snapshot);
    ctx->base_manifest = tl_manifest_acquire(ctx->snapshot->manifest);

    /* next_gen is protected by writer_mu per lock hierarchy. */
    TL_LOCK_WRITER(tl);
    ctx->generation = tl->next_gen++;
    TL_UNLOCK_WRITER(tl);

    const tl_manifest_t* m = ctx->base_manifest;
    uint32_t n_l0 = tl_manifest_l0_count(m);

    /* Nothing to compact. base_manifest stays pinned; the caller's
     * tl_compact_ctx_destroy() releases it regardless of return path. */
    if (n_l0 == 0) {
        tl_atomic_inc_u64(&tl->compaction_select_no_work);
        return TL_EOF;
    }

    size_t max_inputs = (size_t)tl->config.max_compaction_inputs;
    st = tl__compact_select_greedy(ctx, m, max_inputs);
    if (st == TL_OK) {
        tl_atomic_fetch_add_u64(&tl->compaction_select_l0_inputs,
                                (uint64_t)ctx->input_l0_len, TL_MO_RELAXED);
        tl_atomic_fetch_add_u64(&tl->compaction_select_l1_inputs,
                                (uint64_t)ctx->input_l1_len, TL_MO_RELAXED);
    }
    return st;
}

/*===========================================================================
 * Merge Helpers
 *===========================================================================*/

/**
 * Grow a dynamic array to satisfy required element capacity.
 *
 * Uses shared growth policy helpers and optionally zeroes the newly exposed tail.
 */
static tl_status_t tl__grow_array(tl_alloc_ctx_t* alloc,
                                   void** arr,
                                   size_t* cap,
                                   size_t required,
                                   size_t elem_size,
                                   size_t min_cap,
                                   bool zero_new) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(arr != NULL);
    TL_ASSERT(cap != NULL);
    TL_ASSERT(elem_size > 0);
    TL_ASSERT(min_cap > 0);

    if (*cap >= required) {
        return TL_OK;
    }

    size_t old_cap = *cap;
    size_t new_cap = tl__grow_capacity(old_cap, required, min_cap);
    if (new_cap == 0 || tl__alloc_would_overflow(new_cap, elem_size)) {
        return TL_EOVERFLOW;
    }

    void* new_arr = tl__realloc(alloc, *arr, new_cap * elem_size);
    if (new_arr == NULL) {
        return TL_ENOMEM;
    }

    if (zero_new && new_cap > old_cap) {
        memset((char*)new_arr + (old_cap * elem_size), 0,
               (new_cap - old_cap) * elem_size);
    }

    *arr = new_arr;
    *cap = new_cap;
    return TL_OK;
}

/**
 * Ensure output_l1 array has capacity for at least one more segment.
 * Grows the array geometrically (2x) when needed.
 */
static tl_status_t tl__ensure_output_capacity(tl_compact_ctx_t* ctx) {
    return tl__grow_array(ctx->alloc,
                          (void**)&ctx->output_l1,
                          &ctx->output_l1_cap,
                          ctx->output_l1_len + 1,
                          sizeof(tl_segment_t*),
                          16,
                          true);
}

/**
 * Push a dropped record to the deferred drop list.
 * Grows the array geometrically (2x) when needed.
 */
static tl_status_t tl__push_dropped_record(tl_compact_ctx_t* ctx,
                                            tl_ts_t ts,
                                            tl_handle_t handle) {
    tl_status_t st = tl__grow_array(ctx->alloc,
                                    (void**)&ctx->dropped_records,
                                    &ctx->dropped_cap,
                                    ctx->dropped_len + 1,
                                    sizeof(tl_record_t),
                                    64,
                                    false);
    if (st != TL_OK) {
        return st;
    }

    /* Append record */
    ctx->dropped_records[ctx->dropped_len].ts = ts;
    ctx->dropped_records[ctx->dropped_len].handle = handle;
    ctx->dropped_len++;

    return TL_OK;
}

/**
 * Build an L1 segment from the accumulated records for one window and
 * clear the accumulator for the next.
 *
 * @param ctx           Compaction context
 * @param records       Record accumulator to flush
 * @param window_start  Window start bound (inclusive)
 * @param window_end    Window end bound (exclusive), or TL_TS_MAX if unbounded
 * @param end_unbounded True if this is the final, unbounded window
 *
 * When end_unbounded is true, tl_window_bounds() sets window_end to
 * TL_TS_MAX. That value is passed through to segment build unchanged:
 * every record with ts < TL_TS_MAX belongs to the window, and
 * TL_TS_MAX itself is the maximum representable timestamp.
 */
static tl_status_t tl__flush_window_records(tl_compact_ctx_t* ctx,
                                             tl_recvec_t* records,
                                             tl_ts_t window_start,
                                             tl_ts_t window_end,
                                             bool end_unbounded) {
    if (tl_recvec_len(records) == 0) {
        return TL_OK;  /* Empty window - no segment */
    }

    /* Ensure we have space in output array */
    tl_status_t st = tl__ensure_output_capacity(ctx);
    if (st != TL_OK) {
        return st;
    }

    /* Build L1 segment with explicit unbounded flag.
     * When end_unbounded=true, window_end is TL_TS_MAX (per tl_window_bounds). */
    tl_segment_t* seg = NULL;
    st = tl_segment_build_l1(
        ctx->alloc,
        tl_recvec_data(records),
        tl_recvec_len(records),
        ctx->target_page_bytes,
        window_start,
        window_end,
        end_unbounded,
        ctx->generation,
        ctx->applied_seq,
        &seg
    );

    if (st != TL_OK) {
        return st;
    }

    /* Add to output array */
    TL_ASSERT(ctx->output_l1_len < ctx->output_l1_cap);
    ctx->output_l1[ctx->output_l1_len++] = seg;

    /* Clear for next window */
    tl_recvec_clear(records);
    return TL_OK;
}

/**
 * Build a tombstone-only L0 segment for tombstones that extend beyond
 * the compaction output window range.
 *
 * A tombstone is partially outside the output range when:
 * - it starts before the first output window, or
 * - it ends after the last output window, or
 * - it is unbounded (always extends past any bounded last window).
 *
 * The outside portions cannot be folded into output L1 segments (they
 * cover ranges outside this compaction's scope) and must therefore
 * survive as a fresh L0 tombstone-only segment.
 */
static tl_status_t tl__build_residual_tombstones(tl_compact_ctx_t* ctx) {
    tl_intervals_t residual;
    tl_intervals_init(&residual, ctx->alloc);

    /* Bounds of the first and last output windows. */
    tl_ts_t first_w_start, first_w_end;
    bool first_w_unbounded;
    tl_window_bounds(ctx->output_min_wid, ctx->window_size, ctx->window_origin,
                      &first_w_start, &first_w_end, &first_w_unbounded);

    tl_ts_t last_w_start, last_w_end;
    bool last_w_unbounded;
    tl_window_bounds(ctx->output_max_wid, ctx->window_size, ctx->window_origin,
                      &last_w_start, &last_w_end, &last_w_unbounded);

    for (size_t i = 0; i < tl_intervals_len(&ctx->tombs); i++) {
        const tl_interval_t* t = tl_intervals_get(&ctx->tombs, i);

        /* Portion strictly before the first output window. */
        if (t->start < first_w_start) {
            tl_ts_t res_end = TL_MIN(t->end_unbounded ? first_w_start : t->end, first_w_start);
            if (t->start < res_end) {
                tl_status_t st = tl_intervals_insert(&residual, t->start, res_end,
                                                     t->max_seq);
                if (st != TL_OK) {
                    tl_intervals_destroy(&residual);
                    return st;
                }
            }
        }

        /* Portion past the last output window (only meaningful when the
         * last window is bounded). */
        if (!last_w_unbounded) {
            if (t->end_unbounded) {
                /* Use max(t->start, last_w_end) so an unbounded
                 * tombstone whose start lies past last_w_end is not
                 * widened to begin at last_w_end. Widening would
                 * silently delete records in [last_w_end, t->start)
                 * that the original tombstone never covered. */
                tl_ts_t res_start = TL_MAX(t->start, last_w_end);
                tl_status_t st = tl_intervals_insert_unbounded(&residual, res_start,
                                                               t->max_seq);
                if (st != TL_OK) {
                    tl_intervals_destroy(&residual);
                    return st;
                }
            } else if (t->end > last_w_end) {
                tl_ts_t res_start = TL_MAX(t->start, last_w_end);
                if (res_start < t->end) {
                    tl_status_t st = tl_intervals_insert(&residual, res_start, t->end,
                                                         t->max_seq);
                    if (st != TL_OK) {
                        tl_intervals_destroy(&residual);
                        return st;
                    }
                }
            }
        }
    }

    if (!tl_intervals_is_empty(&residual)) {
        size_t tomb_len;
        tl_interval_t* tomb_data = tl_intervals_take(&residual, &tomb_len);

        tl_segment_t* seg = NULL;
        tl_status_t st = tl_segment_build_l0(
            ctx->alloc,
            NULL, 0,           /* No records */
            tomb_data, tomb_len,
            ctx->target_page_bytes,
            ctx->generation,
            ctx->applied_seq,
            &seg
        );

        tl__free(ctx->alloc, tomb_data);

        if (st != TL_OK) {
            tl_intervals_destroy(&residual);
            return st;
        }

        ctx->residual_tomb = seg;
    }

    tl_intervals_destroy(&residual);
    return TL_OK;
}

/*===========================================================================
 * Merge
 *===========================================================================*/

tl_status_t tl_compact_merge(tl_compact_ctx_t* ctx) {
    tl_status_t st;
    if (ctx->applied_seq == 0) {
        return TL_EINVAL;
    }

    /* Build the "input tombstone" set used for residual computation:
     * the union of tombstones from selected input segments only,
     * unclipped. clear(), not init(): ctx_init() already initialised it. */
    tl_intervals_clear(&ctx->tombs);

    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        const tl_segment_t* seg = ctx->input_l0[i];
        if (tl_segment_has_tombstones(seg)) {
            tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
            st = tl_tombstones_add_intervals(&ctx->tombs, seg_tombs,
                                             TL_TS_MIN, 0, true);
            if (st != TL_OK) return st;
        }
    }

    /* L1 inputs should be tombstone-free by invariant, but collect
     * defensively to remain correct if that ever changes. */
    for (size_t i = 0; i < ctx->input_l1_len; i++) {
        const tl_segment_t* seg = ctx->input_l1[i];
        if (tl_segment_has_tombstones(seg)) {
            tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
            st = tl_tombstones_add_intervals(&ctx->tombs, seg_tombs,
                                             TL_TS_MIN, 0, true);
            if (st != TL_OK) return st;
        }
    }
    for (size_t i = 0; i < tl_intervals_len(&ctx->tombs); i++) {
        if (tl_intervals_get(&ctx->tombs, i)->max_seq > ctx->applied_seq) {
            return TL_EINVAL;
        }
    }

    /* Build the "filter tombstone" set: tombstones from the snapshot
     * (the global view, including ones that don't live in the input
     * segments), clipped to the output window range. Filtering must use
     * the snapshot set so a delete issued outside the input scope still
     * suppresses records during merge. */
    tl_intervals_clear(&ctx->tombs_clipped);

    tl_ts_t first_start, first_end;
    bool first_unbounded;
    tl_window_bounds(ctx->output_min_wid, ctx->window_size, ctx->window_origin,
                      &first_start, &first_end, &first_unbounded);

    tl_ts_t last_start, last_end;
    bool last_unbounded;
    tl_window_bounds(ctx->output_max_wid, ctx->window_size, ctx->window_origin,
                      &last_start, &last_end, &last_unbounded);

    st = tl_snapshot_collect_tombstones(ctx->snapshot, &ctx->tombs_clipped,
                                        first_start,
                                        last_unbounded ? 0 : last_end,
                                        last_unbounded);
    if (st != TL_OK) {
        return st;
    }

    if (!tl_intervals_is_empty(&ctx->tombs_clipped)) {
        if (!last_unbounded) {
            tl_intervals_clip(&ctx->tombs_clipped, first_start, last_end);
        } else {
            tl_intervals_clip_lower(&ctx->tombs_clipped, first_start);
        }
    }
    for (size_t i = 0; i < tl_intervals_len(&ctx->tombs_clipped); i++) {
        if (tl_intervals_get(&ctx->tombs_clipped, i)->max_seq > ctx->applied_seq) {
            return TL_EINVAL;
        }
    }

    /* Build segment iterators for K-way merge (direct, not via
     * tl_kmerge_iter_t which is tied to the query plan). */
    size_t total_inputs = ctx->input_l0_len + ctx->input_l1_len;

    /* tie_break_key is uint32_t. */
    if (total_inputs > UINT32_MAX) {
        return TL_EOVERFLOW;
    }

    tl_segment_iter_t* iters = tl__calloc(ctx->alloc, total_inputs,
                                           sizeof(tl_segment_iter_t));
    if (iters == NULL) {
        return TL_ENOMEM;
    }

    /* Iterate the full timestamp range of each input. */
    size_t iter_idx = 0;
    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        tl_segment_iter_init(&iters[iter_idx], ctx->input_l0[i],
                              TL_TS_MIN, 0, true);  /* [TL_TS_MIN, +inf) */
        iter_idx++;
    }
    for (size_t i = 0; i < ctx->input_l1_len; i++) {
        tl_segment_iter_init(&iters[iter_idx], ctx->input_l1[i],
                              TL_TS_MIN, 0, true);
        iter_idx++;
    }

    /* Build heap for K-way merge */
    tl_heap_t heap;
    tl_heap_init(&heap, ctx->alloc);
    st = tl_heap_reserve(&heap, total_inputs);
    if (st != TL_OK) {
        tl__free(ctx->alloc, iters);
        return st;
    }

    /* Prime heap with first record from each iterator. The per-source
     * watermark is just the segment's applied_seq (trivial inline); heap
     * refills below reuse min_entry.watermark, so no side array is needed. */
    for (size_t i = 0; i < total_inputs; i++) {
        tl_record_t rec;
        if (tl_segment_iter_next(&iters[i], &rec) == TL_OK) {
            tl_heap_entry_t entry = {
                .ts = rec.ts,
                .handle = rec.handle,
                .tie_break_key = (uint32_t)i,
                .watermark = tl_segment_applied_seq(iters[i].seg),
                .iter = &iters[i]
            };
            st = tl_heap_push(&heap, &entry);
            if (st != TL_OK) {
                tl_heap_destroy(&heap);
                tl__free(ctx->alloc, iters);
                return st;
            }
        }
    }

    /* K-way merge with tombstone filtering and window partitioning.
     * Filter against the clipped tombstone set (the global view), not
     * the input-only set. */
    tl_intervals_cursor_t tomb_cursor;
    tl_intervals_cursor_init(&tomb_cursor, tl_intervals_as_imm(&ctx->tombs_clipped));

    int64_t current_wid = ctx->output_min_wid;
    tl_ts_t current_window_start, current_window_end;
    bool current_end_unbounded;
    tl_window_bounds(current_wid, ctx->window_size, ctx->window_origin,
                      &current_window_start, &current_window_end,
                      &current_end_unbounded);

    /* Grow the per-window accumulator on demand. Pre-allocating by
     * window count would be infeasible: a TL_TS_MAX record at a 1-hour
     * default window size spans trillions of windows. */
    tl_recvec_t window_records;
    tl_recvec_init(&window_records, ctx->alloc);

    /* Process merged stream */
    while (!tl_heap_is_empty(&heap)) {
        tl_heap_entry_t min_entry;
        st = tl_heap_pop(&heap, &min_entry);
        if (st != TL_OK) {
            goto cleanup;
        }

        /* Refill heap from the source that produced this record */
        tl_segment_iter_t* source_iter = (tl_segment_iter_t*)min_entry.iter;
        tl_record_t next_rec;
        if (tl_segment_iter_next(source_iter, &next_rec) == TL_OK) {
            tl_heap_entry_t refill = {
                .ts = next_rec.ts,
                .handle = next_rec.handle,
                .tie_break_key = min_entry.tie_break_key,
                .watermark = min_entry.watermark,
                .iter = min_entry.iter
            };
            st = tl_heap_push(&heap, &refill);
            if (st != TL_OK) {
                goto cleanup;
            }
        }

        /* A record is deleted when the strongest tombstone covering its
         * timestamp was applied AFTER the record was written. The
         * watermark is the applied-seq the iterator carries with the
         * record; the tombstone cursor returns the maximum max_seq at
         * this timestamp. */
        tl_seq_t tomb_seq = 0;
        if (ctx->tombs_clipped.len > 0) {
            tomb_seq = tl_intervals_cursor_max_seq(&tomb_cursor, min_entry.ts);
        }
        if (tomb_seq > min_entry.watermark) {
            /* Defer the drop callback until publish succeeds; if merge
             * or publish then fails, the record is still visible and
             * firing now would let user code free a live payload. */
            if (ctx->on_drop_handle != NULL) {
                st = tl__push_dropped_record(ctx, min_entry.ts, min_entry.handle);
                if (st != TL_OK) {
                    goto cleanup;
                }
            }
            continue;
        }

        /* Window advance: jump directly to the window containing this
         * record, flushing the current accumulator first. Skipping over
         * empty intermediate windows keeps work O(records) instead of
         * O(window span). Window-id recomputation is only needed when
         * ts crosses out of the current window's end bound. */
        if (!current_end_unbounded && min_entry.ts >= current_window_end) {
            int64_t rec_wid;
            st = tl_window_id_for_ts(min_entry.ts, ctx->window_size,
                                      ctx->window_origin, &rec_wid);
            if (st != TL_OK) {
                goto cleanup;
            }

            if (current_wid < rec_wid) {
                st = tl__flush_window_records(ctx, &window_records,
                                               current_window_start, current_window_end,
                                               current_end_unbounded);
                if (st != TL_OK) {
                    goto cleanup;
                }

                current_wid = rec_wid;
                tl_window_bounds(current_wid, ctx->window_size, ctx->window_origin,
                                  &current_window_start, &current_window_end,
                                  &current_end_unbounded);
            }
        }

        st = tl_recvec_push(&window_records, min_entry.ts, min_entry.handle);
        if (st != TL_OK) {
            goto cleanup;
        }
    }

    /* Flush trailing accumulator. */
    st = tl__flush_window_records(ctx, &window_records,
                                   current_window_start, current_window_end,
                                   current_end_unbounded);
    if (st != TL_OK) {
        goto cleanup;
    }

    /* Tombstones that extend beyond the merged window range survive as
     * a residual L0 segment. */
    st = tl__build_residual_tombstones(ctx);
    if (st != TL_OK) {
        goto cleanup;
    }

    st = TL_OK;

cleanup:
    tl_recvec_destroy(&window_records);
    tl_heap_destroy(&heap);
    tl__free(ctx->alloc, iters);
    return st;
}

/** Build a manifest with compaction changes applied (off-lock). */
static tl_status_t tl__build_compaction_manifest(tl_compact_ctx_t* ctx,
                                                   const tl_manifest_t* base,
                                                   tl_manifest_t** out) {
    tl_status_t st;
    tl_manifest_builder_t builder;
    tl_manifest_builder_init(&builder, ctx->alloc, base);

    /* Remove input segments, add output segments */
    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        st = tl_manifest_builder_remove_l0(&builder, ctx->input_l0[i]);
        if (st != TL_OK) {
            tl_manifest_builder_destroy(&builder);
            return st;
        }
    }

    for (size_t i = 0; i < ctx->input_l1_len; i++) {
        st = tl_manifest_builder_remove_l1(&builder, ctx->input_l1[i]);
        if (st != TL_OK) {
            tl_manifest_builder_destroy(&builder);
            return st;
        }
    }

    for (size_t i = 0; i < ctx->output_l1_len; i++) {
        st = tl_manifest_builder_add_l1(&builder, ctx->output_l1[i]);
        if (st != TL_OK) {
            tl_manifest_builder_destroy(&builder);
            return st;
        }
    }

    if (ctx->residual_tomb != NULL) {
        st = tl_manifest_builder_add_l0(&builder, ctx->residual_tomb);
        if (st != TL_OK) {
            tl_manifest_builder_destroy(&builder);
            return st;
        }
    }

    st = tl_manifest_builder_build(&builder, out);
    tl_manifest_builder_destroy(&builder);
    return st;
}

/*===========================================================================
 * Publication
 *===========================================================================*/

tl_status_t tl_compact_publish(tl_compact_ctx_t* ctx) {
    tl_timelog_t* tl = ctx->tl;
    tl_status_t st;

#ifdef TL_TEST_HOOKS
    if (tl_test_force_ebusy_count > 0) {
        tl_test_force_ebusy_count--;
        return TL_EBUSY;
    }
#endif

    /* Build new manifest off-lock (must not hold writer_mu). */
    tl_manifest_t* new_manifest = NULL;
    st = tl__build_compaction_manifest(ctx, ctx->base_manifest, &new_manifest);
    if (st != TL_OK) {
        return st;
    }

    /* Validate and swap under lock. No allocation beyond this point. */
    TL_LOCK_WRITER(tl);

    /* Manifest changed since selection (concurrent flush/compaction):
     * our base no longer matches reality. Discard the new manifest
     * and return EBUSY so the caller can retry from a fresh selection. */
    if (tl->manifest != ctx->base_manifest) {
        TL_UNLOCK_WRITER(tl);
        tl_manifest_release(new_manifest);
        return TL_EBUSY;
    }

    /* Seqlock-bracketed manifest swap so concurrent readers retry past
     * the transition point. */
    tl_seqlock_write_begin(&tl->view_seq);

    tl_manifest_t* old_manifest = tl->manifest;
    tl->manifest = new_manifest;

    tl_seqlock_write_end(&tl->view_seq);

#ifndef NDEBUG
    /* Pin what we published before releasing writer_mu: a concurrent
     * flush could otherwise replace and release it before validation
     * runs below. */
    tl_manifest_t* validate_m = tl_manifest_acquire(new_manifest);
#endif

    TL_UNLOCK_WRITER(tl);

    tl_manifest_release(old_manifest);

#ifndef NDEBUG
    /* Validate the manifest we published, not the current tl->manifest
     * (which may have moved on already). */
    tl__validate_l1_non_overlap(validate_m);
    tl__validate_l0_generation_order(validate_m);
    tl_manifest_release(validate_m);
#endif

    /* ctx_destroy releases the ctx's refs; manifest holds its own. */
    return TL_OK;
}

/*===========================================================================
 * Main Entry Point
 *===========================================================================*/

tl_status_t tl_compact_one(tl_timelog_t* tl, int max_retries) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(max_retries > 0);  /* publish loop must execute at least once */

    /* Compute the adaptive candidate window under maint_mu, but do NOT
     * commit it yet. Committing before publish would change the live
     * window even if publish later fails or returns EBUSY. The commit
     * happens only after a successful publish; failure path records the
     * miss for backoff. */
    tl_ts_t original_window;
    tl_ts_t candidate_window;

    TL_LOCK_MAINT(tl);
    original_window = tl->effective_window_size;
    candidate_window = original_window;

    /* Grid frozen means L1 segments already exist; the window grid is
     * locked in and adaptive resizing is suppressed. */
    if (!tl->window_grid_frozen && tl->config.adaptive.target_records > 0) {
        candidate_window = tl_adaptive_compute_candidate(
            &tl->adaptive,
            &tl->config.adaptive,
            original_window);
    }
    TL_UNLOCK_MAINT(tl);

    /* Bounded retry loop: each attempt runs select -> merge -> publish
     * against the manifest current at selection time. TL_EBUSY from
     * publish means the manifest moved under us, so the merge result is
     * discarded and the whole cycle redone from a fresh selection.
     * Exhaustion always returns TL_EBUSY per the header contract;
     * select/merge failures on any attempt propagate as-is. */
    for (int attempt = 0; attempt < max_retries; attempt++) {
        tl_compact_ctx_t ctx;
        tl_compact_ctx_init(&ctx, tl, &tl->alloc, candidate_window);

        tl_status_t st = tl_compact_select(&ctx);
        if (st == TL_OK) {
            st = tl_compact_merge(&ctx);
        }
        if (st != TL_OK) {
            tl_compact_ctx_destroy(&ctx);
            return st;
        }

        st = tl_compact_publish(&ctx);
        if (st != TL_EBUSY) {
            if (st == TL_OK) {
                /* Drop callbacks fire only after publish succeeds: at this
                 * point the records are truly retired from the live
                 * manifest. Firing earlier would let user code free a
                 * payload that is still visible to readers. */
                if (ctx.on_drop_handle != NULL) {
                    for (size_t i = 0; i < ctx.dropped_len; i++) {
                        ctx.on_drop_handle(ctx.on_drop_ctx,
                                           ctx.dropped_records[i].ts,
                                           ctx.dropped_records[i].handle);
                    }
                }

                tl_atomic_inc_u64(&tl->compactions_total);

                /* Grid freeze and adaptive commit happen under a single
                 * maint_mu acquisition. */
                if (ctx.output_l1_len > 0 || tl->config.adaptive.target_records > 0) {
                    TL_LOCK_MAINT(tl);

                    /* First L1 segment seals the window grid; subsequent
                     * adaptive resizes would invalidate L1 partitioning. */
                    if (ctx.output_l1_len > 0) {
                        tl->window_grid_frozen = true;
                    }

                    if (tl->config.adaptive.target_records > 0) {
                        tl->effective_window_size = candidate_window;
                        tl_adaptive_record_success(&tl->adaptive);
                    }

                    TL_UNLOCK_MAINT(tl);
                }
            }
            tl_compact_ctx_destroy(&ctx);
            return st;
        }

        /* EBUSY: count the missed publish; a retry is counted only when
         * another attempt actually follows. */
        tl_atomic_inc_u64(&tl->compaction_publish_ebusy);
        if (attempt + 1 < max_retries) {
            tl_atomic_inc_u64(&tl->compaction_retries);
        }
        tl_compact_ctx_destroy(&ctx);
    }

    /* Retries exhausted: tell the adaptive policy to back off next time. */
    if (tl->config.adaptive.target_records > 0) {
        TL_LOCK_MAINT(tl);
        tl_adaptive_record_failure(&tl->adaptive);
        TL_UNLOCK_MAINT(tl);
    }
    return TL_EBUSY;
}
