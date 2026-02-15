#include "tl_compaction.h"
#include "tl_adaptive.h"
#include "../internal/tl_timelog_internal.h"
#include "../internal/tl_locks.h"
#include "../internal/tl_seqlock.h"
#include "../internal/tl_heap.h"
#include "../internal/tl_recvec.h"
#include "../query/tl_segment_iter.h"
#include "../query/tl_snapshot.h"
#include "../storage/tl_window.h"
#include <string.h>

/*===========================================================================
 * Test Hooks (Debug/Test Builds Only)
 *
 * TL_TEST_HOOKS enables deterministic failpoints for testing error paths.
 * This is defined only for test builds via CMake compile definitions.
 *===========================================================================*/

#ifdef TL_TEST_HOOKS
/* Force tl_compact_publish() to return TL_EBUSY for the next N calls.
 * Used by compact_one_exhausts_retries test for deterministic EBUSY testing.
 * Thread-unsafe (test-only): only modify from single-threaded test code.
 *
 * volatile: Prevents compiler from caching value across function boundaries.
 * While tests are single-threaded, the compiler could theoretically hoist
 * the load outside the publish function without volatile. */
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

    /* Initialize empty interval sets */
    tl_intervals_init(&ctx->tombs, alloc);
    tl_intervals_init(&ctx->tombs_clipped, alloc);

    ctx->snapshot = NULL;
    ctx->applied_seq = 0;

    /* Initialize deferred drop records (empty) */
    ctx->dropped_records = NULL;
    ctx->dropped_len = 0;
    ctx->dropped_cap = 0;
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
 * Validate that L0 segments are ordered by generation.
 *
 * L0 segments should be ordered by generation (older first) since they
 * are added in flush order. This invariant ensures correct tie-breaking
 * during merge.
 *
 * @param m  Manifest to validate
 */
static void tl__validate_l0_generation_order(const tl_manifest_t* m) {
    uint32_t n = tl_manifest_l0_count(m);
    if (n <= 1) {
        return;  /* 0 or 1 segment is trivially ordered */
    }

    uint32_t prev_gen = tl_manifest_l0_get(m, 0)->generation;
    for (uint32_t i = 1; i < n; i++) {
        uint32_t gen = tl_manifest_l0_get(m, i)->generation;
        TL_ASSERT(gen > prev_gen && "L0 must be ordered by generation");
        prev_gen = gen;
    }
}

/**
 * Validate that L1 segments in manifest are non-overlapping by window.
 *
 * This is a critical system invariant:
 * "L1 non-overlap: L1 segments are non-overlapping by time window"
 *
 * Uses O(n) linear scan since L1 segments are sorted by window_start
 * (invariant maintained by manifest builder).
 *
 * @param m  Manifest to validate
 */
static void tl__validate_l1_non_overlap(const tl_manifest_t* m) {
    uint32_t n = tl_manifest_l1_count(m);
    if (n <= 1) {
        return;  /* 0 or 1 segment cannot overlap */
    }

    /* O(n) validation: L1 segments are sorted by window_start, so we only
     * need to check adjacent pairs. Overlap if prev.window_end > curr.window_start. */
    for (uint32_t i = 1; i < n; i++) {
        const tl_segment_t* prev = tl_manifest_l1_get(m, i - 1);
        const tl_segment_t* curr = tl_manifest_l1_get(m, i);

        /* Unbounded window must be last (can only be the final segment) */
        TL_ASSERT(!prev->window_end_unbounded && "Unbounded L1 window must be last");

        /* Non-overlap check: prev.window_end <= curr.window_start */
        TL_ASSERT(prev->window_end <= curr->window_start && "L1 overlap detected");
    }
}
#endif /* NDEBUG */

/*===========================================================================
 * Delete Debt Computation (Internal)
 *===========================================================================*/

/** Union immutable tombstones into mutable accumulator via temp buffer. */
static tl_status_t tl__tombs_union_into(tl_intervals_t* accum,
                                         tl_intervals_imm_t add,
                                         tl_alloc_ctx_t* alloc) {
    if (add.len == 0) {
        return TL_OK;
    }

    tl_intervals_t temp;
    tl_intervals_init(&temp, alloc);

    tl_status_t st = tl_intervals_union_imm(&temp,
                                             tl_intervals_as_imm(accum),
                                             add);
    if (st != TL_OK) {
        tl_intervals_destroy(&temp);
        return st;
    }

    tl_intervals_destroy(accum);
    *accum = temp;
    return TL_OK;
}

/** Compute max delete debt ratio across all windows. */
static double tl__compute_delete_debt(const tl_timelog_t* tl,
                                       const tl_manifest_t* m) {
    tl_intervals_t tombs;
    tl_intervals_init(&tombs, (tl_alloc_ctx_t*)&tl->alloc);

    for (uint32_t i = 0; i < tl_manifest_l0_count(m); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(m, i);
        if (tl_segment_has_tombstones(seg)) {
            tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
            tl_status_t union_st = tl__tombs_union_into(&tombs, seg_tombs,
                                                        (tl_alloc_ctx_t*)&tl->alloc);
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
    tl_ts_t window_size = tl->effective_window_size;

    /* Check for unbounded tombstones - short circuit to avoid pathological loop.
     * An unbounded tombstone [t, +inf) means all future windows are affected.
     * Iterating to TL_TS_MAX would be billions of windows - not feasible.
     * Return 1.0 (maximum debt) to trigger compaction immediately. */
    const tl_interval_t* last_tomb = tl_intervals_get(&tombs, tl_intervals_len(&tombs) - 1);
    if (last_tomb->end_unbounded) {
        tl_intervals_destroy(&tombs);
        return 1.0;  /* Maximum debt - forces compaction trigger */
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
    return tl__compute_delete_debt(tl, m);
}
#endif

/*===========================================================================
 * Trigger Logic
 *===========================================================================*/

bool tl_compact_needed(const tl_timelog_t* tl) {
    /*
     * Thread Safety: Must acquire manifest under writer_mu to prevent UAF.
     *
     * Per tl_seqlock.h: "we hold writer_mu during snapshot to ensure the
     * memview capture is consistent with manifest". The seqlock pattern
     * requires writer_mu; reading manifest without it risks UAF since
     * manifest is a plain pointer that can be freed after swap.
     *
     * This is an advisory check; the actual selection phase will re-acquire
     * the manifest for authoritative decision.
     */
    tl_timelog_t* tl_mut = (tl_timelog_t*)tl;  /* Cast away const for lock */
    TL_LOCK_WRITER(tl_mut);

    /* Pin manifest to prevent UAF */
    tl_manifest_t* m = tl_manifest_acquire(tl_mut->manifest);

    TL_UNLOCK_WRITER(tl_mut);

    /* Now we can safely read from the pinned manifest */
    bool needed = false;

    if (tl_manifest_l0_count(m) >= tl->config.max_delta_segments) {
        needed = true;
        goto done;
    }

    if (tl->config.delete_debt_threshold > 0.0) {
        if (tl__compute_delete_debt(tl, m) >= tl->config.delete_debt_threshold) {
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
 * Check if L1 segment's WINDOW overlaps the compaction output window range.
 *
 * CRITICAL: Must use window bounds (window_start/window_end), NOT record bounds
 * (min_ts/max_ts). This is because L1 segments are window-partitioned.
 *
 * Counterexample that breaks invariants if using record bounds:
 * - Existing L1 for window [0,3600) has single record at ts=0
 *   => seg->min_ts=0, seg->max_ts=0, but seg->window_end=3600
 * - New L0 data at ts=1000 (same window)
 * - Record-based overlap: max_ts(0) >= 1000 is false => NOT selected
 * - Compaction creates NEW L1 for window [0,3600)
 * - Result: TWO L1 segments for same window => invariant violation!
 *
 * @param seg                L1 segment to check
 * @param output_first_wstart First output window start
 * @param output_last_wend   Last output window end (or TL_TS_MAX if unbounded)
 * @param output_unbounded   True if last output window is unbounded
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
 * These helpers support L0 segment selection and L1 overlap detection.
 * The selection path is: tl_compact_select() pins manifest and calls
 * greedy selection, which uses the shared L1 selection helper.
 *===========================================================================*/

/**
 * Select L1 segments whose WINDOWS overlap the output range.
 * Must use window bounds (not record bounds) to preserve L1 non-overlap.
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

    size_t overlap_count = 0;
    for (uint32_t i = 0; i < n_l1; i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(m, i);
        if (tl__l1_overlaps_window_range(seg, output_first_wstart,
                                          output_last_wend, output_last_unbounded)) {
            overlap_count++;
        }
    }

    if (overlap_count == 0) {
        return TL_OK;
    }

    if (tl__alloc_would_overflow(overlap_count, sizeof(tl_segment_t*))) {
        return TL_EOVERFLOW;
    }

    ctx->input_l1 = (tl_segment_t**)tl__malloc(ctx->alloc,
                                                overlap_count * sizeof(tl_segment_t*));
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

static size_t tl__segment_estimate_bytes(const tl_segment_t* seg) {
    size_t est = 0;

    if (seg->record_count > SIZE_MAX / sizeof(tl_record_t)) {
        return SIZE_MAX;
    }
    est = (size_t)seg->record_count * sizeof(tl_record_t);

    if (seg->page_count > SIZE_MAX / sizeof(tl_page_meta_t)) {
        return SIZE_MAX;
    }
    size_t page_meta_bytes = (size_t)seg->page_count * sizeof(tl_page_meta_t);
    if (est > SIZE_MAX - page_meta_bytes) {
        return SIZE_MAX;
    }
    est += page_meta_bytes;

    if (seg->tombstones != NULL) {
        if (seg->tombstones->n > SIZE_MAX / sizeof(tl_interval_t)) {
            return SIZE_MAX;
        }
        size_t tomb_bytes = (size_t)seg->tombstones->n * sizeof(tl_interval_t);
        if (est > SIZE_MAX - tomb_bytes) {
            return SIZE_MAX;
        }
        est += tomb_bytes;
        if (est > SIZE_MAX - sizeof(tl_tombstones_t)) {
            return SIZE_MAX;
        }
        est += sizeof(tl_tombstones_t);
    }

    if (est > SIZE_MAX - sizeof(tl_segment_t)) {
        return SIZE_MAX;
    }
    est += sizeof(tl_segment_t);

    return est;
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

    /* Select L0 segments with optional caps (inputs/windows/bytes) */
    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;
    size_t est_bytes = 0;

    uint64_t max_windows = (uint64_t)tl->config.max_compaction_windows; /* 0 = unlimited */
    size_t target_bytes = tl->config.compaction_target_bytes; /* 0 = unlimited */

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
            /* Use overflow-safe subtraction to compute window span.
             * Direct subtraction cand_max_wid - cand_min_wid can overflow
             * in signed space for extreme window ID ranges. */
            int64_t span_diff;
            if (tl_sub_overflow_i64(cand_max_wid, cand_min_wid, &span_diff)) {
                return TL_EOVERFLOW;
            }
            if (span_diff < 0) {
                return TL_EOVERFLOW;  /* max < min shouldn't happen */
            }
            /* span_diff in [0, INT64_MAX]. span = span_diff + 1 in [1, 2^63].
             * 2^63 fits in uint64_t, so this cast and add are safe. */
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

        /* Enforce caps only after we've selected at least one segment.
         * This guarantees forward progress even if a single segment exceeds caps. */
        if (ctx->input_l0_len > 0 && (windows_exceed || bytes_exceed)) {
            break;
        }

        /* Accept segment */
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

    /* Safety: ensure at least one L0 segment is selected */
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

    /* Selection observability - count attempts */
    tl_atomic_inc_u64(&tl->compaction_select_calls);

    /* Acquire snapshot for consistent tombstones + op_seq watermark */
    st = tl_snapshot_acquire_internal(tl, &tl->alloc, &ctx->snapshot);
    if (st != TL_OK) {
        return st;
    }

    ctx->applied_seq = tl_snapshot_seq(ctx->snapshot);
    ctx->base_manifest = tl_manifest_acquire(ctx->snapshot->manifest);

    /* NOTE: next_gen is protected by writer_mu per lock hierarchy. */
    TL_LOCK_WRITER(tl);
    ctx->generation = tl->next_gen++;
    TL_UNLOCK_WRITER(tl);

    const tl_manifest_t* m = ctx->base_manifest;
    uint32_t n_l0 = tl_manifest_l0_count(m);

    /* Exit early if no L0 segments.
     *
     * Note: base_manifest is still pinned here (acquired above). This is
     * intentional - caller MUST call tl_compact_ctx_destroy() which releases
     * base_manifest. This follows the init/destroy lifecycle pattern where
     * ctx_destroy handles cleanup regardless of which phase failed. */
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
 * Flush accumulated records into an L1 segment for the given window.
 * Clears the record vector after building.
 *
 * @param ctx           Compaction context
 * @param records       Record accumulator to flush
 * @param window_start  Window start bound (inclusive)
 * @param window_end    Window end bound (exclusive), or TL_TS_MAX if unbounded
 * @param end_unbounded True if this is the last window (extends to +infinity)
 *
 * Note: When end_unbounded=true, tl_window_bounds() sets window_end=TL_TS_MAX.
 * We pass this directly to segment build - semantically correct because all
 * records with ts < TL_TS_MAX fit in the window, and ts=TL_TS_MAX is the
 * maximum representable timestamp.
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
 * Build tombstone-only L0 segment for residual tombstones that extend
 * beyond the compaction output range.
 *
 * Residual tombstones occur when:
 * - A tombstone interval starts before output_min_ts
 * - A tombstone interval ends after output_max_ts
 * - An unbounded tombstone exists
 */
static tl_status_t tl__build_residual_tombstones(tl_compact_ctx_t* ctx) {
    tl_intervals_t residual;
    tl_intervals_init(&residual, ctx->alloc);

    /* Compute output window bounds - FIRST window and LAST window separately */
    tl_ts_t first_w_start, first_w_end;
    bool first_w_unbounded;
    tl_window_bounds(ctx->output_min_wid, ctx->window_size, ctx->window_origin,
                      &first_w_start, &first_w_end, &first_w_unbounded);

    tl_ts_t last_w_start, last_w_end;
    bool last_w_unbounded;
    tl_window_bounds(ctx->output_max_wid, ctx->window_size, ctx->window_origin,
                      &last_w_start, &last_w_end, &last_w_unbounded);

    /* Check each tombstone for residual portions */
    for (size_t i = 0; i < tl_intervals_len(&ctx->tombs); i++) {
        const tl_interval_t* t = tl_intervals_get(&ctx->tombs, i);

        /* Residual before output range (before first window start) */
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

        /* Residual after output range (only if last window is bounded) */
        if (!last_w_unbounded) {
            if (t->end_unbounded) {
                /* Unbounded tombstone has residual after output range.
                 * CRITICAL: Use max(t->start, last_w_end) to avoid widening deletes.
                 * If t->start > last_w_end, inserting at last_w_end would incorrectly
                 * delete records in [last_w_end, t->start) that were never covered. */
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

    /* If residual tombstones exist, build tombstone-only L0 segment */
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

    /* Step 1: Build effective tombstone set.
     * Use clear(), not init(), because tombs was initialized in ctx_init(). */
    tl_intervals_clear(&ctx->tombs);

    /* Collect tombstones from L0 segments */
    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        const tl_segment_t* seg = ctx->input_l0[i];
        if (tl_segment_has_tombstones(seg)) {
            tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
            st = tl__tombs_union_into(&ctx->tombs, seg_tombs, ctx->alloc);
            if (st != TL_OK) return st;
        }
    }

    /* Defensive: collect from L1 if present (should be empty per invariant) */
    for (size_t i = 0; i < ctx->input_l1_len; i++) {
        const tl_segment_t* seg = ctx->input_l1[i];
        if (tl_segment_has_tombstones(seg)) {
            tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
            st = tl__tombs_union_into(&ctx->tombs, seg_tombs, ctx->alloc);
            if (st != TL_OK) return st;
        }
    }
    for (size_t i = 0; i < tl_intervals_len(&ctx->tombs); i++) {
        if (tl_intervals_get(&ctx->tombs, i)->max_seq > ctx->applied_seq) {
            return TL_EINVAL;
        }
    }

    /* Step 1b: Clipped tombstones for filtering.
     * Use snapshot tombs so deletes outside inputs still apply. */
    tl_intervals_clear(&ctx->tombs_clipped);

    /* Compute output window bounds for clipping. */
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

    /* Step 2: Build input iterators and initialize K-way merge.
     * Uses segment iterators directly (cannot reuse tl_kmerge_iter_t). */
    size_t total_inputs = ctx->input_l0_len + ctx->input_l1_len;

    /* Bounds check: tie_break_key is uint32_t. */
    if (total_inputs > UINT32_MAX) {
        return TL_EOVERFLOW;
    }

    tl_segment_iter_t* iters = tl__calloc(ctx->alloc, total_inputs,
                                           sizeof(tl_segment_iter_t));
    if (iters == NULL) {
        return TL_ENOMEM;
    }

    if (total_inputs > SIZE_MAX / sizeof(tl_seq_t)) {
        tl__free(ctx->alloc, iters);
        return TL_EOVERFLOW;
    }

    tl_seq_t* watermarks = tl__malloc(ctx->alloc, total_inputs * sizeof(tl_seq_t));
    if (watermarks == NULL) {
        tl__free(ctx->alloc, iters);
        return TL_ENOMEM;
    }

    /* Initialize segment iterators (unbounded range). */
    size_t iter_idx = 0;
    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        tl_segment_iter_init(&iters[iter_idx], ctx->input_l0[i],
                              TL_TS_MIN, 0, true);  /* [TL_TS_MIN, +inf) */
        watermarks[iter_idx] = tl_segment_applied_seq(ctx->input_l0[i]);
        iter_idx++;
    }
    for (size_t i = 0; i < ctx->input_l1_len; i++) {
        tl_segment_iter_init(&iters[iter_idx], ctx->input_l1[i],
                              TL_TS_MIN, 0, true);
        watermarks[iter_idx] = tl_segment_applied_seq(ctx->input_l1[i]);
        iter_idx++;
    }

    /* Build heap for K-way merge */
    tl_heap_t heap;
    tl_heap_init(&heap, ctx->alloc);
    st = tl_heap_reserve(&heap, total_inputs);
    if (st != TL_OK) {
        tl__free(ctx->alloc, watermarks);
        tl__free(ctx->alloc, iters);
        return st;
    }

    /* Prime heap with first record from each iterator */
    for (size_t i = 0; i < total_inputs; i++) {
        tl_record_t rec;
        if (tl_segment_iter_next(&iters[i], &rec) == TL_OK) {
            tl_heap_entry_t entry = {
                .ts = rec.ts,
                .handle = rec.handle,
                .tie_break_key = (uint32_t)i,
                .watermark = watermarks[i],
                .iter = &iters[i]
            };
            st = tl_heap_push(&heap, &entry);
            if (st != TL_OK) {
                tl_heap_destroy(&heap);
                tl__free(ctx->alloc, watermarks);
                tl__free(ctx->alloc, iters);
                return st;
            }
        }
    }

    /* Step 3: K-way merge with tombstone filtering and window partitioning */

    /* Tombstone cursor uses CLIPPED tombstones for filtering */
    tl_intervals_cursor_t tomb_cursor;
    tl_intervals_cursor_init(&tomb_cursor, tl_intervals_as_imm(&ctx->tombs_clipped));

    /* Window state for output partitioning. */
    int64_t current_wid = ctx->output_min_wid;
    tl_ts_t current_window_start, current_window_end;
    bool current_end_unbounded;
    tl_window_bounds(current_wid, ctx->window_size, ctx->window_origin,
                      &current_window_start, &current_window_end,
                      &current_end_unbounded);

    /* Output grows dynamically; pre-allocating by window span would fail
     * for TL_TS_MAX records (trillions of windows with default 1h size). */
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

        /* Check if record is deleted by tombstone */
        tl_seq_t tomb_seq = 0;
        if (ctx->tombs_clipped.len > 0) {
            tomb_seq = tl_intervals_cursor_max_seq(&tomb_cursor, min_entry.ts);
        }
        if (tomb_seq > min_entry.watermark) {
            /* Record deleted; defer callback until successful publish.
             * Firing now would allow user to free payloads for records
             * still visible if merge or publish later fails. */
            if (ctx->on_drop_handle != NULL) {
                st = tl__push_dropped_record(ctx, min_entry.ts, min_entry.handle);
                if (st != TL_OK) {
                    goto cleanup;
                }
            }
            continue;  /* Skip this record */
        }

        /* Determine window membership.
         * Avoid per-record division; recompute window_id only when ts
         * exceeds current window end. */
        if (!current_end_unbounded && min_entry.ts >= current_window_end) {
            int64_t rec_wid;
            st = tl_window_id_for_ts(min_entry.ts, ctx->window_size,
                                      ctx->window_origin, &rec_wid);
            if (st != TL_OK) {
                goto cleanup;
            }

            /* Jump directly to rec_wid; skipping empty intermediate windows
             * keeps compaction O(records) not O(windows). */
            if (current_wid < rec_wid) {
                /* Flush current window */
                st = tl__flush_window_records(ctx, &window_records,
                                               current_window_start, current_window_end,
                                               current_end_unbounded);
                if (st != TL_OK) {
                    goto cleanup;
                }

                /* Advance to window containing this record */
                current_wid = rec_wid;
                tl_window_bounds(current_wid, ctx->window_size, ctx->window_origin,
                                  &current_window_start, &current_window_end,
                                  &current_end_unbounded);
            }
        }

        /* Add record to current window accumulator */
        st = tl_recvec_push(&window_records, min_entry.ts, min_entry.handle);
        if (st != TL_OK) {
            goto cleanup;
        }
    }

    /* Flush final window */
    st = tl__flush_window_records(ctx, &window_records,
                                   current_window_start, current_window_end,
                                   current_end_unbounded);
    if (st != TL_OK) {
        goto cleanup;
    }

    /* Step 4: Handle residual tombstones */
    st = tl__build_residual_tombstones(ctx);
    if (st != TL_OK) {
        goto cleanup;
    }

    st = TL_OK;

cleanup:
    tl_recvec_destroy(&window_records);
    tl_heap_destroy(&heap);
    tl__free(ctx->alloc, watermarks);
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
    /* Test hook: force EBUSY for retry exhaustion testing */
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

    /* Strict publish: if manifest changed during merge (concurrent
     * flush), discard result and return EBUSY to force caller retry. */
    if (tl->manifest != ctx->base_manifest) {
        TL_UNLOCK_WRITER(tl);
        tl_manifest_release(new_manifest);
        return TL_EBUSY;
    }

    /* Seqlock region for manifest swap */
    tl_seqlock_write_begin(&tl->view_seq);

    /* Swap manifest */
    tl_manifest_t* old_manifest = tl->manifest;
    tl->manifest = new_manifest;

    tl_seqlock_write_end(&tl->view_seq);

#ifndef NDEBUG
    /* Pin the published manifest before unlock to prevent UAF.
     * Without pin, a concurrent flush could replace+release it
     * before our validation call below. */
    tl_manifest_t* validate_m = tl_manifest_acquire(new_manifest);
#endif

    TL_UNLOCK_WRITER(tl);

    /* Release old manifest */
    tl_manifest_release(old_manifest);

#ifndef NDEBUG
    /* Validate what we published, not current tl->manifest */
    tl__validate_l1_non_overlap(validate_m);
    tl__validate_l0_generation_order(validate_m);
    tl_manifest_release(validate_m);
#endif

    /* ctx_destroy will release ctx's refs; manifest holds its own refs. */
    return TL_OK;
}

/*===========================================================================
 * Main Entry Point
 *===========================================================================*/

tl_status_t tl_compact_one(tl_timelog_t* tl, int max_retries) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(max_retries > 0);  /* Ensures publish loop executes at least once */

    /* Adaptive integration: compute candidate window under maint_mu,
     * commit only after successful publish, record failure on exhaustion. */
    tl_ts_t original_window;
    tl_ts_t candidate_window;

    TL_LOCK_MAINT(tl);
    original_window = tl->effective_window_size;
    candidate_window = original_window;

    /* Skip adaptive selection when the grid is frozen (L1 segments exist). */
    if (!tl->window_grid_frozen && tl->config.adaptive.target_records > 0) {
        /* Compute candidate under maint_mu */
        candidate_window = tl_adaptive_compute_candidate(
            &tl->adaptive,
            &tl->config.adaptive,
            original_window);
        /* Do not commit yet; commit only after successful publish. */
    }
    TL_UNLOCK_MAINT(tl);

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc, candidate_window);

    tl_status_t st;

    st = tl_compact_select(&ctx);
    if (st != TL_OK) {
        tl_compact_ctx_destroy(&ctx);
        return st;
    }

    st = tl_compact_merge(&ctx);
    if (st != TL_OK) {
        tl_compact_ctx_destroy(&ctx);
        return st;
    }

    /* Strict publish with bounded retries.
     * On EBUSY (manifest changed during merge), re-select and re-merge.
     * This keeps semantics simple at the cost of possible repeated work. */
    tl_status_t publish_st = TL_EBUSY;
    for (int attempt = 0; attempt < max_retries; attempt++) {
        publish_st = tl_compact_publish(&ctx);
        if (publish_st != TL_EBUSY) {
            if (publish_st == TL_OK) {
                /* Fire deferred drop callbacks; this is safe only after successful
                 * publish (records truly retired from newest manifest). */
                if (ctx.on_drop_handle != NULL) {
                    for (size_t i = 0; i < ctx.dropped_len; i++) {
                        ctx.on_drop_handle(ctx.on_drop_ctx,
                                           ctx.dropped_records[i].ts,
                                           ctx.dropped_records[i].handle);
                    }
                }

                /* Bump compaction counter */
                tl_atomic_inc_u64(&tl->compactions_total);

                /* Grid freeze and adaptive commit under one maint lock hold. */
                if (ctx.output_l1_len > 0 || tl->config.adaptive.target_records > 0) {
                    TL_LOCK_MAINT(tl);

                    /* Freeze grid after first L1 creation. */
                    if (ctx.output_l1_len > 0) {
                        tl->window_grid_frozen = true;
                    }

                    /* Adaptive: commit candidate window */
                    if (tl->config.adaptive.target_records > 0) {
                        tl->effective_window_size = candidate_window;
                        tl_adaptive_record_success(&tl->adaptive);
                    }

                    TL_UNLOCK_MAINT(tl);
                }
            }
            tl_compact_ctx_destroy(&ctx);
            return publish_st;
        }

        /* EBUSY: count and retry from a fresh selection. */
        tl_atomic_inc_u64(&tl->compaction_publish_ebusy);
        if (attempt + 1 < max_retries) {
            tl_atomic_inc_u64(&tl->compaction_retries);
        }

        /* Re-select and re-merge from current manifest */
        tl_compact_ctx_destroy(&ctx);
        tl_compact_ctx_init(&ctx, tl, &tl->alloc, candidate_window);

        st = tl_compact_select(&ctx);
        if (st != TL_OK) {
            tl_compact_ctx_destroy(&ctx);
            return st;
        }

        st = tl_compact_merge(&ctx);
        if (st != TL_OK) {
            tl_compact_ctx_destroy(&ctx);
            return st;
        }
    }

    /* Retries exhausted; record an adaptive failure. */
    tl_compact_ctx_destroy(&ctx);
    if (tl->config.adaptive.target_records > 0) {
        TL_LOCK_MAINT(tl);
        tl_adaptive_record_failure(&tl->adaptive);
        TL_UNLOCK_MAINT(tl);
    }
    return publish_st;
}
