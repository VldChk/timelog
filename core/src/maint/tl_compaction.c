#include "tl_compaction.h"
#include "tl_adaptive.h"
#include "../internal/tl_timelog_internal.h"
#include "../internal/tl_locks.h"
#include "../internal/tl_seqlock.h"
#include "../internal/tl_heap.h"
#include "../internal/tl_recvec.h"
#include "../query/tl_segment_iter.h"
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
 * Validate that L1 segments in manifest are non-overlapping by window.
 *
 * This is a critical system invariant per CLAUDE.md:
 * "L1 non-overlap: L1 segments are non-overlapping by time window"
 *
 * Runs in O(n²) which is acceptable for debug validation with typical
 * L1 segment counts (<100). Production code should never violate this.
 *
 * @param m  Manifest to validate
 */
static void tl__validate_l1_non_overlap(const tl_manifest_t* m) {
    uint32_t n = tl_manifest_l1_count(m);
    if (n <= 1) {
        return;  /* 0 or 1 segment cannot overlap */
    }

    for (uint32_t i = 0; i < n; i++) {
        const tl_segment_t* seg_i = tl_manifest_l1_get(m, i);
        for (uint32_t j = i + 1; j < n; j++) {
            const tl_segment_t* seg_j = tl_manifest_l1_get(m, j);

            /* Check for overlap: segments overlap if neither ends before the other starts.
             * Using half-open intervals [start, end), overlap occurs if:
             * NOT (i.end <= j.start OR j.end <= i.start)
             * = i.end > j.start AND j.end > i.start */
            bool overlap = (seg_i->window_end > seg_j->window_start) &&
                           (seg_j->window_end > seg_i->window_start);

            TL_ASSERT(!overlap && "L1 non-overlap invariant violated after compaction");
        }
    }
}
#endif /* NDEBUG */

/*===========================================================================
 * Delete Debt Computation (Internal)
 *===========================================================================*/

/**
 * Helper: Union immutable tombstones into mutable accumulator.
 * Uses temp buffer for proper tl_intervals_union_imm() semantics.
 */
static tl_status_t tl__tombs_union_into(tl_intervals_t* accum,
                                         tl_intervals_imm_t add,
                                         tl_alloc_ctx_t* alloc) {
    if (add.len == 0) {
        return TL_OK;  /* Nothing to add */
    }
    if (tl_intervals_is_empty(accum)) {
        /* First set - just copy */
        for (size_t i = 0; i < add.len; i++) {
            tl_status_t st;
            if (add.data[i].end_unbounded) {
                st = tl_intervals_insert_unbounded(accum, add.data[i].start);
            } else {
                st = tl_intervals_insert(accum, add.data[i].start, add.data[i].end);
            }
            if (st != TL_OK) return st;
        }
        return TL_OK;
    }

    /* Union into temp, then swap */
    tl_intervals_t temp;
    tl_intervals_init(&temp, alloc);

    tl_status_t st = tl_intervals_union_imm(&temp,
                                             tl_intervals_as_imm(accum),
                                             add);
    if (st != TL_OK) {
        tl_intervals_destroy(&temp);
        return st;
    }

    /* Swap temp into accum */
    tl_intervals_destroy(accum);
    *accum = temp;
    return TL_OK;
}

/**
 * Compute maximum delete debt ratio across all windows.
 * Used for delete_debt_threshold trigger.
 */
static double tl__compute_delete_debt(const tl_timelog_t* tl,
                                       const tl_manifest_t* m) {
    tl_intervals_t tombs;
    tl_intervals_init(&tombs, (tl_alloc_ctx_t*)&tl->alloc);

    /* Collect all tombstones from L0 using the safe union helper. */
    for (uint32_t i = 0; i < tl_manifest_l0_count(m); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(m, i);
        if (tl_segment_has_tombstones(seg)) {
            tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
            /* Use safe union helper - ignore errors for this heuristic */
            tl__tombs_union_into(&tombs, seg_tombs, (tl_alloc_ctx_t*)&tl->alloc);
        }
    }

    if (tl_intervals_is_empty(&tombs)) {
        tl_intervals_destroy(&tombs);
        return 0.0;
    }

    /* Find max delete debt ratio per window */
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

    /* All tombstones are bounded - safe to iterate.
     * Use tomb_max = end - 1 for half-open semantics: tombstone [start, end)
     * covers timestamps up to end-1, so we need the window containing end-1,
     * not the window containing end (which may be the NEXT window). */
    tl_ts_t tomb_min = tl_intervals_get(&tombs, 0)->start;
    tl_ts_t tomb_max = (last_tomb->end > TL_TS_MIN) ? (last_tomb->end - 1) : TL_TS_MIN;

    int64_t min_wid, max_wid;
    tl_status_t st;

    /* Handle window ID computation with overflow protection */
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

    /* Cap window iteration to prevent DoS from adversarial inputs.
     * If span is huge, assume max debt - this is a heuristic anyway.
     *
     * C-12 fix: Use overflow-safe subtraction for window span.
     * Direct subtraction can overflow if window IDs have opposite signs
     * (e.g., min_wid = -INT64_MAX/2, max_wid = INT64_MAX/2). */
    const int64_t MAX_DEBT_WINDOWS = 1000;
    int64_t debt_span;
    if (tl_sub_overflow_i64(max_wid, min_wid, &debt_span)) {
        /* Overflow - conservatively assume high debt */
        tl_intervals_destroy(&tombs);
        return 1.0;
    }
    if (debt_span < 0 || debt_span > MAX_DEBT_WINDOWS) {
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
 * Phase 1: Trigger Logic
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

    /* Trigger 1: L0 count threshold */
    if (tl_manifest_l0_count(m) >= tl->config.max_delta_segments) {
        needed = true;
        goto done;
    }

    /* Trigger 2: Delete debt threshold (optional) */
    if (tl->config.delete_debt_threshold > 0.0) {
        /* Compute per-window delete debt
         * This is expensive - only do if threshold is configured */
        if (tl__compute_delete_debt(tl, m) >= tl->config.delete_debt_threshold) {
            needed = true;
            goto done;
        }
    }

    /* Trigger 3: Explicit request via tl_compact() sets compact_pending
     * This is checked by caller (worker loop) via pending flag */

done:
    tl_manifest_release(m);
    return needed;
}

/*===========================================================================
 * Phase 2: Selection
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
 * Select overlapping L1 segments using WINDOW BOUNDS.
 *
 * Per Compaction Policy LLD Section 6.1: "Select all L1 segments whose
 * windows intersect those window_ids". This must use window bounds
 * (window_start/window_end), NOT record bounds (min_ts/max_ts).
 *
 * CRITICAL INVARIANT: L1 selection must be based on window bounds to
 * maintain L1 non-overlap. Using min_ts/max_ts would cause spurious
 * overlap detection and potential correctness issues.
 *
 * @param ctx  Context with output_min_wid/output_max_wid already set
 * @param m    Pinned manifest to select from
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
static tl_status_t tl__compact_select_l1(tl_compact_ctx_t* ctx,
                                          const tl_manifest_t* m) {
    /* Compute output WINDOW bounds for L1 selection */
    tl_ts_t output_first_wstart, output_first_wend;
    bool output_first_unbounded;
    tl_window_bounds(ctx->output_min_wid, ctx->window_size, ctx->window_origin,
                      &output_first_wstart, &output_first_wend, &output_first_unbounded);

    tl_ts_t output_last_wstart, output_last_wend;
    bool output_last_unbounded;
    tl_window_bounds(ctx->output_max_wid, ctx->window_size, ctx->window_origin,
                      &output_last_wstart, &output_last_wend, &output_last_unbounded);

    /* Count and pin overlapping L1 segments */
    uint32_t n_l1 = tl_manifest_l1_count(m);
    if (n_l1 == 0) {
        return TL_OK;  /* No L1 segments to select */
    }

    /* Count overlapping L1 segments first */
    size_t overlap_count = 0;
    for (uint32_t i = 0; i < n_l1; i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(m, i);
        if (tl__l1_overlaps_window_range(seg, output_first_wstart,
                                          output_last_wend, output_last_unbounded)) {
            overlap_count++;
        }
    }

    if (overlap_count == 0) {
        return TL_OK;  /* No overlapping L1 segments */
    }

    ctx->input_l1 = (tl_segment_t**)tl__malloc(ctx->alloc,
                                                overlap_count * sizeof(tl_segment_t*));
    if (ctx->input_l1 == NULL) {
        return TL_ENOMEM;
    }

    /* Pin overlapping L1 segments */
    for (uint32_t i = 0; i < n_l1; i++) {
        tl_segment_t* seg = tl_manifest_l1_get(m, i);
        if (tl__l1_overlaps_window_range(seg, output_first_wstart,
                                          output_last_wend, output_last_unbounded)) {
            ctx->input_l1[ctx->input_l1_len++] = tl_segment_acquire(seg);
        }
    }

    return TL_OK;
}

/**
 * Greedy L0 selection (original algorithm).
 *
 * Accumulates L0 segments until one of the caps is hit:
 * - max_compaction_inputs
 * - max_compaction_windows (via expanding bounds check)
 * - compaction_target_bytes
 *
 * IMPORTANT: This function MUST NOT re-pin manifest or re-increment next_gen.
 * The caller (tl_compact_select) has already done this. The manifest is passed
 * as parameter to make this explicit.
 *
 * @param ctx        Context with base_manifest already pinned
 * @param m          Pinned manifest (same as ctx->base_manifest)
 * @param max_inputs Max L0 inputs (0 = unlimited)
 * @return TL_OK on success, TL_EOF if no L0s, TL_ENOMEM/TL_EOVERFLOW on error
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
            if (seg->record_count > SIZE_MAX / sizeof(tl_record_t)) {
                seg_bytes = SIZE_MAX;
            } else {
                seg_bytes = (size_t)seg->record_count * sizeof(tl_record_t);
            }

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
 * Phase 2: Selection - Entry Point
 *===========================================================================*/

tl_status_t tl_compact_select(tl_compact_ctx_t* ctx) {
    tl_timelog_t* tl = ctx->tl;

    /* Pin current manifest.
     * NOTE: next_gen is protected by writer_mu per lock hierarchy. */
    TL_LOCK_WRITER(tl);
    ctx->base_manifest = tl_manifest_acquire(tl->manifest);
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
        return TL_EOF;
    }

    size_t max_inputs = (size_t)tl->config.max_compaction_inputs;

    return tl__compact_select_greedy(ctx, m, max_inputs);
}

/*===========================================================================
 * Phase 3: Merge - Helpers
 *===========================================================================*/

/**
 * Ensure output_l1 array has capacity for at least one more segment.
 * Grows the array geometrically (2x) when needed.
 */
static tl_status_t tl__ensure_output_capacity(tl_compact_ctx_t* ctx) {
    if (ctx->output_l1_len < ctx->output_l1_cap) {
        return TL_OK;  /* Already have space */
    }

    /* Grow capacity: start at 16, then double */
    size_t new_cap = (ctx->output_l1_cap == 0) ? 16 : ctx->output_l1_cap * 2;

    /* Overflow guard: check that new_cap * sizeof(ptr) doesn't wrap */
    if (new_cap > SIZE_MAX / sizeof(tl_segment_t*)) {
        return TL_EOVERFLOW;
    }

    tl_segment_t** new_arr = (tl_segment_t**)tl__realloc(ctx->alloc,
                                                          (void*)ctx->output_l1,
                                                          new_cap * sizeof(tl_segment_t*));
    if (new_arr == NULL) {
        return TL_ENOMEM;
    }

    /* Zero out the new portion */
    for (size_t i = ctx->output_l1_cap; i < new_cap; i++) {
        new_arr[i] = NULL;
    }

    ctx->output_l1 = new_arr;
    ctx->output_l1_cap = new_cap;
    return TL_OK;
}

/**
 * Push a dropped record to the deferred drop list.
 * Grows the array geometrically (2x) when needed.
 */
static tl_status_t tl__push_dropped_record(tl_compact_ctx_t* ctx,
                                            tl_ts_t ts,
                                            tl_handle_t handle) {
    /* Ensure capacity */
    if (ctx->dropped_len >= ctx->dropped_cap) {
        size_t new_cap = (ctx->dropped_cap == 0) ? 64 : ctx->dropped_cap * 2;

        /* Overflow guard */
        if (new_cap > SIZE_MAX / sizeof(tl_record_t)) {
            return TL_EOVERFLOW;
        }

        tl_record_t* new_arr = tl__realloc(ctx->alloc, ctx->dropped_records,
                                            new_cap * sizeof(tl_record_t));
        if (new_arr == NULL) {
            return TL_ENOMEM;
        }

        ctx->dropped_records = new_arr;
        ctx->dropped_cap = new_cap;
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
                tl_status_t st = tl_intervals_insert(&residual, t->start, res_end);
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
                tl_status_t st = tl_intervals_insert_unbounded(&residual, res_start);
                if (st != TL_OK) {
                    tl_intervals_destroy(&residual);
                    return st;
                }
            } else if (t->end > last_w_end) {
                tl_ts_t res_start = TL_MAX(t->start, last_w_end);
                if (res_start < t->end) {
                    tl_status_t st = tl_intervals_insert(&residual, res_start, t->end);
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
 * Phase 3: Merge
 *===========================================================================*/

tl_status_t tl_compact_merge(tl_compact_ctx_t* ctx) {
    tl_status_t st;

    /* ===================================================================
     * Step 1: Build effective tombstone set
     * Per Compaction Policy LLD Section 7.2
     *
     * Note: tombs was initialized in ctx_init; use clear() not init()
     * to avoid leak if merge is called multiple times.
     * =================================================================== */
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

    /* Step 1b: Create clipped copy of tombstones for filtering.
     * Keep original tombs for residual computation (done after merge).
     *
     * Note: tombs_clipped was initialized in ctx_init; use clear() not init(). */
    tl_intervals_clear(&ctx->tombs_clipped);
    for (size_t i = 0; i < tl_intervals_len(&ctx->tombs); i++) {
        const tl_interval_t* t = tl_intervals_get(&ctx->tombs, i);
        if (t->end_unbounded) {
            st = tl_intervals_insert_unbounded(&ctx->tombs_clipped, t->start);
        } else {
            st = tl_intervals_insert(&ctx->tombs_clipped, t->start, t->end);
        }
        if (st != TL_OK) return st;
    }

    /* Clip to output window range [first_window_start, last_window_end) */
    tl_ts_t first_start, first_end;
    bool first_unbounded;
    tl_window_bounds(ctx->output_min_wid, ctx->window_size, ctx->window_origin,
                      &first_start, &first_end, &first_unbounded);

    tl_ts_t last_start, last_end;
    bool last_unbounded;
    tl_window_bounds(ctx->output_max_wid, ctx->window_size, ctx->window_origin,
                      &last_start, &last_end, &last_unbounded);

    if (!last_unbounded) {
        tl_intervals_clip(&ctx->tombs_clipped, first_start, last_end);
    } else {
        tl_intervals_clip_lower(&ctx->tombs_clipped, first_start);
    }

    /* ===================================================================
     * Step 2: Build input iterators and initialize K-way merge
     *
     * We use segment iterators directly + heap for custom merge.
     * Cannot reuse tl_kmerge_iter_t (expects query plan sources).
     * =================================================================== */
    size_t total_inputs = ctx->input_l0_len + ctx->input_l1_len;
    tl_segment_iter_t* iters = tl__calloc(ctx->alloc, total_inputs,
                                           sizeof(tl_segment_iter_t));
    if (iters == NULL) {
        return TL_ENOMEM;
    }

    /* Initialize segment iterators (unbounded range - all records) */
    size_t iter_idx = 0;
    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        tl_segment_iter_init(&iters[iter_idx++], ctx->input_l0[i],
                              TL_TS_MIN, 0, true);  /* [TL_TS_MIN, +inf) */
    }
    for (size_t i = 0; i < ctx->input_l1_len; i++) {
        tl_segment_iter_init(&iters[iter_idx++], ctx->input_l1[i],
                              TL_TS_MIN, 0, true);
    }

    /* Build heap for K-way merge. */
    tl_heap_t heap;
    tl_heap_init(&heap, ctx->alloc);
    st = tl_heap_reserve(&heap, total_inputs);
    if (st != TL_OK) {
        tl__free(ctx->alloc, iters);
        return st;
    }

    /* Prime heap with first record from each iterator. */
    for (size_t i = 0; i < total_inputs; i++) {
        tl_record_t rec;
        if (tl_segment_iter_next(&iters[i], &rec) == TL_OK) {
            tl_heap_entry_t entry = {
                .ts = rec.ts,
                .handle = rec.handle,
                .component_id = (uint32_t)i,
                .iter = &iters[i]  /* Store iterator pointer for refill */
            };
            st = tl_heap_push(&heap, &entry);
            if (st != TL_OK) {
                tl_heap_destroy(&heap);
                tl__free(ctx->alloc, iters);
                return st;
            }
        }
    }

    /* ===================================================================
     * Step 3: K-way merge with tombstone filtering and window partitioning
     * =================================================================== */

    /* Initialize tombstone cursor for filtering (use CLIPPED tombstones) */
    tl_intervals_cursor_t tomb_cursor;
    tl_intervals_cursor_init(&tomb_cursor, tl_intervals_as_imm(&ctx->tombs_clipped));

    /* Window state for output partitioning */
    int64_t current_wid = ctx->output_min_wid;
    tl_ts_t current_window_start, current_window_end;
    bool current_end_unbounded;
    tl_window_bounds(current_wid, ctx->window_size, ctx->window_origin,
                      &current_window_start, &current_window_end,
                      &current_end_unbounded);

    /* Current window accumulator */
    tl_recvec_t window_records;
    tl_recvec_init(&window_records, ctx->alloc);

    /* Output array starts empty and grows dynamically via tl__ensure_output_capacity().
     * This avoids pre-allocating based on window span, which would fail for
     * TL_TS_MAX records (trillions of windows with default 1-hour size). */

    /* Process merged stream */
    while (!tl_heap_is_empty(&heap)) {
        tl_heap_entry_t min_entry;
        st = tl_heap_pop(&heap, &min_entry);
        if (st != TL_OK) break;

        /* Refill heap from the source that provided this record */
        tl_segment_iter_t* source_iter = (tl_segment_iter_t*)min_entry.iter;
        tl_record_t next_rec;
        if (tl_segment_iter_next(source_iter, &next_rec) == TL_OK) {
            tl_heap_entry_t refill = {
                .ts = next_rec.ts,
                .handle = next_rec.handle,
                .component_id = min_entry.component_id,
                .iter = min_entry.iter
            };
            st = tl_heap_push(&heap, &refill);
            if (st != TL_OK) {
                goto cleanup;
            }
        }

        /* Check if record is deleted by tombstone */
        if (tl_intervals_cursor_is_deleted(&tomb_cursor, min_entry.ts)) {
            /* Record is deleted - collect for deferred callback.
             *
             * CRITICAL: We do NOT invoke on_drop_handle here because:
             * 1. Compaction may fail (ENOMEM) after this point
             * 2. Publish may fail (EBUSY) requiring retry
             * 3. If we fire callbacks now and then fail, user code may
             *    free payloads for records that are STILL VISIBLE
             *
             * Callbacks are fired only after successful publish. */
            if (ctx->on_drop_handle != NULL) {
                st = tl__push_dropped_record(ctx, min_entry.ts, min_entry.handle);
                if (st != TL_OK) {
                    goto cleanup;
                }
            }
            continue;  /* Skip this record */
        }

        /* Determine which window this record belongs to */
        int64_t rec_wid;
        st = tl_window_id_for_ts(min_entry.ts, ctx->window_size,
                                  ctx->window_origin, &rec_wid);
        if (st != TL_OK) {
            goto cleanup;
        }

        /* If we've moved to a new window, flush the current window and jump.
         * IMPORTANT: We jump directly to rec_wid instead of iterating through
         * empty intermediate windows. This makes compaction O(records) instead
         * of O(windows), which matters for sparse data spanning wide time ranges
         * (e.g., records at ts=0 and ts=TL_TS_MAX). */
        if (current_wid < rec_wid) {
            /* Flush current window (may be empty - that's fine) */
            st = tl__flush_window_records(ctx, &window_records,
                                           current_window_start, current_window_end,
                                           current_end_unbounded);
            if (st != TL_OK) {
                goto cleanup;
            }

            /* Jump directly to the window containing this record */
            current_wid = rec_wid;
            tl_window_bounds(current_wid, ctx->window_size, ctx->window_origin,
                              &current_window_start, &current_window_end,
                              &current_end_unbounded);
        }

        /* Add record to current window accumulator.
         * tl_recvec_push takes (ts, handle) separately, not a record struct. */
        st = tl_recvec_push(&window_records, min_entry.ts, min_entry.handle);
        if (st != TL_OK) {
            goto cleanup;
        }
    }

    /* Flush final window (may be unbounded if contains TL_TS_MAX records) */
    st = tl__flush_window_records(ctx, &window_records,
                                   current_window_start, current_window_end,
                                   current_end_unbounded);
    if (st != TL_OK) {
        goto cleanup;
    }

    /* ===================================================================
     * Step 4: Handle residual tombstones
     * =================================================================== */
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

/**
 * Build a manifest with our compaction changes applied.
 *
 * This is the "off-lock" expensive work for L0→L1 compaction.
 *
 * @param ctx           Compaction context
 * @param base          Base manifest to build from
 * @param out           Output manifest pointer
 * @return TL_OK on success, TL_ENOMEM on failure
 */
static tl_status_t tl__build_compaction_manifest(tl_compact_ctx_t* ctx,
                                                   const tl_manifest_t* base,
                                                   tl_manifest_t** out) {
    tl_status_t st;
    tl_manifest_builder_t builder;
    /* Cast away const - builder init doesn't modify base, only copies pointers */
    tl_manifest_builder_init(&builder, ctx->alloc, (tl_manifest_t*)base);

    /* Queue removal of input L0 segments */
    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        st = tl_manifest_builder_remove_l0(&builder, ctx->input_l0[i]);
        if (st != TL_OK) {
            tl_manifest_builder_destroy(&builder);
            return st;
        }
    }

    /* Queue removal of input L1 segments */
    for (size_t i = 0; i < ctx->input_l1_len; i++) {
        st = tl_manifest_builder_remove_l1(&builder, ctx->input_l1[i]);
        if (st != TL_OK) {
            tl_manifest_builder_destroy(&builder);
            return st;
        }
    }

    /* Queue addition of output L1 segments */
    for (size_t i = 0; i < ctx->output_l1_len; i++) {
        st = tl_manifest_builder_add_l1(&builder, ctx->output_l1[i]);
        if (st != TL_OK) {
            tl_manifest_builder_destroy(&builder);
            return st;
        }
    }

    /* Add residual tombstone segment (if any) */
    if (ctx->residual_tomb != NULL) {
        st = tl_manifest_builder_add_l0(&builder, ctx->residual_tomb);
        if (st != TL_OK) {
            tl_manifest_builder_destroy(&builder);
            return st;
        }
    }

    /* Build new manifest */
    st = tl_manifest_builder_build(&builder, out);
    tl_manifest_builder_destroy(&builder);
    return st;
}

/*===========================================================================
 * Phase 4: Publication
 *===========================================================================*/

tl_status_t tl_compact_publish(tl_compact_ctx_t* ctx) {
    tl_timelog_t* tl = ctx->tl;
    tl_status_t st;

#ifdef TL_TEST_HOOKS
    /* Test hook: force EBUSY returns for deterministic retry exhaustion testing.
     * Decrement counter and return EBUSY without doing any work. */
    if (tl_test_force_ebusy_count > 0) {
        tl_test_force_ebusy_count--;
        return TL_EBUSY;
    }
#endif

    /*
     * Phase 1: Build new manifest OFF-LOCK (allocation happens here).
     * Build assuming base_manifest is still current.
     * Per timelog_v1_lld_background_maintenance.md: "Long-running build
     * phases must not hold writer_mu."
     */
    tl_manifest_t* new_manifest = NULL;
    st = tl__build_compaction_manifest(ctx, ctx->base_manifest, &new_manifest);
    if (st != TL_OK) {
        return st;
    }

    /*
     * Phase 2: Validate and swap under lock.
     * NO ALLOCATION beyond this point (all builds happen off-lock).
     */
    TL_LOCK_WRITER(tl);

    /* C-09: Strict publish validation.
     *
     * Check if manifest changed during merge (concurrent flush or compaction).
     * If changed, return TL_EBUSY to force retry from fresh selection.
     *
     * This is the "strict publish" protocol (V1):
     * - Discards merge result if manifest diverged
     * - Caller retries with new selection or fails after max_retries
     *
     * See tl__compact_one_step() for retry logic and Phase-2 deferred notes. */
    if (tl->manifest != ctx->base_manifest) {
        /* Manifest changed - caller must retry with fresh selection */
        TL_UNLOCK_WRITER(tl);
        tl_manifest_release(new_manifest);
        return TL_EBUSY;
    }

    /* Enter seqlock region for actual swap */
    tl_seqlock_write_begin(&tl->view_seq);

    /* Swap manifest */
    tl_manifest_t* old_manifest = tl->manifest;
    tl->manifest = new_manifest;

    tl_seqlock_write_end(&tl->view_seq);

#ifndef NDEBUG
    /* C-13 fix: Pin the exact manifest we just published for validation.
     * MUST happen before unlock - a concurrent flush could otherwise
     * replace and release new_manifest before we validate it.
     *
     * Race condition prevented:
     * Without this pin, a concurrent flush could:
     * 1. Acquire writer_mu after we release it
     * 2. Replace tl->manifest with flush_manifest
     * 3. Release old = new_manifest (refcnt goes to 0)
     * 4. Free new_manifest
     * Then our validation call below would be UAF.
     *
     * By acquiring before unlock, we ensure refcnt >= 2 while we hold it,
     * so even if flush replaces and releases, our copy survives. */
    tl_manifest_t* validate_m = tl_manifest_acquire(new_manifest);
#endif

    TL_UNLOCK_WRITER(tl);

    /* Release old manifest (safe after unlock) */
    tl_manifest_release(old_manifest);

#ifndef NDEBUG
    /* Validate the exact manifest we published (not current tl->manifest).
     * Using validate_m ensures we check what we built, not what a concurrent
     * flush might have replaced it with. */
    tl__validate_l1_non_overlap(validate_m);
    tl_manifest_release(validate_m);
#endif

    /* NOTE: We do NOT clear output_l1_len or residual_tomb here.
     *
     * Ownership semantics:
     * - ctx built output segments (ctx has refs)
     * - manifest_builder_build() acquired refs (manifest has refs)
     * - Both refs are valid and independent
     *
     * ctx_destroy will release ctx's refs, leaving manifest's refs.
     * This is correct reference counting semantics. */

    return TL_OK;
}

/*===========================================================================
 * Main Entry Point
 *===========================================================================*/

tl_status_t tl_compact_one(tl_timelog_t* tl, int max_retries) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(max_retries > 0);  /* Ensures publish loop executes at least once */

    /*-----------------------------------------------------------------------
     * Adaptive Segmentation Integration
     *
     * 1. Compute candidate window BEFORE ctx_init (under maint_mu)
     * 2. Set effective_window_size for ctx to use
     * 3. After compaction completes: record success/failure under maint_mu
     * 4. On failure: restore original window (under maint_mu)
     *
     * Lock note: ALL reads and writes of effective_window_size and adaptive
     * state occur under maint_mu to avoid data races, even though the
     * maintenance thread is typically the only accessor.
     *-----------------------------------------------------------------------*/
    tl_ts_t original_window;
    tl_ts_t candidate_window;

    TL_LOCK_MAINT(tl);
    original_window = tl->effective_window_size;
    candidate_window = original_window;

    /* C-10: Only compute adaptive candidate if grid is NOT frozen.
     * Once L1 segments exist, the window grid is frozen to prevent
     * L1 overlap violations from window size changes. */
    if (!tl->window_grid_frozen && tl->config.adaptive.target_records > 0) {
        /* Compute candidate under maint_mu (reads adaptive state) */
        candidate_window = tl_adaptive_compute_candidate(
            &tl->adaptive,
            &tl->config.adaptive,
            original_window);
        /* Note: DO NOT set effective_window_size here - LLD-strict commit
         * only after successful publish. Override ctx.window_size instead. */
    }
    TL_UNLOCK_MAINT(tl);

    tl_compact_ctx_t ctx;
    tl_compact_ctx_init(&ctx, tl, &tl->alloc, candidate_window);

    tl_status_t st;

    /* Phase 1: Selection */
    st = tl_compact_select(&ctx);
    if (st != TL_OK) {
        tl_compact_ctx_destroy(&ctx);
        /* Adaptive: record failure for ENOMEM (no restore needed - we didn't
         * commit to effective_window_size). TL_EOF (no work) is not a failure. */
        if (tl->config.adaptive.target_records > 0 && st == TL_ENOMEM) {
            TL_LOCK_MAINT(tl);
            tl_adaptive_record_failure(&tl->adaptive);
            TL_UNLOCK_MAINT(tl);
        }
        return st;  /* TL_EOF = no work, TL_ENOMEM = error */
    }

    /* Phase 2: Merge */
    st = tl_compact_merge(&ctx);
    if (st != TL_OK) {
        tl_compact_ctx_destroy(&ctx);
        if (tl->config.adaptive.target_records > 0 && st == TL_ENOMEM) {
            TL_LOCK_MAINT(tl);
            tl_adaptive_record_failure(&tl->adaptive);
            TL_UNLOCK_MAINT(tl);
        }
        return st;
    }

    /* Phase 3: Publish with retries
     *
     * C-09 Documentation: STRICT PUBLISH vs REBASE
     *
     * Current behavior (V1): Strict publish with bounded retries.
     * If the manifest changed during merge (concurrent flush), we:
     * 1. Discard the merge result (return TL_EBUSY)
     * 2. Retry from fresh selection (up to max_retries attempts)
     * 3. If retries exhausted, compaction fails and returns TL_EBUSY
     *
     * Alternative (Phase-2 deferred): Rebase strategy.
     * Instead of discarding, rebuild manifest incorporating the concurrent
     * change while preserving our merge result. This avoids wasted work
     * under high flush rates but adds complexity.
     *
     * V1 rationale:
     * - Simplicity: Strict publish is straightforward to implement correctly
     * - Correctness: No risk of ordering bugs in rebase logic
     * - Acceptable for typical workloads: Concurrent flush during compaction
     *   is rare unless flush rate exceeds compaction rate significantly
     *
     * Livelock risk:
     * - Under extreme flush rates, compaction may repeatedly fail to publish
     * - max_retries (3) bounds wasted CPU, but L0 segments accumulate
     * - Mitigation: Increase flush_interval or reduce memtable size to lower
     *   flush rate relative to compaction time
     *
     * Reference: Compaction LLD Section 8.2 (Publication Protocol)
     */
    tl_status_t publish_st = TL_EBUSY;
    for (int attempt = 0; attempt < max_retries; attempt++) {
        publish_st = tl_compact_publish(&ctx);
        if (publish_st != TL_EBUSY) {
            /* Success or fatal error - stop retrying */
            if (publish_st == TL_OK) {
                /* Publication succeeded - NOW fire deferred drop callbacks.
                 *
                 * CRITICAL: These callbacks are only safe to fire AFTER
                 * successful publication because:
                 * 1. Records are now truly retired from the newest manifest
                 * 2. No retry will re-process these records
                 * 3. User code can safely begin their reclamation process
                 *
                 * Note: Existing snapshots may still reference these records
                 * until released - user must use epoch/RCU/grace period. */
                if (ctx.on_drop_handle != NULL) {
                    for (size_t i = 0; i < ctx.dropped_len; i++) {
                        ctx.on_drop_handle(ctx.on_drop_ctx,
                                           ctx.dropped_records[i].ts,
                                           ctx.dropped_records[i].handle);
                    }
                }

                /* Increment compaction counter */
                tl_atomic_inc_u64(&tl->compactions_total);

                /* Post-publish maint_mu block: C-10 grid freeze + adaptive updates.
                 *
                 * C-10: Freeze window grid after first L1 creation.
                 * Once frozen, adaptive segmentation cannot change window size.
                 *
                 * Adaptive: Commit window and record success.
                 * THIS is when we commit effective_window_size (LLD-strict).
                 *
                 * Both checks in one lock acquisition for efficiency. */
                if (ctx.output_l1_len > 0 || tl->config.adaptive.target_records > 0) {
                    TL_LOCK_MAINT(tl);

                    /* C-10: Freeze grid after first L1 creation.
                     * This prevents future adaptive changes from breaking
                     * L1 non-overlap invariant with existing segments. */
                    if (ctx.output_l1_len > 0) {
                        tl->window_grid_frozen = true;
                    }

                    /* Adaptive: commit window and record success */
                    if (tl->config.adaptive.target_records > 0) {
                        tl->effective_window_size = candidate_window;
                        tl_adaptive_record_success(&tl->adaptive);
                    }

                    TL_UNLOCK_MAINT(tl);
                }
            } else {
                /* Fatal error (ENOMEM) - record failure (no restore needed) */
                if (tl->config.adaptive.target_records > 0 && publish_st == TL_ENOMEM) {
                    TL_LOCK_MAINT(tl);
                    tl_adaptive_record_failure(&tl->adaptive);
                    TL_UNLOCK_MAINT(tl);
                }
            }
            tl_compact_ctx_destroy(&ctx);
            return publish_st;
        }

        /* Publish returned EBUSY (manifest changed). Count and retry. */
        tl_atomic_inc_u64(&tl->compaction_publish_ebusy);
        if (attempt + 1 < max_retries) {
            tl_atomic_inc_u64(&tl->compaction_retries);
        }

        /* Manifest changed - re-select and re-merge for retry.
         * This is expensive but correct - ensures we don't publish
         * stale outputs. */
        tl_compact_ctx_destroy(&ctx);
        tl_compact_ctx_init(&ctx, tl, &tl->alloc, candidate_window);

        st = tl_compact_select(&ctx);
        if (st != TL_OK) {
            tl_compact_ctx_destroy(&ctx);
            if (tl->config.adaptive.target_records > 0 && st == TL_ENOMEM) {
                TL_LOCK_MAINT(tl);
                tl_adaptive_record_failure(&tl->adaptive);
                TL_UNLOCK_MAINT(tl);
            }
            return st;
        }

        st = tl_compact_merge(&ctx);
        if (st != TL_OK) {
            tl_compact_ctx_destroy(&ctx);
            if (tl->config.adaptive.target_records > 0 && st == TL_ENOMEM) {
                TL_LOCK_MAINT(tl);
                tl_adaptive_record_failure(&tl->adaptive);
                TL_UNLOCK_MAINT(tl);
            }
            return st;
        }
    }

    /* Retries exhausted - EBUSY is counted as failure per LLD */
    tl_compact_ctx_destroy(&ctx);
    if (tl->config.adaptive.target_records > 0) {
        TL_LOCK_MAINT(tl);
        tl_adaptive_record_failure(&tl->adaptive);  /* EBUSY counts as failure */
        TL_UNLOCK_MAINT(tl);
    }
    return publish_st;
}
