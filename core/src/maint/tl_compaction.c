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
                          tl_alloc_ctx_t* alloc) {
    TL_ASSERT(ctx != NULL);
    TL_ASSERT(tl != NULL);
    TL_ASSERT(alloc != NULL);

    memset(ctx, 0, sizeof(*ctx));
    ctx->tl = tl;
    ctx->alloc = alloc;

    /* Copy config values */
    ctx->window_size = tl->effective_window_size;
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
    tl__free(ctx->alloc, ctx->input_l0);
    ctx->input_l0 = NULL;
    ctx->input_l0_len = 0;

    for (size_t i = 0; i < ctx->input_l1_len; i++) {
        if (ctx->input_l1[i] != NULL) {
            tl_segment_release(ctx->input_l1[i]);
        }
    }
    tl__free(ctx->alloc, ctx->input_l1);
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
    tl__free(ctx->alloc, ctx->output_l1);
    ctx->output_l1 = NULL;
    ctx->output_l1_len = 0;
    ctx->output_l1_cap = 0;

    /* Release unpublished output L0 segments (Phase 2: reshape) */
    for (size_t i = 0; i < ctx->output_l0_len; i++) {
        if (ctx->output_l0[i] != NULL) {
            tl_segment_release(ctx->output_l0[i]);
        }
    }
    tl__free(ctx->alloc, ctx->output_l0);
    ctx->output_l0 = NULL;
    ctx->output_l0_len = 0;
    ctx->output_l0_cap = 0;

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
     * If span is huge, assume max debt - this is a heuristic anyway. */
    const int64_t MAX_DEBT_WINDOWS = 1000;
    if (max_wid - min_wid > MAX_DEBT_WINDOWS) {
        tl_intervals_destroy(&tombs);
        return 1.0;  /* Assume high debt for large spans */
    }

    for (int64_t wid = min_wid; wid <= max_wid; wid++) {
        tl_ts_t w_start, w_end;
        bool w_unbounded;
        tl_window_bounds(wid, window_size, tl->config.window_origin,
                          &w_start, &w_end, &w_unbounded);

        /* Skip unbounded windows for delete debt (infinite debt is meaningless) */
        if (w_unbounded) {
            continue;
        }

        /* Clip tombstones to window and compute covered span. */
        tl_intervals_t clipped;
        tl_intervals_init(&clipped, (tl_alloc_ctx_t*)&tl->alloc);
        for (size_t i = 0; i < tl_intervals_len(&tombs); i++) {
            const tl_interval_t* t = tl_intervals_get(&tombs, i);
            if (t->end_unbounded) {
                tl_intervals_insert_unbounded(&clipped, t->start);
            } else {
                tl_intervals_insert(&clipped, t->start, t->end);
            }
        }
        /* Clip to bounded window - this converts any unbounded to bounded */
        tl_intervals_clip(&clipped, w_start, w_end);

        tl_ts_t span = tl_intervals_covered_span(&clipped);
        double ratio = (double)span / (double)window_size;
        if (ratio > max_ratio) {
            max_ratio = ratio;
        }

        tl_intervals_destroy(&clipped);
    }

    tl_intervals_destroy(&tombs);
    return max_ratio;
}

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
 * Phase 2 Selection: Helper Functions
 *
 * These helpers support window-bounded selection (Phase 2 OOO Scaling).
 * The selection path is: tl_compact_select() pins manifest and dispatches to
 * either window-bounded or greedy selection, both of which call into the
 * shared L1 selection helper.
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

    ctx->input_l1 = tl__malloc(ctx->alloc,
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
    ctx->input_l0 = tl__malloc(ctx->alloc, l0_count * sizeof(tl_segment_t*));
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
            /* Use overflow-safe subtraction.
             * On overflow or inverted range (diff < 0): treat as exceeding window cap.
             * This ensures we don't fail compaction - we just enforce the cap. */
            int64_t diff;
            if (tl_sub_overflow_i64(cand_max_wid, cand_min_wid, &diff) || diff < 0) {
                windows_exceed = true;
            } else {
                /* Safe: diff >= 0 and fits in int64_t. (uint64_t)diff + 1 fits in uint64_t. */
                uint64_t span = (uint64_t)diff + 1;
                windows_exceed = (span > max_windows);
            }
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
            } else if ((est_bytes + seg_bytes) > target_bytes) {
                bytes_exceed = true;
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

/**
 * Window-bounded L0 selection (Phase 2 OOO Scaling).
 *
 * Instead of greedy accumulation, this algorithm:
 * 1. Finds the oldest L0 min_ts to anchor target window range
 * 2. Computes target range [target_wid_start, target_wid_start + max_windows - 1]
 * 3. Selects only L0 segments whose window range overlaps target range
 *
 * This bounds compaction scope under OOO workloads, preventing the
 * quadratic throughput collapse seen with greedy selection on wide spans.
 *
 * If no L0s overlap the target window range, falls back to greedy selection
 * to guarantee forward progress.
 *
 * @param ctx         Context with base_manifest already pinned
 * @param m           Pinned manifest
 * @param max_windows Max window span for target range (must be > 0)
 * @param max_inputs  Max L0 inputs (0 = unlimited)
 * @return TL_OK on success, TL_EOF if no L0s, TL_ENOMEM/TL_EOVERFLOW on error
 */
static tl_status_t tl__compact_select_window_bounded(tl_compact_ctx_t* ctx,
                                                       const tl_manifest_t* m,
                                                       uint64_t max_windows,
                                                       size_t max_inputs) {
    tl_timelog_t* tl = ctx->tl;
    tl_status_t st;
    uint32_t n_l0 = tl_manifest_l0_count(m);

    TL_ASSERT(max_windows > 0);  /* Caller guarantees this */

    if (n_l0 == 0) {
        return TL_EOF;
    }

    /* Step 1: Find oldest L0 min_ts to anchor target window range */
    tl_ts_t oldest_min_ts = TL_TS_MAX;
    for (uint32_t i = 0; i < n_l0; i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(m, i);
        if (seg->min_ts < oldest_min_ts) {
            oldest_min_ts = seg->min_ts;
        }
    }

    /* Step 2: Compute target window range [target_wid_start, target_wid_end] */
    int64_t target_wid_start;
    st = tl_window_id_for_ts(oldest_min_ts, ctx->window_size,
                              ctx->window_origin, &target_wid_start);
    if (st != TL_OK) {
        return st;
    }

    /* Overflow-safe computation of target_wid_end.
     * Handle both positive overflow (near INT64_MAX) and negative underflow. */
    int64_t target_wid_end;
    int64_t span_minus_one = (int64_t)(max_windows - 1);

    /* Check for overflow: target_wid_start + span_minus_one */
    if (target_wid_start > 0 && span_minus_one > INT64_MAX - target_wid_start) {
        target_wid_end = INT64_MAX;  /* Saturate on positive overflow */
    } else if (target_wid_start < 0 && span_minus_one < INT64_MIN - target_wid_start) {
        /* This shouldn't happen with positive span, but handle defensively */
        target_wid_end = target_wid_start;
    } else {
        target_wid_end = target_wid_start + span_minus_one;
    }

    /* Step 3: Allocate L0 input array */
    size_t l0_count = (size_t)n_l0;
    if (l0_count > SIZE_MAX / sizeof(tl_segment_t*)) {
        return TL_EOVERFLOW;
    }
    ctx->input_l0 = tl__malloc(ctx->alloc, l0_count * sizeof(tl_segment_t*));
    if (ctx->input_l0 == NULL) {
        return TL_ENOMEM;
    }

    /* Step 4: Select L0 segments overlapping target windows */
    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;

    for (uint32_t i = 0; i < n_l0; i++) {
        if (max_inputs > 0 && ctx->input_l0_len >= max_inputs) {
            break;
        }

        tl_segment_t* seg = tl_manifest_l0_get(m, i);

        /* Compute this segment's window range */
        int64_t seg_wid_min, seg_wid_max;
        st = tl_window_id_for_ts(seg->min_ts, ctx->window_size,
                                  ctx->window_origin, &seg_wid_min);
        if (st != TL_OK) {
            return st;
        }
        st = tl_window_id_for_ts(seg->max_ts, ctx->window_size,
                                  ctx->window_origin, &seg_wid_max);
        if (st != TL_OK) {
            return st;
        }

        /* Check overlap: [seg_wid_min, seg_wid_max] ∩ [target_wid_start, target_wid_end] */
        if (seg_wid_max < target_wid_start || seg_wid_min > target_wid_end) {
            /* No overlap - skip this segment */
            continue;
        }

        /* Track if this single L0 exceeds window cap (observability).
         * Use overflow-safe arithmetic to avoid UB. */
        int64_t diff;
        if (tl_sub_overflow_i64(seg_wid_max, seg_wid_min, &diff)) {
            /* Overflow in subtraction means astronomical span - definitely exceeds */
            tl_atomic_inc_u64(&tl->window_bound_exceeded);
        } else {
            /* Safe: diff >= 0 since seg_wid_max >= seg_wid_min for overlapping segs.
             * Add 1 for inclusive count, with overflow check. */
            int64_t seg_span = (diff <= INT64_MAX - 1) ? diff + 1 : INT64_MAX;
            if (seg_span > (int64_t)max_windows) {
                tl_atomic_inc_u64(&tl->window_bound_exceeded);
            }
        }

        /* Accept segment */
        ctx->input_l0[ctx->input_l0_len++] = tl_segment_acquire(seg);
        min_ts = TL_MIN(min_ts, seg->min_ts);
        max_ts = TL_MAX(max_ts, seg->max_ts);
    }

    /* Step 5: If no overlap found, fall back to greedy (forward progress guarantee).
     * This can happen if all L0s are outside the target range (unusual but possible). */
    if (ctx->input_l0_len == 0) {
        tl__free(ctx->alloc, ctx->input_l0);
        ctx->input_l0 = NULL;
        return tl__compact_select_greedy(ctx, m, max_inputs);
    }

    /* Step 6: Set output bounds and continue with L1 selection */
    ctx->output_min_ts = min_ts;
    ctx->output_max_ts = max_ts;

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
 * Phase 2d: Reshape Compaction - Trigger and Selection
 *
 * Reshape compaction (L0→L0) splits wide L0 segments into window-contained
 * pieces without merging with L1. This reduces fan-in for subsequent L0→L1
 * compaction, preventing quadratic throughput collapse under OOO workloads.
 *
 * Trigger conditions (OR logic):
 * 1. High L0 count: L0 count >= reshape_l0_threshold
 * 2. Wide span: L0 window span > max_compaction_windows (only if max_windows > 0)
 *
 * Cooldown prevents infinite reshape loops when workload is inherently wide.
 *===========================================================================*/

/**
 * Check if reshape compaction should be triggered.
 *
 * CRITICAL: Must pin manifest under writer_mu before reading it.
 * maint_mu does NOT protect manifest pointer - only writer_mu does.
 *
 * CONCURRENCY: This function reads `consecutive_reshapes` without holding
 * writer_mu. This is safe because tl_compact_one() is only called from
 * the maintenance worker which holds maint_mu, serializing all reads
 * and writes to consecutive_reshapes. Direct calls to tl_compact_one()
 * from user code must also be serialized externally.
 *
 * @param tl            Timelog instance
 * @param out_manifest  Output: pinned manifest (ALWAYS set, caller must ALWAYS
 *                      release unless ownership transferred to compact_ctx)
 * @return true if reshape should be triggered, false otherwise
 */
static bool tl__should_reshape(tl_timelog_t* tl, tl_manifest_t** out_manifest) {
    /* Pin manifest under brief lock (same pattern as tl_compact_select) */
    TL_LOCK_WRITER(tl);
    tl_manifest_t* m = tl_manifest_acquire(tl->manifest);
    TL_UNLOCK_WRITER(tl);

    *out_manifest = m;  /* Caller must release */

    uint32_t l0_count = tl_manifest_l0_count(m);

    /* No work: zero L0 segments */
    if (l0_count == 0) {
        return false;
    }

    /* Cooldown check (single-threaded access via maintenance serialization).
     * Prevents infinite reshape loops when workload is inherently wide. */
    if (tl->consecutive_reshapes >= tl->config.reshape_cooldown_max) {
        return false;
    }

    /* Condition 1: High L0 count triggers reshape (OR logic).
     * This helps when many small L0s would cause high merge fan-in. */
    if (l0_count >= tl->config.reshape_l0_threshold) {
        return true;
    }

    /* Condition 2: Wide span triggers reshape (only if max_windows > 0).
     * When window-bounded compaction is enabled, reshape helps split wide
     * L0s into manageable pieces before L0→L1 merge.
     *
     * LIMITATION: This uses global L0 span (min/max across ALL L0 segments),
     * not the span of the candidate window-bounded compaction. This can trigger
     * reshape unnecessarily when a stale far-past segment exists while current
     * backlog is narrow. A future optimization could compute span on the actual
     * compaction candidate to focus reshape where it matters most. */
    uint64_t max_windows = (uint64_t)tl->config.max_compaction_windows;
    if (max_windows == 0) {
        return false;  /* Unlimited mode: no span-based trigger */
    }

    /* Compute global L0 span (see LIMITATION above) */
    tl_ts_t min_ts = TL_TS_MAX, max_ts = TL_TS_MIN;
    for (uint32_t i = 0; i < l0_count; i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(m, i);
        min_ts = TL_MIN(min_ts, seg->min_ts);
        max_ts = TL_MAX(max_ts, seg->max_ts);
    }

    int64_t min_wid, max_wid;
    if (tl_window_id_for_ts(min_ts, tl->effective_window_size,
                            tl->config.window_origin, &min_wid) != TL_OK) {
        return false;
    }
    if (tl_window_id_for_ts(max_ts, tl->effective_window_size,
                            tl->config.window_origin, &max_wid) != TL_OK) {
        return false;
    }

    /* Calculate span using overflow-safe arithmetic.
     * If overflow occurs, span is astronomical - definitely exceeds. */
    int64_t diff;
    if (tl_sub_overflow_i64(max_wid, min_wid, &diff) || diff < 0) {
        return true;  /* Overflow or inverted range - trigger reshape */
    }
    /* Safe: diff >= 0 and fits in int64_t (otherwise subtraction would overflow).
     * Since diff <= INT64_MAX, (uint64_t)diff + 1 <= INT64_MAX + 1 which fits in uint64_t. */
    uint64_t span = (uint64_t)diff + 1;
    return span > max_windows;
}

/**
 * Select L0 segments for reshape compaction.
 *
 * Reshape selection is simpler than L0→L1:
 * - Select up to reshape_max_inputs oldest L0 segments
 * - NO L1 selection (reshape produces L0, not L1)
 * - Set is_reshape = true
 *
 * @param ctx      Compaction context (must have base_manifest NOT pinned yet)
 * @param pinned   Pre-pinned manifest from tl__should_reshape (ownership transfers)
 * @return TL_OK on success, TL_EOF if no L0s, TL_ENOMEM on failure
 */
static tl_status_t tl__compact_select_reshape(tl_compact_ctx_t* ctx,
                                               tl_manifest_t* pinned) {
    tl_timelog_t* tl = ctx->tl;

    /* Transfer ownership of pinned manifest to ctx */
    ctx->base_manifest = pinned;

    /* Get next generation under writer_mu */
    TL_LOCK_WRITER(tl);
    ctx->generation = tl->next_gen++;
    TL_UNLOCK_WRITER(tl);

    uint32_t max_inputs = tl->config.reshape_max_inputs;
    uint32_t n_l0 = tl_manifest_l0_count(pinned);

    if (n_l0 == 0) {
        return TL_EOF;
    }

    /* Select up to max_inputs oldest L0s */
    uint32_t to_select = TL_MIN(max_inputs, n_l0);

    ctx->input_l0 = tl__malloc(ctx->alloc, to_select * sizeof(tl_segment_t*));
    if (ctx->input_l0 == NULL) {
        return TL_ENOMEM;
    }

    for (uint32_t i = 0; i < to_select; i++) {
        ctx->input_l0[ctx->input_l0_len++] =
            tl_segment_acquire(tl_manifest_l0_get(pinned, i));
    }

    /* NO L1 selection for reshape */
    ctx->input_l1_len = 0;

    /* Mark as reshape mode */
    ctx->is_reshape = true;

    /* Compute output bounds (needed for merge) */
    tl_ts_t min_ts = TL_TS_MAX, max_ts = TL_TS_MIN;
    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        min_ts = TL_MIN(min_ts, ctx->input_l0[i]->min_ts);
        max_ts = TL_MAX(max_ts, ctx->input_l0[i]->max_ts);
    }

    ctx->output_min_ts = min_ts;
    ctx->output_max_ts = max_ts;

    tl_status_t st;
    st = tl_window_id_for_ts(min_ts, ctx->window_size,
                              ctx->window_origin, &ctx->output_min_wid);
    if (st != TL_OK) return st;

    st = tl_window_id_for_ts(max_ts, ctx->window_size,
                              ctx->window_origin, &ctx->output_max_wid);
    if (st != TL_OK) return st;

    return TL_OK;
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

    /* Get config values for dispatch decision */
    uint64_t max_windows = (uint64_t)tl->config.max_compaction_windows;
    size_t max_inputs = (size_t)tl->config.max_compaction_inputs;

    /* Phase 2 OOO Scaling: Dispatch to appropriate selection algorithm.
     *
     * When max_windows > 0, use window-bounded selection which:
     * - Anchors on oldest L0 and selects only overlapping L0s within target range
     * - Bounds compaction scope to prevent quadratic throughput collapse under OOO
     * - Falls back to greedy if no overlap (guarantees forward progress)
     *
     * When max_windows == 0 (unlimited), use greedy selection (original algorithm)
     * which accumulates L0s until caps are hit. */
    if (max_windows > 0) {
        return tl__compact_select_window_bounded(ctx, m, max_windows, max_inputs);
    }

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

    tl_segment_t** new_arr = tl__realloc(ctx->alloc, ctx->output_l1,
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
 * Ensure output_l0 array has capacity for at least one more segment.
 * Grows the array geometrically (2x) when needed.
 * Used by reshape compaction (Phase 2d).
 */
static tl_status_t tl__ensure_output_l0_capacity(tl_compact_ctx_t* ctx) {
    if (ctx->output_l0_len < ctx->output_l0_cap) {
        return TL_OK;  /* Already have space */
    }

    /* Grow capacity: start at 16, then double */
    size_t new_cap = (ctx->output_l0_cap == 0) ? 16 : ctx->output_l0_cap * 2;

    /* Overflow guard: check that new_cap * sizeof(ptr) doesn't wrap */
    if (new_cap > SIZE_MAX / sizeof(tl_segment_t*)) {
        return TL_EOVERFLOW;
    }

    tl_segment_t** new_arr = tl__realloc(ctx->alloc, ctx->output_l0,
                                          new_cap * sizeof(tl_segment_t*));
    if (new_arr == NULL) {
        return TL_ENOMEM;
    }

    /* Zero out the new portion */
    for (size_t i = ctx->output_l0_cap; i < new_cap; i++) {
        new_arr[i] = NULL;
    }

    ctx->output_l0 = new_arr;
    ctx->output_l0_cap = new_cap;
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

/*===========================================================================
 * Phase 3d: Reshape Merge
 *
 * Reshape merge differs from regular merge:
 * - Outputs L0 segments (not L1)
 * - Does NOT filter records by tombstones (all records preserved)
 * - Emits records-only L0 segments per window (Option B approach)
 * - Emits ONE tombstone-only L0 segment containing full tombstone union
 * - This avoids tombstone loss in gap windows (windows with no records)
 *===========================================================================*/

/**
 * Flush accumulated records into an L0 segment (records only, no tombstones).
 * Used by reshape merge to produce window-contained L0 segments.
 *
 * @param ctx           Compaction context
 * @param records       Record accumulator to flush
 * @param all_tombs     Tombstone set to clip to window, or NULL for records-only
 * @param window_start  Window start bound (inclusive)
 * @param window_end    Window end bound (exclusive), or TL_TS_MAX if unbounded
 * @param end_unbounded True if this is the unbounded final window
 */
static tl_status_t tl__flush_reshape_window(tl_compact_ctx_t* ctx,
                                             tl_recvec_t* records,
                                             const tl_intervals_t* all_tombs,
                                             tl_ts_t window_start,
                                             tl_ts_t window_end,
                                             bool end_unbounded) {
    tl_status_t st;

    /* Clip tombstones to this window (if provided) */
    tl_intervals_t window_tombs;
    tl_intervals_init(&window_tombs, ctx->alloc);

    /* Copy all tombstones to window_tombs (skip if NULL - records only mode) */
    if (all_tombs != NULL) {
        for (size_t i = 0; i < tl_intervals_len(all_tombs); i++) {
            const tl_interval_t* t = tl_intervals_get(all_tombs, i);
            if (t->end_unbounded) {
                st = tl_intervals_insert_unbounded(&window_tombs, t->start);
            } else {
                st = tl_intervals_insert(&window_tombs, t->start, t->end);
            }
            if (st != TL_OK) {
                tl_intervals_destroy(&window_tombs);
                return st;
            }
        }

        /* Clip to window bounds */
        if (end_unbounded) {
            tl_intervals_clip_lower(&window_tombs, window_start);
        } else {
            tl_intervals_clip(&window_tombs, window_start, window_end);
        }
    }

    /* Skip if no records AND no tombstones (empty window) */
    size_t rec_count = tl_recvec_len(records);
    size_t tomb_count = tl_intervals_len(&window_tombs);

    if (rec_count == 0 && tomb_count == 0) {
        tl_intervals_destroy(&window_tombs);
        tl_recvec_clear(records);
        return TL_OK;
    }

    /* Ensure output L0 array capacity */
    st = tl__ensure_output_l0_capacity(ctx);
    if (st != TL_OK) {
        tl_intervals_destroy(&window_tombs);
        return st;
    }

    /* Extract tombstone array (ownership transfers) */
    size_t tomb_len = 0;
    tl_interval_t* tomb_arr = NULL;
    if (tomb_count > 0) {
        tomb_arr = tl_intervals_take(&window_tombs, &tomb_len);
    }

    /* Build L0 segment with records and tombstones */
    tl_segment_t* seg = NULL;
    st = tl_segment_build_l0(
        ctx->alloc,
        tl_recvec_data(records),
        rec_count,
        tomb_arr,
        tomb_len,
        ctx->target_page_bytes,
        ctx->generation,
        &seg
    );

    /* Free tombstone array (segment_build copies it) */
    if (tomb_arr != NULL) {
        tl__free(ctx->alloc, tomb_arr);
    }

    tl_intervals_destroy(&window_tombs);

    if (st != TL_OK) {
        return st;
    }

    /* Add to output L0 array */
    TL_ASSERT(ctx->output_l0_len < ctx->output_l0_cap);
    ctx->output_l0[ctx->output_l0_len++] = seg;

    /* Clear record accumulator for next window */
    tl_recvec_clear(records);
    return TL_OK;
}

/**
 * Emit a tombstone-only L0 segment containing the full tombstone union.
 *
 * CRITICAL FOR CORRECTNESS: This function ensures ALL tombstones from
 * reshape inputs are preserved in a single segment. This is the safe
 * approach (Option B from LLD) that avoids the complexity of per-window
 * tombstone splitting which can drop tombstones in gap windows.
 *
 * @param ctx  Compaction context with tombs already collected
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
static tl_status_t tl__emit_full_tombstone_segment(tl_compact_ctx_t* ctx) {
    tl_status_t st;

    /* Skip if no tombstones */
    if (tl_intervals_is_empty(&ctx->tombs)) {
        return TL_OK;
    }

    /* Ensure output L0 array capacity */
    st = tl__ensure_output_l0_capacity(ctx);
    if (st != TL_OK) {
        return st;
    }

    /* Extract tombstone array (makes a copy).
     * Check for overflow before allocation - tl_segment_build_l0 requires
     * tombstones_len to fit in uint32_t, and we must avoid size_t overflow. */
    size_t tomb_len = tl_intervals_len(&ctx->tombs);
    if (tomb_len > UINT32_MAX) {
        return TL_EOVERFLOW;
    }
    if (tomb_len > SIZE_MAX / sizeof(tl_interval_t)) {
        return TL_EOVERFLOW;
    }
    tl_interval_t* tomb_arr = tl__malloc(ctx->alloc, tomb_len * sizeof(tl_interval_t));
    if (tomb_arr == NULL) {
        return TL_ENOMEM;
    }

    for (size_t i = 0; i < tomb_len; i++) {
        const tl_interval_t* t = tl_intervals_get(&ctx->tombs, i);
        tomb_arr[i] = *t;
    }

    /* Build tombstone-only L0 segment */
    tl_segment_t* seg = NULL;
    st = tl_segment_build_l0(
        ctx->alloc,
        NULL, 0,  /* No records */
        tomb_arr, tomb_len,
        ctx->target_page_bytes,
        ctx->generation,
        &seg
    );

    tl__free(ctx->alloc, tomb_arr);

    if (st != TL_OK) {
        return st;
    }

    TL_ASSERT(ctx->output_l0_len < ctx->output_l0_cap);
    ctx->output_l0[ctx->output_l0_len++] = seg;

    return TL_OK;
}

/**
 * Execute reshape merge (L0→L0).
 *
 * Unlike regular merge:
 * - Does NOT filter records by tombstones (all records preserved)
 * - Outputs L0 segments partitioned by window (records only)
 * - Emits ONE tombstone-only segment containing the FULL tombstone union
 *
 * TOMBSTONE PRESERVATION (CRITICAL):
 * This implementation uses the "Option B" approach from the LLD review:
 * - Record segments are window-contained (one per window with records)
 * - ALL tombstones are emitted in a single tombstone-only segment
 * This is simpler and avoids the bug where per-window clipping drops
 * tombstones in windows that have no records (gap windows).
 *
 * @param ctx  Context with selected reshape inputs (is_reshape must be true)
 * @return TL_OK on success, error code on failure
 */
static tl_status_t tl__compact_merge_reshape(tl_compact_ctx_t* ctx) {
    tl_status_t st;

    TL_ASSERT(ctx->is_reshape);
    TL_ASSERT(ctx->input_l1_len == 0);  /* Reshape has no L1 inputs */

    /* ===================================================================
     * Step 1: Collect all tombstones from input L0 segments
     * =================================================================== */
    tl_intervals_clear(&ctx->tombs);

    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        const tl_segment_t* seg = ctx->input_l0[i];
        if (tl_segment_has_tombstones(seg)) {
            tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
            st = tl__tombs_union_into(&ctx->tombs, seg_tombs, ctx->alloc);
            if (st != TL_OK) return st;
        }
    }

    /* ===================================================================
     * Step 2: Build input iterators and initialize K-way merge
     * =================================================================== */
    size_t total_inputs = ctx->input_l0_len;  /* No L1 inputs for reshape */
    tl_segment_iter_t* iters = tl__calloc(ctx->alloc, total_inputs,
                                           sizeof(tl_segment_iter_t));
    if (iters == NULL) {
        return TL_ENOMEM;
    }

    /* Initialize segment iterators (unbounded range - all records) */
    for (size_t i = 0; i < total_inputs; i++) {
        tl_segment_iter_init(&iters[i], ctx->input_l0[i],
                              TL_TS_MIN, 0, true);  /* [TL_TS_MIN, +inf) */
    }

    /* Build heap for K-way merge */
    tl_heap_t heap;
    tl_heap_init(&heap, ctx->alloc);
    st = tl_heap_reserve(&heap, total_inputs);
    if (st != TL_OK) {
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
                .component_id = (uint32_t)i,
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

    /* ===================================================================
     * Step 3: K-way merge with window partitioning (NO tombstone filtering)
     *
     * Unlike regular merge, reshape does NOT filter by tombstones.
     * All records are preserved; tombstones are clipped to windows.
     * =================================================================== */

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

        /* NOTE: Unlike regular merge, NO tombstone filtering here.
         * All records are preserved; we're just partitioning by window. */

        /* Determine which window this record belongs to */
        int64_t rec_wid;
        st = tl_window_id_for_ts(min_entry.ts, ctx->window_size,
                                  ctx->window_origin, &rec_wid);
        if (st != TL_OK) {
            goto cleanup;
        }

        /* If we've moved to a new window, flush the current window and jump */
        if (current_wid < rec_wid) {
            /* Flush current window as L0 (records only - no tombstones).
             * Tombstones are emitted separately in a single segment at the end
             * to ensure none are lost in gap windows. */
            st = tl__flush_reshape_window(ctx, &window_records, NULL,
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

        /* Add record to current window accumulator */
        st = tl_recvec_push(&window_records, min_entry.ts, min_entry.handle);
        if (st != TL_OK) {
            goto cleanup;
        }
    }

    /* Flush final window (records only) */
    st = tl__flush_reshape_window(ctx, &window_records, NULL,
                                   current_window_start, current_window_end,
                                   current_end_unbounded);
    if (st != TL_OK) {
        goto cleanup;
    }

    /* ===================================================================
     * Step 4: Emit ALL tombstones as a single tombstone-only segment
     *
     * CRITICAL CORRECTNESS FIX (Option B from LLD review):
     * Instead of per-window tombstone clipping (which drops tombstones in
     * gap windows), we emit the FULL tombstone union in a single segment.
     * This ensures no tombstones are ever lost during reshape.
     * =================================================================== */
    st = tl__emit_full_tombstone_segment(ctx);
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

/*===========================================================================
 * Phase 4: Publication - Helpers
 *===========================================================================*/

/**
 * Check if all compaction inputs are still present in a manifest.
 *
 * Used by rebase publish to verify that inputs haven't been removed
 * by a concurrent compaction while we were merging.
 *
 * @param m    Manifest to check (pinned, so safe to read)
 * @param ctx  Compaction context with input segment lists
 * @return true if all inputs found, false if any missing
 */
static bool tl__all_inputs_present(const tl_manifest_t* m,
                                    const tl_compact_ctx_t* ctx) {
    /* Check all L0 inputs */
    for (size_t i = 0; i < ctx->input_l0_len; i++) {
        bool found = false;
        uint32_t n_l0 = tl_manifest_l0_count(m);
        for (uint32_t j = 0; j < n_l0 && !found; j++) {
            found = (tl_manifest_l0_get(m, j) == ctx->input_l0[i]);
        }
        if (!found) return false;
    }

    /* Check all L1 inputs */
    for (size_t i = 0; i < ctx->input_l1_len; i++) {
        bool found = false;
        uint32_t n_l1 = tl_manifest_l1_count(m);
        for (uint32_t j = 0; j < n_l1 && !found; j++) {
            found = (tl_manifest_l1_get(m, j) == ctx->input_l1[i]);
        }
        if (!found) return false;
    }

    return true;
}

/**
 * Check if current manifest has L1 segments that conflict with our output.
 *
 * A conflict exists if a NEW L1 segment (not in our inputs) overlaps with
 * our output window range. This would violate the L1 non-overlap invariant.
 *
 * CRITICAL: Must use window_start/window_end for overlap check, NOT
 * min_ts/max_ts. L1 segments are defined by their window bounds.
 *
 * @param current  Current manifest (pinned, safe to read)
 * @param ctx      Compaction context with output window bounds and inputs
 * @return true if conflict exists, false if safe to rebase
 */
static bool tl__has_l1_overlap_conflict(const tl_manifest_t* current,
                                         const tl_compact_ctx_t* ctx) {
    /* Compute output window bounds (not timestamp bounds!) */
    tl_ts_t output_first_wstart, output_first_wend;
    bool output_first_unbounded;
    tl_window_bounds(ctx->output_min_wid, ctx->window_size, ctx->window_origin,
                     &output_first_wstart, &output_first_wend, &output_first_unbounded);

    tl_ts_t output_last_wstart, output_last_wend;
    bool output_last_unbounded;
    tl_window_bounds(ctx->output_max_wid, ctx->window_size, ctx->window_origin,
                     &output_last_wstart, &output_last_wend, &output_last_unbounded);

    /* Check each L1 in current manifest */
    uint32_t n_l1 = tl_manifest_l1_count(current);
    for (uint32_t i = 0; i < n_l1; i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(current, i);

        /* Skip segments that are our inputs (we're replacing them) */
        bool is_input = false;
        for (size_t j = 0; j < ctx->input_l1_len; j++) {
            if (seg == ctx->input_l1[j]) {
                is_input = true;
                break;
            }
        }
        if (is_input) continue;

        /* Use window_start/window_end for L1 overlap check (CRITICAL) */
        if (tl__l1_overlaps_window_range(seg, output_first_wstart,
                                          output_last_wend, output_last_unbounded)) {
            return true;  /* Conflict detected */
        }
    }

    return false;
}

/**
 * Build a manifest with our compaction changes applied.
 *
 * This is the "off-lock" expensive work. Handles both L0→L1 (normal)
 * and L0→L0 (reshape) compaction modes.
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

    /* Queue addition of outputs (L0 for reshape, L1 for normal) */
    if (ctx->is_reshape) {
        for (size_t i = 0; i < ctx->output_l0_len; i++) {
            st = tl_manifest_builder_add_l0(&builder, ctx->output_l0[i]);
            if (st != TL_OK) {
                tl_manifest_builder_destroy(&builder);
                return st;
            }
        }
    } else {
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
    tl_manifest_t* current = NULL;

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

    /* Fast path: manifest unchanged */
    if (tl->manifest == ctx->base_manifest) {
        goto do_swap;
    }

    /*
     * Rebase path: manifest changed during merge.
     * Pin current manifest under lock, then unlock to validate off-lock.
     * This prevents UAF while we examine the current manifest.
     */
    current = tl_manifest_acquire(tl->manifest);
    TL_UNLOCK_WRITER(tl);

    /* Validate inputs still exist in current manifest (off-lock) */
    if (!tl__all_inputs_present(current, ctx)) {
        tl_atomic_inc_u64(&tl->rebase_publish_fallback);
        tl_manifest_release(current);
        tl_manifest_release(new_manifest);
        return TL_EBUSY;
    }

    /* For L0→L1 compaction: check L1 overlap conflict (off-lock) */
    if (!ctx->is_reshape && ctx->output_l1_len > 0) {
        if (tl__has_l1_overlap_conflict(current, ctx)) {
            tl_atomic_inc_u64(&tl->rebase_l1_conflict);
            tl_manifest_release(current);
            tl_manifest_release(new_manifest);
            return TL_EBUSY;
        }
    }

    /*
     * Rebase valid - but we built manifest from base_manifest.
     * Rebuild from CURRENT manifest off-lock (allocations happen here).
     */
    tl_manifest_release(new_manifest);
    new_manifest = NULL;

    st = tl__build_compaction_manifest(ctx, current, &new_manifest);
    if (st != TL_OK) {
        tl_manifest_release(current);
        return st;
    }

    /* Re-acquire lock and re-validate pointer before swap */
    TL_LOCK_WRITER(tl);

    if (tl->manifest != current) {
        /* Manifest changed AGAIN during rebuild - give up, full retry */
        TL_UNLOCK_WRITER(tl);
        tl_manifest_release(current);
        tl_manifest_release(new_manifest);
        return TL_EBUSY;
    }

    tl_atomic_inc_u64(&tl->rebase_publish_success);

do_swap:
    /* Enter seqlock region for actual swap */
    tl_seqlock_write_begin(&tl->view_seq);

    /* Swap manifest */
    tl_manifest_t* old_manifest = tl->manifest;
    tl->manifest = new_manifest;

    tl_seqlock_write_end(&tl->view_seq);

    /* Update reshape cooldown counter.
     * Safe: maintenance is single-threaded (maint_mu serialization). */
    if (ctx->is_reshape) {
        tl->consecutive_reshapes++;
    } else {
        tl->consecutive_reshapes = 0;
    }

    TL_UNLOCK_WRITER(tl);

    /* Release pinned current manifest (if we used rebase path) */
    if (current != NULL) {
        tl_manifest_release(current);
    }

    /* Release old manifest (safe after unlock) */
    tl_manifest_release(old_manifest);

#ifndef NDEBUG
    /* Validate critical L1 non-overlap invariant after compaction.
     * new_manifest is what we just published - safe to read since we built it
     * and it's now referenced by tl->manifest (won't be freed). */
    tl__validate_l1_non_overlap(new_manifest);
#endif

    /* NOTE: We do NOT clear output_l1_len/output_l0_len or residual_tomb here.
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

/**
 * Internal helper: run select and merge for the given mode.
 *
 * @param ctx            Initialized context
 * @param use_reshape    True for reshape mode, false for L0→L1
 * @param pinned         Pre-pinned manifest for reshape (NULL for L0→L1)
 * @return TL_OK on success, error code on failure
 */
static tl_status_t tl__compact_select_and_merge(tl_compact_ctx_t* ctx,
                                                  bool use_reshape,
                                                  tl_manifest_t* pinned) {
    tl_status_t st;

    /* Selection */
    if (use_reshape) {
        st = tl__compact_select_reshape(ctx, pinned);
    } else {
        st = tl_compact_select(ctx);
    }
    if (st != TL_OK) {
        return st;
    }

    /* Merge */
    if (use_reshape) {
        st = tl__compact_merge_reshape(ctx);
    } else {
        st = tl_compact_merge(ctx);
    }

    return st;
}

tl_status_t tl_compact_one(tl_timelog_t* tl, int max_retries) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(max_retries > 0);  /* Ensures publish loop executes at least once */

    /*-----------------------------------------------------------------------
     * Phase 2d: Determine compaction mode (L0→L1 vs Reshape)
     *
     * Strategy dispatch (checked under maint_mu for cooldown):
     * - TL_COMPACT_RESHAPE: always use reshape
     * - TL_COMPACT_L0_L1: always use normal L0→L1
     * - TL_COMPACT_AUTO: decide based on tl__should_reshape()
     *-----------------------------------------------------------------------*/
    tl_compaction_strategy_t strategy = tl->config.compaction_strategy;
    bool use_reshape = false;
    tl_manifest_t* reshape_pinned = NULL;

    if (strategy == TL_COMPACT_RESHAPE) {
        /* Force reshape mode - pin manifest for selection */
        use_reshape = true;
        TL_LOCK_WRITER(tl);
        reshape_pinned = tl_manifest_acquire(tl->manifest);
        TL_UNLOCK_WRITER(tl);
    } else if (strategy == TL_COMPACT_AUTO) {
        /* Check cooldown and trigger conditions.
         * NOTE: should_reshape reads consecutive_reshapes which is protected
         * by writer_mu in publish, but we're checking under no lock here.
         * This is safe because:
         * 1. Maintenance thread is single-threaded (maint_mu serializes)
         * 2. consecutive_reshapes is only written by publish under writer_mu
         * 3. Worst case: we use stale count, which just affects trigger heuristic */
        use_reshape = tl__should_reshape(tl, &reshape_pinned);
        if (!use_reshape && reshape_pinned != NULL) {
            /* Not using reshape - release the pinned manifest */
            tl_manifest_release(reshape_pinned);
            reshape_pinned = NULL;
        }
    }
    /* TL_COMPACT_L0_L1: use_reshape stays false */

    /*-----------------------------------------------------------------------
     * Adaptive Segmentation Integration (Phase 7)
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

    if (tl->config.adaptive.target_records > 0) {
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
    tl_compact_ctx_init(&ctx, tl, &tl->alloc);

    /* Override window_size with candidate (don't commit to tl until success) */
    ctx.window_size = candidate_window;

    tl_status_t st;

    /* Phase 1-2: Selection and Merge */
    st = tl__compact_select_and_merge(&ctx, use_reshape, reshape_pinned);
    reshape_pinned = NULL;  /* Ownership transferred to ctx or released on error */

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

    /* Phase 3: Publish with retries.
     * Track publish result separately to avoid it being overwritten
     * by select/merge during retry preparation. */
    tl_status_t publish_st = TL_EBUSY;  /* Default if loop never runs (impossible) */
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
                 * until released - user must use epoch/RCU/grace period.
                 *
                 * NOTE: Reshape does NOT drop records (no tombstone filtering),
                 * so dropped_len will be 0 for reshape compactions. */
                if (ctx.on_drop_handle != NULL) {
                    for (size_t i = 0; i < ctx.dropped_len; i++) {
                        ctx.on_drop_handle(ctx.on_drop_ctx,
                                           ctx.dropped_records[i].ts,
                                           ctx.dropped_records[i].handle);
                    }
                }

                /* Increment appropriate compaction counter */
                if (ctx.is_reshape) {
                    tl_atomic_inc_u64(&tl->reshape_compactions_total);
                } else {
                    tl_atomic_inc_u64(&tl->compactions_total);
                }

                /* Adaptive: commit window and record success.
                 * THIS is when we commit effective_window_size (LLD-strict). */
                if (tl->config.adaptive.target_records > 0) {
                    TL_LOCK_MAINT(tl);
                    tl->effective_window_size = candidate_window;
                    tl_adaptive_record_success(&tl->adaptive);
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

        /* Manifest changed - re-select and re-merge for retry.
         * This is expensive but correct - ensures we don't publish
         * stale outputs.
         *
         * Note: On retry, we use the SAME candidate_window and SAME mode.
         * The window size and reshape decision shouldn't change mid-compaction.
         *
         * For reshape retries, we need to re-pin manifest. */
        tl_compact_ctx_destroy(&ctx);
        tl_compact_ctx_init(&ctx, tl, &tl->alloc);
        ctx.window_size = candidate_window;  /* Re-apply candidate */

        /* For reshape retry, re-pin manifest */
        tl_manifest_t* retry_pinned = NULL;
        if (use_reshape) {
            if (strategy == TL_COMPACT_RESHAPE) {
                /* Forced reshape mode - just pin manifest */
                TL_LOCK_WRITER(tl);
                retry_pinned = tl_manifest_acquire(tl->manifest);
                TL_UNLOCK_WRITER(tl);
            } else {
                /* AUTO mode: re-check should_reshape since manifest changed */
                if (!tl__should_reshape(tl, &retry_pinned)) {
                    /* Reshape no longer needed - fall back to normal mode */
                    use_reshape = false;
                    if (retry_pinned != NULL) {
                        tl_manifest_release(retry_pinned);
                        retry_pinned = NULL;
                    }
                }
            }
        }

        st = tl__compact_select_and_merge(&ctx, use_reshape, retry_pinned);
        retry_pinned = NULL;  /* Ownership transferred */

        if (st != TL_OK) {
            /* Selection/merge failed during retry - propagate this error */
            tl_compact_ctx_destroy(&ctx);
            /* Adaptive: record failure for ENOMEM (no restore needed) */
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
