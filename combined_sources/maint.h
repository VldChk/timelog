/*
============================================================================

   COMBINED HEADER FILE: maint.h

   Generated from: core\src\maint
   Generated at:   2026-01-26 20:20:58

   This file combines all .h files from the maint/ subfolder.

   Files included:
 *   - tl_adaptive.h
 *   - tl_compaction.h

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: tl_adaptive.h
/*   FROM: maint/
/*
/******************************************************************************/
#ifndef TL_ADAPTIVE_H
#define TL_ADAPTIVE_H

/*===========================================================================
 * Adaptive Segmentation Module
 *
 * Implements adaptive window size computation for L1 segmentation based on
 * data density. The feature dynamically adjusts compaction window sizes to
 * maintain approximately constant segment sizes (target_records per segment).
 *
 * Design Principles (LLD Section 4):
 * 1. Backward compatible: Disabled by default (target_records == 0)
 * 2. Non-invasive: Pure policy module with clean integration points
 * 3. Safe: No allocation in policy loop, overflow-safe arithmetic
 * 4. Testable: Pure functions enable comprehensive unit testing
 * 5. Stable: All fallback paths return current_window (not base) for stability
 *
 * Single Source of Truth:
 * - tl->effective_window_size is THE authoritative window
 * - tl_adaptive_state_t tracks EWMA, counters, and density metrics only
 *
 * Thread Safety:
 * - All state updates happen under maint_mu (single writer: maintenance thread)
 * - Density updates occur ONLY when maintenance thread performs flush
 * - Manual tl_flush() does NOT update density (acceptable constraint)
 *
 * Reference: docs/timelog_adaptive_segmentation_lld_c17.md (draft-5)
 *===========================================================================*/

#include "timelog/timelog.h"  /* For tl_adaptive_config_t, tl_ts_t, tl_status_t */
#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"

#include <stdint.h>
#include <stdbool.h>
#include <math.h>  /* For llround, isnan, isinf */

/*===========================================================================
 * Forward Declarations
 *===========================================================================*/

struct tl_timelog;
typedef struct tl_timelog tl_timelog_t;

/*
 * NOTE: tl_adaptive_config_t is now defined in timelog.h (public API).
 * This allows users to configure adaptive segmentation via tl_config_t.adaptive.
 */

/*===========================================================================
 * Adaptive Runtime State
 *
 * Single-writer: maintenance thread ONLY. Protected by maint_mu.
 *
 * CRITICAL: `tl->effective_window_size` is the SINGLE SOURCE OF TRUTH
 * for the current window. This struct tracks EWMA, counters, and
 * last-flush metrics for density computation — NOT the authoritative window.
 *===========================================================================*/

typedef struct tl_adaptive_state {
    /* Density tracking (from last flush by maintenance thread) */
    uint64_t        last_flush_records;
    tl_ts_t         last_flush_min_ts;
    tl_ts_t         last_flush_max_ts;
    uint64_t        flush_count;
    uint64_t        last_density_update_flush;

    /* EWMA state */
    double          ewma_density;
    bool            ewma_initialized;

    /* Failure tracking */
    uint32_t        consecutive_failures;
    /* NOTE: last_compact_windows removed - not used in current implementation.
     * The LLD defines it for desired_segments_per_compact feature which is
     * not yet implemented. Add back if/when that feature is added. */
} tl_adaptive_state_t;

/*===========================================================================
 * Flush Metrics
 *
 * Metrics captured during flush for adaptive policy.
 * Record-only bounds (excludes tombstones).
 *
 * Placed in tl_adaptive.h (not tl_flush.h) because:
 * - Only consumed by adaptive policy module
 * - Avoids cross-layer header dependencies
 *===========================================================================*/

typedef struct tl_flush_metrics {
    uint64_t    record_count;   /* run_len + ooo_len */
    tl_ts_t     min_ts;         /* Min of record timestamps */
    tl_ts_t     max_ts;         /* Max of record timestamps */
    bool        has_records;    /* record_count > 0 */
} tl_flush_metrics_t;

/*===========================================================================
 * Configuration Validation
 *
 * Validates adaptive configuration parameters.
 * Called during tl_open() if adaptive.target_records > 0.
 *
 * Validation rules:
 * - min_window <= max_window (if both > 0)
 * - alpha in [0.0, 1.0]
 * - window_quantum >= 0
 * - hysteresis_pct in [0, 100]
 *
 * @param cfg  Adaptive configuration to validate
 * @return TL_OK if valid, TL_EINVAL if invalid
 *===========================================================================*/

tl_status_t tl_adaptive_config_validate(const tl_adaptive_config_t* cfg);

/*===========================================================================
 * State Lifecycle
 *
 * Initializes adaptive state to all zeros.
 * Called during tl_open() after config normalization.
 *
 * @param state  State to initialize
 *===========================================================================*/

void tl_adaptive_state_init(tl_adaptive_state_t* state);

/*===========================================================================
 * Density Update
 *
 * Updates EWMA density based on flush metrics.
 * Called after flush, ONLY by maintenance thread.
 *
 * LOCK CONSTRAINT: Caller must hold maint_mu. This function is only
 * called when the maintenance thread performs a flush (background mode).
 * Manual tl_flush() does NOT update density (acceptable: manual mode
 * users don't use adaptive anyway).
 *
 * Density = record_count / span, where span = max_ts - min_ts + 1
 * (The +1 accounts for the fact that a single record has span = 1)
 *
 * Skips update if:
 * - record_count == 0
 * - span <= 0 (invalid or overflow)
 * - Computed density is NaN or Inf
 *
 * @param state    Adaptive state (modified)
 * @param cfg      Adaptive configuration
 * @param metrics  Flush metrics (record-only bounds)
 *===========================================================================*/

void tl_adaptive_update_density(tl_adaptive_state_t* state,
                                const tl_adaptive_config_t* cfg,
                                const tl_flush_metrics_t* metrics);

/*===========================================================================
 * Window Computation
 *
 * Computes candidate window size based on current state and config.
 * Called before compaction in the maintenance path.
 *
 * CRITICAL SEMANTICS: Returns current_window in ALL fallback cases:
 * - Adaptive disabled (target_records == 0)
 * - Warmup not complete (flush_count < warmup_flushes)
 * - No valid EWMA density (ewma_density <= 0)
 * - Density stale (flush_count - last_update > stale_flushes)
 * - Arithmetic failure (overflow, NaN, candidate <= 0)
 *
 * This "keep current" rule is critical for control-loop stability.
 * Resetting to base_window causes oscillation.
 *
 * Algorithm:
 * 1. Check fallback conditions → return current_window
 * 2. candidate = target_records / ewma_density
 * 3. Apply failure backoff if triggered
 * 4. Clamp to [min_window, max_window]
 * 5. Apply hysteresis (skip small changes)
 * 6. Apply quantum snapping (nearest-quantum rounding)
 * 7. Return candidate or current_window on any failure
 *
 * @param state           Adaptive state (read-only)
 * @param cfg             Adaptive configuration
 * @param current_window  Current effective window (tl->effective_window_size)
 * @return Candidate window, or current_window if no change needed
 *===========================================================================*/

tl_ts_t tl_adaptive_compute_candidate(const tl_adaptive_state_t* state,
                                      const tl_adaptive_config_t* cfg,
                                      tl_ts_t current_window);

/*===========================================================================
 * Success/Failure Tracking
 *
 * Called ONLY after compaction publish completes.
 *
 * INTEGRATION (caller must):
 * After successful publish:
 *   1. tl->effective_window_size = candidate;  // Single source of truth
 *   2. tl_adaptive_record_success(&tl->adaptive);
 *
 * On failure (ENOMEM/EBUSY):
 *   1. tl_adaptive_record_failure(&tl->adaptive);
 *   2. DO NOT update tl->effective_window_size
 *
 * @param state  Adaptive state (modified)
 *===========================================================================*/

void tl_adaptive_record_success(tl_adaptive_state_t* state);
void tl_adaptive_record_failure(tl_adaptive_state_t* state);

/*===========================================================================
 * Advisory Resize Query (M-20)
 *
 * Returns true if adaptive segmentation has sufficient samples to potentially
 * resize the window. Used by scheduler to decide if compaction should run.
 *
 * This is an advisory function only - actual resize decision happens in
 * tl_adaptive_compute_candidate() which includes warmup checks, staleness,
 * hysteresis, etc.
 *
 * Thread Safety: This function reads fields without locking (intentionally).
 * Reads may be racy but are benign for advisory use. See implementation for
 * detailed rationale. Callers must NOT use this for correctness decisions.
 *
 * @param tl  Timelog instance (must not be NULL)
 * @return true if resize might be beneficial, false otherwise
 *===========================================================================*/

bool tl_adaptive_wants_resize(const tl_timelog_t* tl);

/*===========================================================================
 * Internal Computation Helpers (Exposed for Testing)
 *
 * These are implementation details but exposed in the header for unit testing.
 * Do NOT call these directly in production code.
 *===========================================================================*/

#ifdef TL_ADAPTIVE_INTERNAL_TEST

/**
 * Compute raw candidate from target_records and density.
 * Returns candidate window as double, or 0.0 if density is invalid.
 */
double tl__adaptive_compute_raw_candidate(uint64_t target_records, double density);

/**
 * Apply guardrails (clamp to [min_window, max_window]).
 * Returns clamped value.
 */
double tl__adaptive_apply_guardrails(double candidate,
                                     tl_ts_t min_window,
                                     tl_ts_t max_window);

/**
 * Check if hysteresis should skip the change.
 * Returns true if |candidate - current| / current < threshold.
 */
bool tl__adaptive_hysteresis_skip(double candidate,
                                  tl_ts_t current_window,
                                  uint32_t hysteresis_pct);

/**
 * Apply nearest-quantum snapping.
 * Returns snapped value, or current_window if snapping fails.
 *
 * Algorithm (per LLD):
 * 1. wi = llround(candidate)
 * 2. qid = floor_div(wi, quantum)
 * 3. snapped = qid * quantum
 * 4. remainder = wi - snapped
 * 5. if remainder >= quantum/2: round up (with overflow guard)
 * 6. return snapped if > 0, else current_window
 */
tl_ts_t tl__adaptive_snap_to_quantum(double candidate,
                                     tl_ts_t window_quantum,
                                     tl_ts_t current_window);

/**
 * Compute span from min_ts to max_ts with overflow check.
 * Returns span on success (always >= 1 for valid input), or 0 on overflow.
 * Note: span = max_ts - min_ts + 1 (single record has span 1)
 */
int64_t tl__adaptive_compute_span(tl_ts_t min_ts, tl_ts_t max_ts);

#endif /* TL_ADAPTIVE_INTERNAL_TEST */

#endif /* TL_ADAPTIVE_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_adaptive.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_compaction.h
/*   FROM: maint/
/*
/******************************************************************************/
#ifndef TL_COMPACTION_H
#define TL_COMPACTION_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_intervals.h"
#include "../storage/tl_segment.h"
#include "../storage/tl_manifest.h"

/*===========================================================================
 * Compaction Module
 *
 * Implements L0 -> L1 compaction for the LSM-style storage layer.
 *
 * Goals (Compaction Policy LLD Section 1):
 * 1. Bound read amplification: L0 count <= max_delta_segments
 * 2. Enforce L1 non-overlap: L1 segments aligned to time windows
 * 3. Fold tombstones: L1 segments are tombstone-free
 * 4. Preserve snapshot isolation: atomic manifest publication
 * 5. Support handle drop callback: notify when records retired
 *
 * Phases:
 * 1. Trigger check (tl_compact_needed)
 * 2. Selection (tl_compact_select)
 * 3. Merge (tl_compact_merge)
 * 4. Publication (tl_compact_publish)
 *
 * Thread Safety:
 * - Compaction is serialized externally by maint_mu (one compaction at a time)
 * - writer_mu held only during short publication phase
 * - Long-running merge happens without locks
 *
 * Trigger Coupling with Flush (Background Mode):
 * - tl_compact_needed() is only called when flush work is pending
 * - This is safe because compaction triggers depend on segment state
 * - See tl_compact_needed() documentation for full details
 *
 * Handle Drop Callback Semantics:
 * - Callbacks are DEFERRED until AFTER successful publication
 * - During merge, dropped records are collected but NOT fired
 * - Only after publish succeeds are callbacks invoked for all dropped records
 * - If compaction fails/retries, pending drops are discarded (will be re-collected)
 * - IMPORTANT: This is a "retire" notification, NOT a "safe to free" signal
 * - Existing snapshots may still reference the dropped record until released
 * - User must implement their own epoch/RCU/hazard-pointer scheme if they
 *   need safe payload reclamation (see tl_on_drop_fn docs in timelog.h)
 *
 * Reference: timelog_v1_lld_compaction_policy.md
 *===========================================================================*/

/* Forward declaration - actual struct in tl_timelog_internal.h */
struct tl_timelog;
typedef struct tl_timelog tl_timelog_t;

/*===========================================================================
 * Compaction Context
 *
 * Holds all state for a single compaction operation.
 * Created by select, populated by merge, consumed by publish.
 *===========================================================================*/

typedef struct tl_compact_ctx {
    tl_timelog_t*       tl;              /* Parent instance */
    tl_alloc_ctx_t*     alloc;           /* Allocator */

    /* Input segments (pinned during compaction) */
    tl_segment_t**      input_l0;        /* Selected L0 segments */
    size_t              input_l0_len;
    tl_segment_t**      input_l1;        /* Selected L1 segments */
    size_t              input_l1_len;

    /* Manifest snapshot at selection time */
    tl_manifest_t*      base_manifest;   /* Pinned base manifest */

    /* Effective tombstone set */
    tl_intervals_t      tombs;           /* Union of all tombstones (unclipped) */
    tl_intervals_t      tombs_clipped;   /* Tombstones clipped to output range */

    /* Output segments */
    tl_segment_t**      output_l1;       /* New L1 segments */
    size_t              output_l1_len;
    size_t              output_l1_cap;

    tl_segment_t*       residual_tomb;   /* Tombstone-only L0 for residuals */

    /* Configuration (copied from tl) */
    tl_ts_t             window_size;
    tl_ts_t             window_origin;
    size_t              target_page_bytes;
    uint32_t            generation;

    /* Handle drop callback (matches tl_config_t naming) */
    tl_on_drop_fn       on_drop_handle;
    void*               on_drop_ctx;

    /* Deferred drop records - collected during merge, fired after publish.
     *
     * CRITICAL CORRECTNESS INVARIANT: If compaction fails (ENOMEM/EBUSY)
     * or retries, callbacks MUST NOT fire for records still visible in
     * the manifest. This would violate the on_drop_handle contract and
     * can cause double-free/UAF in user code that treats it as final
     * reclamation.
     *
     * Solution: Collect dropped (ts, handle) pairs during merge, but only
     * invoke callbacks after successful publish. On failure/retry, the
     * drops are discarded when ctx is destroyed; re-merge re-collects them.
     *
     * Uses tl_record_t for storage since it has (ts, handle) pair. */
    tl_record_t*        dropped_records;
    size_t              dropped_len;
    size_t              dropped_cap;

    /* Output range (computed from input selection) */
    tl_ts_t             output_min_ts;
    tl_ts_t             output_max_ts;
    int64_t             output_min_wid;  /* First output window ID */
    int64_t             output_max_wid;  /* Last output window ID (inclusive) */
} tl_compact_ctx_t;

/*===========================================================================
 * Context Lifecycle
 *===========================================================================*/

/**
 * Initialize compaction context.
 * Does NOT select segments - call tl_compact_select() next.
 *
 * @param window_size Effective window size (caller must read under maint_mu)
 */
void tl_compact_ctx_init(tl_compact_ctx_t* ctx,
                          tl_timelog_t* tl,
                          tl_alloc_ctx_t* alloc,
                          tl_ts_t window_size);

/**
 * Destroy compaction context and release all pinned resources.
 * Safe to call at any point (partial initialization cleanup).
 */
void tl_compact_ctx_destroy(tl_compact_ctx_t* ctx);

/*===========================================================================
 * Compaction Phases
 *===========================================================================*/

/**
 * Phase 1: Check if compaction is needed.
 *
 * Returns true if:
 * - L0 count >= max_delta_segments
 * - compact_pending flag is set (checked by caller)
 * - Delete debt threshold exceeded (optional)
 *
 * Briefly acquires writer_mu to pin manifest (prevents UAF).
 * This is an advisory check; selection re-validates.
 *
 * Flush/Compaction Trigger Coupling (Background Mode):
 * =====================================================
 * In background mode, the worker loop only calls this function when:
 *   - do_flush is true (flush work pending), AND
 *   - do_compact is false (compact_pending was NOT already set)
 *
 * See tl_timelog.c:1749: `if (!do_compact && do_flush)`
 *
 * This is an optimization based on the invariant:
 *
 *   "Compaction triggers can only change when segments change"
 *
 * Segment state changes only via:
 * - Flush: creates new L0 segments (increases L0 count, adds tombstones)
 * - Compaction: removes L0/L1, creates L1 (decreases L0 count)
 *
 * On idle periodic wakes with no pending work, calling this is wasteful
 * because triggers are unchanged from the previous check.
 *
 * When compact_pending is already set (explicit tl_compact() request), this
 * function is SKIPPED because we already know compaction should run.
 *
 * IMPORTANT: This coupling means delete-debt compaction won't be triggered
 * on pure idle wakes without write activity. Users wanting prompt delete-debt
 * response should either:
 * - Use tl_compact() for explicit compaction requests
 * - Ensure continued write activity
 *
 * This coupling does NOT affect:
 * - Explicit requests via compact_pending flag (bypasses this check entirely)
 * - Manual mode (tl_maint_step always checks triggers unconditionally)
 *
 * Reference: tl_timelog.c worker loop (tl__maint_worker_entry)
 */
bool tl_compact_needed(const tl_timelog_t* tl);

/**
 * Phase 2: Select segments for compaction.
 *
 * Implements baseline policy (Compaction Policy LLD Section 6.1):
 * 1. Pin current manifest
 * 2. Select all L0 segments
 * 3. Compute covered time range (records + tombstones)
 * 4. Select overlapping L1 segments
 *
 * IMPORTANT: Caller MUST call tl_compact_ctx_destroy() regardless of
 * return status. This function acquires resources (manifest pin, segment
 * refs) that are cleaned up by destroy. This follows the init/destroy
 * lifecycle pattern - select may partially succeed before failing.
 *
 * @param ctx  Initialized compaction context
 * @return TL_OK on success (inputs selected and pinned)
 *         TL_EOF if no work needed
 *         TL_ENOMEM on allocation failure
 *         TL_EOVERFLOW if window ID computation overflows
 */
tl_status_t tl_compact_select(tl_compact_ctx_t* ctx);

/**
 * Phase 3: Execute compaction merge.
 *
 * Implements merge algorithm (Compaction Policy LLD Section 7):
 * 1. Build effective tombstone set
 * 2. K-way merge all input segments
 * 3. Skip deleted records (tombstone filtering)
 * 4. Partition output by window boundaries
 * 5. Build L1 segments for windows with live records
 * 6. Build residual tombstone segment if needed
 *
 * Deleted records are COLLECTED but callbacks are NOT fired here.
 * See header comment for deferred callback semantics - callbacks
 * are only invoked after successful publish in tl_compact_one().
 *
 * @param ctx  Context with selected inputs
 * @return TL_OK on success (outputs built)
 *         TL_ENOMEM on allocation failure
 *         TL_EOVERFLOW if window span too large
 */
tl_status_t tl_compact_merge(tl_compact_ctx_t* ctx);

/**
 * Phase 4: Publish compaction results.
 *
 * Implements publication protocol (Compaction Policy LLD Section 8):
 * 1. Build new manifest (OFF-LOCK - this is the expensive part)
 * 2. Acquire writer_mu + seqlock
 * 3. Verify manifest unchanged (abort if changed)
 * 4. Swap manifest pointer (O(1))
 * 5. Release locks
 * 6. Release old manifest
 *
 * @param ctx  Context with built outputs
 * @return TL_OK on success
 *         TL_EBUSY if manifest changed (caller should retry)
 *         TL_ENOMEM on allocation failure
 */
tl_status_t tl_compact_publish(tl_compact_ctx_t* ctx);

/**
 * Complete compaction (all phases).
 *
 * Convenience function that runs select -> merge -> publish.
 * On TL_EBUSY from publish, retries up to max_retries times.
 *
 * @param tl          Timelog instance
 * @param max_retries Max publish retries (default 3)
 * @return TL_OK on success
 *         TL_EOF if no work needed
 *         TL_EBUSY if all retries exhausted
 *         TL_ENOMEM on allocation failure
 *         TL_EOVERFLOW if window span too large
 */
tl_status_t tl_compact_one(tl_timelog_t* tl, int max_retries);

#ifdef TL_TEST_HOOKS
/**
 * Test-only: compute delete debt ratio for a manifest.
 * Exposes internal heuristic for unit testing.
 */
double tl_test_compute_delete_debt(const tl_timelog_t* tl,
                                   const tl_manifest_t* m);
#endif

#endif /* TL_COMPACTION_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_compaction.h
/------------------------------------------------------------------------------/
