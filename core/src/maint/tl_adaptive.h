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
