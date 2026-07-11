#ifndef TL_ADAPTIVE_H
#define TL_ADAPTIVE_H

/*===========================================================================
 * Adaptive Segmentation Module
 *
 * Computes compaction window sizes from observed data density so that each
 * window holds approximately target_records records, even as the input
 * timestamp rate changes. Disabled by default (target_records == 0).
 *
 * Properties:
 * - No allocation in the policy loop; overflow-safe arithmetic throughout
 * - All fallback paths return the current window (never reset to a base),
 *   which keeps the control loop stable on bad samples
 *
 * Single source of truth:
 * - tl->effective_window_size is the authoritative window
 * - tl_adaptive_state_t holds only EWMA, counters, and density metrics
 *
 * Thread Safety:
 * - State updates run under maint_mu (single writer: maintenance thread)
 * - Density updates fire only when the maintenance thread performs a flush;
 *   manual tl_flush() does not update density
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
} tl_adaptive_state_t;

/*===========================================================================
 * Flush Metrics
 *
 * Metrics captured during flush for the adaptive policy.
 * Bounds cover records only (tombstones excluded).
 *===========================================================================*/

typedef struct tl_flush_metrics {
    uint64_t    record_count;   /* run_len + ooo_len */
    tl_ts_t     min_ts;         /* Min of record timestamps */
    tl_ts_t     max_ts;         /* Max of record timestamps */
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
 * Compute the candidate window for the next compaction.
 *
 * The candidate is target_records / ewma_density, then adjusted by failure
 * backoff, guardrails, hysteresis, and quantum snapping.
 *
 * Every "not ready" or "computation failed" path returns current_window
 * (NOT a base_window). Resetting to a fixed base causes the control loop
 * to oscillate; "keep current" is what gives the loop stability.
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
 * Called by the caller ONLY after compaction publish completes.
 *
 * After a successful publish, the caller must commit the new window AND
 * record success:
 *     tl->effective_window_size = candidate;
 *     tl_adaptive_record_success(&tl->adaptive);
 *
 * On publish failure (ENOMEM/EBUSY), record failure and leave
 * tl->effective_window_size unchanged.
 *
 * @param state  Adaptive state (modified)
 *===========================================================================*/

void tl_adaptive_record_success(tl_adaptive_state_t* state);
void tl_adaptive_record_failure(tl_adaptive_state_t* state);

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
 * Snap a candidate window to the nearest multiple of window_quantum using
 * half-up rounding. Returns current_window for any out-of-range or
 * non-finite input.
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
