/*===========================================================================
 * tl_adaptive.c - Adaptive Segmentation Implementation
 *
 * Window size computation for L1 segmentation, driven by EWMA-smoothed
 * data density. The policy loop allocates nothing.
 *===========================================================================*/

#include "tl_adaptive.h"
#include "../internal/tl_timelog_internal.h"  /* For tl_timelog_t internals */
#include "../storage/tl_window.h"  /* For tl_floor_div_i64, tl_sub_overflow_i64 */

#include <math.h>   /* llround, isnan, isinf, fabs */
#include <string.h> /* memset */

/*===========================================================================
 * Configuration Validation
 *===========================================================================*/

tl_status_t tl_adaptive_config_validate(const tl_adaptive_config_t* cfg) {
    if (cfg == NULL) {
        return TL_EINVAL;
    }

    /* Disabled config (all zeros) is always valid */
    if (cfg->target_records == 0) {
        return TL_OK;
    }

    /* Validate alpha: must be finite and in [0.0, 1.0] */
    if (!isfinite(cfg->alpha) || cfg->alpha < 0.0 || cfg->alpha > 1.0) {
        return TL_EINVAL;
    }

    /* Validate non-negative values (tl_ts_t is signed, negative is invalid) */
    if (cfg->min_window < 0 || cfg->max_window < 0 || cfg->window_quantum < 0) {
        return TL_EINVAL;
    }

    /* Validate guardrails: min <= max (when both are specified) */
    if (cfg->min_window > 0 && cfg->max_window > 0) {
        if (cfg->min_window > cfg->max_window) {
            return TL_EINVAL;
        }
    }

    /* Validate hysteresis: must be in [0, 100] */
    if (cfg->hysteresis_pct > 100) {
        return TL_EINVAL;
    }

    return TL_OK;
}

/*===========================================================================
 * State Lifecycle
 *===========================================================================*/

void tl_adaptive_state_init(tl_adaptive_state_t* state) {
    TL_ASSERT(state != NULL);
    memset(state, 0, sizeof(*state));
}

/*===========================================================================
 * Internal Computation Helpers
 *
 * These are exposed in the header when TL_ADAPTIVE_INTERNAL_TEST is defined.
 *===========================================================================*/

/**
 * Compute span from min_ts to max_ts with overflow check.
 * Returns span on success (always >= 1 for valid input), or 0 on overflow.
 * Note: span = max_ts - min_ts + 1 (single record has span 1)
 */
int64_t tl__adaptive_compute_span(tl_ts_t min_ts, tl_ts_t max_ts) {
    /* Invalid: max < min */
    if (max_ts < min_ts) {
        return 0;
    }

    /* Compute max_ts - min_ts with overflow check */
    int64_t diff;
    if (tl_sub_overflow_i64(max_ts, min_ts, &diff)) {
        return 0;  /* Overflow */
    }

    /* Add 1 for inclusive span, check for overflow */
    if (diff > INT64_MAX - 1) {
        return 0;  /* Would overflow when adding 1 */
    }

    return diff + 1;
}

/**
 * Compute raw candidate from target_records and density.
 * Returns candidate window as double, or 0.0 if density is invalid.
 */
double tl__adaptive_compute_raw_candidate(uint64_t target_records, double density) {
    /* Invalid density: zero, negative, NaN, or Inf */
    if (density <= 0.0 || isnan(density) || isinf(density)) {
        return 0.0;
    }

    return (double)target_records / density;
}

/**
 * Apply guardrails (clamp to [min_window, max_window]).
 * Zero values mean "no limit".
 */
double tl__adaptive_apply_guardrails(double candidate,
                                     tl_ts_t min_window,
                                     tl_ts_t max_window) {
    double result = candidate;

    /* Apply minimum (if specified) */
    if (min_window > 0 && result < (double)min_window) {
        result = (double)min_window;
    }

    /* Apply maximum (if specified) */
    if (max_window > 0 && result > (double)max_window) {
        result = (double)max_window;
    }

    return result;
}

/**
 * Check if hysteresis should skip the change.
 * Returns true if |candidate - current| / current < threshold.
 */
bool tl__adaptive_hysteresis_skip(double candidate,
                                  tl_ts_t current_window,
                                  uint32_t hysteresis_pct) {
    /* Zero threshold means never skip */
    if (hysteresis_pct == 0) {
        return false;
    }

    /* Zero current means can't compute relative change, don't skip */
    if (current_window <= 0) {
        return false;
    }

    double current = (double)current_window;
    double diff = fabs(candidate - current);
    double threshold = current * ((double)hysteresis_pct / 100.0);

    /* Skip if change is STRICTLY less than threshold */
    return diff < threshold;
}

/**
 * Snap a floating-point candidate window to the nearest multiple of
 * window_quantum using banker-style midpoint rounding (midpoint and above
 * rounds up). Returns current_window for any out-of-range or non-finite
 * input so the adaptive control loop remains stable on bad samples.
 *
 * The threshold (q+1)/2 produces correct half-up rounding for both even
 * and odd quanta (e.g. q=7 -> threshold 4; q=8 -> threshold 4).
 */
tl_ts_t tl__adaptive_snap_to_quantum(double candidate,
                                     tl_ts_t window_quantum,
                                     tl_ts_t current_window) {
    /* Zero or negative quantum means no snapping, just round */
    if (window_quantum <= 0) {
        /* Range check: avoid UB in llround for out-of-range values */
        if (candidate <= 0.0 || isnan(candidate) || isinf(candidate) ||
            candidate >= (double)INT64_MAX) {
            return current_window;
        }
        long long wi = llround(candidate);
        return (wi > 0) ? (tl_ts_t)wi : current_window;
    }

    if (candidate <= 0.0 || isnan(candidate) || isinf(candidate)) {
        return current_window;
    }

    /* Avoid UB in llround for out-of-range values */
    if (candidate >= (double)INT64_MAX) {
        return current_window;
    }

    long long wi = llround(candidate);
    if (wi <= 0) {
        return current_window;
    }

    int64_t q = (int64_t)window_quantum;
    int64_t qid = tl_floor_div_i64(wi, q);

    /* Defensive overflow check: mathematically qid * q <= wi < INT64_MAX,
     * but a corrupted density could trigger this path. */
    if (qid > 0 && q > INT64_MAX / qid) {
        return current_window;
    }

    int64_t snapped = qid * q;
    int64_t remainder = wi - snapped;

    /* Half-up rounding: (q+1)/2 produces correct threshold for odd and
     * even quanta alike. */
    if (remainder >= (q + 1) / 2) {
        if (snapped > TL_TS_MAX - q) {
            return current_window;
        }
        snapped += q;
    }

    return (snapped > 0) ? (tl_ts_t)snapped : current_window;
}

/*===========================================================================
 * Density Update
 *===========================================================================*/

void tl_adaptive_update_density(tl_adaptive_state_t* state,
                                const tl_adaptive_config_t* cfg,
                                const tl_flush_metrics_t* metrics) {
    TL_ASSERT(state != NULL);
    TL_ASSERT(cfg != NULL);
    TL_ASSERT(metrics != NULL);

    /* Always increment flush count (even if no records) */
    state->flush_count++;

    /* Skip if no records */
    if (metrics->record_count == 0) {
        return;
    }

    /* Compute span with overflow check */
    int64_t span = tl__adaptive_compute_span(metrics->min_ts, metrics->max_ts);
    if (span <= 0) {
        return;  /* Invalid span (overflow or max < min) */
    }

    /* Compute density: records / span */
    double sample_density = (double)metrics->record_count / (double)span;

    /* Validate computed density */
    if (sample_density <= 0.0 || isnan(sample_density) || isinf(sample_density)) {
        return;
    }

    if (!state->ewma_initialized) {
        /* Seed EWMA with the first sample directly. */
        state->ewma_density = sample_density;
        state->ewma_initialized = true;
    } else {
        /* new = alpha * sample + (1 - alpha) * old */
        state->ewma_density = cfg->alpha * sample_density +
                              (1.0 - cfg->alpha) * state->ewma_density;

        /* Reset on NaN/Inf/non-positive to stop bad state propagating. */
        if (!isfinite(state->ewma_density) || state->ewma_density <= 0.0) {
            state->ewma_density = sample_density;
        }
    }

    /* Update tracking fields */
    state->last_flush_records = metrics->record_count;
    state->last_flush_min_ts = metrics->min_ts;
    state->last_flush_max_ts = metrics->max_ts;
    state->last_density_update_flush = state->flush_count;
}

/*===========================================================================
 * Window Computation
 *===========================================================================*/

tl_ts_t tl_adaptive_compute_candidate(const tl_adaptive_state_t* state,
                                      const tl_adaptive_config_t* cfg,
                                      tl_ts_t current_window) {
    TL_ASSERT(state != NULL);
    TL_ASSERT(cfg != NULL);

    /*-----------------------------------------------------------------------
     * Fallback checks: every "not ready" condition returns current_window
     * rather than the configured base. Resetting to base on transient
     * problems would oscillate the window between base and the target,
     * destabilising the control loop.
     *-----------------------------------------------------------------------*/

    if (cfg->target_records == 0) {
        return current_window;
    }

    if (state->flush_count < cfg->warmup_flushes) {
        return current_window;
    }

    if (!state->ewma_initialized) {
        return current_window;
    }

    if (state->ewma_density <= 0.0 ||
        isnan(state->ewma_density) ||
        isinf(state->ewma_density)) {
        return current_window;
    }

    /* Stale density: too many flushes since the last density update.
     * The recorded density no longer reflects the current input rate. */
    if (cfg->stale_flushes > 0) {
        uint64_t flushes_since_update = state->flush_count -
                                        state->last_density_update_flush;
        if (flushes_since_update > cfg->stale_flushes) {
            return current_window;
        }
    }

    /*-----------------------------------------------------------------------
     * Compute candidate window
     *
     * Target a stable record count per window: candidate = target / density.
     * Apply backoff after repeated publish failures, clamp to guardrails,
     * gate small changes via hysteresis, then snap to the quantum grid.
     * Re-clamp after snapping because rounding can push past the
     * guardrails at edge cases.
     *-----------------------------------------------------------------------*/

    double candidate = tl__adaptive_compute_raw_candidate(cfg->target_records,
                                                          state->ewma_density);
    if (candidate <= 0.0) {
        return current_window;
    }

    /* Backoff expands the window when recent compactions failed, giving
     * the system more headroom before retrying. */
    if (cfg->failure_backoff_threshold > 0 &&
        state->consecutive_failures >= cfg->failure_backoff_threshold) {
        double backoff_mult = 1.0 + (double)cfg->failure_backoff_pct / 100.0;
        candidate *= backoff_mult;
    }

    candidate = tl__adaptive_apply_guardrails(candidate,
                                              cfg->min_window,
                                              cfg->max_window);

    if (candidate <= 0.0 || isnan(candidate) || isinf(candidate)) {
        return current_window;
    }

    /* Hysteresis band: avoid resizing on small fluctuations that would
     * churn windows. The band is a percentage of current_window. */
    if (tl__adaptive_hysteresis_skip(candidate, current_window,
                                     cfg->hysteresis_pct)) {
        return current_window;
    }

    tl_ts_t result = tl__adaptive_snap_to_quantum(candidate,
                                                  cfg->window_quantum,
                                                  current_window);

    /* Snapping can round outside the guardrails (e.g. candidate just
     * below max_window rounds up across the boundary). Re-clamp. */
    if (cfg->min_window > 0 && result < cfg->min_window) {
        result = cfg->min_window;
    }
    if (cfg->max_window > 0 && result > cfg->max_window) {
        result = cfg->max_window;
    }

    return result;
}

/*===========================================================================
 * Success/Failure Tracking
 *===========================================================================*/

void tl_adaptive_record_success(tl_adaptive_state_t* state) {
    TL_ASSERT(state != NULL);
    state->consecutive_failures = 0;
}

void tl_adaptive_record_failure(tl_adaptive_state_t* state) {
    TL_ASSERT(state != NULL);
    /* Guard against overflow (very unlikely but be safe) */
    if (state->consecutive_failures < UINT32_MAX) {
        state->consecutive_failures++;
    }
}
