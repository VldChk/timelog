/*===========================================================================
 * tl_adaptive.c - Adaptive Segmentation Implementation
 *
 * Implements adaptive window size computation for L1 segmentation based on
 * data density. Pure policy module with no allocation in the computation loop.
 *
 * Reference: docs/timelog_adaptive_segmentation_lld_c17.md (draft-5)
 *===========================================================================*/

#include "tl_adaptive.h"
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

    /* Check for invalid candidate */
    if (candidate <= 0.0 || isnan(candidate) || isinf(candidate)) {
        return current_window;
    }

    /* Range check: avoid UB in llround for out-of-range values */
    if (candidate >= (double)INT64_MAX) {
        return current_window;
    }

    /* Step 1: Round candidate to nearest integer */
    long long wi = llround(candidate);
    if (wi <= 0) {
        return current_window;
    }

    /* Step 2: Floor division to get quantum ID */
    int64_t q = (int64_t)window_quantum;
    int64_t qid = tl_floor_div_i64(wi, q);

    /* Step 3: Compute snapped value */
    int64_t snapped = qid * q;

    /* Step 4: Compute remainder */
    int64_t remainder = wi - snapped;

    /* Step 5: Round up if remainder >= ceil(quantum/2)
     * Use (q+1)/2 for correct rounding with odd quantums.
     * For q=7: threshold=4 (values 4,5,6 round up)
     * For q=8: threshold=4 (values 4,5,6,7 round up) */
    if (remainder >= (q + 1) / 2) {
        /* Overflow guard: check if snapped + q would overflow */
        if (snapped > TL_TS_MAX - q) {
            return current_window;
        }
        snapped += q;
    }

    /* Step 6: Return if valid, else fallback */
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
    if (!metrics->has_records || metrics->record_count == 0) {
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

    /* Update EWMA */
    if (!state->ewma_initialized) {
        /* First sample: initialize directly (no smoothing) */
        state->ewma_density = sample_density;
        state->ewma_initialized = true;
    } else {
        /* Subsequent samples: EWMA smoothing */
        /* new = alpha * sample + (1 - alpha) * old */
        state->ewma_density = cfg->alpha * sample_density +
                              (1.0 - cfg->alpha) * state->ewma_density;

        /* Guard against corrupted EWMA state (NaN propagation).
         * If the result is not finite or is <= 0, reset to current sample. */
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
     * Fallback checks - all return current_window for control-loop stability
     *-----------------------------------------------------------------------*/

    /* Check 1: Adaptive disabled */
    if (cfg->target_records == 0) {
        return current_window;
    }

    /* Check 2: Warmup not complete */
    if (state->flush_count < cfg->warmup_flushes) {
        return current_window;
    }

    /* Check 3: EWMA not initialized */
    if (!state->ewma_initialized) {
        return current_window;
    }

    /* Check 4: Invalid EWMA density (zero, negative, NaN, Inf) */
    if (state->ewma_density <= 0.0 ||
        isnan(state->ewma_density) ||
        isinf(state->ewma_density)) {
        return current_window;
    }

    /* Check 5: Density is stale */
    if (cfg->stale_flushes > 0) {
        uint64_t flushes_since_update = state->flush_count -
                                        state->last_density_update_flush;
        if (flushes_since_update > cfg->stale_flushes) {
            return current_window;
        }
    }

    /*-----------------------------------------------------------------------
     * Compute candidate window
     *-----------------------------------------------------------------------*/

    /* Step 5: Compute raw candidate = target_records / ewma_density */
    double candidate = tl__adaptive_compute_raw_candidate(cfg->target_records,
                                                          state->ewma_density);
    if (candidate <= 0.0) {
        return current_window;
    }

    /* Step 6: Apply failure backoff if triggered */
    if (cfg->failure_backoff_threshold > 0 &&
        state->consecutive_failures >= cfg->failure_backoff_threshold) {
        double backoff_mult = 1.0 + (double)cfg->failure_backoff_pct / 100.0;
        candidate *= backoff_mult;
    }

    /* Step 7: Clamp to guardrails */
    candidate = tl__adaptive_apply_guardrails(candidate,
                                              cfg->min_window,
                                              cfg->max_window);

    /* Validate candidate after guardrails */
    if (candidate <= 0.0 || isnan(candidate) || isinf(candidate)) {
        return current_window;
    }

    /* Step 8: Apply hysteresis - skip small changes */
    if (tl__adaptive_hysteresis_skip(candidate, current_window,
                                     cfg->hysteresis_pct)) {
        return current_window;
    }

    /* Step 9-10: Apply quantum snapping (returns current_window on failure) */
    tl_ts_t result = tl__adaptive_snap_to_quantum(candidate,
                                                  cfg->window_quantum,
                                                  current_window);

    /* Step 11: Re-clamp to guardrails after snapping.
     * Quantum snapping might round outside the guardrail boundaries.
     * E.g., candidate=99.9, max=100, quantum=10 -> snapped=100 (ok)
     * but candidate=95.1, max=100, quantum=10 -> snapped=100 (ok)
     * and candidate=95.5, max=100, quantum=10 -> snapped=100 (close to boundary)
     * In edge cases snapping could push result past guardrails. */
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
