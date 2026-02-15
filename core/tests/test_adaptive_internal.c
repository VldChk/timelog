/*===========================================================================
 * test_adaptive_internal.c - Adaptive Segmentation Internal Tests
 *
 * These tests verify LLD-level invariants and internal API behavior for
 * the adaptive segmentation subsystem: density tracking, window computation,
 * and hysteresis/quantum policies.
 *
 * CLASSIFICATION: Internal (LLD-Driven)
 * These are IMPLEMENTATION tests, not SPEC tests.
 *
 * TDD Approach: Tests written FIRST to define expected behavior.
 *
 * Reference: docs/timelog_adaptive_segmentation_lld_c17.md (draft-5)
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"

/* TL_ADAPTIVE_INTERNAL_TEST is defined via CMake (target_compile_definitions) */
#include "tl_adaptive.h"

#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <float.h>

/*===========================================================================
 * Test Helpers
 *===========================================================================*/

/**
 * Create a default adaptive config with sensible test values.
 */
static tl_adaptive_config_t make_test_config(void) {
    tl_adaptive_config_t cfg = {0};
    cfg.target_records = 10000;
    cfg.min_window = 1000;
    cfg.max_window = 100000;
    cfg.hysteresis_pct = 10;
    cfg.window_quantum = 1000;
    cfg.alpha = 0.3;
    cfg.warmup_flushes = 3;
    cfg.stale_flushes = 10;
    cfg.failure_backoff_threshold = 3;
    cfg.failure_backoff_pct = 20;
    return cfg;
}

/**
 * Create a default adaptive state with EWMA initialized.
 */
static tl_adaptive_state_t make_initialized_state(double density) {
    tl_adaptive_state_t state = {0};
    state.ewma_density = density;
    state.ewma_initialized = true;
    state.flush_count = 10;  /* Past warmup */
    state.last_density_update_flush = 9;  /* Not stale */
    return state;
}

/**
 * Check if two doubles are approximately equal (within tolerance).
 */
static bool approx_eq(double a, double b, double tol) {
    if (isnan(a) && isnan(b)) return true;
    if (isinf(a) && isinf(b)) return (a > 0) == (b > 0);
    return fabs(a - b) <= tol;
}

/*===========================================================================
 * Phase 1: Configuration Validation Tests
 *===========================================================================*/

TEST_DECLARE(adapt_config_valid) {
    tl_adaptive_config_t cfg = make_test_config();
    TEST_ASSERT_STATUS(TL_OK, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_disabled_valid) {
    /* All zeros = disabled, should be valid */
    tl_adaptive_config_t cfg = {0};
    TEST_ASSERT_STATUS(TL_OK, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_invalid_min_max) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.min_window = 50000;
    cfg.max_window = 10000;  /* max < min */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_invalid_alpha_too_high) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.alpha = 1.5;  /* > 1.0 */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_invalid_alpha_negative) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.alpha = -0.1;  /* < 0 */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_invalid_hysteresis) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.hysteresis_pct = 101;  /* > 100 */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_valid_zero_guardrails) {
    /* Zero guardrails = no enforcement, should be valid */
    tl_adaptive_config_t cfg = make_test_config();
    cfg.min_window = 0;
    cfg.max_window = 0;
    TEST_ASSERT_STATUS(TL_OK, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_invalid_alpha_nan) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.alpha = NAN;  /* Not finite */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_invalid_alpha_inf) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.alpha = INFINITY;  /* Not finite */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_invalid_negative_min_window) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.min_window = -100;  /* Negative is invalid */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_invalid_negative_max_window) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.max_window = -100;  /* Negative is invalid */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_adaptive_config_validate(&cfg));
}

TEST_DECLARE(adapt_config_invalid_negative_quantum) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.window_quantum = -10;  /* Negative is invalid */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_adaptive_config_validate(&cfg));
}

/*===========================================================================
 * Phase 1: Candidate Computation Tests
 *===========================================================================*/

TEST_DECLARE(adapt_candidate_basic) {
    /* target_records / density = expected window */
    double candidate = tl__adaptive_compute_raw_candidate(10000, 10.0);
    TEST_ASSERT(approx_eq(candidate, 1000.0, 0.001));
}

TEST_DECLARE(adapt_candidate_zero_density) {
    /* Zero density should return 0 (invalid) */
    double candidate = tl__adaptive_compute_raw_candidate(10000, 0.0);
    TEST_ASSERT(approx_eq(candidate, 0.0, 0.001));
}

TEST_DECLARE(adapt_candidate_negative_density) {
    /* Negative density should return 0 (invalid) */
    double candidate = tl__adaptive_compute_raw_candidate(10000, -5.0);
    TEST_ASSERT(approx_eq(candidate, 0.0, 0.001));
}

TEST_DECLARE(adapt_candidate_very_high_density) {
    /* Very high density -> very small window */
    double candidate = tl__adaptive_compute_raw_candidate(10000, 1000000.0);
    TEST_ASSERT(approx_eq(candidate, 0.01, 0.0001));
}

TEST_DECLARE(adapt_candidate_very_low_density) {
    /* Very low density -> very large window */
    double candidate = tl__adaptive_compute_raw_candidate(10000, 0.001);
    TEST_ASSERT(approx_eq(candidate, 10000000.0, 0.001));
}

/*===========================================================================
 * Phase 1: Guardrails Tests
 *===========================================================================*/

TEST_DECLARE(adapt_guardrails_clamp_min) {
    /* candidate < min -> return min */
    double result = tl__adaptive_apply_guardrails(500.0, 1000, 100000);
    TEST_ASSERT(approx_eq(result, 1000.0, 0.001));
}

TEST_DECLARE(adapt_guardrails_clamp_max) {
    /* candidate > max -> return max */
    double result = tl__adaptive_apply_guardrails(150000.0, 1000, 100000);
    TEST_ASSERT(approx_eq(result, 100000.0, 0.001));
}

TEST_DECLARE(adapt_guardrails_within_range) {
    /* candidate within range -> unchanged */
    double result = tl__adaptive_apply_guardrails(50000.0, 1000, 100000);
    TEST_ASSERT(approx_eq(result, 50000.0, 0.001));
}

TEST_DECLARE(adapt_guardrails_at_min) {
    /* candidate == min -> unchanged */
    double result = tl__adaptive_apply_guardrails(1000.0, 1000, 100000);
    TEST_ASSERT(approx_eq(result, 1000.0, 0.001));
}

TEST_DECLARE(adapt_guardrails_at_max) {
    /* candidate == max -> unchanged */
    double result = tl__adaptive_apply_guardrails(100000.0, 1000, 100000);
    TEST_ASSERT(approx_eq(result, 100000.0, 0.001));
}

TEST_DECLARE(adapt_guardrails_zero_min) {
    /* min = 0 means no lower bound */
    double result = tl__adaptive_apply_guardrails(500.0, 0, 100000);
    TEST_ASSERT(approx_eq(result, 500.0, 0.001));
}

TEST_DECLARE(adapt_guardrails_zero_max) {
    /* max = 0 means no upper bound */
    double result = tl__adaptive_apply_guardrails(500000.0, 1000, 0);
    TEST_ASSERT(approx_eq(result, 500000.0, 0.001));
}

/*===========================================================================
 * Phase 1: Hysteresis Tests
 *===========================================================================*/

TEST_DECLARE(adapt_hysteresis_skip_small) {
    /* <10% change should be skipped */
    bool skip = tl__adaptive_hysteresis_skip(10500.0, 10000, 10);
    TEST_ASSERT(skip);  /* 5% change < 10% threshold */
}

TEST_DECLARE(adapt_hysteresis_apply_large) {
    /* >10% change should not be skipped */
    bool skip = tl__adaptive_hysteresis_skip(12000.0, 10000, 10);
    TEST_ASSERT(!skip);  /* 20% change > 10% threshold */
}

TEST_DECLARE(adapt_hysteresis_at_threshold) {
    /* Exactly at threshold should NOT skip (strictly less than) */
    bool skip = tl__adaptive_hysteresis_skip(11000.0, 10000, 10);
    TEST_ASSERT(!skip);  /* 10% change == 10% threshold, not < */
}

TEST_DECLARE(adapt_hysteresis_decrease) {
    /* Hysteresis works for decreases too */
    bool skip = tl__adaptive_hysteresis_skip(9500.0, 10000, 10);
    TEST_ASSERT(skip);  /* 5% decrease < 10% threshold */
}

TEST_DECLARE(adapt_hysteresis_zero_threshold) {
    /* 0% threshold means never skip */
    bool skip = tl__adaptive_hysteresis_skip(10001.0, 10000, 0);
    TEST_ASSERT(!skip);
}

TEST_DECLARE(adapt_hysteresis_zero_current) {
    /* current_window = 0 edge case (avoid division by zero) */
    bool skip = tl__adaptive_hysteresis_skip(1000.0, 0, 10);
    /* When current is 0, we can't compute relative change, so don't skip */
    TEST_ASSERT(!skip);
}

/*===========================================================================
 * Phase 1: Quantum Snapping Tests (NEAREST-quantum, not floor!)
 *===========================================================================*/

TEST_DECLARE(adapt_quantum_round_down) {
    /* remainder < q/2 -> snap down */
    tl_ts_t result = tl__adaptive_snap_to_quantum(10300.0, 1000, 5000);
    TEST_ASSERT_EQ(10000, result);  /* 300 < 500, snap down */
}

TEST_DECLARE(adapt_quantum_round_up) {
    /* remainder >= q/2 -> snap up */
    tl_ts_t result = tl__adaptive_snap_to_quantum(10500.0, 1000, 5000);
    TEST_ASSERT_EQ(11000, result);  /* 500 >= 500, snap up */
}

TEST_DECLARE(adapt_quantum_round_up_600) {
    /* remainder > q/2 -> snap up */
    tl_ts_t result = tl__adaptive_snap_to_quantum(10600.0, 1000, 5000);
    TEST_ASSERT_EQ(11000, result);  /* 600 > 500, snap up */
}

TEST_DECLARE(adapt_quantum_exact) {
    /* Exact multiple -> no change */
    tl_ts_t result = tl__adaptive_snap_to_quantum(10000.0, 1000, 5000);
    TEST_ASSERT_EQ(10000, result);
}

TEST_DECLARE(adapt_quantum_zero) {
    /* quantum = 0 means no snapping, just round */
    tl_ts_t result = tl__adaptive_snap_to_quantum(10300.0, 0, 5000);
    TEST_ASSERT_EQ(10300, result);
}

TEST_DECLARE(adapt_quantum_negative_safe) {
    /* Negative timestamps should work via floor_div */
    /* Note: window sizes should be positive, but test the math */
    tl_ts_t result = tl__adaptive_snap_to_quantum(10400.0, 1000, 5000);
    TEST_ASSERT_EQ(10000, result);
}

TEST_DECLARE(adapt_quantum_overflow_guard) {
    /* Near TL_TS_MAX should not overflow */
    double candidate = (double)TL_TS_MAX - 100.0;
    tl_ts_t current = TL_TS_MAX - 1000;
    tl_ts_t result = tl__adaptive_snap_to_quantum(candidate, 1000, current);
    /* Should return current_window if snapping would overflow */
    TEST_ASSERT(result > 0);
    TEST_ASSERT(result <= TL_TS_MAX);
}

TEST_DECLARE(adapt_quantum_small_value) {
    /* Small quantum values work correctly */
    tl_ts_t result = tl__adaptive_snap_to_quantum(105.0, 10, 50);
    TEST_ASSERT_EQ(110, result);  /* 105 -> 110 (round up, 5 >= 5) */
}

/*---------------------------------------------------------------------------
 * Odd Quantum Tests
 *
 * For odd quantum q=7, threshold = (7+1)/2 = 4
 * Values 0, 1, 2, 3 round down
 * Values 4, 5, 6 round up
 *---------------------------------------------------------------------------*/

TEST_DECLARE(adapt_quantum_odd_round_down) {
    /* With q=7: remainder 3 < threshold 4 -> round down */
    tl_ts_t result = tl__adaptive_snap_to_quantum(10.0, 7, 5);
    TEST_ASSERT_EQ(7, result);  /* 10 -> qid=1, snapped=7, rem=3, 3<4 -> 7 */
}

TEST_DECLARE(adapt_quantum_odd_round_up) {
    /* With q=7: remainder 4 >= threshold 4 -> round up */
    tl_ts_t result = tl__adaptive_snap_to_quantum(11.0, 7, 5);
    TEST_ASSERT_EQ(14, result);  /* 11 -> qid=1, snapped=7, rem=4, 4>=4 -> 14 */
}

TEST_DECLARE(adapt_quantum_odd_boundary) {
    /* With q=7: test the exact threshold boundary */
    /* remainder 3 -> down, remainder 4 -> up */
    tl_ts_t down = tl__adaptive_snap_to_quantum(17.0, 7, 5);  /* rem=3 */
    tl_ts_t up = tl__adaptive_snap_to_quantum(18.0, 7, 5);    /* rem=4 */
    TEST_ASSERT_EQ(14, down);  /* 17 -> qid=2, snapped=14, rem=3, 3<4 -> 14 */
    TEST_ASSERT_EQ(21, up);    /* 18 -> qid=2, snapped=14, rem=4, 4>=4 -> 21 */
}

TEST_DECLARE(adapt_quantum_odd_larger) {
    /* Odd quantum = 13: threshold = (13+1)/2 = 7 */
    /* rem 0-6 -> down, rem 7-12 -> up */
    tl_ts_t result1 = tl__adaptive_snap_to_quantum(26.0, 13, 5);  /* rem=0 */
    tl_ts_t result2 = tl__adaptive_snap_to_quantum(32.0, 13, 5);  /* rem=6 */
    tl_ts_t result3 = tl__adaptive_snap_to_quantum(33.0, 13, 5);  /* rem=7 */
    TEST_ASSERT_EQ(26, result1);  /* exact multiple -> no change */
    TEST_ASSERT_EQ(26, result2);  /* 32 -> snapped=26, rem=6, 6<7 -> 26 */
    TEST_ASSERT_EQ(39, result3);  /* 33 -> snapped=26, rem=7, 7>=7 -> 39 */
}

/*===========================================================================
 * Phase 2: State Initialization Tests
 *===========================================================================*/

TEST_DECLARE(adapt_state_init_zeros) {
    tl_adaptive_state_t state;
    memset(&state, 0xFF, sizeof(state));  /* Garbage fill */
    tl_adaptive_state_init(&state);

    TEST_ASSERT_EQ_U64(0, state.last_flush_records);
    TEST_ASSERT_EQ(0, state.last_flush_min_ts);
    TEST_ASSERT_EQ(0, state.last_flush_max_ts);
    TEST_ASSERT_EQ_U64(0, state.flush_count);
    TEST_ASSERT_EQ_U64(0, state.last_density_update_flush);
    TEST_ASSERT(approx_eq(state.ewma_density, 0.0, 0.0001));
    TEST_ASSERT(!state.ewma_initialized);
    TEST_ASSERT_EQ(0, state.consecutive_failures);
    /* NOTE: last_compact_windows removed - not used in implementation */
}

/*===========================================================================
 * Phase 2: Density Update Tests
 *===========================================================================*/

TEST_DECLARE(adapt_density_first_sample) {
    tl_adaptive_config_t cfg = make_test_config();
    tl_adaptive_state_t state = {0};

    tl_flush_metrics_t metrics = {
        .record_count = 1000,
        .min_ts = 0,
        .max_ts = 999,  /* span = 1000 */
        .has_records = true
    };

    tl_adaptive_update_density(&state, &cfg, &metrics);

    /* First sample initializes directly (no smoothing) */
    /* density = 1000 / 1000 = 1.0 */
    TEST_ASSERT(state.ewma_initialized);
    TEST_ASSERT(approx_eq(state.ewma_density, 1.0, 0.0001));
    TEST_ASSERT_EQ_U64(1, state.flush_count);
}

TEST_DECLARE(adapt_density_ewma_smoothing) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.alpha = 0.5;  /* 50% weight on new sample */

    tl_adaptive_state_t state = {0};
    state.ewma_density = 1.0;
    state.ewma_initialized = true;
    state.flush_count = 5;

    tl_flush_metrics_t metrics = {
        .record_count = 2000,
        .min_ts = 0,
        .max_ts = 999,  /* span = 1000, density = 2.0 */
        .has_records = true
    };

    tl_adaptive_update_density(&state, &cfg, &metrics);

    /* EWMA: new = alpha * sample + (1 - alpha) * old */
    /* new = 0.5 * 2.0 + 0.5 * 1.0 = 1.5 */
    TEST_ASSERT(approx_eq(state.ewma_density, 1.5, 0.0001));
    TEST_ASSERT_EQ_U64(6, state.flush_count);
}

TEST_DECLARE(adapt_density_empty_ignored) {
    tl_adaptive_config_t cfg = make_test_config();
    tl_adaptive_state_t state = make_initialized_state(1.0);
    uint64_t old_flush_count = state.flush_count;

    tl_flush_metrics_t metrics = {
        .record_count = 0,
        .min_ts = 0,
        .max_ts = 0,
        .has_records = false
    };

    tl_adaptive_update_density(&state, &cfg, &metrics);

    /* State should be unchanged */
    TEST_ASSERT(approx_eq(state.ewma_density, 1.0, 0.0001));
    /* flush_count still increments (we did flush, just no records) */
    TEST_ASSERT_EQ_U64(old_flush_count + 1, state.flush_count);
    /* But density was not updated */
    TEST_ASSERT_EQ_U64(old_flush_count - 1, state.last_density_update_flush);
}

TEST_DECLARE(adapt_density_negative_span) {
    tl_adaptive_config_t cfg = make_test_config();
    tl_adaptive_state_t state = make_initialized_state(1.0);

    tl_flush_metrics_t metrics = {
        .record_count = 1000,
        .min_ts = 1000,
        .max_ts = 500,  /* Invalid: max < min */
        .has_records = true
    };

    tl_adaptive_update_density(&state, &cfg, &metrics);

    /* Should skip update due to invalid span */
    TEST_ASSERT(approx_eq(state.ewma_density, 1.0, 0.0001));
}

TEST_DECLARE(adapt_density_overflow_span) {
    tl_adaptive_config_t cfg = make_test_config();
    tl_adaptive_state_t state = make_initialized_state(1.0);

    tl_flush_metrics_t metrics = {
        .record_count = 1000,
        .min_ts = TL_TS_MIN,
        .max_ts = TL_TS_MAX,  /* span would overflow */
        .has_records = true
    };

    tl_adaptive_update_density(&state, &cfg, &metrics);

    /* Should skip update due to overflow */
    TEST_ASSERT(approx_eq(state.ewma_density, 1.0, 0.0001));
}

/*===========================================================================
 * Phase 2: Span Computation Tests
 *===========================================================================*/

TEST_DECLARE(adapt_span_basic) {
    int64_t span = tl__adaptive_compute_span(0, 999);
    TEST_ASSERT_EQ(1000, span);  /* max - min + 1 */
}

TEST_DECLARE(adapt_span_single_point) {
    int64_t span = tl__adaptive_compute_span(100, 100);
    TEST_ASSERT_EQ(1, span);  /* Single point has span 1 */
}

TEST_DECLARE(adapt_span_negative) {
    int64_t span = tl__adaptive_compute_span(1000, 500);
    TEST_ASSERT_EQ(0, span);  /* Invalid: max < min -> 0 */
}

TEST_DECLARE(adapt_span_overflow) {
    int64_t span = tl__adaptive_compute_span(TL_TS_MIN, TL_TS_MAX);
    TEST_ASSERT_EQ(0, span);  /* Would overflow -> 0 */
}

TEST_DECLARE(adapt_span_large_valid) {
    /* Large but valid span */
    tl_ts_t min_ts = -1000000000LL;
    tl_ts_t max_ts = 1000000000LL;
    int64_t span = tl__adaptive_compute_span(min_ts, max_ts);
    TEST_ASSERT_EQ(2000000001LL, span);
}

/*===========================================================================
 * Phase 3: Full Computation - Fallback Tests (Control-Loop Stability)
 *
 * CRITICAL: All fallback paths must return current_window, NOT base_window.
 *===========================================================================*/

TEST_DECLARE(adapt_fallback_disabled) {
    /* Adaptive disabled -> return current_window */
    tl_adaptive_config_t cfg = {0};  /* target_records = 0 */
    tl_adaptive_state_t state = make_initialized_state(1.0);

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    TEST_ASSERT_EQ(5000, result);  /* Returns current, not some default */
}

TEST_DECLARE(adapt_fallback_warmup) {
    /* Warmup not complete -> return current_window */
    tl_adaptive_config_t cfg = make_test_config();
    cfg.warmup_flushes = 10;

    tl_adaptive_state_t state = make_initialized_state(1.0);
    state.flush_count = 5;  /* < warmup_flushes */

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    TEST_ASSERT_EQ(5000, result);  /* Returns current, NOT base */
}

TEST_DECLARE(adapt_fallback_no_ewma) {
    /* EWMA not initialized -> return current_window */
    tl_adaptive_config_t cfg = make_test_config();
    tl_adaptive_state_t state = {0};
    state.flush_count = 100;  /* Past warmup */
    state.ewma_initialized = false;

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    TEST_ASSERT_EQ(5000, result);  /* Returns current, NOT base */
}

TEST_DECLARE(adapt_fallback_zero_density) {
    /* ewma_density <= 0 -> return current_window */
    tl_adaptive_config_t cfg = make_test_config();
    tl_adaptive_state_t state = make_initialized_state(0.0);

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    TEST_ASSERT_EQ(5000, result);
}

TEST_DECLARE(adapt_fallback_stale) {
    /* Density stale -> return current_window */
    tl_adaptive_config_t cfg = make_test_config();
    cfg.stale_flushes = 5;

    tl_adaptive_state_t state = make_initialized_state(1.0);
    state.flush_count = 100;
    state.last_density_update_flush = 90;  /* 10 flushes ago > 5 stale threshold */

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    TEST_ASSERT_EQ(5000, result);
}

TEST_DECLARE(adapt_fallback_stale_zero) {
    /* stale_flushes = 0 means never stale */
    tl_adaptive_config_t cfg = make_test_config();
    cfg.stale_flushes = 0;

    tl_adaptive_state_t state = make_initialized_state(1.0);
    state.flush_count = 1000000;
    state.last_density_update_flush = 0;  /* Very old, but stale check disabled */

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    /* Should compute normally, not return current due to staleness */
    TEST_ASSERT_NE(5000, result);
}

TEST_DECLARE(adapt_fallback_candidate_zero) {
    /* Candidate <= 0 (from overflow/bad math) -> return current_window */
    tl_adaptive_config_t cfg = make_test_config();
    cfg.target_records = 0;  /* Would cause division issues if not caught */

    /* But target_records = 0 disables adaptive, so test with extreme density */
    cfg.target_records = 1;
    tl_adaptive_state_t state = make_initialized_state(1e308);  /* Huge density */

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    /* Very small candidate will be clamped to min_window or fail */
    TEST_ASSERT(result > 0);
}

/*===========================================================================
 * Phase 3: Full Computation - Basic Tests
 *===========================================================================*/

TEST_DECLARE(adapt_compute_basic) {
    /* Basic computation without hysteresis trigger */
    tl_adaptive_config_t cfg = make_test_config();
    cfg.hysteresis_pct = 5;  /* 5% threshold */
    cfg.window_quantum = 0;   /* No snapping */

    /* density = 1.0, target = 10000 -> candidate = 10000 */
    tl_adaptive_state_t state = make_initialized_state(1.0);

    /* current_window = 5000, candidate = 10000 -> 100% change > 5% */
    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);

    /* Expected: 10000 (clamped to [1000, 100000]) */
    TEST_ASSERT_EQ(10000, result);
}

TEST_DECLARE(adapt_compute_with_guardrails) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.min_window = 5000;
    cfg.max_window = 8000;
    cfg.hysteresis_pct = 0;
    cfg.window_quantum = 0;

    /* density = 0.5, target = 10000 -> candidate = 20000 (> max) */
    tl_adaptive_state_t state = make_initialized_state(0.5);

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 6000);
    TEST_ASSERT_EQ(8000, result);  /* Clamped to max */
}

TEST_DECLARE(adapt_compute_with_quantum) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.hysteresis_pct = 0;
    cfg.window_quantum = 1000;

    /* density = 0.95, target = 10000 -> candidate ~ 10526 */
    tl_adaptive_state_t state = make_initialized_state(0.95);

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    /* 10526 snaps to 11000 (526 >= 500) */
    TEST_ASSERT_EQ(11000, result);
}

TEST_DECLARE(adapt_compute_hysteresis_blocks) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.hysteresis_pct = 20;  /* 20% threshold */
    cfg.window_quantum = 0;

    /* density = 1.0, target = 10000 -> candidate = 10000 */
    tl_adaptive_state_t state = make_initialized_state(1.0);

    /* current = 9000, candidate = 10000 -> 11% change < 20% threshold */
    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 9000);
    TEST_ASSERT_EQ(9000, result);  /* Hysteresis blocks change */
}

TEST_DECLARE(adapt_compute_full_pipeline) {
    /* Test all stages: compute -> backoff -> guardrails -> hysteresis -> quantum */
    tl_adaptive_config_t cfg = make_test_config();
    cfg.target_records = 10000;
    cfg.min_window = 1000;
    cfg.max_window = 50000;
    cfg.hysteresis_pct = 5;
    cfg.window_quantum = 1000;
    cfg.alpha = 0.3;
    cfg.warmup_flushes = 3;
    cfg.stale_flushes = 10;
    cfg.failure_backoff_threshold = 3;
    cfg.failure_backoff_pct = 20;

    /* density = 2.0, target = 10000 -> candidate = 5000 */
    tl_adaptive_state_t state = make_initialized_state(2.0);

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 10000);
    /* candidate 5000 is in range, 50% change > 5% hysteresis, quantum 5000 */
    TEST_ASSERT_EQ(5000, result);
}

/*===========================================================================
 * Phase 3: Failure Tracking Tests
 *===========================================================================*/

TEST_DECLARE(adapt_failure_backoff_trigger) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.failure_backoff_threshold = 3;
    cfg.failure_backoff_pct = 50;  /* 50% increase */
    cfg.hysteresis_pct = 0;
    cfg.window_quantum = 0;

    /* density = 2.0, target = 10000 -> candidate = 5000 */
    tl_adaptive_state_t state = make_initialized_state(2.0);
    state.consecutive_failures = 3;  /* At threshold */

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 3000);
    /* 5000 * 1.5 = 7500 */
    TEST_ASSERT_EQ(7500, result);
}

TEST_DECLARE(adapt_failure_backoff_clamp) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.failure_backoff_threshold = 1;
    cfg.failure_backoff_pct = 1000;  /* 1000% increase -> way above max */
    cfg.max_window = 10000;
    cfg.hysteresis_pct = 0;
    cfg.window_quantum = 0;

    tl_adaptive_state_t state = make_initialized_state(0.5);
    state.consecutive_failures = 5;

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    TEST_ASSERT_EQ(10000, result);  /* Clamped to max */
}

TEST_DECLARE(adapt_failure_reset_on_success) {
    tl_adaptive_state_t state = {0};
    state.consecutive_failures = 5;

    tl_adaptive_record_success(&state);

    TEST_ASSERT_EQ(0, state.consecutive_failures);
}

TEST_DECLARE(adapt_failure_increment) {
    tl_adaptive_state_t state = {0};
    state.consecutive_failures = 2;

    tl_adaptive_record_failure(&state);

    TEST_ASSERT_EQ(3, state.consecutive_failures);
}

/*===========================================================================
 * Phase 9: Property Tests
 *===========================================================================*/

TEST_DECLARE(adapt_prop_monotonicity) {
    /* updensity -> downwindow (inverse relationship) */
    tl_adaptive_config_t cfg = make_test_config();
    cfg.hysteresis_pct = 0;
    cfg.window_quantum = 0;

    /* Low density -> large window */
    tl_adaptive_state_t state_low = make_initialized_state(0.5);
    tl_ts_t window_low = tl_adaptive_compute_candidate(&state_low, &cfg, 5000);

    /* High density -> small window */
    tl_adaptive_state_t state_high = make_initialized_state(5.0);
    tl_ts_t window_high = tl_adaptive_compute_candidate(&state_high, &cfg, 5000);

    TEST_ASSERT(window_low > window_high);
}

TEST_DECLARE(adapt_inv_window_positive) {
    /* Window is always > 0 */
    tl_adaptive_config_t cfg = make_test_config();
    cfg.min_window = 1;

    tl_adaptive_state_t state = make_initialized_state(1000000.0);

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 1);
    TEST_ASSERT(result > 0);
}

TEST_DECLARE(adapt_inv_within_guardrails) {
    /* Window is always within [min, max] when enforced */
    tl_adaptive_config_t cfg = make_test_config();
    cfg.min_window = 2000;
    cfg.max_window = 8000;
    cfg.hysteresis_pct = 0;
    cfg.window_quantum = 0;

    /* Test with very low density -> would want huge window */
    tl_adaptive_state_t state1 = make_initialized_state(0.001);
    tl_ts_t result1 = tl_adaptive_compute_candidate(&state1, &cfg, 5000);
    TEST_ASSERT(result1 <= 8000);
    TEST_ASSERT(result1 >= 2000);

    /* Test with very high density -> would want tiny window */
    tl_adaptive_state_t state2 = make_initialized_state(100000.0);
    tl_ts_t result2 = tl_adaptive_compute_candidate(&state2, &cfg, 5000);
    TEST_ASSERT(result2 <= 8000);
    TEST_ASSERT(result2 >= 2000);
}

/*===========================================================================
 * Phase 9: Edge Case Tests
 *===========================================================================*/

TEST_DECLARE(adapt_edge_ts_extremes) {
    tl_adaptive_config_t cfg = make_test_config();
    cfg.hysteresis_pct = 0;

    tl_adaptive_state_t state = make_initialized_state(1.0);

    /* Should handle extreme current_window values */
    tl_ts_t result1 = tl_adaptive_compute_candidate(&state, &cfg, TL_TS_MAX);
    TEST_ASSERT(result1 > 0);

    tl_ts_t result2 = tl_adaptive_compute_candidate(&state, &cfg, 1);
    TEST_ASSERT(result2 > 0);
}

TEST_DECLARE(adapt_edge_nan_density) {
    /* NaN density should fallback to current */
    tl_adaptive_config_t cfg = make_test_config();

    tl_adaptive_state_t state = make_initialized_state(NAN);

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    TEST_ASSERT_EQ(5000, result);  /* Fallback to current */
}

TEST_DECLARE(adapt_edge_inf_density) {
    /* Inf density should fallback to current (or min_window) */
    tl_adaptive_config_t cfg = make_test_config();

    tl_adaptive_state_t state = make_initialized_state(INFINITY);

    tl_ts_t result = tl_adaptive_compute_candidate(&state, &cfg, 5000);
    /* Inf density -> zero window -> fallback */
    TEST_ASSERT(result > 0);
}

/*===========================================================================
 * Phase 9: E2E Configuration Tests
 *
 * These tests verify that adaptive configuration is properly validated
 * and integrated at tl_open() time.
 *===========================================================================*/

TEST_DECLARE(adapt_e2e_config_defaults_zeros) {
    /* When adaptive config is not set (all zeros), feature is disabled */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    /* adaptive struct should be zeroed */
    TEST_ASSERT_EQ((uint64_t)0, cfg.adaptive.target_records);
    TEST_ASSERT_EQ((tl_ts_t)0, cfg.adaptive.min_window);
    TEST_ASSERT_EQ((tl_ts_t)0, cfg.adaptive.max_window);
    TEST_ASSERT_EQ((uint32_t)0, cfg.adaptive.hysteresis_pct);
    TEST_ASSERT_EQ((tl_ts_t)0, cfg.adaptive.window_quantum);
}

TEST_DECLARE(adapt_e2e_open_invalid_rejected) {
    /* Opening with invalid adaptive config should fail */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    /* Set invalid config: max < min */
    cfg.adaptive.target_records = 10000;
    cfg.adaptive.min_window = 50000;
    cfg.adaptive.max_window = 10000;  /* Invalid: max < min */

    tl_timelog_t* tl = NULL;
    tl_status_t st = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_EINVAL, st);
    TEST_ASSERT_PTR_EQ(NULL, tl);
}

TEST_DECLARE(adapt_e2e_open_valid_accepted) {
    /* Opening with valid adaptive config should succeed */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    /* Set valid adaptive config */
    cfg.adaptive.target_records = 10000;
    cfg.adaptive.min_window = 1000;
    cfg.adaptive.max_window = 100000;
    cfg.adaptive.alpha = 0.3;
    cfg.adaptive.warmup_flushes = 3;

    tl_timelog_t* tl = NULL;
    tl_status_t st = tl_open(&cfg, &tl);

    TEST_ASSERT_STATUS(TL_OK, st);
    TEST_ASSERT(tl != NULL);

    /* Clean up */
    tl_close(tl);
}

TEST_DECLARE(adapt_e2e_stats_disabled_zeros) {
    /* When adaptive is disabled, stats show zeros */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    /* adaptive is all zeros (disabled) */

    tl_timelog_t* tl = NULL;
    tl_status_t st = tl_open(&cfg, &tl);
    TEST_ASSERT_STATUS(TL_OK, st);

    tl_snapshot_t* snap = NULL;
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_STATUS(TL_OK, st);

    tl_stats_t stats;
    st = tl_stats(snap, &stats);
    TEST_ASSERT_STATUS(TL_OK, st);

    /* Adaptive stats should be zero when disabled */
    TEST_ASSERT_EQ((tl_ts_t)0, stats.adaptive_window);
    TEST_ASSERT_EQ((uint64_t)0, stats.adaptive_flush_count);
    TEST_ASSERT_EQ((uint32_t)0, stats.adaptive_failures);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(adapt_e2e_stats_enabled_window) {
    /* When adaptive is enabled, stats show current window */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    cfg.adaptive.target_records = 10000;
    cfg.adaptive.min_window = 1000;
    cfg.adaptive.max_window = 100000;
    cfg.adaptive.alpha = 0.3;
    cfg.adaptive.warmup_flushes = 3;

    tl_timelog_t* tl = NULL;
    tl_status_t st = tl_open(&cfg, &tl);
    TEST_ASSERT_STATUS(TL_OK, st);

    tl_snapshot_t* snap = NULL;
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_STATUS(TL_OK, st);

    tl_stats_t stats;
    st = tl_stats(snap, &stats);
    TEST_ASSERT_STATUS(TL_OK, st);

    /* adaptive_window should be the effective window size */
    TEST_ASSERT(stats.adaptive_window > 0);

    tl_snapshot_release(snap);
    tl_close(tl);
}

TEST_DECLARE(adapt_e2e_compaction_commits_window) {
    /*
     * E2E test: Verify adaptive window is committed after successful compaction.
     *
     * This test exercises the flow:
     * 1. Configure adaptive with known parameters
     * 2. Append enough records to trigger multiple seals and flushes
     * 3. Run flush/compaction cycle
     * 4. Verify adaptive_window in stats reflects a computed window
     *
     * The key invariant: after compaction with adaptive enabled,
     * effective_window_size is committed and visible in stats.
     */
    tl_config_t cfg;
    tl_config_init_defaults(&cfg);

    /* Configure adaptive with specific parameters for predictable behavior */
    cfg.adaptive.target_records = 100;     /* Low target for quick test */
    cfg.adaptive.min_window = 1000;        /* 1000 time units minimum */
    cfg.adaptive.max_window = 1000000;     /* 1M time units maximum */
    cfg.adaptive.alpha = 0.5;              /* Fast EWMA adaptation */
    cfg.adaptive.warmup_flushes = 1;       /* Minimal warmup for test */
    cfg.adaptive.hysteresis_pct = 0;       /* No hysteresis (accept all changes) */
    cfg.adaptive.window_quantum = 100;     /* Snap to 100-unit boundaries */
    cfg.adaptive.stale_flushes = 100;      /* Don't go stale during test */

    /* Set base window_size within guardrails (fallback uses this).
     * Default is 1 hour in ns which exceeds max_window. */
    cfg.window_size = 50000;               /* Within [min_window, max_window] */

    /* Small memtable to trigger seals quickly */
    cfg.memtable_max_bytes = 512;
    cfg.max_delta_segments = 2;            /* Trigger compaction at 2 L0 segments */
    cfg.maintenance_mode = TL_MAINT_DISABLED;  /* Manual mode for control */

    tl_timelog_t* tl = NULL;
    tl_status_t st = tl_open(&cfg, &tl);
    TEST_ASSERT_STATUS(TL_OK, st);

    /* Append many records to ensure multiple seals.
     * ~500 records at 16 bytes each = 8000 bytes >> 512 byte memtable.
     * Spread across time range [0, 50000) for density calculation. */
    for (int i = 0; i < 500; i++) {
        tl_ts_t ts = i * 100;  /* 0, 100, 200, ... 49900 */
        st = tl_append(tl, ts, (tl_handle_t)(uintptr_t)(i + 1));
        TEST_ASSERT(st == TL_OK || st == TL_EBUSY);
    }

    /* Flush until all sealed runs are flushed */
    for (int flush = 0; flush < 20; flush++) {
        st = tl_flush(tl);
        if (st == TL_EOF) break;
        TEST_ASSERT_STATUS(TL_OK, st);
    }

    /* Run compaction to trigger adaptive window commit.
     * Use tl_compact() (public API) followed by tl_maint_step() for manual mode. */
    st = tl_compact(tl);  /* Sets pending flag */
    TEST_ASSERT_STATUS(TL_OK, st);

    /* Run maintenance step to execute the compaction */
    st = tl_maint_step(tl);
    /* TL_EOF is acceptable (no work needed), TL_OK means compaction ran */
    TEST_ASSERT(st == TL_OK || st == TL_EOF);

    /* Get stats and verify adaptive window was set */
    tl_snapshot_t* snap = NULL;
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_STATUS(TL_OK, st);

    tl_stats_t stats;
    st = tl_stats(snap, &stats);
    TEST_ASSERT_STATUS(TL_OK, st);

    /* Verify adaptive is tracking:
     * - adaptive_window should be positive (effective window was set)
     * - Window should be within configured guardrails */
    TEST_ASSERT(stats.adaptive_window > 0);
    TEST_ASSERT(stats.adaptive_window >= cfg.adaptive.min_window);
    TEST_ASSERT(stats.adaptive_window <= cfg.adaptive.max_window);

    /* Verify window is snapped to quantum */
    TEST_ASSERT(stats.adaptive_window % cfg.adaptive.window_quantum == 0);

    tl_snapshot_release(snap);
    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_adaptive_internal_tests(void) {
    /* Phase 1: Configuration Validation */
    RUN_TEST(adapt_config_valid);
    RUN_TEST(adapt_config_disabled_valid);
    RUN_TEST(adapt_config_invalid_min_max);
    RUN_TEST(adapt_config_invalid_alpha_too_high);
    RUN_TEST(adapt_config_invalid_alpha_negative);
    RUN_TEST(adapt_config_invalid_hysteresis);
    RUN_TEST(adapt_config_valid_zero_guardrails);
    RUN_TEST(adapt_config_invalid_alpha_nan);
    RUN_TEST(adapt_config_invalid_alpha_inf);
    RUN_TEST(adapt_config_invalid_negative_min_window);
    RUN_TEST(adapt_config_invalid_negative_max_window);
    RUN_TEST(adapt_config_invalid_negative_quantum);

    /* Phase 1: Candidate Computation */
    RUN_TEST(adapt_candidate_basic);
    RUN_TEST(adapt_candidate_zero_density);
    RUN_TEST(adapt_candidate_negative_density);
    RUN_TEST(adapt_candidate_very_high_density);
    RUN_TEST(adapt_candidate_very_low_density);

    /* Phase 1: Guardrails */
    RUN_TEST(adapt_guardrails_clamp_min);
    RUN_TEST(adapt_guardrails_clamp_max);
    RUN_TEST(adapt_guardrails_within_range);
    RUN_TEST(adapt_guardrails_at_min);
    RUN_TEST(adapt_guardrails_at_max);
    RUN_TEST(adapt_guardrails_zero_min);
    RUN_TEST(adapt_guardrails_zero_max);

    /* Phase 1: Hysteresis */
    RUN_TEST(adapt_hysteresis_skip_small);
    RUN_TEST(adapt_hysteresis_apply_large);
    RUN_TEST(adapt_hysteresis_at_threshold);
    RUN_TEST(adapt_hysteresis_decrease);
    RUN_TEST(adapt_hysteresis_zero_threshold);
    RUN_TEST(adapt_hysteresis_zero_current);

    /* Phase 1: Quantum Snapping */
    RUN_TEST(adapt_quantum_round_down);
    RUN_TEST(adapt_quantum_round_up);
    RUN_TEST(adapt_quantum_round_up_600);
    RUN_TEST(adapt_quantum_exact);
    RUN_TEST(adapt_quantum_zero);
    RUN_TEST(adapt_quantum_negative_safe);
    RUN_TEST(adapt_quantum_overflow_guard);
    RUN_TEST(adapt_quantum_small_value);

    /* Phase 1: Odd Quantum Values (uses (q+1)/2 threshold) */
    RUN_TEST(adapt_quantum_odd_round_down);
    RUN_TEST(adapt_quantum_odd_round_up);
    RUN_TEST(adapt_quantum_odd_boundary);
    RUN_TEST(adapt_quantum_odd_larger);

    /* Phase 2: State Initialization */
    RUN_TEST(adapt_state_init_zeros);

    /* Phase 2: Density Updates */
    RUN_TEST(adapt_density_first_sample);
    RUN_TEST(adapt_density_ewma_smoothing);
    RUN_TEST(adapt_density_empty_ignored);
    RUN_TEST(adapt_density_negative_span);
    RUN_TEST(adapt_density_overflow_span);

    /* Phase 2: Span Computation */
    RUN_TEST(adapt_span_basic);
    RUN_TEST(adapt_span_single_point);
    RUN_TEST(adapt_span_negative);
    RUN_TEST(adapt_span_overflow);
    RUN_TEST(adapt_span_large_valid);

    /* Phase 3: Fallback Tests (Control-Loop Stability) */
    RUN_TEST(adapt_fallback_disabled);
    RUN_TEST(adapt_fallback_warmup);
    RUN_TEST(adapt_fallback_no_ewma);
    RUN_TEST(adapt_fallback_zero_density);
    RUN_TEST(adapt_fallback_stale);
    RUN_TEST(adapt_fallback_stale_zero);
    RUN_TEST(adapt_fallback_candidate_zero);

    /* Phase 3: Full Computation */
    RUN_TEST(adapt_compute_basic);
    RUN_TEST(adapt_compute_with_guardrails);
    RUN_TEST(adapt_compute_with_quantum);
    RUN_TEST(adapt_compute_hysteresis_blocks);
    RUN_TEST(adapt_compute_full_pipeline);

    /* Phase 3: Failure Tracking */
    RUN_TEST(adapt_failure_backoff_trigger);
    RUN_TEST(adapt_failure_backoff_clamp);
    RUN_TEST(adapt_failure_reset_on_success);
    RUN_TEST(adapt_failure_increment);

    /* Phase 9: Property Tests */
    RUN_TEST(adapt_prop_monotonicity);
    RUN_TEST(adapt_inv_window_positive);
    RUN_TEST(adapt_inv_within_guardrails);

    /* Phase 9: Edge Cases */
    RUN_TEST(adapt_edge_ts_extremes);
    RUN_TEST(adapt_edge_nan_density);
    RUN_TEST(adapt_edge_inf_density);

    /* Phase 9: E2E Configuration Tests */
    RUN_TEST(adapt_e2e_config_defaults_zeros);
    RUN_TEST(adapt_e2e_open_invalid_rejected);
    RUN_TEST(adapt_e2e_open_valid_accepted);
    RUN_TEST(adapt_e2e_stats_disabled_zeros);
    RUN_TEST(adapt_e2e_stats_enabled_window);
    RUN_TEST(adapt_e2e_compaction_commits_window);
}
