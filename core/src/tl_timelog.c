#include "timelog/timelog.h"
#include "internal/tl_defs.h"
#include "internal/tl_alloc.h"
#include "internal/tl_log.h"
#include "internal/tl_sync.h"
#include "internal/tl_seqlock.h"
#include "internal/tl_locks.h"
#include "internal/tl_timelog_internal.h"
#include "delta/tl_memtable.h"
#include "delta/tl_memview.h"
#include "delta/tl_memrun.h"
#include "delta/tl_flush.h"
#include "storage/tl_manifest.h"
#include "query/tl_snapshot.h"
#include "query/tl_plan.h"
#include "query/tl_merge_iter.h"
#include "query/tl_filter.h"
#include "query/tl_point.h"
#include "maint/tl_compaction.h"
#include "maint/tl_adaptive.h"

#include <string.h>

/*===========================================================================
 * Iterator Structure
 *
 * The iterator wraps the query plan, K-way merge, and tombstone filter
 * to provide a simple interface for iterating over query results.
 *===========================================================================*/

struct tl_iter {
    /* Query plan (owns sources and tombstones) - NOT used in point mode */
    tl_plan_t           plan;

    /* K-way merge iterator - NOT used in point mode */
    tl_kmerge_iter_t    kmerge;

    /* Tombstone filter iterator - NOT used in point mode */
    tl_filter_iter_t    filter;

    /* Point lookup result - ONLY used in point mode */
    tl_point_result_t   point_result;
    size_t              point_idx;      /* Current index in point_result */

    /* Parent snapshot (for debug tracking) */
    tl_snapshot_t*      snapshot;

    /* Allocator (borrowed from snapshot) */
    tl_alloc_ctx_t*     alloc;

    /* State */
    bool                done;
    bool                initialized;
    bool                point_mode;     /* True if using point fast path */
};

/*===========================================================================
 * Status Code Strings
 *===========================================================================*/

static const char* status_strings[] = {
    "success",                          /* TL_OK = 0 */
    "end of iteration",                 /* TL_EOF = 1 */
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, /* 2-9 unused */
    "invalid argument",                 /* TL_EINVAL = 10 */
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, /* 11-19 unused */
    "invalid state",                    /* TL_ESTATE = 20 */
    "resource busy",                    /* TL_EBUSY = 21 */
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, /* 22-29 unused */
    "out of memory",                    /* TL_ENOMEM = 30 */
    "arithmetic overflow",              /* TL_EOVERFLOW = 31 */
};

#define STATUS_STRINGS_COUNT (sizeof(status_strings) / sizeof(status_strings[0]))

const char* tl_strerror(tl_status_t s) {
    if (s == TL_EINTERNAL) {
        return "internal error";
    }

    if ((size_t)s < STATUS_STRINGS_COUNT && status_strings[s] != NULL) {
        return status_strings[s];
    }

    return "unknown error";
}

/*===========================================================================
 * Configuration Defaults
 *===========================================================================*/

/**
 * Compute default window size based on time unit.
 * Returns 1 hour in the specified time unit.
 */
static tl_ts_t default_window_size(tl_time_unit_t unit) {
    switch (unit) {
        case TL_TIME_S:  return TL_WINDOW_1H_S;
        case TL_TIME_MS: return TL_WINDOW_1H_MS;
        case TL_TIME_US: return TL_WINDOW_1H_US;
        case TL_TIME_NS: return TL_WINDOW_1H_NS;
        default:         return TL_WINDOW_1H_MS;
    }
}

tl_status_t tl_config_init_defaults(tl_config_t* cfg) {
    if (cfg == NULL) {
        return TL_EINVAL;
    }

    memset(cfg, 0, sizeof(*cfg));

    /* Time resolution */
    cfg->time_unit = TL_TIME_MS;

    /* Storage sizing */
    cfg->target_page_bytes   = TL_DEFAULT_TARGET_PAGE_BYTES;
    cfg->memtable_max_bytes  = TL_DEFAULT_MEMTABLE_MAX_BYTES;
    cfg->ooo_budget_bytes    = 0; /* Will be computed as memtable_max_bytes / 10 */

    /* Backpressure */
    cfg->sealed_max_runs = TL_DEFAULT_SEALED_MAX_RUNS;
    cfg->sealed_wait_ms  = TL_DEFAULT_SEALED_WAIT_MS;

    /* Watermark scheduling: ENABLED by default for better OOO handling.
     * Zero values here mean "auto-derive" in normalize_config.
     * Watermarks will be derived as: hi_wm = 75%, lo_wm = 25% of sealed_max_runs.
     * User can explicitly set values to override. */
    cfg->sealed_hi_wm = 0;  /* 0 = auto-derive in normalize_config */
    cfg->sealed_lo_wm = 0;  /* 0 = auto-derive in normalize_config */

    /* Maintenance timing: 0 means use default (100ms) in normalize */
    cfg->maintenance_wakeup_ms = 0;

    /* Compaction */
    cfg->max_delta_segments     = TL_DEFAULT_MAX_DELTA_SEGMENTS;
    cfg->window_size            = 0; /* Will use default based on time_unit */
    cfg->window_origin          = 0;
    cfg->delete_debt_threshold  = 0.0; /* Disabled */
    cfg->compaction_target_bytes = 0;  /* Unlimited */
    cfg->max_compaction_inputs   = 0;  /* Unlimited */
    cfg->max_compaction_windows  = TL_DEFAULT_MAX_COMPACTION_WINDOWS;

    /* Phase 2 OOO Scaling: Reshape compaction tuning */
    cfg->compaction_strategy    = TL_COMPACT_AUTO;
    cfg->reshape_l0_threshold   = TL_DEFAULT_RESHAPE_L0_THRESHOLD;
    cfg->reshape_max_inputs     = TL_DEFAULT_RESHAPE_MAX_INPUTS;
    cfg->reshape_cooldown_max   = TL_DEFAULT_RESHAPE_COOLDOWN_MAX;

    /* Maintenance: Background by default for automatic segment management.
     * Users doing bulk OOO ingestion should set to TL_MAINT_DISABLED. */
    cfg->maintenance_mode = TL_MAINT_BACKGROUND;

    /* Allocator: NULL means use libc defaults */
    cfg->allocator.ctx        = NULL;
    cfg->allocator.malloc_fn  = NULL;
    cfg->allocator.calloc_fn  = NULL;
    cfg->allocator.realloc_fn = NULL;
    cfg->allocator.free_fn    = NULL;

    /* Logging: NULL means disabled */
    cfg->log_fn    = NULL;
    cfg->log_ctx   = NULL;
    cfg->log_level = TL_LOG_INFO;  /* Default: INFO and below */

    /* Drop callback: NULL means disabled */
    cfg->on_drop_handle = NULL;
    cfg->on_drop_ctx    = NULL;

    return TL_OK;
}

/*===========================================================================
 * Internal Instance State
 *
 * The struct tl_timelog definition is in tl_timelog_internal.h.
 * This ensures a single authoritative definition shared by all internal
 * modules that need field access (tl_timelog.c, tl_snapshot.c, etc.).
 *===========================================================================*/

/*===========================================================================
 * Internal Validation
 *===========================================================================*/

/**
 * Validate configuration values.
 * Returns TL_OK if valid, error code otherwise.
 *
 * Note: Enum checks use explicit casts to int to catch negative values,
 * since C enums are signed integers and callers could pass invalid casts.
 */
static tl_status_t validate_config(const tl_config_t* cfg) {
    TL_ASSERT(cfg != NULL);

    /* Time unit must be valid (check both lower and upper bounds).
     * TL_TIME_S = 0 is the lower bound, TL_TIME_NS is the upper bound. */
    if ((int)cfg->time_unit < (int)TL_TIME_S ||
        (int)cfg->time_unit > (int)TL_TIME_NS) {
        return TL_EINVAL;
    }

    /* Page size must be reasonable */
    if (cfg->target_page_bytes > 0 &&
        cfg->target_page_bytes < TL_RECORD_SIZE * TL_MIN_PAGE_ROWS) {
        return TL_EINVAL;
    }

    /* Maintenance mode must be valid (check both bounds).
     * TL_MAINT_DISABLED = 0 is the lower bound. */
    if ((int)cfg->maintenance_mode < (int)TL_MAINT_DISABLED ||
        (int)cfg->maintenance_mode > (int)TL_MAINT_BACKGROUND) {
        return TL_EINVAL;
    }

    /* Delete debt threshold must be in [0, 1] if set */
    if (cfg->delete_debt_threshold < 0.0 || cfg->delete_debt_threshold > 1.0) {
        return TL_EINVAL;
    }

    /* Window size must be non-negative (0 means use default).
     * A negative window size doesn't make sense for time-based windowing. */
    if (cfg->window_size < 0) {
        return TL_EINVAL;
    }

    /* Validate adaptive segmentation config.
     * tl_adaptive_config_validate() returns TL_OK if disabled (target_records == 0).
     * Otherwise, it validates min/max guardrails, alpha, and other parameters. */
    tl_status_t adapt_st = tl_adaptive_config_validate(&cfg->adaptive);
    if (adapt_st != TL_OK) {
        return adapt_st;
    }

    /* Watermark validation (OOO Scaling Phase 1):
     *
     * Case 1: hi_wm=0 AND lo_wm=0 → Auto-derive (valid, default: 75%/25%)
     * Case 2: hi_wm>0 AND lo_wm=0 → Valid (drain to empty before compaction)
     * Case 3: hi_wm=0 AND lo_wm>0 → INVALID (hi_wm must be set if lo_wm is set)
     * Case 4: hi_wm>0 AND lo_wm>=hi_wm → INVALID (must have lo_wm < hi_wm)
     * Case 5: hi_wm>0 AND lo_wm<hi_wm → Valid watermark pair
     */
    if (cfg->sealed_hi_wm == 0 && cfg->sealed_lo_wm > 0) {
        /* Case 3: lo_wm set without hi_wm */
        return TL_EINVAL;
    }

    if (cfg->sealed_hi_wm > 0 && cfg->sealed_lo_wm >= cfg->sealed_hi_wm) {
        /* Case 4: lo_wm must be strictly less than hi_wm */
        return TL_EINVAL;
    }

    /* Phase 2 OOO Scaling: compaction_strategy must be valid enum value */
    if ((int)cfg->compaction_strategy < (int)TL_COMPACT_AUTO ||
        (int)cfg->compaction_strategy > (int)TL_COMPACT_RESHAPE) {
        return TL_EINVAL;
    }

    return TL_OK;
}

/**
 * Apply default values to config where zero means "use default".
 *
 * IMPORTANT: Order matters! Values that depend on other config values must
 * be computed AFTER those dependencies are defaulted.
 */
static void normalize_config(tl_timelog_t* tl) {
    tl_config_t* cfg = &tl->config;

    /* =======================================================================
     * Step 1: Apply defaults to base config values first
     * ======================================================================= */

    if (cfg->target_page_bytes == 0) {
        cfg->target_page_bytes = TL_DEFAULT_TARGET_PAGE_BYTES;
    }

    if (cfg->memtable_max_bytes == 0) {
        cfg->memtable_max_bytes = TL_DEFAULT_MEMTABLE_MAX_BYTES;
    }

    if (cfg->sealed_max_runs == 0) {
        cfg->sealed_max_runs = TL_DEFAULT_SEALED_MAX_RUNS;
    }

    if (cfg->max_delta_segments == 0) {
        cfg->max_delta_segments = TL_DEFAULT_MAX_DELTA_SEGMENTS;
    }

    /* =======================================================================
     * Step 2: Compute derived values (depend on base config)
     * ======================================================================= */

    /* Window size: 0 means use default based on time unit */
    if (cfg->window_size == 0) {
        tl->effective_window_size = default_window_size(cfg->time_unit);
    } else {
        tl->effective_window_size = cfg->window_size;
    }

    /* OOO budget: 0 means memtable_max_bytes / 10.
     * MUST come after memtable_max_bytes is defaulted! */
    if (cfg->ooo_budget_bytes == 0) {
        tl->effective_ooo_budget = cfg->memtable_max_bytes / 10;
    } else {
        tl->effective_ooo_budget = cfg->ooo_budget_bytes;
    }

    /* =======================================================================
     * Step 3: Watermark normalization (OOO Scaling Phase 1)
     *
     * Watermarks are ENABLED by default for better OOO handling.
     * - If hi_wm=0 AND lo_wm=0: auto-derive from sealed_max_runs (75%/25%)
     * - If hi_wm>0: use explicit values (clamp/adjust as needed)
     * ======================================================================= */
    if (cfg->sealed_hi_wm == 0 && cfg->sealed_lo_wm == 0) {
        /* Auto-derive watermarks from sealed_max_runs (default behavior).
         *
         * Formula (overflow-safe):
         *   lo_wm = floor(25% * n) = n / 4
         *   hi_wm = ceil(75% * n) = n - lo_wm
         *
         * This is mathematically equivalent to (3n+3)/4 but avoids overflow
         * for large n. The hysteresis band is intuitive: hi + lo ≈ n.
         *
         * Examples:
         *   n=4 → lo=1, hi=3 (default config)
         *   n=8 → lo=2, hi=6 (recommended for OOO workloads)
         *   n=1 → lo=0, hi=1 (degenerate but valid) */
        tl->effective_sealed_lo_wm = cfg->sealed_max_runs / 4;
        tl->effective_sealed_hi_wm = cfg->sealed_max_runs - tl->effective_sealed_lo_wm;
        tl->watermarks_enabled = true;
    } else if (cfg->sealed_hi_wm > 0) {
        /* User provided explicit watermarks - clamp and validate */
        if (cfg->sealed_hi_wm > cfg->sealed_max_runs) {
            cfg->sealed_hi_wm = cfg->sealed_max_runs;
        }

        /* Ensure lo_wm < hi_wm after clamping */
        if (cfg->sealed_lo_wm >= cfg->sealed_hi_wm) {
            cfg->sealed_lo_wm = (cfg->sealed_hi_wm > 1) ? cfg->sealed_hi_wm - 1 : 0;
        }

        tl->effective_sealed_hi_wm = cfg->sealed_hi_wm;
        tl->effective_sealed_lo_wm = cfg->sealed_lo_wm;
        tl->watermarks_enabled = true;
    } else {
        /* UNREACHABLE: hi_wm=0 with lo_wm>0 is rejected by validate_config().
         * This assertion documents the invariant - if we ever reach here,
         * validation logic has a bug. */
        TL_ASSERT(0 && "unreachable: validate_config should reject hi_wm=0 with lo_wm>0");
        tl->effective_sealed_hi_wm = 0;
        tl->effective_sealed_lo_wm = 0;
        tl->watermarks_enabled = false;
    }

    /* =======================================================================
     * Step 4: Maintenance timing
     * ======================================================================= */
    if (cfg->maintenance_wakeup_ms == 0) {
        cfg->maintenance_wakeup_ms = TL_DEFAULT_MAINTENANCE_WAKEUP_MS;
    }

    /* =======================================================================
     * Step 5: Phase 2 OOO Scaling reshape parameters
     *
     * These follow the "0 = use default" pattern for consistency with other
     * config values. This allows zero-initialized configs to work correctly.
     * ======================================================================= */
    if (cfg->reshape_l0_threshold == 0) {
        cfg->reshape_l0_threshold = TL_DEFAULT_RESHAPE_L0_THRESHOLD;
    }
    if (cfg->reshape_max_inputs == 0) {
        cfg->reshape_max_inputs = TL_DEFAULT_RESHAPE_MAX_INPUTS;
    }
    if (cfg->reshape_cooldown_max == 0) {
        cfg->reshape_cooldown_max = TL_DEFAULT_RESHAPE_COOLDOWN_MAX;
    }
}

/*===========================================================================
 * Lock Initialization Helpers
 *===========================================================================*/

static tl_status_t init_locks(tl_timelog_t* tl) {
    tl_status_t s;

    s = tl_mutex_init(&tl->writer_mu);
    if (s != TL_OK) return s;

    s = tl_mutex_init(&tl->flush_mu);
    if (s != TL_OK) {
        tl_mutex_destroy(&tl->writer_mu);
        return s;
    }

    s = tl_mutex_init(&tl->maint_mu);
    if (s != TL_OK) {
        tl_mutex_destroy(&tl->flush_mu);
        tl_mutex_destroy(&tl->writer_mu);
        return s;
    }

    s = tl_cond_init(&tl->maint_cond);
    if (s != TL_OK) {
        tl_mutex_destroy(&tl->maint_mu);
        tl_mutex_destroy(&tl->flush_mu);
        tl_mutex_destroy(&tl->writer_mu);
        return s;
    }

    s = tl_mutex_init(&tl->memtable_mu);
    if (s != TL_OK) {
        tl_cond_destroy(&tl->maint_cond);
        tl_mutex_destroy(&tl->maint_mu);
        tl_mutex_destroy(&tl->flush_mu);
        tl_mutex_destroy(&tl->writer_mu);
        return s;
    }

    tl_seqlock_init(&tl->view_seq);

    return TL_OK;
}

static void destroy_locks(tl_timelog_t* tl) {
    tl_mutex_destroy(&tl->memtable_mu);
    tl_cond_destroy(&tl->maint_cond);
    tl_mutex_destroy(&tl->maint_mu);
    tl_mutex_destroy(&tl->flush_mu);
    tl_mutex_destroy(&tl->writer_mu);
}

/*===========================================================================
 * Lifecycle Implementation
 *===========================================================================*/

/**
 * Open a timelog instance.
 *
 * @param cfg  Configuration, or NULL to use defaults. When NULL is passed,
 *             tl_config_init_defaults() values are used. This is the
 *             recommended way to create a simple instance for testing.
 * @param out  Output pointer to receive the instance. Must not be NULL.
 * @return TL_OK on success, error code on failure.
 *
 * Note: tl_open(NULL, &tl) is a valid and documented convenience pattern.
 */
tl_status_t tl_open(const tl_config_t* cfg, tl_timelog_t** out) {
    tl_status_t status;
    tl_timelog_t* tl = NULL;
    tl_config_t default_cfg;

    /* Validate output pointer */
    if (out == NULL) {
        return TL_EINVAL;
    }
    *out = NULL;

    /* Use defaults if no config provided (documented convenience pattern) */
    if (cfg == NULL) {
        tl_config_init_defaults(&default_cfg);
        cfg = &default_cfg;
    }

    /* Validate configuration */
    status = validate_config(cfg);
    if (status != TL_OK) {
        return status;
    }

    /* Create temporary allocator context for initial allocation */
    tl_alloc_ctx_t temp_alloc;
    tl__alloc_init(&temp_alloc, &cfg->allocator);

    /* Allocate instance */
    tl = TL_NEW(&temp_alloc, tl_timelog_t);
    if (tl == NULL) {
        tl__alloc_destroy(&temp_alloc);
        return TL_ENOMEM;
    }

    /* Initialize instance */
    memset(tl, 0, sizeof(*tl));

    /* Copy configuration (immutable after this) */
    tl->config = *cfg;

    /* Initialize allocator (using same settings as temp) */
    tl__alloc_init(&tl->alloc, &cfg->allocator);

    /* Initialize logger */
    tl__log_init(&tl->log, cfg->log_fn, cfg->log_ctx, cfg->log_level);

    /* Normalize configuration values */
    normalize_config(tl);

    /* Initialize synchronization primitives (Phase 1) */
    status = init_locks(tl);
    if (status != TL_OK) {
        tl__alloc_destroy(&tl->alloc);
        temp_alloc.alloc.free_fn(temp_alloc.alloc.ctx, tl);
        return status;
    }

    /* Initialize memtable (Phase 4) */
    status = tl_memtable_init(&tl->memtable,
                               &tl->alloc,
                               tl->config.memtable_max_bytes,
                               tl->effective_ooo_budget,
                               tl->config.sealed_max_runs);
    if (status != TL_OK) {
        destroy_locks(tl);
        tl__alloc_destroy(&tl->alloc);
        temp_alloc.alloc.free_fn(temp_alloc.alloc.ctx, tl);
        return status;
    }

    /* Initialize manifest (Phase 5) */
    status = tl_manifest_create(&tl->alloc, &tl->manifest);
    if (status != TL_OK) {
        tl_memtable_destroy(&tl->memtable);
        destroy_locks(tl);
        tl__alloc_destroy(&tl->alloc);
        temp_alloc.alloc.free_fn(temp_alloc.alloc.ctx, tl);
        return status;
    }
    tl->next_gen = 1;

    /* Initialize snapshot memview cache (optional) */
    tl->memview_cache = NULL;
    tl->memview_cache_epoch = 0;

#ifdef TL_DEBUG
    /* Initialize debug snapshot counter */
    tl_atomic_init_u32(&tl->snapshot_count, 0);
#endif

    /* Initialize operational counters (cumulative since open) */
    tl_atomic_init_u64(&tl->seals_total, 0);
    tl_atomic_init_u64(&tl->ooo_budget_hits, 0);
    tl_atomic_init_u64(&tl->backpressure_waits, 0);
    tl_atomic_init_u64(&tl->flushes_total, 0);
    tl_atomic_init_u64(&tl->compactions_total, 0);

    /* Initialize OOO Scaling counters (Phase 1) */
    tl_atomic_init_u64(&tl->flush_first_cycles, 0);
    tl_atomic_init_u64(&tl->compaction_deferred, 0);
    tl_atomic_init_u64(&tl->compaction_forced, 0);

    /* Initialize OOO Scaling counters (Phase 2) */
    tl_atomic_init_u64(&tl->reshape_compactions_total, 0);
    tl_atomic_init_u64(&tl->rebase_publish_success, 0);
    tl_atomic_init_u64(&tl->rebase_publish_fallback, 0);
    tl_atomic_init_u64(&tl->window_bound_exceeded, 0);
    tl_atomic_init_u64(&tl->rebase_l1_conflict, 0);

    /* Initialize reshape cooldown counter (protected by maint_mu) */
    tl->consecutive_reshapes = 0;

    /* Initialize lifecycle state */
    tl->is_open = true;

    /* Initialize maintenance state (Phase 7).
     * All fields are plain bools/enum protected by maint_mu.
     * Worker is auto-started below when mode is TL_MAINT_BACKGROUND. */
    tl->maint_state = TL_WORKER_STOPPED;
    tl->maint_shutdown = false;
    tl->flush_pending = false;
    tl->compact_pending = false;

    /* Initialize adaptive segmentation state (V-Next).
     * All zeros = disabled behavior; state tracks EWMA and counters only. */
    tl_adaptive_state_init(&tl->adaptive);

    /* Auto-start background maintenance worker when mode is BACKGROUND.
     * This is the default mode - automatic segment management without
     * explicit tl_maint_start() call. Users doing bulk OOO ingestion
     * should set mode to TL_MAINT_DISABLED for better performance. */
    if (tl->config.maintenance_mode == TL_MAINT_BACKGROUND) {
        status = tl_maint_start(tl);
        if (status != TL_OK) {
            /* Failed to start worker - clean up and fail open */
            tl_manifest_release(tl->manifest);
            tl_memtable_destroy(&tl->memtable);
            destroy_locks(tl);
            tl__alloc_destroy(&tl->alloc);
            temp_alloc.alloc.free_fn(temp_alloc.alloc.ctx, tl);
            return status;
        }
    }

    /* Log successful open */
    tl_log_ctx_t* log = &tl->log;
    TL_LOG_INFO("timelog opened: time_unit=%d, page_bytes=%zu, memtable_bytes=%zu",
                (int)tl->config.time_unit,
                tl->config.target_page_bytes,
                tl->config.memtable_max_bytes);

    *out = tl;
    return TL_OK;
}

void tl_close(tl_timelog_t* tl) {
    if (tl == NULL) {
        return;
    }

    if (!tl->is_open) {
        return;
    }

    tl_log_ctx_t* log = &tl->log;
    TL_LOG_INFO("timelog closing");

    /* Stop maintenance worker before closing (Phase 7).
     * tl_maint_stop() is idempotent and works for any mode.
     * We do this BEFORE setting is_open = false because tl_maint_stop
     * doesn't check is_open (allowing cleanup flexibility). */
    tl_maint_stop(tl);

    /* Mark as closed (prevents further operations) */
    tl->is_open = false;

#ifdef TL_DEBUG
    /*
     * Debug-only check: assert no outstanding snapshots.
     * If this assertion fires, the caller has a snapshot leak.
     * All snapshots must be released before calling tl_close().
     */
    uint32_t outstanding = tl_atomic_load_relaxed_u32(&tl->snapshot_count);
    TL_ASSERT_MSG(outstanding == 0,
        "tl_close() called with outstanding snapshots - caller must release all snapshots first");
#endif

    /* Release manifest (Phase 5) */
    if (tl->manifest != NULL) {
        tl_manifest_release(tl->manifest);
        tl->manifest = NULL;
    }

    /* Release cached memview (if any) */
    if (tl->memview_cache != NULL) {
        tl_memview_shared_release(tl->memview_cache);
        tl->memview_cache = NULL;
    }

    /* Destroy memtable (Phase 4) */
    tl_memtable_destroy(&tl->memtable);

    /* Destroy synchronization primitives */
    destroy_locks(tl);

    /* Get allocator context before we destroy it */
    tl_alloc_ctx_t alloc = tl->alloc;

    /* Destroy allocator tracking */
    tl__alloc_destroy(&tl->alloc);

    /* Free the instance itself using the original allocator */
    alloc.alloc.free_fn(alloc.alloc.ctx, tl);
}

/*===========================================================================
 * Write Path Implementation (Phase 4)
 *===========================================================================*/

/* Forward declaration for deferred signaling (defined in maintenance section) */
static void tl__maint_request_flush(tl_timelog_t* tl);

/**
 * Handle sealing with backpressure after a successful write.
 *
 * Must be called with writer_mu held. Returns with writer_mu held.
 * Will temporarily drop writer_mu if waiting for space.
 *
 * DEFERRED SIGNALING: This function does NOT signal the maintenance worker.
 * The caller MUST check *need_signal after releasing writer_mu and call
 * tl__maint_request_flush() if true. This respects lock ordering.
 *
 * @param tl          Timelog instance
 * @param need_signal Output: true if caller should signal maintenance worker
 * @return TL_OK if seal succeeded or not needed,
 *         TL_EBUSY if caller should trigger flush (manual mode only)
 */
static tl_status_t handle_seal_with_backpressure(tl_timelog_t* tl,
                                                  bool* need_signal) {
    *need_signal = false;

    /* Check if seal is needed */
    if (!tl_memtable_should_seal(&tl->memtable)) {
        return TL_OK;
    }

    /* Track if OOO budget triggered the seal (for instrumentation) */
    bool ooo_triggered = tl_memtable_ooo_budget_exceeded(&tl->memtable);

    /* Try to seal */
    tl_status_t seal_st = tl_memtable_seal(&tl->memtable,
                                            &tl->memtable_mu,
                                            &tl->maint_cond);
    if (seal_st == TL_OK) {
        /* Seal succeeded - signal needed (deferred until after unlock) */
        tl_atomic_inc_u64(&tl->seals_total);
        if (ooo_triggered) {
            tl_atomic_inc_u64(&tl->ooo_budget_hits);
        }
        *need_signal = true;
        return TL_OK;
    }

    if (seal_st != TL_EBUSY) {
        /* Unexpected error */
        return seal_st;
    }

    /* TL_EBUSY: sealed queue is full */
    if (tl->config.maintenance_mode == TL_MAINT_DISABLED) {
        /* Manual mode: return EBUSY so caller can call tl_flush() */
        return TL_EBUSY;
    }

    /* Background mode: wait for flush to make space, then retry seal.
     * Must drop writer_mu while waiting to allow flush to proceed.
     * This is safe because the write already succeeded. */
    tl_atomic_inc_u64(&tl->backpressure_waits);
    TL_UNLOCK_WRITER(tl);

    TL_LOCK_MEMTABLE(tl);
    bool have_space = tl_memtable_wait_for_space(&tl->memtable,
                                                   &tl->memtable_mu,
                                                   &tl->maint_cond,
                                                   tl->config.sealed_wait_ms);
    TL_UNLOCK_MEMTABLE(tl);

    /* Re-acquire writer lock */
    TL_LOCK_WRITER(tl);

    if (!have_space) {
        /* Timeout waiting for space - still return TL_OK since write succeeded.
         * The next write will also try to seal/wait. */
        return TL_OK;
    }

    /* Retry seal now that we have space */
    seal_st = tl_memtable_seal(&tl->memtable,
                                &tl->memtable_mu,
                                &tl->maint_cond);
    if (seal_st == TL_OK) {
        /* Seal succeeded - signal needed (deferred until after unlock) */
        tl_atomic_inc_u64(&tl->seals_total);
        *need_signal = true;
    }
    /* Ignore any error - write succeeded, this is best-effort */
    return TL_OK;
}

tl_status_t tl_append(tl_timelog_t* tl, tl_ts_t ts, tl_handle_t handle) {
    if (tl == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    tl_status_t st;
    bool need_signal = false;

    /* Acquire writer lock */
    TL_LOCK_WRITER(tl);

    /* Insert into memtable */
    st = tl_memtable_insert(&tl->memtable, ts, handle);
    if (st != TL_OK) {
        TL_UNLOCK_WRITER(tl);
        return st;
    }

    /* Handle seal with backpressure (deferred signaling) */
    st = handle_seal_with_backpressure(tl, &need_signal);

    TL_UNLOCK_WRITER(tl);

    /* Deferred signal AFTER releasing writer_mu (respects lock ordering) */
    if (need_signal) {
        tl__maint_request_flush(tl);
    }

    return st;
}

tl_status_t tl_append_batch(tl_timelog_t* tl, const tl_record_t* records,
                            size_t n, uint32_t flags) {
    if (tl == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }
    if (n == 0) {
        return TL_OK; /* No-op for empty batch */
    }
    if (records == NULL) {
        return TL_EINVAL;
    }

    tl_status_t st;
    bool need_signal = false;

    /* Acquire writer lock */
    TL_LOCK_WRITER(tl);

    /* Insert batch into memtable */
    st = tl_memtable_insert_batch(&tl->memtable, records, n, flags);
    if (st != TL_OK) {
        TL_UNLOCK_WRITER(tl);
        return st;
    }

    /* Handle seal with backpressure (deferred signaling) */
    st = handle_seal_with_backpressure(tl, &need_signal);

    TL_UNLOCK_WRITER(tl);

    /* Deferred signal AFTER releasing writer_mu (respects lock ordering) */
    if (need_signal) {
        tl__maint_request_flush(tl);
    }

    return st;
}

tl_status_t tl_delete_range(tl_timelog_t* tl, tl_ts_t t1, tl_ts_t t2) {
    if (tl == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    /* Validate range: half-open interval [t1, t2) must not be negative.
     * - t1 == t2: Empty range, allowed as no-op (no work, returns TL_OK)
     * - t1 > t2:  Invalid negative range, rejected as TL_EINVAL */
    if (t1 > t2) {
        return TL_EINVAL;
    }

    tl_status_t st;
    bool need_signal = false;

    /* Acquire writer lock */
    TL_LOCK_WRITER(tl);

    /* Insert tombstone into memtable */
    st = tl_memtable_insert_tombstone(&tl->memtable, t1, t2);
    if (st != TL_OK) {
        TL_UNLOCK_WRITER(tl);
        return st;
    }

    /* Handle seal with backpressure (deferred signaling) */
    st = handle_seal_with_backpressure(tl, &need_signal);

    TL_UNLOCK_WRITER(tl);

    /* Deferred signal AFTER releasing writer_mu (respects lock ordering) */
    if (need_signal) {
        tl__maint_request_flush(tl);
    }

    return st;
}

tl_status_t tl_delete_before(tl_timelog_t* tl, tl_ts_t cutoff) {
    if (tl == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    tl_status_t st;
    bool need_signal = false;

    /* Acquire writer lock */
    TL_LOCK_WRITER(tl);

    /* Insert unbounded tombstone [TL_TS_MIN, cutoff) */
    st = tl_memtable_insert_tombstone(&tl->memtable, TL_TS_MIN, cutoff);
    if (st != TL_OK) {
        TL_UNLOCK_WRITER(tl);
        return st;
    }

    /* Handle seal with backpressure (deferred signaling) */
    st = handle_seal_with_backpressure(tl, &need_signal);

    TL_UNLOCK_WRITER(tl);

    /* Deferred signal AFTER releasing writer_mu (respects lock ordering) */
    if (need_signal) {
        tl__maint_request_flush(tl);
    }

    return st;
}

/*===========================================================================
 * Phase 8 Stubs (Compaction)
 *
 * These functions are placeholders for Phase 8 implementation.
 * They return appropriate values for Phase 7 testing.
 *===========================================================================*/

/**
 * Check if compaction is needed.
 * Delegates to compaction module (Phase 8).
 */
static bool tl__compaction_needed(tl_timelog_t* tl) {
    return tl_compact_needed(tl);
}

/**
 * Perform one compaction step.
 * Delegates to compaction module (Phase 8).
 */
static tl_status_t tl__compact_one_step(tl_timelog_t* tl) {
    /* Use 3 retries per Compaction Policy LLD Section 8 */
    return tl_compact_one(tl, 3);
}

/*===========================================================================
 * Flush Implementation
 *===========================================================================*/

/**
 * Flush a single memrun to L0 segment and publish to manifest.
 *
 * Algorithm (from plan_phase5.md Section 3.2):
 * 1. Build L0 segment OFF-LOCK (expensive)
 * 2. Under writer_mu + seqlock:
 *    - Swap manifest to include new L0
 *    - Pop memrun from sealed queue (INSIDE seqlock for atomicity)
 * 3. Release old references (after unlock)
 *
 * @param tl  Timelog instance
 * @param mr  Pinned memrun (caller holds reference, we release it on success)
 * @return TL_OK on success, error otherwise
 */
static tl_status_t flush_one_memrun(tl_timelog_t* tl, tl_memrun_t* mr) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(mr != NULL);

    tl_status_t st;

    /* Step 1: Acquire generation under writer_mu to prevent races.
     * We only need the lock briefly to get a unique generation. */
    TL_LOCK_WRITER(tl);
    uint32_t gen = tl->next_gen++;
    TL_UNLOCK_WRITER(tl);

    /* Step 2: Build L0 segment OFF-LOCK (expensive operation) */
    tl_flush_ctx_t ctx = {
        .alloc = &tl->alloc,
        .target_page_bytes = tl->config.target_page_bytes,
        .generation = gen
    };

    tl_segment_t* seg = NULL;
    st = tl_flush_build(&ctx, mr, &seg);
    if (st != TL_OK) {
        return st;
    }

    /* Step 3: Publication under writer_mu + seqlock */
    TL_LOCK_WRITER(tl);
    tl_seqlock_write_begin(&tl->view_seq);

    /* Build new manifest with L0 segment added */
    tl_manifest_builder_t builder;
    tl_manifest_builder_init(&builder, &tl->alloc, tl->manifest);
    st = tl_manifest_builder_add_l0(&builder, seg);
    if (st != TL_OK) {
        tl_manifest_builder_destroy(&builder);
        tl_seqlock_write_end(&tl->view_seq);
        TL_UNLOCK_WRITER(tl);
        tl_segment_release(seg);
        return st;
    }

    tl_manifest_t* new_manifest = NULL;
    st = tl_manifest_builder_build(&builder, &new_manifest);
    tl_manifest_builder_destroy(&builder);
    if (st != TL_OK) {
        tl_seqlock_write_end(&tl->view_seq);
        TL_UNLOCK_WRITER(tl);
        tl_segment_release(seg);
        return st;
    }

    /* Swap manifest */
    tl_manifest_t* old_manifest = tl->manifest;
    tl->manifest = new_manifest;

    /* Remove memrun from sealed queue INSIDE seqlock critical section.
     * This ensures atomicity: no snapshot sees BOTH segment AND memrun.
     * Lock ordering (writer_mu -> memtable_mu) is respected per hierarchy.
     */
    TL_LOCK_MEMTABLE(tl);
    tl_memtable_pop_oldest(&tl->memtable, &tl->maint_cond);
    TL_UNLOCK_MEMTABLE(tl);

    tl_seqlock_write_end(&tl->view_seq);
    TL_UNLOCK_WRITER(tl);

    /* Step 3: Release old references (safe after unlock) */
    tl_manifest_release(old_manifest);
    tl_memrun_release(mr);  /* Release our pin from peek_oldest */

    /* Increment flush counter */
    tl_atomic_inc_u64(&tl->flushes_total);

    return TL_OK;
}

/*===========================================================================
 * tl__flush_one - Flush One Sealed Memrun
 *
 * This is a wrapper around flush_one_memrun that handles:
 * 1. Acquire flush_mu (serializes flush operations)
 * 2. Peek + pin memrun from sealed queue
 * 3. Capture flush metrics for adaptive density (record-only bounds)
 * 4. Call flush_one_memrun
 * 5. Handle errors with proper cleanup
 * 6. Update adaptive density if enabled (under maint_mu)
 *
 * ADAPTIVE INTEGRATION (Phase 6):
 * Only this function (maintenance thread path) updates density.
 * Manual tl_flush() does NOT update density - acceptable because
 * manual mode users don't use adaptive segmentation anyway.
 *
 * Lock ordering note: maint_mu is acquired AFTER flush_mu is released
 * to respect the lock hierarchy (maint_mu -> flush_mu).
 *
 * @return TL_OK     - One memrun flushed successfully
 *         TL_EOF    - No sealed memruns to flush
 *         TL_ENOMEM - Build failed (memrun preserved for retry)
 *         TL_EINTERNAL - Publication failed
 *===========================================================================*/
static tl_status_t tl__flush_one(tl_timelog_t* tl) {
    TL_ASSERT(tl != NULL);

    /* Serialize flush operations */
    TL_LOCK_FLUSH(tl);

    /* Peek and pin oldest sealed memrun */
    tl_memrun_t* mr = NULL;
    TL_LOCK_MEMTABLE(tl);
    tl_status_t st = tl_memtable_peek_oldest(&tl->memtable, &mr);
    TL_UNLOCK_MEMTABLE(tl);

    if (st != TL_OK || mr == NULL) {
        TL_UNLOCK_FLUSH(tl);
        return TL_EOF;  /* No work */
    }

    /*-----------------------------------------------------------------------
     * Capture flush metrics BEFORE flush (memrun will be released on success).
     * Record-only bounds - excludes tombstones per LLD.
     *-----------------------------------------------------------------------*/
    tl_flush_metrics_t metrics = { 0 };
    if (tl->config.adaptive.target_records > 0) {
        size_t run_len = tl_memrun_run_len(mr);
        size_t ooo_len = tl_memrun_ooo_len(mr);
        metrics.record_count = (uint64_t)(run_len + ooo_len);
        metrics.has_records = (metrics.record_count > 0);

        if (metrics.has_records) {
            const tl_record_t* run = tl_memrun_run_data(mr);
            const tl_record_t* ooo = tl_memrun_ooo_data(mr);

            /* Compute record-only min/max.
             * Both run and ooo are sorted, so min is first, max is last. */
            if (run_len > 0 && ooo_len > 0) {
                metrics.min_ts = TL_MIN(run[0].ts, ooo[0].ts);
                metrics.max_ts = TL_MAX(run[run_len - 1].ts, ooo[ooo_len - 1].ts);
            } else if (run_len > 0) {
                metrics.min_ts = run[0].ts;
                metrics.max_ts = run[run_len - 1].ts;
            } else {  /* ooo_len > 0 */
                metrics.min_ts = ooo[0].ts;
                metrics.max_ts = ooo[ooo_len - 1].ts;
            }
        }
    }

    /* Build and publish (releases our reference on success) */
    st = flush_one_memrun(tl, mr);

    if (st != TL_OK) {
        /* On failure, release our pin - memrun stays in queue for retry */
        tl_memrun_release(mr);
    }

    TL_UNLOCK_FLUSH(tl);

    /*-----------------------------------------------------------------------
     * Update adaptive density AFTER releasing flush_mu (lock ordering).
     * Call on ALL successful flushes (even tombstone-only) so flush_count
     * increments properly for stale_flushes detection. The function will
     * skip density update if no records present.
     *-----------------------------------------------------------------------*/
    if (st == TL_OK && tl->config.adaptive.target_records > 0) {
        TL_LOCK_MAINT(tl);
        tl_adaptive_update_density(&tl->adaptive,
                                   &tl->config.adaptive,
                                   &metrics);
        TL_UNLOCK_MAINT(tl);
    }

    return st;
}

tl_status_t tl_flush(tl_timelog_t* tl) {
    if (tl == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    tl_status_t st;

    /* Serialize flushes with flush_mu to prevent concurrent flush operations.
     * Lock ordering: flush_mu -> writer_mu (per lock hierarchy). */
    TL_LOCK_FLUSH(tl);

    /* Flush loop: seal active, flush all sealed, retry until everything flushed.
     * This ensures the contract "flush active + sealed before return". */
    for (;;) {
        /* Try to seal current active memtable if non-empty */
        TL_LOCK_WRITER(tl);
        bool need_seal = !tl_memtable_is_active_empty(&tl->memtable);
        if (need_seal) {
            st = tl_memtable_seal(&tl->memtable,
                                   &tl->memtable_mu,
                                   &tl->maint_cond);
            if (st != TL_OK && st != TL_EBUSY) {
                TL_UNLOCK_WRITER(tl);
                TL_UNLOCK_FLUSH(tl);
                return st;
            }
            /* TL_EBUSY means queue full - flush sealed memruns first */
        }
        TL_UNLOCK_WRITER(tl);

        /* Flush one sealed memrun */
        tl_memrun_t* mr = NULL;
        TL_LOCK_MEMTABLE(tl);
        st = tl_memtable_peek_oldest(&tl->memtable, &mr);
        TL_UNLOCK_MEMTABLE(tl);

        if (st != TL_OK || mr == NULL) {
            /* No sealed memruns - check if we're done */
            TL_LOCK_WRITER(tl);
            bool active_empty = tl_memtable_is_active_empty(&tl->memtable);
            TL_UNLOCK_WRITER(tl);

            if (active_empty) {
                break;  /* All flushed - done */
            }
            /* Active not empty but couldn't seal - this shouldn't happen
             * since we just flushed and freed queue space. Retry once. */
            continue;
        }

        /* Flush this memrun (releases our reference on success) */
        st = flush_one_memrun(tl, mr);
        if (st != TL_OK) {
            /* Release our pin and propagate error */
            tl_memrun_release(mr);
            TL_UNLOCK_FLUSH(tl);
            return st;
        }
        /* Loop to flush more or retry sealing */
    }

    TL_UNLOCK_FLUSH(tl);
    return TL_OK;
}

/*===========================================================================
 * Maintenance Request Helpers (Phase 7)
 *
 * These functions implement the deferred signaling pattern:
 * - Set flag UNDER maint_mu (atomically with respect to worker)
 * - Signal condvar only if worker is RUNNING
 * - MUST be called AFTER releasing writer_mu (lock ordering)
 *
 * CRITICAL: Always set the flag, but only signal if worker is RUNNING.
 * This ensures work isn't lost if writes happen before tl_maint_start().
 *===========================================================================*/

/**
 * Request flush work from background worker.
 *
 * Sets flush_pending flag and signals worker if running.
 * Called from write path after detecting sealed memruns exist.
 *
 * MUST be called AFTER releasing writer_mu (deferred signaling pattern).
 */
static void tl__maint_request_flush(tl_timelog_t* tl) {
    TL_ASSERT(tl != NULL);

    /* Skip if not in background mode */
    if (tl->config.maintenance_mode != TL_MAINT_BACKGROUND) {
        return;
    }

    TL_LOCK_MAINT(tl);

    /* ALWAYS set flag - preserves work even if worker not yet started */
    tl->flush_pending = true;

    /* Only signal if worker is actually running */
    if (tl->maint_state == TL_WORKER_RUNNING) {
        tl_cond_signal(&tl->maint_cond);
    }

    TL_UNLOCK_MAINT(tl);
}

/**
 * Request compaction work.
 *
 * Sets compact_pending flag and signals worker if running in background mode.
 * In manual mode, sets the flag for tl_maint_step() to honor.
 * Called from tl_compact() API.
 *
 * MUST be called AFTER releasing any higher-priority locks.
 */
static void tl__maint_request_compact(tl_timelog_t* tl) {
    TL_ASSERT(tl != NULL);

    TL_LOCK_MAINT(tl);

    /* ALWAYS set flag - in manual mode, tl_maint_step() checks this;
     * in background mode, worker checks this. */
    tl->compact_pending = true;

    /* Only signal if background mode AND worker is actually running */
    if (tl->config.maintenance_mode == TL_MAINT_BACKGROUND &&
        tl->maint_state == TL_WORKER_RUNNING) {
        tl_cond_signal(&tl->maint_cond);
    }

    TL_UNLOCK_MAINT(tl);
}

/*===========================================================================
 * Compaction API
 *===========================================================================*/

tl_status_t tl_compact(tl_timelog_t* tl) {
    if (tl == NULL) {
        return TL_EINVAL;
    }

    if (!tl->is_open) {
        return TL_ESTATE;
    }

    /* Request compaction (deferred signaling handled internally) */
    tl__maint_request_compact(tl);

    return TL_OK;
}

/*===========================================================================
 * Snapshot API Implementation (Phase 5)
 *===========================================================================*/

tl_status_t tl_snapshot_acquire(const tl_timelog_t* tl, tl_snapshot_t** out) {
    if (tl == NULL || out == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    /* Cast away const - internal locking requires non-const access */
    return tl_snapshot_acquire_internal((tl_timelog_t*)tl,
                                        (tl_alloc_ctx_t*)&tl->alloc,
                                        out);
}

void tl_snapshot_release(tl_snapshot_t* s) {
    tl_snapshot_release_internal(s);
}

/*===========================================================================
 * Iterator Internal Helpers
 *===========================================================================*/

/**
 * Create and initialize an iterator for the given range.
 *
 * This is the common implementation for all iterator creation functions.
 * It allocates the iterator, builds the query plan, initializes the merge
 * iterator, and sets up the tombstone filter.
 *
 * @param snap         Snapshot to iterate
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY used if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf)
 * @param out          Output iterator pointer
 * @return TL_OK on success, error code on failure
 */
static tl_status_t iter_create_internal(tl_snapshot_t* snap,
                                         tl_ts_t t1, tl_ts_t t2,
                                         bool t2_unbounded,
                                         tl_iter_t** out) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    tl_alloc_ctx_t* alloc = snap->alloc;
    tl_status_t st;

    /* Allocate iterator */
    tl_iter_t* it = TL_NEW(alloc, tl_iter_t);
    if (it == NULL) {
        return TL_ENOMEM;
    }
    memset(it, 0, sizeof(*it));
    it->snapshot = snap;
    it->alloc = alloc;

    /* Build query plan */
    st = tl_plan_build(&it->plan, snap, alloc, t1, t2, t2_unbounded);
    if (st != TL_OK) {
        tl__free(alloc, it);
        return st;
    }

    /* Check if plan is empty (no sources) */
    if (tl_plan_is_empty(&it->plan)) {
        it->done = true;
        it->initialized = true;
        *out = it;
#ifdef TL_DEBUG
        tl_snapshot_iter_created(snap);
#endif
        return TL_OK;
    }

    /* Initialize K-way merge iterator */
    st = tl_kmerge_iter_init(&it->kmerge, &it->plan, alloc);
    if (st != TL_OK) {
        tl_plan_destroy(&it->plan);
        tl__free(alloc, it);
        return st;
    }

    /* Initialize tombstone filter */
    tl_intervals_imm_t tombs = {
        .data = tl_plan_tombstones(&it->plan),
        .len = tl_plan_tomb_count(&it->plan)
    };
    tl_filter_iter_init(&it->filter, &it->kmerge, tombs);

    it->done = tl_filter_iter_done(&it->filter);
    it->initialized = true;

#ifdef TL_DEBUG
    tl_snapshot_iter_created(snap);
#endif

    *out = it;
    return TL_OK;
}

/*===========================================================================
 * Iterator API Implementation (Phase 5)
 *===========================================================================*/

tl_status_t tl_iter_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                          tl_iter_t** out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }
    /* Validate range: t1 must be < t2 for non-empty bounded range */
    if (t1 >= t2) {
        /* Create empty iterator for empty/invalid range */
        tl_iter_t* it = TL_NEW(snap->alloc, tl_iter_t);
        if (it == NULL) {
            return TL_ENOMEM;
        }
        memset(it, 0, sizeof(*it));
        it->snapshot = (tl_snapshot_t*)snap;
        it->alloc = snap->alloc;
        it->done = true;
        it->initialized = true;
#ifdef TL_DEBUG
        tl_snapshot_iter_created((tl_snapshot_t*)snap);
#endif
        *out = it;
        return TL_OK;
    }

    return iter_create_internal((tl_snapshot_t*)snap, t1, t2, false, out);
}

tl_status_t tl_iter_since(const tl_snapshot_t* snap, tl_ts_t t1,
                          tl_iter_t** out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    /* Unbounded query [t1, +inf) */
    return iter_create_internal((tl_snapshot_t*)snap, t1, 0, true, out);
}

tl_status_t tl_iter_until(const tl_snapshot_t* snap, tl_ts_t t2,
                          tl_iter_t** out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    /* [TL_TS_MIN, t2) */
    return iter_create_internal((tl_snapshot_t*)snap, TL_TS_MIN, t2, false, out);
}

tl_status_t tl_iter_equal(const tl_snapshot_t* snap, tl_ts_t ts,
                          tl_iter_t** out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    /* [ts, ts+1) - but guard against overflow */
    if (ts == TL_TS_MAX) {
        /* ts+1 would overflow, use unbounded with post-filter */
        /* For simplicity, create [ts, +inf) and filter will naturally stop */
        return iter_create_internal((tl_snapshot_t*)snap, ts, 0, true, out);
    }

    return iter_create_internal((tl_snapshot_t*)snap, ts, ts + 1, false, out);
}

tl_status_t tl_iter_point(const tl_snapshot_t* snap, tl_ts_t ts,
                          tl_iter_t** out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    *out = NULL;

    tl_alloc_ctx_t* alloc = snap->alloc;

    /* Allocate iterator */
    tl_iter_t* it = TL_NEW(alloc, tl_iter_t);
    if (it == NULL) {
        return TL_ENOMEM;
    }
    memset(it, 0, sizeof(*it));
    it->snapshot = (tl_snapshot_t*)snap;
    it->alloc = alloc;
    it->point_mode = true;
    it->point_idx = 0;

    /* Use dedicated point lookup fast path */
    tl_status_t st = tl_point_lookup(&it->point_result, snap, ts, alloc);
    if (st != TL_OK) {
        tl__free(alloc, it);
        return st;
    }

    it->done = (it->point_result.count == 0);
    it->initialized = true;

#ifdef TL_DEBUG
    tl_snapshot_iter_created((tl_snapshot_t*)snap);
#endif

    *out = it;
    return TL_OK;
}

tl_status_t tl_iter_next(tl_iter_t* it, tl_record_t* out) {
    if (it == NULL || out == NULL) {
        return TL_EINVAL;
    }
    if (!it->initialized) {
        return TL_ESTATE;
    }
    if (it->done) {
        return TL_EOF;
    }

    /* Point mode: iterate over pre-computed results */
    if (it->point_mode) {
        if (it->point_idx >= it->point_result.count) {
            it->done = true;
            return TL_EOF;
        }
        *out = it->point_result.records[it->point_idx];
        it->point_idx++;
        if (it->point_idx >= it->point_result.count) {
            it->done = true;
        }
        return TL_OK;
    }

    /* Range mode: use filter iterator */
    tl_status_t st = tl_filter_iter_next(&it->filter, out);
    if (st == TL_EOF) {
        it->done = true;
    }
    return st;
}

void tl_iter_destroy(tl_iter_t* it) {
    if (it == NULL) {
        return;
    }

#ifdef TL_DEBUG
    if (it->snapshot != NULL) {
        tl_snapshot_iter_destroyed(it->snapshot);
    }
#endif

    /* Point mode: destroy point result */
    if (it->point_mode) {
        tl_point_result_destroy(&it->point_result);
        tl_alloc_ctx_t* alloc = it->alloc;
        tl__free(alloc, it);
        return;
    }

    /* Range mode: destroy in reverse order of creation */
    /* Filter has no destroy - it's just a wrapper */

    if (it->initialized && !tl_plan_is_empty(&it->plan)) {
        tl_kmerge_iter_destroy(&it->kmerge);
    }

    tl_plan_destroy(&it->plan);

    tl_alloc_ctx_t* alloc = it->alloc;
    tl__free(alloc, it);
}

tl_status_t tl_scan_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                          tl_scan_fn fn, void* ctx) {
    if (snap == NULL || fn == NULL) {
        return TL_EINVAL;
    }

    tl_iter_t* it = NULL;
    tl_status_t st = tl_iter_range(snap, t1, t2, &it);
    if (st != TL_OK) {
        return st;
    }

    tl_record_t rec;
    while ((st = tl_iter_next(it, &rec)) == TL_OK) {
        tl_scan_decision_t decision = fn(ctx, &rec);
        if (decision == TL_SCAN_STOP) {
            break;
        }
    }

    tl_iter_destroy(it);

    /* TL_EOF is expected and means successful completion */
    return (st == TL_EOF) ? TL_OK : st;
}

/*===========================================================================
 * Timestamp Navigation (Phase 5)
 *===========================================================================*/

tl_status_t tl_min_ts(const tl_snapshot_t* snap, tl_ts_t* out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    if (!snap->has_data) {
        return TL_EOF;
    }

    /* Use iterator to find first visible (non-deleted) record.
     * This correctly accounts for tombstones. */
    tl_iter_t* it = NULL;
    tl_status_t st = tl_iter_since(snap, TL_TS_MIN, &it);
    if (st != TL_OK) {
        return st;
    }

    tl_record_t rec;
    st = tl_iter_next(it, &rec);
    if (st == TL_OK) {
        *out = rec.ts;
    }

    tl_iter_destroy(it);
    return st;
}

tl_status_t tl_max_ts(const tl_snapshot_t* snap, tl_ts_t* out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    if (!snap->has_data) {
        return TL_EOF;
    }

    /* Use iterator to find last visible (non-deleted) record.
     * This correctly accounts for tombstones.
     * Note: This scans the entire dataset - could be optimized with
     * a reverse iterator or tombstone-aware bounds check. */
    tl_iter_t* it = NULL;
    tl_status_t st = tl_iter_since(snap, TL_TS_MIN, &it);
    if (st != TL_OK) {
        return st;
    }

    tl_record_t rec;
    tl_ts_t last_ts = 0;
    bool found = false;

    while (tl_iter_next(it, &rec) == TL_OK) {
        last_ts = rec.ts;
        found = true;
    }

    tl_iter_destroy(it);

    if (!found) {
        return TL_EOF;  /* All records deleted by tombstones */
    }

    *out = last_ts;
    return TL_OK;
}

tl_status_t tl_next_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    if (!snap->has_data) {
        return TL_EOF;
    }

    /* Guard against overflow */
    if (ts == TL_TS_MAX) {
        return TL_EOF;
    }

    /* Create iterator starting at ts+1 */
    tl_iter_t* it = NULL;
    tl_status_t st = tl_iter_since(snap, ts + 1, &it);
    if (st != TL_OK) {
        return st;
    }

    /* Get first record */
    tl_record_t rec;
    st = tl_iter_next(it, &rec);
    if (st == TL_OK) {
        *out = rec.ts;
    }

    tl_iter_destroy(it);
    return st;
}

tl_status_t tl_prev_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    if (!snap->has_data) {
        return TL_EOF;
    }

    /* Guard against underflow */
    if (ts == TL_TS_MIN) {
        return TL_EOF;
    }

    /* Create iterator for [TL_TS_MIN, ts) and scan to find the last.
     *
     * Note: We use TL_TS_MIN instead of snap->min_ts for defensive safety.
     * If snap->min_ts was incorrectly set (bug elsewhere), this ensures we
     * still search the full valid range. Performance is acceptable since
     * we're doing a full scan anyway to find the last timestamp. */
    tl_iter_t* it = NULL;
    tl_status_t st = tl_iter_range(snap, TL_TS_MIN, ts, &it);
    if (st != TL_OK) {
        return st;
    }

    /* Scan to find the last timestamp */
    tl_record_t rec;
    tl_ts_t last_ts = 0;
    bool found = false;

    while (tl_iter_next(it, &rec) == TL_OK) {
        last_ts = rec.ts;
        found = true;
    }

    tl_iter_destroy(it);

    if (!found) {
        return TL_EOF;
    }

    *out = last_ts;
    return TL_OK;
}

/*===========================================================================
 * Background Maintenance Worker (Phase 7)
 *
 * The worker thread loop follows the Background Maintenance LLD Section 6:
 * 1. Wait for work (flush_pending OR compact_pending) or shutdown
 * 2. Copy and clear flags under maint_mu (atomically, no race)
 * 3. Execute work outside maint_mu (respects lock ordering)
 * 4. Repeat until shutdown
 *
 * Lock acquisition order within loop:
 * - maint_mu: held only during wait and flag copy/clear
 * - flush_mu: held during flush work (via tl__flush_one)
 * - writer_mu: held during publication (via flush_one_memrun)
 *
 * CRITICAL: All pending flags are plain bools protected by maint_mu.
 * No atomics are used. This eliminates the lost-work race.
 *===========================================================================*/

/* Backoff state for ENOMEM retry (prevents CPU spin) */
#define TL_MAINT_BACKOFF_INIT_MS   10
#define TL_MAINT_BACKOFF_MAX_MS    100

static void* tl__maint_worker_entry(void* arg) {
    tl_timelog_t* tl = (tl_timelog_t*)arg;
    uint32_t backoff_ms = TL_MAINT_BACKOFF_INIT_MS;

    for (;;) {
        bool do_flush = false;
        bool do_compact = false;

        /*-------------------------------------------------------------------
         * Phase 1: Wait for work or shutdown (under maint_mu)
         *
         * All state is protected by maint_mu - plain reads, no atomics.
         *-------------------------------------------------------------------*/
        TL_LOCK_MAINT(tl);

        /* Predicate loop handles spurious wakeups AND missed signals.
         *
         * Using timed wait (periodic wake) ensures the worker checks for
         * pressure even if a signal was missed due to race conditions.
         * Default interval: 100ms (from config.maintenance_wakeup_ms).
         *
         * All fields are plain bools, read under maint_mu. */
        while (!tl->maint_shutdown &&
               !tl->flush_pending &&
               !tl->compact_pending) {
            tl_cond_timedwait(&tl->maint_cond, &tl->maint_mu,
                              tl->config.maintenance_wakeup_ms);
        }

        /* Check shutdown first (takes priority) */
        if (tl->maint_shutdown) {
            TL_UNLOCK_MAINT(tl);
            break;  /* Exit loop, thread will terminate */
        }

        /* Copy flags and clear under maint_mu.
         * Since we hold the lock, this is atomic with respect to setters. */
        do_flush = tl->flush_pending;
        do_compact = tl->compact_pending;

        tl->flush_pending = false;
        tl->compact_pending = false;

        TL_UNLOCK_MAINT(tl);

        /*-------------------------------------------------------------------
         * Phase 2a: Read sealed queue length (OOO Scaling Phase 1)
         *
         * Check sealed queue to detect missed signals and enter flush-first
         * mode when watermarks are enabled and pressure is high.
         *-------------------------------------------------------------------*/
        TL_LOCK_MEMTABLE(tl);
        size_t sealed_len = tl_memtable_sealed_len(&tl->memtable);
        TL_UNLOCK_MEMTABLE(tl);

        /* Override missed signals: if work exists, do it */
        if (sealed_len > 0) {
            do_flush = true;
        }

        /* Check compaction heuristic only if there's pending flush work.
         *
         * Rationale: tl__compaction_needed() acquires writer_mu and may compute
         * delete-debt (expensive segment scan). On idle periodic wakes with no
         * pending work, this is wasted effort. We only check heuristics when:
         * - do_compact is not already set (explicit request already handled)
         * - do_flush is true (flush will create new L0 segments)
         *
         * CORRECTNESS: This gating is safe because compaction triggers (L0 count
         * and delete-debt) can only change when new segments are created via flush.
         * Tombstones from tl_delete_range() go into the memtable and don't affect
         * segment-level delete-debt until flushed. Therefore, if there's no flush
         * work pending, compaction triggers haven't changed since the last check.
         *
         * BEHAVIOR CHANGE: This means delete-debt compaction won't be checked on
         * pure idle periodic wakes (no sealed runs). Users who require prompt
         * delete-debt cleanup should ensure write activity continues or use
         * tl_compact() for explicit compaction requests. */
        if (!do_compact && do_flush) {
            if (tl__compaction_needed(tl)) {
                do_compact = true;
            }
        }

        /*-------------------------------------------------------------------
         * Phase 2b: Execute flush work (outside maint_mu)
         *
         * When watermarks are enabled and sealed_len >= hi_wm, enter
         * flush-first mode: drain aggressively until <= lo_wm before
         * allowing compaction. This breaks the "sealed-queue → writer stall"
         * feedback loop under OOO workloads.
         *
         * Legacy behavior (watermarks disabled): flush one, check compaction.
         *-------------------------------------------------------------------*/
        if (do_flush) {
            bool flush_first_mode = false;

            /* Watermark check: if >= hi_wm, enter flush-first mode */
            if (tl->watermarks_enabled && sealed_len >= tl->effective_sealed_hi_wm) {
                flush_first_mode = true;
                tl_atomic_inc_u64(&tl->flush_first_cycles);
            }

            tl_status_t st;
            while ((st = tl__flush_one(tl)) == TL_OK) {
                /* Re-read sealed_len after each flush */
                TL_LOCK_MEMTABLE(tl);
                sealed_len = tl_memtable_sealed_len(&tl->memtable);
                TL_UNLOCK_MEMTABLE(tl);

                if (flush_first_mode) {
                    /* Flush-first: drain until <= lo_wm */
                    if (sealed_len <= tl->effective_sealed_lo_wm) {
                        /* Pressure relieved, allow compaction */
                        if (tl__compaction_needed(tl)) {
                            do_compact = true;
                        }
                        break;
                    }
                    /* Continue flushing (no fairness check in flush-first mode) */
                } else {
                    /* Legacy fairness: flush one, check compaction */
                    if (tl__compaction_needed(tl)) {
                        do_compact = true;
                        break;
                    }
                }
            }

            /* Handle transient errors: backoff sleep to prevent CPU spin.
             * Both ENOMEM (memory pressure) and EINTERNAL (publication failure)
             * may be transient and benefit from backoff before retry. */
            if (st == TL_ENOMEM || st == TL_EINTERNAL) {
                tl_sleep_ms(backoff_ms);
                backoff_ms = (backoff_ms * 2 > TL_MAINT_BACKOFF_MAX_MS)
                           ? TL_MAINT_BACKOFF_MAX_MS : backoff_ms * 2;

                /* Log transient error (once per backoff cycle = natural throttling).
                 * Per Background Maintenance LLD Section 12. */
                {
                    tl_log_ctx_t* log = &tl->log;
                    TL_LOG_WARN("Flush failed (%s), retrying after %u ms backoff",
                                tl_strerror(st), backoff_ms);
                    (void)log;  /* Silence unused warning if logging disabled */
                }
            } else {
                backoff_ms = TL_MAINT_BACKOFF_INIT_MS;  /* Reset on success */
            }

            /* Re-signal if more work remains.
             * This handles:
             * - ENOMEM: retry after backoff (memory may free up)
             * - EINTERNAL: retry after backoff (transient issue may resolve)
             * - TL_OK: broke for compaction fairness, more memruns may exist
             *
             * TL_EOF means no more sealed memruns - no re-signal needed.
             *
             * CRITICAL: Without this, TL_EINTERNAL would silently drop work.
             * The memrun stays in the queue but flush_pending wouldn't be set,
             * leaving the worker sleeping forever. */
            if (st != TL_EOF) {
                TL_LOCK_MEMTABLE(tl);
                bool more_work = tl_memtable_has_sealed(&tl->memtable);
                TL_UNLOCK_MEMTABLE(tl);
                if (more_work) {
                    /* Re-set flag under maint_mu (atomically with potential signal) */
                    TL_LOCK_MAINT(tl);
                    tl->flush_pending = true;
                    TL_UNLOCK_MAINT(tl);
                }
            }
        }

        /*-------------------------------------------------------------------
         * Phase 3: Execute compaction work (outside maint_mu)
         *
         * Compaction is triggered by:
         * - Explicit request (compact_pending was set)
         * - Automatic heuristic (tl__compaction_needed returned true during flush)
         *
         * OOO Scaling Phase 1: Watermark-based deferral with safety valve.
         * - Defer compaction if sealed > lo_wm (flush pressure high)
         * - UNLESS L0 >= max_delta_segments (safety valve: force compaction)
         *
         * Error handling mirrors flush: backoff on transient errors,
         * re-set compact_pending to ensure retry.
         *-------------------------------------------------------------------*/
        if (do_compact) {
            tl_status_t st;

            /* Re-read sealed_len for watermark check */
            TL_LOCK_MEMTABLE(tl);
            sealed_len = tl_memtable_sealed_len(&tl->memtable);
            TL_UNLOCK_MEMTABLE(tl);

            /* Get L0 count for safety valve.
             *
             * CRITICAL: Must use pin/read/release pattern to prevent UAF.
             * Per tl_compact_needed() documentation: "reading manifest without
             * writer_mu risks UAF since manifest is a plain pointer that can
             * be freed after swap." The seqlock protects readers DURING a swap,
             * but the manifest pointer itself can become dangling afterward. */
            TL_LOCK_WRITER(tl);
            tl_manifest_t* m_pinned = tl_manifest_acquire(tl->manifest);
            TL_UNLOCK_WRITER(tl);

            uint32_t l0_count = tl_manifest_l0_count(m_pinned);
            tl_manifest_release(m_pinned);

            /* Watermark check with HARD SAFETY VALVE:
             * - Defer compaction if sealed > lo_wm (soft rule)
             * - UNLESS L0 debt >= max_delta_segments (hard rule - MUST compact)
             *
             * SEMANTIC NOTE (delete-debt deferral):
             * When watermark pressure is high (sealed > lo_wm) but L0 is below
             * the safety cap, ALL compaction is deferred - including delete-debt
             * triggered compaction. This means tombstones may remain in segments
             * longer than delete_debt_threshold would normally allow.
             *
             * This is an intentional trade-off: we prioritize reducing writer
             * stalls (via aggressive flush) over prompt tombstone cleanup. The
             * safety valve ensures compaction eventually runs when L0 debt
             * becomes critical. For workloads where delete-debt cleanup is
             * time-sensitive, consider increasing max_delta_segments to trigger
             * the safety valve earlier, or reducing watermark pressure by
             * increasing sealed_max_runs. */
            bool pressure_high = tl->watermarks_enabled &&
                                 sealed_len > tl->effective_sealed_lo_wm;
            bool l0_debt_critical = (l0_count >= tl->config.max_delta_segments);

            if (pressure_high && !l0_debt_critical) {
                /* Defer compaction: flush pressure too high, L0 debt acceptable */
                tl_atomic_inc_u64(&tl->compaction_deferred);

                /* Prevent busy-spin: set flush_pending if work exists,
                 * remember to compact later via compact_pending */
                TL_LOCK_MAINT(tl);
                if (sealed_len > 0) {
                    tl->flush_pending = true;  /* Try flushing instead */
                }
                tl->compact_pending = true;    /* Remember to compact later */
                TL_UNLOCK_MAINT(tl);

                /* Reset backoff since deferral is expected behavior, not an error.
                 * Without this, a previous transient error's backoff would persist. */
                backoff_ms = TL_MAINT_BACKOFF_INIT_MS;

                /* Skip compaction this cycle - continue to next iteration */
                continue;
            }

            /* Compact: either pressure is low OR L0 debt is critical */
            if (l0_debt_critical && pressure_high) {
                tl_atomic_inc_u64(&tl->compaction_forced);
            }

            st = tl__compact_one_step(tl);

            /* Handle transient errors with backoff */
            if (st == TL_ENOMEM || st == TL_EBUSY || st == TL_EINTERNAL) {
                tl_sleep_ms(backoff_ms);
                backoff_ms = (backoff_ms * 2 > TL_MAINT_BACKOFF_MAX_MS)
                           ? TL_MAINT_BACKOFF_MAX_MS : backoff_ms * 2;

                /* Log transient error (once per backoff cycle = natural throttling).
                 * Per Background Maintenance LLD Section 12: "Any fatal error should
                 * be surfaced... and logged in background mode." Transient errors
                 * also benefit from logging for diagnostics. */
                {
                    tl_log_ctx_t* log = &tl->log;
                    TL_LOG_WARN("Compaction failed (%s), retrying after %u ms backoff",
                                tl_strerror(st), backoff_ms);
                    (void)log;  /* Silence unused warning if logging disabled */
                }

                /* Re-set compact_pending for retry.
                 * EBUSY = manifest changed during publish (will retry).
                 * ENOMEM/EINTERNAL = transient, worth retrying after backoff. */
                TL_LOCK_MAINT(tl);
                tl->compact_pending = true;
                TL_UNLOCK_MAINT(tl);
            } else if (st == TL_EOVERFLOW) {
                /* Non-retryable: window span too large for this dataset.
                 * Log and continue - don't set compact_pending (no point retrying).
                 * Reset backoff since this isn't a transient failure. */
                tl_log_ctx_t* log = &tl->log;
                TL_LOG_ERROR("Compaction failed: window span overflow (TL_EOVERFLOW)");
                (void)log;  /* Silence unused warning if logging disabled */
                backoff_ms = TL_MAINT_BACKOFF_INIT_MS;
            } else if (st == TL_OK) {
                /* Success - reset backoff */
                backoff_ms = TL_MAINT_BACKOFF_INIT_MS;
            }
            /* TL_EOF = no work needed, no action required */
        }
    }

    return NULL;
}

/*===========================================================================
 * tl_maint_start - Start Background Worker
 *
 * State machine transitions: STOPPED -> RUNNING
 *
 * Algorithm:
 * 1. Validate inputs and mode
 * 2. Check state machine (STOPPED required)
 * 3. Reset shutdown flag
 * 4. Create worker thread
 * 5. Transition to RUNNING state
 * 6. Signal worker if pending work already exists
 *
 * Idempotency: If state is RUNNING, returns TL_OK without action.
 *
 * Returns:
 * - TL_OK       Worker started (or already running)
 * - TL_EINVAL   tl is NULL
 * - TL_ESTATE   Not open or not in BACKGROUND mode
 * - TL_EBUSY    Stop in progress (state is STOPPING) - retry later
 * - TL_EINTERNAL Thread creation failed
 *
 * All state access is under maint_mu - no atomics needed.
 *===========================================================================*/

tl_status_t tl_maint_start(tl_timelog_t* tl) {
    if (tl == NULL) {
        return TL_EINVAL;
    }

    /* Lifecycle validation */
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    /* Mode validation */
    if (tl->config.maintenance_mode != TL_MAINT_BACKGROUND) {
        return TL_ESTATE;
    }

    TL_LOCK_MAINT(tl);

    /* State machine check */
    switch (tl->maint_state) {
        case TL_WORKER_RUNNING:
            /* Idempotency: already running */
            TL_UNLOCK_MAINT(tl);
            return TL_OK;

        case TL_WORKER_STOPPING:
            /* Another thread is stopping - cannot start until stop completes.
             * Return TL_EBUSY so caller knows to retry later. */
            TL_UNLOCK_MAINT(tl);
            return TL_EBUSY;

        case TL_WORKER_STOPPED:
            /* Valid state for start - continue */
            break;
    }

    /* Reset shutdown flag (may be set from previous stop) */
    tl->maint_shutdown = false;

    /* Create worker thread */
    tl_status_t st = tl_thread_create(&tl->maint_thread,
                                       tl__maint_worker_entry,
                                       tl);
    if (st != TL_OK) {
        TL_UNLOCK_MAINT(tl);
        return TL_EINTERNAL;
    }

    /* Transition to RUNNING state */
    tl->maint_state = TL_WORKER_RUNNING;

    /* If pending work already exists (writes happened before start),
     * signal the worker so it doesn't sleep forever waiting. */
    if (tl->flush_pending || tl->compact_pending) {
        tl_cond_signal(&tl->maint_cond);
    }

    TL_UNLOCK_MAINT(tl);
    return TL_OK;
}

/*===========================================================================
 * tl_maint_stop - Stop Background Worker
 *
 * State machine transitions: RUNNING -> STOPPING -> STOPPED
 *
 * Algorithm:
 * 1. Validate inputs (not mode - allows cleanup flexibility)
 * 2. Check state machine (RUNNING required for action)
 * 3. Transition to STOPPING state
 * 4. Set shutdown flag + signal worker
 * 5. Join thread (blocking, OUTSIDE maint_mu)
 * 6. Transition to STOPPED state (only on successful join)
 *
 * CRITICAL: Thread join must happen on the original struct member, NOT a copy.
 * tl_thread_join() may modify the tl_thread_t struct (e.g., to mark as joined).
 * Joining a copy is undefined behavior on some platforms.
 *
 * The join is performed OUTSIDE maint_mu to prevent deadlock:
 * - Worker may be inside flush work holding lower-priority locks
 * - We must not block while holding maint_mu
 *
 * We do NOT check mode here. This allows tl_close() to call stop
 * unconditionally without checking mode.
 *===========================================================================*/

tl_status_t tl_maint_stop(tl_timelog_t* tl) {
    if (tl == NULL) {
        return TL_EINVAL;
    }

    TL_LOCK_MAINT(tl);

    /* State machine check */
    switch (tl->maint_state) {
        case TL_WORKER_STOPPED:
            /* Idempotency: already stopped - fall through */
        case TL_WORKER_STOPPING:
            /* Another thread is stopping - let it complete.
             * Both cases are safe: return OK without action.
             * This prevents double-join (undefined behavior). */
            TL_UNLOCK_MAINT(tl);
            return TL_OK;

        case TL_WORKER_RUNNING:
            /* Valid state for stop - continue */
            break;
    }

    /* Transition to STOPPING state.
     * This prevents concurrent stop calls from attempting double-join. */
    tl->maint_state = TL_WORKER_STOPPING;

    /* Signal shutdown to worker */
    tl->maint_shutdown = true;

    /* Wake worker from cond_wait */
    tl_cond_signal(&tl->maint_cond);

    TL_UNLOCK_MAINT(tl);

    /* Join thread OUTSIDE maint_mu (may block while worker finishes).
     * CRITICAL: Join on the original struct member, NOT a copy.
     * tl_thread_join() may modify the struct. */
    tl_status_t st = tl_thread_join(&tl->maint_thread, NULL);

    /* Final state transition */
    TL_LOCK_MAINT(tl);
    if (st == TL_OK) {
        /* Successful join: transition to STOPPED, reset flags */
        tl->maint_state = TL_WORKER_STOPPED;
        tl->maint_shutdown = false;
    } else {
        /* Join failed: stay in STOPPING state.
         * This is a severe error - system may be inconsistent.
         * DO NOT clear shutdown - thread may still be running. */
        /* maint_state remains STOPPING - caller must handle */
    }
    TL_UNLOCK_MAINT(tl);

    return (st == TL_OK) ? TL_OK : TL_EINTERNAL;
}

/*===========================================================================
 * tl_maint_step - Manual Mode One Unit of Work
 *
 * Priority (from Background Maintenance LLD Section 5):
 * 1. Flush one sealed memrun (bounds memory)
 * 2. Compact one step if needed (bounds read amplification)
 *
 * This function is synchronous - it performs work and returns.
 *
 * Compaction is triggered by EITHER:
 * - Automatic heuristic (L0 count, delete debt)
 * - Explicit request via tl_compact() (sets compact_pending flag)
 *===========================================================================*/

tl_status_t tl_maint_step(tl_timelog_t* tl) {
    if (tl == NULL) {
        return TL_EINVAL;
    }

    /* Lifecycle validation */
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    /* Mode validation */
    if (tl->config.maintenance_mode != TL_MAINT_DISABLED) {
        return TL_ESTATE;
    }

    /* Priority 1: Flush */
    TL_LOCK_MEMTABLE(tl);
    bool has_sealed = tl_memtable_has_sealed(&tl->memtable);
    TL_UNLOCK_MEMTABLE(tl);

    if (has_sealed) {
        tl_status_t st = tl__flush_one(tl);
        if (st == TL_OK || st == TL_ENOMEM) {
            return st;  /* Work done (or failed with recoverable error) */
        }
        /* TL_EOF from flush_one means queue was empty (race), fall through */
    }

    /* Priority 2: Compaction - triggered by heuristic OR explicit request */
    bool was_explicit = false;

    TL_LOCK_MAINT(tl);
    if (tl->compact_pending) {
        was_explicit = true;
        /* DON'T clear yet - only clear on success to match background behavior */
    }
    TL_UNLOCK_MAINT(tl);

    /* Also check automatic heuristic (L0 count, delete debt) */
    bool do_compact = was_explicit || tl__compaction_needed(tl);

    if (do_compact) {
        tl_status_t st = tl__compact_one_step(tl);

        /* Clear compact_pending on success, no-work, or fatal errors.
         * Transient errors (ENOMEM, EBUSY, EINTERNAL) preserve the request.
         * EOVERFLOW is fatal (non-retryable) - clear to prevent infinite loop. */
        if (was_explicit && (st == TL_OK || st == TL_EOF || st == TL_EOVERFLOW)) {
            TL_LOCK_MAINT(tl);
            tl->compact_pending = false;
            TL_UNLOCK_MAINT(tl);
        }

        /* Log fatal errors in manual mode for diagnostics.
         * Transient errors are caller's responsibility to handle/log. */
        if (st == TL_EOVERFLOW) {
            tl_log_ctx_t* log = &tl->log;
            TL_LOG_ERROR("Compaction failed: window span overflow (TL_EOVERFLOW)");
            (void)log;
        }

        return st;
    }

    return TL_EOF;  /* No work to do */
}

/*===========================================================================
 * Statistics and Diagnostics
 *
 * tl_stats(): Gather aggregate statistics from a snapshot.
 * Statistics reflect RAW data in the snapshot (before tombstone filtering).
 *
 * tl_validate() (debug only): Orchestrator that calls module validators.
 * Returns TL_OK in release builds (no validation).
 *
 * Reference: Phase 6 Plan, Software Design Spec Section 5
 *===========================================================================*/

tl_status_t tl_stats(const tl_snapshot_t* snap, tl_stats_t* out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    /* Zero-initialize output */
    memset(out, 0, sizeof(*out));

    /*
     * Get snapshot components.
     * Use accessor functions for encapsulation.
     */
    const tl_manifest_t* manifest = tl_snapshot_manifest(snap);
    const tl_memview_t* memview = tl_snapshot_memview(snap);

    /*
     * Count L0 segments.
     * Use accessor function for manifest.
     */
    out->segments_l0 = tl_manifest_l0_count(manifest);

    /*
     * Count L1 segments.
     */
    out->segments_l1 = tl_manifest_l1_count(manifest);

    /*
     * Count total pages and records from manifest.
     * Iterate through all segments in both layers.
     */
    uint64_t total_pages = 0;
    uint64_t total_records = 0;

    /* L0 segments */
    for (uint32_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);
        total_pages += seg->page_count;
        total_records += seg->record_count;
    }

    /* L1 segments */
    for (uint32_t i = 0; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);
        total_pages += seg->page_count;
        total_records += seg->record_count;
    }

    out->pages_total = total_pages;

    /*
     * records_estimate includes both storage and memview records.
     * This is RAW data before tombstone filtering.
     */
    total_records += tl_memview_run_len(memview);
    total_records += tl_memview_ooo_len(memview);

    /* Add records from sealed memruns */
    for (size_t i = 0; i < tl_memview_sealed_len(memview); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(memview, i);
        total_records += tl_memrun_run_len(mr);
        total_records += tl_memrun_ooo_len(mr);
    }

    out->records_estimate = total_records;

    /*
     * Bounds: Use snapshot's precomputed bounds.
     *
     * These are RAW bounds (include tombstoned records).
     * For VISIBLE bounds, callers should use tl_min_ts/tl_max_ts
     * with iteration to find actual visible min/max.
     */
    if (tl_snapshot_has_data(snap)) {
        out->min_ts = tl_snapshot_min_ts(snap);
        out->max_ts = tl_snapshot_max_ts(snap);
    } else {
        /* No data: use sentinel bounds per public API contract */
        out->min_ts = TL_TS_MAX;
        out->max_ts = TL_TS_MIN;
    }

    /*
     * Tombstone count: TOTAL tombstone intervals (NOT deduplicated).
     *
     * Sum tombstones from all sources:
     * - Active memview tombstones
     * - Sealed memrun tombstones
     * - L0 segment tombstones (L1 never has tombstones)
     */
    uint64_t tombstone_count = 0;

    /* Memview active tombstones */
    tombstone_count += tl_memview_tomb_len(memview);

    /* Sealed memrun tombstones */
    for (size_t i = 0; i < tl_memview_sealed_len(memview); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(memview, i);
        tl_intervals_imm_t mr_tombs = tl_memrun_tombs_imm(mr);
        tombstone_count += mr_tombs.len;
    }

    /* L0 segment tombstones */
    for (uint32_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);
        if (tl_segment_has_tombstones(seg)) {
            tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
            tombstone_count += seg_tombs.len;
        }
    }

    out->tombstone_count = tombstone_count;

    /*
     * Memtable metrics: snapshot-time values from memview.
     *
     * These reflect the state at snapshot acquisition time:
     * - active_records: records in active run buffer (not yet sealed)
     * - ooo_records: records in OOO buffer (out-of-order inserts)
     * - sealed_runs: memruns queued for flush
     */
    out->memtable_active_records = (uint64_t)tl_memview_run_len(memview);
    out->memtable_ooo_records = (uint64_t)tl_memview_ooo_len(memview);
    out->memtable_sealed_runs = (uint64_t)tl_memview_sealed_len(memview);

    /*
     * Operational counters (cumulative since open).
     * Read from parent timelog instance with relaxed ordering.
     * These are monotonically increasing counters.
     */
    tl_timelog_t* tl = (tl_timelog_t*)snap->parent;  /* Cast for lock macros */
    if (tl != NULL) {
        out->seals_total = tl_atomic_load_relaxed_u64(&tl->seals_total);
        out->ooo_budget_hits = tl_atomic_load_relaxed_u64(&tl->ooo_budget_hits);
        out->backpressure_waits = tl_atomic_load_relaxed_u64(&tl->backpressure_waits);
        out->flushes_total = tl_atomic_load_relaxed_u64(&tl->flushes_total);
        out->compactions_total = tl_atomic_load_relaxed_u64(&tl->compactions_total);

        /* OOO Scaling metrics (Phase 1) */
        out->flush_first_cycles = tl_atomic_load_relaxed_u64(&tl->flush_first_cycles);
        out->compaction_deferred_cycles = tl_atomic_load_relaxed_u64(&tl->compaction_deferred);
        out->compaction_forced_cycles = tl_atomic_load_relaxed_u64(&tl->compaction_forced);

        /* OOO Scaling metrics (Phase 2) */
        out->reshape_compactions_total = tl_atomic_load_relaxed_u64(&tl->reshape_compactions_total);
        out->rebase_publish_success = tl_atomic_load_relaxed_u64(&tl->rebase_publish_success);
        out->rebase_publish_fallback = tl_atomic_load_relaxed_u64(&tl->rebase_publish_fallback);
        out->window_bound_exceeded = tl_atomic_load_relaxed_u64(&tl->window_bound_exceeded);
        out->rebase_l1_conflict = tl_atomic_load_relaxed_u64(&tl->rebase_l1_conflict);

        /*
         * Adaptive segmentation metrics (V-Next).
         * Read under maint_mu for safe access to adaptive state.
         *
         * These are only populated when adaptive is enabled.
         * When disabled (target_records == 0), values remain zero
         * from the memset at the start.
         */
        if (tl->config.adaptive.target_records > 0) {
            TL_LOCK_MAINT(tl);
            out->adaptive_window = tl->effective_window_size;
            out->adaptive_ewma_density = tl->adaptive.ewma_density;
            out->adaptive_flush_count = tl->adaptive.flush_count;
            out->adaptive_failures = tl->adaptive.consecutive_failures;
            TL_UNLOCK_MAINT(tl);
        }
    }

    return TL_OK;
}

tl_status_t tl_validate(const tl_snapshot_t* snap) {
    /* NULL check always applies (programmer error) */
    if (snap == NULL) {
        return TL_EINVAL;
    }

#ifndef TL_DEBUG
    /*
     * In release builds, validation is a no-op.
     * This allows callers to unconditionally call tl_validate()
     * without performance impact in production.
     */
    (void)snap;
    return TL_OK;
#else
    /*
     * Debug builds: Full validation via orchestrator pattern.
     *
     * The orchestrator calls module validators in bottom-up order:
     * 1. Manifest validator (calls segment validator on each segment)
     * 2. Memview validator
     *
     * Each module validator calls its sub-component validators.
     * This avoids code duplication and ensures consistent checks.
     */
    const tl_manifest_t* manifest = tl_snapshot_manifest(snap);
    const tl_memview_t* memview = tl_snapshot_memview(snap);

    /*
     * Step 1: Validate manifest.
     *
     * tl_manifest_validate() internally:
     * - Validates L0 segments (each via tl_segment_validate)
     * - Validates L1 segments (each via tl_segment_validate)
     * - Checks L1 sorting and non-overlapping windows
     * - Checks unbounded window guard
     * - Validates cached bounds
     *
     * tl_segment_validate() internally:
     * - Validates page catalog (each page via tl_page_validate)
     * - Validates tombstones via tl_intervals_arr_validate
     * - Checks level-specific invariants (L0/L1 rules)
     * - Validates bounds coverage
     */
    if (!tl_manifest_validate(manifest)) {
        return TL_EINTERNAL;
    }

    /*
     * Step 2: Validate memview.
     *
     * tl_memview_validate() checks:
     * - active_run sorted
     * - active_ooo sorted
     * - active_tombs valid via tl_intervals_arr_validate
     * - sealed memrun pointers non-NULL
     * - has_data consistency
     */
    if (!tl_memview_validate(memview)) {
        return TL_EINTERNAL;
    }

    /*
     * Step 3: Validate snapshot-level invariants.
     *
     * These are consistency checks across the snapshot components.
     */

    /* If snapshot has_data, bounds must be valid (min <= max) */
    if (snap->has_data) {
        if (snap->min_ts > snap->max_ts) {
            return TL_EINTERNAL;
        }
    }

    return TL_OK;
#endif /* TL_DEBUG */
}

/*===========================================================================
 * Publication Protocol Helpers (Phase 1)
 *
 * These functions implement the atomic publication pattern used by both
 * flush and compaction. The actual publish work is done between
 * tl__publish_begin() and tl__publish_end().
 *
 * From timelog_v1_c_software_design_spec.md Section 4.3:
 *
 * 1. Lock writer_mu
 * 2. view_seq++ (odd = publish in progress)
 * 3. Swap manifest pointer + update state
 * 4. view_seq++ (even = publish complete)
 * 5. Unlock writer_mu
 *===========================================================================*/

/**
 * Begin publication phase.
 * Acquires writer_mu and increments seqlock to odd.
 *
 * @param tl Timelog instance
 */
void tl__publish_begin(tl_timelog_t* tl) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(tl->is_open);

    TL_LOCK_WRITER(tl);
    tl_seqlock_write_begin(&tl->view_seq);

    /* Now seq is odd - no snapshot can proceed */
}

/**
 * End publication phase.
 * Increments seqlock to even and releases writer_mu.
 *
 * @param tl Timelog instance
 */
void tl__publish_end(tl_timelog_t* tl) {
    TL_ASSERT(tl != NULL);

    tl_seqlock_write_end(&tl->view_seq);
    TL_UNLOCK_WRITER(tl);

    /* Now seq is even - snapshots can proceed */
}
