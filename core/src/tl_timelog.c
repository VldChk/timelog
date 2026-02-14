#include "timelog/timelog.h"
#include "internal/tl_defs.h"
#include "internal/tl_alloc.h"
#include "internal/tl_log.h"
#include "internal/tl_sync.h"
#include "internal/tl_seqlock.h"
#include "internal/tl_search.h"
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
#include "query/tl_segment_range.h"
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

    /* Maintenance timing: 0 means use default (100ms) in normalize */
    cfg->maintenance_wakeup_ms = 0;

    /* Compaction */
    cfg->max_delta_segments     = TL_DEFAULT_MAX_DELTA_SEGMENTS;
    cfg->window_size            = 0; /* Will use default based on time_unit */
    cfg->window_origin          = 0;
    cfg->delete_debt_threshold  = 0.0; /* Disabled */
    cfg->compaction_target_bytes = 0;  /* Unlimited */
    cfg->max_compaction_inputs   = 0;  /* Unlimited */
    cfg->max_compaction_windows  = 0;  /* 0 = unlimited (greedy selection) */

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

    /* Log level must be valid (TL_LOG_NONE = -1 is special "disable" value).
     * TL_LOG_ERROR = 0 to TL_LOG_TRACE = 4 are valid levels. */
    if (cfg->log_level != TL_LOG_NONE &&
        ((int)cfg->log_level < (int)TL_LOG_ERROR ||
         (int)cfg->log_level > (int)TL_LOG_TRACE)) {
        return TL_EINVAL;
    }

    /* Validate adaptive segmentation config.
     * tl_adaptive_config_validate() returns TL_OK if disabled (target_records == 0).
     * Otherwise, it validates min/max guardrails, alpha, and other parameters. */
    tl_status_t adapt_st = tl_adaptive_config_validate(&cfg->adaptive);
    if (adapt_st != TL_OK) {
        return adapt_st;
    }

    /* Validate allocator: if custom allocator is provided, realloc_fn is required.
     *
     * Rationale: Many internal structures (heap, recvec, intervals) use realloc
     * for growth. If realloc_fn is NULL, tl__realloc() returns NULL which causes
     * TL_ENOMEM errors - misleading since it's a configuration error, not OOM.
     *
     * We detect "custom allocator" by checking if malloc_fn is non-NULL.
     * If malloc_fn is provided without realloc_fn, reject early with clear error. */
    if (cfg->allocator.malloc_fn != NULL && cfg->allocator.realloc_fn == NULL) {
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
     * Step 3: Maintenance timing
     * ======================================================================= */
    if (cfg->maintenance_wakeup_ms == 0) {
        cfg->maintenance_wakeup_ms = TL_DEFAULT_MAINTENANCE_WAKEUP_MS;
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

    s = tl_cond_init(&tl->memtable_cond);
    if (s != TL_OK) {
        tl_mutex_destroy(&tl->memtable_mu);
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
    tl_cond_destroy(&tl->memtable_cond);
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
    tl->op_seq = 0;

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
    tl_atomic_init_u64(&tl->compaction_retries, 0);
    tl_atomic_init_u64(&tl->compaction_publish_ebusy, 0);
    tl_atomic_init_u64(&tl->compaction_select_calls, 0);
    tl_atomic_init_u64(&tl->compaction_select_l0_inputs, 0);
    tl_atomic_init_u64(&tl->compaction_select_l1_inputs, 0);
    tl_atomic_init_u64(&tl->compaction_select_no_work, 0);

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

    /* C-10: Initialize window grid freeze flag.
     * Check if manifest already has L1 segments (future-proofing for persistence).
     * If L1 exists, freeze the grid to prevent window size changes.
     * Single-threaded context - no lock needed. */
    tl->window_grid_frozen = (tl_manifest_l1_count(tl->manifest) > 0);

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
     * doesn't check is_open (allowing cleanup flexibility).
     *
     * CRITICAL: If join fails (TL_EINTERNAL), worker thread may still be
     * running. Proceeding to destroy locks would cause memory corruption.
     * Fail-fast is the safest option. */
    tl_status_t stop_st = tl_maint_stop(tl);
    if (stop_st == TL_EINTERNAL) {
        TL_LOG_ERROR("tl_close: worker join failed, aborting to prevent corruption");
        abort();  /* Worker thread may still be running; must not proceed */
    }

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

    /* Release manifest (Phase 5)
     *
     * NOTE (H-05): on_drop_handle is NOT invoked for remaining records.
     * The callback fires only during compaction for tombstone-deleted records.
     * Caller retains ownership of all handles not explicitly deleted by tombstones.
     * See tl_on_drop_fn documentation in timelog.h for full contract. */
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

static void tl__emit_drop_callbacks(tl_timelog_t* tl,
                                    tl_record_t* dropped,
                                    size_t dropped_len) {
    if (dropped_len > 0 && tl->config.on_drop_handle != NULL) {
        for (size_t i = 0; i < dropped_len; i++) {
            tl->config.on_drop_handle(tl->config.on_drop_ctx,
                                      dropped[i].ts,
                                      dropped[i].handle);
        }
    }
    if (dropped != NULL) {
        tl__free(&tl->alloc, dropped);
    }
}

static tl_status_t tl__next_op_seq(tl_timelog_t* tl, tl_seq_t* out) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(out != NULL);
    if (tl->op_seq == UINT64_MAX) {
        return TL_EOVERFLOW;
    }
    tl->op_seq++;
    *out = tl->op_seq;
    return TL_OK;
}

static bool tl__inc_ts_safe(tl_ts_t ts, tl_ts_t* next) {
    TL_ASSERT(next != NULL);
    if (ts == TL_TS_MAX) {
        return false;
    }
    *next = ts + 1;
    return true;
}

static void tl__range_end_from_inclusive_max(tl_ts_t max_inclusive,
                                              tl_ts_t* t2,
                                              bool* t2_unbounded) {
    TL_ASSERT(t2 != NULL);
    TL_ASSERT(t2_unbounded != NULL);
    *t2_unbounded = !tl__inc_ts_safe(max_inclusive, t2);
    if (*t2_unbounded) {
        *t2 = 0;
    }
}

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
 *         TL_EBUSY if backpressure occurred (write succeeded, do not retry)
 */
static tl_status_t handle_seal_with_backpressure(tl_timelog_t* tl,
                                                  bool* need_signal,
                                                  tl_record_t** out_dropped,
                                                  size_t* out_dropped_len) {
    *need_signal = false;
    if (out_dropped != NULL && out_dropped_len != NULL) {
        *out_dropped = NULL;
        *out_dropped_len = 0;
    }

    /* Check if seal is needed */
    if (!tl_memtable_should_seal(&tl->memtable)) {
        return TL_OK;
    }

    /* Track if OOO budget triggered the seal (for instrumentation).
     * Increment counter immediately since the budget WAS exceeded,
     * regardless of whether the seal ultimately succeeds or times out. */
    if (tl_memtable_ooo_budget_exceeded(&tl->memtable)) {
        tl_atomic_inc_u64(&tl->ooo_budget_hits);
    }

    /* Try to seal (no signal: seal GROWS queue, not frees space) */
    tl_record_t* dropped = NULL;
    size_t dropped_len = 0;
    tl_status_t seal_st = tl_memtable_seal_ex(&tl->memtable,
                                               &tl->memtable_mu,
                                               NULL,
                                               tl->op_seq,
                                               &dropped,
                                               &dropped_len);
    if (seal_st == TL_OK) {
        /* Seal succeeded - signal needed (deferred until after unlock) */
        tl_atomic_inc_u64(&tl->seals_total);
        *need_signal = true;
        if (out_dropped != NULL && out_dropped_len != NULL) {
            *out_dropped = dropped;
            *out_dropped_len = dropped_len;
        } else if (dropped != NULL) {
            tl__free(&tl->alloc, dropped);
        }
        return TL_OK;
    }

    if (dropped != NULL) {
        tl__free(&tl->alloc, dropped);
    }

    if (seal_st != TL_EBUSY) {
        /* Seal failed with error other than queue-full (e.g., TL_ENOMEM).
         * Write already succeeded (this function is called post-insert),
         * so return TL_EBUSY to prevent caller from retrying (duplicates).
         * Waiting for queue space won't help - this isn't a capacity issue. */
        return TL_EBUSY;
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
                                                   &tl->memtable_cond,
                                                   tl->config.sealed_wait_ms);
    TL_UNLOCK_MEMTABLE(tl);

    /* Re-acquire writer lock */
    TL_LOCK_WRITER(tl);

    if (!have_space) {
        /* Timeout waiting for space. Write succeeded, but backpressure exceeded.
         * Return TL_EBUSY to signal caller (consistent with manual mode).
         * Caller should NOT retry - record is already in memtable. */
        return TL_EBUSY;
    }

    /* Retry seal now that we have space (no signal: seal GROWS queue) */
    dropped = NULL;
    dropped_len = 0;
    seal_st = tl_memtable_seal_ex(&tl->memtable,
                                   &tl->memtable_mu,
                                   NULL,
                                   tl->op_seq,
                                   &dropped,
                                   &dropped_len);
    if (seal_st == TL_OK) {
        /* Seal succeeded - signal needed (deferred until after unlock) */
        tl_atomic_inc_u64(&tl->seals_total);
        *need_signal = true;
        if (out_dropped != NULL && out_dropped_len != NULL) {
            *out_dropped = dropped;
            *out_dropped_len = dropped_len;
        } else if (dropped != NULL) {
            tl__free(&tl->alloc, dropped);
        }
        return TL_OK;
    }

    if (dropped != NULL) {
        tl__free(&tl->alloc, dropped);
    }

    /* Seal failed after write succeeded. Return TL_EBUSY to signal backpressure.
     * We don't propagate TL_ENOMEM because:
     * 1. The write DID succeed (record is in memtable)
     * 2. Returning ENOMEM might cause caller to retry, creating duplicates
     * 3. Seal failure is just a form of backpressure - maintenance will handle it */
    return TL_EBUSY;
}

/*
 * API Guard Pattern:
 * All public write/query APIs that require an open timelog validate:
 *   - tl != NULL     -> TL_EINVAL
 *   - tl->is_open    -> TL_ESTATE
 * This pattern is intentionally kept explicit (not factored into a helper)
 * for debuggability and clarity. See Section 8.2 of internal_review_task_list.md.
 */
tl_status_t tl_append(tl_timelog_t* tl, tl_ts_t ts, tl_handle_t handle) {
    if (tl == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    bool need_signal = false;
    tl_record_t* dropped = NULL;
    size_t dropped_len = 0;

    /* Acquire writer lock */
    TL_LOCK_WRITER(tl);

    /* Insert into memtable */
    tl_seq_t seq = 0;
    tl_status_t seq_st = tl__next_op_seq(tl, &seq);
    if (seq_st != TL_OK) {
        TL_UNLOCK_WRITER(tl);
        return seq_st;
    }
    tl_status_t insert_st = tl_memtable_insert(&tl->memtable, ts, handle, seq);
    if (insert_st != TL_OK && insert_st != TL_EBUSY) {
        TL_UNLOCK_WRITER(tl);
        return insert_st;
    }

    /* Handle seal with backpressure (deferred signaling) */
    tl_status_t seal_st = handle_seal_with_backpressure(tl, &need_signal,
                                                        &dropped, &dropped_len);

    TL_UNLOCK_WRITER(tl);

    /* Deferred signal AFTER releasing writer_mu (respects lock ordering) */
    if (need_signal) {
        tl__maint_request_flush(tl);
    }
    tl__emit_drop_callbacks(tl, dropped, dropped_len);

    if (insert_st == TL_EBUSY || seal_st == TL_EBUSY) {
        return TL_EBUSY;
    }

    return seal_st;
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

    bool need_signal = false;
    tl_record_t* dropped = NULL;
    size_t dropped_len = 0;

    /* Acquire writer lock */
    TL_LOCK_WRITER(tl);

    /* Insert batch into memtable */
    tl_seq_t seq = 0;
    tl_status_t seq_st = tl__next_op_seq(tl, &seq);
    if (seq_st != TL_OK) {
        TL_UNLOCK_WRITER(tl);
        return seq_st;
    }
    tl_status_t insert_st = tl_memtable_insert_batch(&tl->memtable, records, n,
                                                      flags, seq);
    if (insert_st != TL_OK && insert_st != TL_EBUSY) {
        TL_UNLOCK_WRITER(tl);
        /* C-08 fix: With all-or-nothing semantics (pre-reserve in slow path),
         * failure means NO records were inserted. Return the actual error code
         * so callers can distinguish true failures from backpressure.
         *
         * TL_ENOMEM/TL_EOVERFLOW = true failure, caller can rollback all INCREFs
         * TL_EBUSY is returned only when writes succeeded but backpressure
         * occurred (seal queue full or OOO head flush failure). */
        return insert_st;
    }

    /* Handle seal with backpressure (deferred signaling) */
    tl_status_t seal_st = handle_seal_with_backpressure(tl, &need_signal,
                                                        &dropped, &dropped_len);

    TL_UNLOCK_WRITER(tl);

    /* Deferred signal AFTER releasing writer_mu (respects lock ordering) */
    if (need_signal) {
        tl__maint_request_flush(tl);
    }
    tl__emit_drop_callbacks(tl, dropped, dropped_len);

    if (insert_st == TL_EBUSY || seal_st == TL_EBUSY) {
        return TL_EBUSY;
    }

    return seal_st;
}

tl_status_t tl_delete_range(tl_timelog_t* tl, tl_ts_t t1, tl_ts_t t2) {
    if (tl == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    /* Validate range: half-open interval [t1, t2) must not be negative.
     * - t1 == t2: Empty range, early return as no-op (no work, avoids lock)
     * - t1 > t2:  Invalid negative range, rejected as TL_EINVAL */
    if (t1 == t2) {
        return TL_OK;  /* Empty range is no-op */
    }
    if (t1 > t2) {
        return TL_EINVAL;
    }

    tl_status_t st;
    bool need_signal = false;
    tl_record_t* dropped = NULL;
    size_t dropped_len = 0;

    /* Acquire writer lock */
    TL_LOCK_WRITER(tl);

    /* Insert tombstone into memtable */
    tl_seq_t seq = 0;
    tl_status_t seq_st = tl__next_op_seq(tl, &seq);
    if (seq_st != TL_OK) {
        TL_UNLOCK_WRITER(tl);
        return seq_st;
    }
    st = tl_memtable_insert_tombstone(&tl->memtable, t1, t2, seq);
    if (st != TL_OK) {
        TL_UNLOCK_WRITER(tl);
        return st;
    }

    /* Handle seal with backpressure (deferred signaling) */
    st = handle_seal_with_backpressure(tl, &need_signal, &dropped, &dropped_len);

    TL_UNLOCK_WRITER(tl);

    /* Deferred signal AFTER releasing writer_mu (respects lock ordering) */
    if (need_signal) {
        tl__maint_request_flush(tl);
    }
    tl__emit_drop_callbacks(tl, dropped, dropped_len);

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
    tl_record_t* dropped = NULL;
    size_t dropped_len = 0;

    if (cutoff == TL_TS_MIN) {
        return TL_OK;
    }

    /* Acquire writer lock */
    TL_LOCK_WRITER(tl);

    /* Insert tombstone [TL_TS_MIN, cutoff) */
    tl_seq_t seq = 0;
    tl_status_t seq_st = tl__next_op_seq(tl, &seq);
    if (seq_st != TL_OK) {
        TL_UNLOCK_WRITER(tl);
        return seq_st;
    }
    st = tl_memtable_insert_tombstone(&tl->memtable, TL_TS_MIN, cutoff, seq);
    if (st != TL_OK) {
        TL_UNLOCK_WRITER(tl);
        return st;
    }

    /* Handle seal with backpressure (deferred signaling) */
    st = handle_seal_with_backpressure(tl, &need_signal, &dropped, &dropped_len);

    TL_UNLOCK_WRITER(tl);

    /* Deferred signal AFTER releasing writer_mu (respects lock ordering) */
    if (need_signal) {
        tl__maint_request_flush(tl);
    }
    tl__emit_drop_callbacks(tl, dropped, dropped_len);

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
static bool tl__compaction_needed(const tl_timelog_t* tl) {
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
 *
 * Uses "rebase publish" pattern (same as compaction) to minimize writer_mu
 * critical section. All allocations happen OFF-LOCK; under lock we only do
 * pointer comparison and swap.
 *===========================================================================*/

/**
 * Attempt to publish a pre-built L0 segment to manifest.
 *
 * Uses "rebase publish" pattern from compaction (tl_compaction.c:1206-1277):
 * 1. Capture base manifest (brief writer_mu lock to acquire ref)
 * 2. Build new manifest OFF-LOCK (all allocations here)
 * 3. Validate and swap under writer_mu (NO ALLOCATION)
 *
 * @param tl   Timelog instance
 * @param mr   Pinned memrun (caller holds reference)
 * @param seg  Pre-built L0 segment (caller holds reference)
 * @return TL_OK     Success, seg ref released (manifest owns it), mr released
 *         TL_EBUSY  Manifest changed (concurrent compaction), retry needed
 *                   seg NOT released (caller retries or releases)
 *                   mr NOT released (caller handles)
 *         Other     Error, seg released here, mr NOT released
 */
static tl_status_t flush_publish(tl_timelog_t* tl, tl_memrun_t* mr, tl_segment_t* seg) {
    tl_status_t st;

    /* Step 1: Capture base manifest (brief lock, acquire ref).
     * Per Codex review: must pin under writer_mu to prevent ABA/UAF. */
    TL_LOCK_WRITER(tl);
    tl_manifest_t* base = tl->manifest;
    tl_manifest_acquire(base);
    TL_UNLOCK_WRITER(tl);

    /* Step 2: Build new manifest OFF-LOCK (all allocations here).
     * Per engineering rule: "keep writer_mu short; never do expensive work." */
    tl_manifest_builder_t builder;
    tl_manifest_builder_init(&builder, &tl->alloc, base);
    st = tl_manifest_builder_add_l0(&builder, seg);
    if (st != TL_OK) {
        tl_manifest_builder_destroy(&builder);
        tl_manifest_release(base);
        tl_segment_release(seg);
        return st;
    }

    tl_manifest_t* new_manifest = NULL;
    st = tl_manifest_builder_build(&builder, &new_manifest);
    tl_manifest_builder_destroy(&builder);
    if (st != TL_OK) {
        tl_manifest_release(base);
        tl_segment_release(seg);
        return st;
    }

    /* Step 3: Validate and swap under lock (NO ALLOCATION beyond this point). */
    TL_LOCK_WRITER(tl);

    if (tl->manifest != base) {
        /* Concurrent compaction changed manifest - retry needed.
         * This is rare but possible when compaction publishes between
         * our base capture (step 1) and this validation. */
        TL_UNLOCK_WRITER(tl);
        tl_manifest_release(new_manifest);
        tl_manifest_release(base);
        /* NOTE: seg NOT released - caller will retry with it */
        return TL_EBUSY;
    }

    /* Swap manifest under seqlock */
    tl_seqlock_write_begin(&tl->view_seq);
    tl_manifest_t* old = tl->manifest;
    tl->manifest = new_manifest;

    /* Remove memrun from sealed queue INSIDE seqlock critical section.
     * This ensures atomicity: no snapshot sees BOTH segment AND memrun.
     * Lock ordering (writer_mu -> memtable_mu) is respected per hierarchy. */
    TL_LOCK_MEMTABLE(tl);
    tl_memtable_pop_oldest(&tl->memtable, &tl->memtable_cond);
    TL_UNLOCK_MEMTABLE(tl);

    tl_seqlock_write_end(&tl->view_seq);
    TL_UNLOCK_WRITER(tl);

    /* Release old references (safe after unlock).
     * Note: old == base at this point (we verified tl->manifest == base above). */
    tl_manifest_release(base);  /* Our captured reference */
    tl_manifest_release(old);   /* The swapped-out manifest */
    tl_memrun_release(mr);      /* Caller's pin - successful publish consumes it */

    /* Release caller's segment ref. The manifest builder acquired its own ref
     * when we called tl_manifest_builder_add_l0(), so the segment is now owned
     * by the new manifest. Without this release, each flush leaks one segment. */
    tl_segment_release(seg);

    tl_atomic_inc_u64(&tl->flushes_total);
    return TL_OK;
}

static void flush_discard_memrun(tl_timelog_t* tl, tl_memrun_t* mr) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(mr != NULL);

    TL_LOCK_WRITER(tl);
    tl_seqlock_write_begin(&tl->view_seq);
    TL_LOCK_MEMTABLE(tl);
    tl_memtable_pop_oldest(&tl->memtable, &tl->memtable_cond);
    TL_UNLOCK_MEMTABLE(tl);
    tl_seqlock_write_end(&tl->view_seq);
    TL_UNLOCK_WRITER(tl);

    tl_memrun_release(mr);
    tl_atomic_inc_u64(&tl->flushes_total);
}

/**
 * Flush a single memrun to L0 segment and publish to manifest.
 *
 * Algorithm (revised for "rebase publish" pattern):
 * 1. Acquire generation under writer_mu (brief)
 * 2. Build L0 segment OFF-LOCK (expensive, only once)
 * 3. Publish with retry loop (manifest may become stale)
 *
 * Retry rationale: Concurrent compaction can change manifest between our
 * base capture and publish. We use same retry limit (3) as compaction.
 *
 * @param tl  Timelog instance
 * @param mr  Pinned memrun (caller holds reference)
 * @return TL_OK     Success (mr released)
 *         TL_EBUSY  Retries exhausted (mr NOT released - caller handles)
 *         TL_ENOMEM Build failed (mr NOT released)
 */
static tl_status_t flush_one_memrun(tl_timelog_t* tl, tl_memrun_t* mr) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(mr != NULL);

    tl_status_t st;

    /* Step 1: Acquire generation under writer_mu to prevent races.
     * We only need the lock briefly to get a unique generation.
     * Note: flush_mu is held by caller, serializing generation assignment
     * per Codex review (prevents generation ordering issues on retry). */
    TL_LOCK_WRITER(tl);
    uint32_t gen = tl->next_gen++;
    TL_UNLOCK_WRITER(tl);

    /* Step 2: Capture tombstone snapshot for filtering and watermark */
    tl_snapshot_t* snap = NULL;
    st = tl_snapshot_acquire_internal(tl, &tl->alloc, &snap);
    if (st != TL_OK) {
        return st;
    }

    tl_intervals_t tombs;
    tl_intervals_init(&tombs, &tl->alloc);

    tl_ts_t min_ts = tl_memrun_min_ts(mr);
    tl_ts_t max_ts = tl_memrun_max_ts(mr);
    tl_ts_t t2 = 0;
    bool t2_unbounded = false;
    tl__range_end_from_inclusive_max(max_ts, &t2, &t2_unbounded);

    st = tl_snapshot_collect_tombstones(snap, &tombs,
                                        min_ts, t2, t2_unbounded);
    if (st != TL_OK) {
        tl_intervals_destroy(&tombs);
        tl_snapshot_release_internal(snap);
        return st;
    }

    if (!tl_intervals_is_empty(&tombs)) {
        if (t2_unbounded) {
            tl_intervals_clip_lower(&tombs, min_ts);
        } else {
            tl_intervals_clip(&tombs, min_ts, t2);
        }
    }

    /* Step 3: Build L0 segment OFF-LOCK (expensive, only once) */
    tl_flush_ctx_t ctx = {
        .alloc = &tl->alloc,
        .target_page_bytes = tl->config.target_page_bytes,
        .generation = gen,
        .applied_seq = tl_snapshot_seq(snap),
        .tombs = tl_intervals_as_imm(&tombs),
        .collect_drops = (tl->config.on_drop_handle != NULL)
    };

    tl_segment_t* seg = NULL;
    tl_record_t* dropped = NULL;
    size_t dropped_len = 0;
    st = tl_flush_build(&ctx, mr, &seg, &dropped, &dropped_len);
    tl_intervals_destroy(&tombs);
    tl_snapshot_release_internal(snap);
    if (st != TL_OK) {
        return st;  /* mr NOT released - caller handles */
    }

    if (seg == NULL) {
        flush_discard_memrun(tl, mr);
        if (dropped_len > 0 && tl->config.on_drop_handle != NULL) {
            for (size_t i = 0; i < dropped_len; i++) {
                tl->config.on_drop_handle(tl->config.on_drop_ctx,
                                          dropped[i].ts,
                                          dropped[i].handle);
            }
        }
        if (dropped != NULL) {
            tl__free(&tl->alloc, dropped);
        }
        return TL_OK;
    }

    /* Step 4: Publish with retry (manifest may become stale during build).
     * Use same retry limit (3) as compaction for consistency.
     * flush_mu is held by caller, serializing this entire operation. */
    for (int attempt = 0; attempt < 3; attempt++) {
        st = flush_publish(tl, mr, seg);
        if (st != TL_EBUSY) {
            /* Success or hard error - either way, we're done.
             * On success: flush_publish released mr and transferred seg.
             * On error: flush_publish released seg, we return error. */
            if (st == TL_OK) {
                if (dropped_len > 0 && tl->config.on_drop_handle != NULL) {
                    for (size_t i = 0; i < dropped_len; i++) {
                        tl->config.on_drop_handle(tl->config.on_drop_ctx,
                                                  dropped[i].ts,
                                                  dropped[i].handle);
                    }
                }
            }
            if (dropped != NULL) {
                tl__free(&tl->alloc, dropped);
            }
            return st;
        }
        /* TL_EBUSY: manifest changed by concurrent compaction.
         * seg is still valid (not released on EBUSY) - retry with it. */
    }

    /* Exhausted retries (rare: concurrent compaction storm).
     * Release segment, but NOT mr - caller must release it. */
    tl_segment_release(seg);
    if (dropped != NULL) {
        tl__free(&tl->alloc, dropped);
    }
    return TL_EBUSY;
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
 *         TL_EBUSY  - Publish retries exhausted (rare: concurrent compaction
 *                     storm; memrun preserved for retry on next cycle)
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
            tl_ts_t ooo_min = mr->ooo_min_ts;
            tl_ts_t ooo_max = mr->ooo_max_ts;

            /* Compute record-only min/max.
             * run is sorted; OOO runs expose precomputed min/max. */
            if (run_len > 0 && ooo_len > 0) {
                metrics.min_ts = TL_MIN(run[0].ts, ooo_min);
                metrics.max_ts = TL_MAX(run[run_len - 1].ts, ooo_max);
            } else if (run_len > 0) {
                metrics.min_ts = run[0].ts;
                metrics.max_ts = run[run_len - 1].ts;
            } else {  /* ooo_len > 0 */
                metrics.min_ts = ooo_min;
                metrics.max_ts = ooo_max;
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
            /* No signal: seal GROWS queue, manual mode has no backpressure waiters */
            st = tl_memtable_seal(&tl->memtable,
                                   &tl->memtable_mu,
                                   NULL,
                                   tl->op_seq);
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

    tl_ts_t t2 = 0;
    bool t2_unbounded = false;
    tl__range_end_from_inclusive_max(ts, &t2, &t2_unbounded);
    return iter_create_internal((tl_snapshot_t*)snap, ts, t2, t2_unbounded, out);
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

    tl_ts_t next = 0;
    if (!tl__inc_ts_safe(ts, &next)) {
        return TL_EOF;
    }

    /* Create iterator starting at ts+1 */
    tl_iter_t* it = NULL;
    tl_status_t st = tl_iter_since(snap, next, &it);
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

typedef enum tl_work_t {
    TL_WORK_NONE               = 0,
    TL_WORK_FLUSH              = 1u << 0,
    TL_WORK_COMPACT_EXPLICIT   = 1u << 1,
    TL_WORK_COMPACT_HEURISTIC  = 1u << 2,
    TL_WORK_RESHAPE_L0         = 1u << 3  /* Reserved for future use */
} tl_work_t;

static void* tl__maint_worker_entry(void* arg) {
    tl_timelog_t* tl = (tl_timelog_t*)arg;
    uint32_t backoff_ms = TL_MAINT_BACKOFF_INIT_MS;

    for (;;) {
        tl_work_t work = TL_WORK_NONE;

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
        if (tl->flush_pending) {
            work |= TL_WORK_FLUSH;
        }
        if (tl->compact_pending) {
            work |= TL_WORK_COMPACT_EXPLICIT;
        }

        tl->flush_pending = false;
        tl->compact_pending = false;

        TL_UNLOCK_MAINT(tl);

        /*-------------------------------------------------------------------
         * Phase 2a: Read sealed queue length
         *
         * Check sealed queue to detect missed signals.
         *-------------------------------------------------------------------*/
        TL_LOCK_MEMTABLE(tl);
        size_t sealed_len = tl_memtable_sealed_len(&tl->memtable);
        TL_UNLOCK_MEMTABLE(tl);

        /* Override missed signals: if work exists, do it */
        if (sealed_len > 0) {
            work |= TL_WORK_FLUSH;
        }

        /* Check compaction heuristic only if there's pending flush work.
         *
         * Rationale: tl__compaction_needed() acquires writer_mu and may compute
         * delete-debt (expensive segment scan). On idle periodic wakes with no
         * pending work, this is wasted effort. We only check heuristics when:
         * - explicit compaction not already requested
         * - flush work is pending (flush will create new L0 segments)
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
        if (!(work & TL_WORK_COMPACT_EXPLICIT) && (work & TL_WORK_FLUSH)) {
            if (tl__compaction_needed(tl)) {
                work |= TL_WORK_COMPACT_HEURISTIC;
            }
        }

        /*-------------------------------------------------------------------
         * Phase 2b: Execute flush work (outside maint_mu)
         *
         * Simple fairness policy: flush one, then check compaction.
         *-------------------------------------------------------------------*/
        if (work & TL_WORK_FLUSH) {
            tl_status_t st;
            while ((st = tl__flush_one(tl)) == TL_OK) {
                /* Fairness: flush one, check compaction */
                if (tl__compaction_needed(tl)) {
                    work |= TL_WORK_COMPACT_HEURISTIC;
                    break;
                }
            }

            /* Handle transient errors: backoff sleep to prevent CPU spin.
             * ENOMEM (memory pressure), EBUSY (publish retries exhausted due to
             * concurrent compaction storm), and EINTERNAL (publication failure)
             * may all be transient and benefit from backoff before retry. */
            if (st == TL_ENOMEM || st == TL_EBUSY || st == TL_EINTERNAL) {
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
             * - EBUSY: retry after backoff (compaction storm may subside)
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
         * Error handling mirrors flush: backoff on transient errors,
         * re-set compact_pending to ensure retry.
         *-------------------------------------------------------------------*/
        if (work & (TL_WORK_COMPACT_EXPLICIT | TL_WORK_COMPACT_HEURISTIC)) {
            tl_status_t st = tl__compact_one_step(tl);

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

static bool tl__range_overlap_half_open(tl_ts_t a1,
                                     tl_ts_t a2,
                                     bool a2_unbounded,
                                     tl_ts_t b1,
                                     tl_ts_t b2,
                                     bool b2_unbounded,
                                     tl_ts_t* out_lo,
                                     tl_ts_t* out_hi,
                                     bool* out_hi_unbounded) {
    tl_ts_t lo = (a1 > b1) ? a1 : b1;

    bool hi_unbounded = a2_unbounded && b2_unbounded;
    tl_ts_t hi = 0;
    if (!hi_unbounded) {
        hi = a2_unbounded ? b2 : (b2_unbounded ? a2 : TL_MIN(a2, b2));
        if (lo >= hi) {
            return false;
        }
    }

    if (out_lo != NULL) *out_lo = lo;
    if (out_hi != NULL) *out_hi = hi;
    if (out_hi_unbounded != NULL) *out_hi_unbounded = hi_unbounded;
    return true;
}

static uint64_t tl__count_records_sorted_range(const tl_record_t* data,
                                               size_t len,
                                               tl_ts_t t1,
                                               tl_ts_t t2,
                                               bool t2_unbounded) {
    if (data == NULL || len == 0) {
        return 0;
    }

    size_t lo = tl_record_lower_bound(data, len, t1);
    size_t hi = t2_unbounded ? len : tl_record_lower_bound(data, len, t2);
    if (hi <= lo) {
        return 0;
    }
    return (uint64_t)(hi - lo);
}

static uint64_t tl__count_records_in_memrun_range(const tl_memrun_t* mr,
                                                  tl_ts_t t1,
                                                  tl_ts_t t2,
                                                  bool t2_unbounded) {
    uint64_t total = 0;
    total += tl__count_records_sorted_range(tl_memrun_run_data(mr),
                                            tl_memrun_run_len(mr),
                                            t1, t2, t2_unbounded);

    size_t run_count = tl_memrun_ooo_run_count(mr);
    for (size_t i = 0; i < run_count; i++) {
        const tl_ooorun_t* run = tl_memrun_ooo_run_at(mr, i);
        total += tl__count_records_sorted_range(tl_ooorun_records(run),
                                                tl_ooorun_len(run),
                                                t1, t2, t2_unbounded);
    }

    return total;
}

static bool tl__memrun_record_bounds(const tl_memrun_t* mr,
                                     tl_ts_t* out_min,
                                     tl_ts_t* out_max) {
    bool has = false;
    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;

    if (tl_memrun_run_len(mr) > 0) {
        const tl_record_t* run = tl_memrun_run_data(mr);
        min_ts = TL_MIN(min_ts, run[0].ts);
        max_ts = TL_MAX(max_ts, run[tl_memrun_run_len(mr) - 1].ts);
        has = true;
    }

    for (size_t i = 0; i < tl_memrun_ooo_run_count(mr); i++) {
        const tl_ooorun_t* run = tl_memrun_ooo_run_at(mr, i);
        if (tl_ooorun_len(run) == 0) {
            continue;
        }
        min_ts = TL_MIN(min_ts, tl_ooorun_min_ts(run));
        max_ts = TL_MAX(max_ts, tl_ooorun_max_ts(run));
        has = true;
    }

    if (!has) {
        return false;
    }

    *out_min = min_ts;
    *out_max = max_ts;
    return true;
}

static uint64_t tl__visible_records_in_segment(const tl_segment_t* seg,
                                               const tl_interval_t* tombs,
                                               size_t tomb_count) {
    if (!tl_segment_has_records(seg)) {
        return 0;
    }

    tl_ts_t src_start = tl_segment_record_min_ts(seg);
    tl_ts_t src_end = tl_segment_record_max_ts(seg);
    bool src_end_unbounded = (src_end == TL_TS_MAX);
    tl_ts_t src_end_exclusive = src_end_unbounded ? 0 : (src_end + 1);

    uint64_t gross = src_end_unbounded
        ? tl_count_records_in_segment_since(seg, src_start)
        : tl_count_records_in_segment_range(seg, src_start, src_end_exclusive);

    tl_seq_t watermark = tl_segment_applied_seq(seg);
    for (size_t i = 0; i < tomb_count; i++) {
        const tl_interval_t* f = &tombs[i];
        if (f->max_seq <= watermark) {
            continue;
        }

        tl_ts_t ov_lo = 0, ov_hi = 0;
        bool ov_hi_unbounded = false;
        if (!tl__range_overlap_half_open(src_start, src_end_exclusive, src_end_unbounded,
                                         f->start, f->end, f->end_unbounded,
                                         &ov_lo, &ov_hi, &ov_hi_unbounded)) {
            continue;
        }

        uint64_t dec = ov_hi_unbounded
            ? tl_count_records_in_segment_since(seg, ov_lo)
            : tl_count_records_in_segment_range(seg, ov_lo, ov_hi);
        TL_ASSERT(dec <= gross);
        gross = (dec <= gross) ? (gross - dec) : 0;
    }

    return gross;
}

static uint64_t tl__visible_records_in_memrun(const tl_memrun_t* mr,
                                              const tl_interval_t* tombs,
                                              size_t tomb_count) {
    tl_ts_t src_min = 0, src_max = 0;
    if (!tl__memrun_record_bounds(mr, &src_min, &src_max)) {
        return 0;
    }

    bool src_end_unbounded = (src_max == TL_TS_MAX);
    tl_ts_t src_end_exclusive = src_end_unbounded ? 0 : (src_max + 1);

    uint64_t gross = tl__count_records_in_memrun_range(mr,
                                                        src_min,
                                                        src_end_exclusive,
                                                        src_end_unbounded);

    tl_seq_t watermark = tl_memrun_applied_seq(mr);
    for (size_t i = 0; i < tomb_count; i++) {
        const tl_interval_t* f = &tombs[i];
        if (f->max_seq <= watermark) {
            continue;
        }

        tl_ts_t ov_lo = 0, ov_hi = 0;
        bool ov_hi_unbounded = false;
        if (!tl__range_overlap_half_open(src_min, src_end_exclusive, src_end_unbounded,
                                         f->start, f->end, f->end_unbounded,
                                         &ov_lo, &ov_hi, &ov_hi_unbounded)) {
            continue;
        }

        uint64_t dec = tl__count_records_in_memrun_range(mr,
                                                         ov_lo,
                                                         ov_hi,
                                                         ov_hi_unbounded);
        TL_ASSERT(dec <= gross);
        gross = (dec <= gross) ? (gross - dec) : 0;
    }

    return gross;
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
     * Count total pages and records from immutable sources.
     * For records_estimate, use watermark-aware subtraction over immutable
     * sources (segments + sealed memruns) without row scans.
     */
    uint64_t total_pages = 0;
    uint64_t immutable_visible_records = 0;

    tl_intervals_t skyline;
    tl_intervals_init(&skyline, snap->alloc);
    tl_status_t skyline_st = tl_snapshot_collect_tombstones(snap,
                                                            &skyline,
                                                            TL_TS_MIN,
                                                            0,
                                                            true);
    if (skyline_st != TL_OK) {
        tl_intervals_destroy(&skyline);
        return skyline_st;
    }

    tl_intervals_imm_t skyline_imm = tl_intervals_as_imm(&skyline);
    const tl_interval_t* skyline_data = skyline_imm.data;
    size_t skyline_len = skyline_imm.len;

    /* L0 segments */
    for (uint32_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);
        total_pages += seg->page_count;
        immutable_visible_records += tl__visible_records_in_segment(seg,
                                                                    skyline_data,
                                                                    skyline_len);
    }

    /* L1 segments */
    for (uint32_t i = 0; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);
        total_pages += seg->page_count;
        immutable_visible_records += tl__visible_records_in_segment(seg,
                                                                    skyline_data,
                                                                    skyline_len);
    }

    out->pages_total = total_pages;

    uint64_t total_records = immutable_visible_records;

    /* Mutable memview remains approximate by contract. */
    total_records += tl_memview_run_len(memview);
    total_records += tl_memview_ooo_total_len(memview);

    /* Sealed memruns use watermark-aware immutable counting. */
    for (size_t i = 0; i < tl_memview_sealed_len(memview); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(memview, i);
        total_records += tl__visible_records_in_memrun(mr,
                                                        skyline_data,
                                                        skyline_len);
    }

    out->records_estimate = total_records;
    tl_intervals_destroy(&skyline);

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
    out->memtable_ooo_records = (uint64_t)tl_memview_ooo_total_len(memview);
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
        out->compaction_retries = tl_atomic_load_relaxed_u64(&tl->compaction_retries);
        out->compaction_publish_ebusy = tl_atomic_load_relaxed_u64(&tl->compaction_publish_ebusy);
        out->compaction_select_calls = tl_atomic_load_relaxed_u64(&tl->compaction_select_calls);
        out->compaction_select_l0_inputs = tl_atomic_load_relaxed_u64(&tl->compaction_select_l0_inputs);
        out->compaction_select_l1_inputs = tl_atomic_load_relaxed_u64(&tl->compaction_select_l1_inputs);
        out->compaction_select_no_work = tl_atomic_load_relaxed_u64(&tl->compaction_select_no_work);

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
     * - active_ooo_head sorted (ts, handle)
     * - active_ooo_runs valid and gen-ordered
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
 * Publication Protocol Note
 *
 * Both flush and compaction publish paths use direct seqlock calls rather
 * than combined helpers. This is intentional because validation must occur
 * BETWEEN acquiring writer_mu and entering the seqlock critical section:
 *
 *   TL_LOCK_WRITER(tl);
 *   if (manifest changed) { UNLOCK + return TL_EBUSY; }  // Validation here!
 *   tl_seqlock_write_begin(&tl->view_seq);
 *   ... swap manifest ...
 *   tl_seqlock_write_end(&tl->view_seq);
 *   TL_UNLOCK_WRITER(tl);
 *
 * A combined tl__publish_begin() that does LOCK+seqlock_begin atomically
 * cannot accommodate this validation step. See Section 8.6 of review notes.
 *===========================================================================*/
