#include "timelog/timelog.h"
#include "internal/tl_defs.h"
#include "internal/tl_alloc.h"
#include "internal/tl_log.h"
#include "internal/tl_sync.h"
#include "internal/tl_seqlock.h"
#include "internal/tl_locks.h"

#include <string.h>

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

    /* Compaction */
    cfg->max_delta_segments     = TL_DEFAULT_MAX_DELTA_SEGMENTS;
    cfg->window_size            = 0; /* Will use default based on time_unit */
    cfg->window_origin          = 0;
    cfg->delete_debt_threshold  = 0.0; /* Disabled */
    cfg->compaction_target_bytes = 0;  /* Unlimited */
    cfg->max_compaction_inputs   = 0;  /* Unlimited */
    cfg->max_compaction_windows  = 0;  /* Unlimited */

    /* Maintenance */
    cfg->maintenance_mode = TL_MAINT_DISABLED;

    /* Allocator: NULL means use libc defaults */
    cfg->allocator.ctx        = NULL;
    cfg->allocator.malloc_fn  = NULL;
    cfg->allocator.calloc_fn  = NULL;
    cfg->allocator.realloc_fn = NULL;
    cfg->allocator.free_fn    = NULL;

    /* Logging: NULL means disabled */
    cfg->log_fn  = NULL;
    cfg->log_ctx = NULL;

    /* Drop callback: NULL means disabled */
    cfg->on_drop_handle = NULL;
    cfg->on_drop_ctx    = NULL;

    return TL_OK;
}

/*===========================================================================
 * Internal Instance State
 *===========================================================================*/

/**
 * Core timelog instance structure.
 *
 * Design notes:
 * - Cache-aligned to prevent false sharing in concurrent access
 * - Frequently accessed fields grouped together
 * - Immutable config stored inline (no indirection)
 */
struct tl_timelog {
    /*-----------------------------------------------------------------------
     * Configuration (immutable after init)
     *-----------------------------------------------------------------------*/
    tl_config_t     config;

    /* Computed/normalized config values */
    tl_ts_t         effective_window_size;
    size_t          effective_ooo_budget;

    /*-----------------------------------------------------------------------
     * Subsystem Contexts
     *-----------------------------------------------------------------------*/
    tl_alloc_ctx_t  alloc;
    tl_log_ctx_t    log;

    /*-----------------------------------------------------------------------
     * Synchronization (Phase 1)
     *
     * Lock ordering: maint_mu -> flush_mu -> writer_mu -> memtable_mu
     *-----------------------------------------------------------------------*/

    /* Writer mutex: serializes manifest publication and snapshot capture.
     * Held briefly during the publish phase of flush/compaction. */
    tl_mutex_t      writer_mu;

    /* Flush mutex: serializes flush build + publish (single flusher). */
    tl_mutex_t      flush_mu;

    /* Maintenance mutex: protects maint state flags and thread lifecycle. */
    tl_mutex_t      maint_mu;
    tl_cond_t       maint_cond;

    /* Memtable mutex: protects sealed memrun queue. */
    tl_mutex_t      memtable_mu;

    /* Seqlock for snapshot consistency. Even = idle, odd = publish in progress. */
    tl_seqlock_t    view_seq;

    /*-----------------------------------------------------------------------
     * State Flags
     *
     * IMPORTANT: All flags accessed by multiple threads must be atomic.
     * - maint_started: read in tl__request_flush/compact without lock
     * - maint_shutdown: read by worker, set by close
     * - flush_pending/compact_pending: set by writers, read by maintenance
     *
     * is_open is only modified at open/close boundaries when no other
     * threads should be accessing the instance.
     *-----------------------------------------------------------------------*/
    bool            is_open;
    tl_atomic_u32   maint_started;        /* Worker thread running (0=no, 1=yes) */
    tl_atomic_u32   maint_shutdown;       /* Signal worker to exit (0=running, 1=shutdown) */
    tl_atomic_u32   flush_pending;        /* Work available for flush (0=no, 1=yes) */
    tl_atomic_u32   compact_pending;      /* Work available for compaction (0=no, 1=yes) */

    /*-----------------------------------------------------------------------
     * Maintenance Thread (Phase 7)
     *-----------------------------------------------------------------------*/
    tl_thread_t     maint_thread;

    /*-----------------------------------------------------------------------
     * Future: Storage, Delta subsystems
     *-----------------------------------------------------------------------*/

    /* Manifest pointer (Phase 3) - atomic for lock-free reads */
    /* tl_atomic_ptr  manifest; */

    /* Memtable (Phase 4) */
    /* tl_memtable_t* memtable; */
};

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
    tl__log_init(&tl->log, cfg->log_fn, cfg->log_ctx);

    /* Normalize configuration values */
    normalize_config(tl);

    /* Initialize synchronization primitives (Phase 1) */
    status = init_locks(tl);
    if (status != TL_OK) {
        tl__alloc_destroy(&tl->alloc);
        temp_alloc.alloc.free_fn(temp_alloc.alloc.ctx, tl);
        return status;
    }

    /* Initialize state flags */
    tl->is_open = true;
    tl_atomic_init_u32(&tl->maint_started, 0);
    tl_atomic_init_u32(&tl->maint_shutdown, 0);
    tl_atomic_init_u32(&tl->flush_pending, 0);
    tl_atomic_init_u32(&tl->compact_pending, 0);

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

    /* Mark as closed first (prevents further operations) */
    tl->is_open = false;

    /* Stop maintenance thread if running (Phase 7) */
    if (tl_atomic_load_acquire_u32(&tl->maint_started)) {
        TL_LOCK_MAINT(tl);
        tl_atomic_store_release_u32(&tl->maint_shutdown, 1);
        tl_cond_signal(&tl->maint_cond);
        TL_UNLOCK_MAINT(tl);

        tl_thread_join(&tl->maint_thread, NULL);
        tl_atomic_store_release_u32(&tl->maint_started, 0);
    }

    /*
     * Future cleanup (to be added in subsequent phases):
     *
     * 1. Wait for and release all snapshots
     *    - In debug builds, assert no outstanding snapshots
     *
     * 2. Release manifest and all segments
     *    - tl_manifest_release(tl->manifest);
     *
     * 3. Destroy memtable
     *    - tl_memtable_destroy(tl->memtable);
     */

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
 * Stub Implementations for Remaining API
 *
 * These are placeholder stubs that return TL_ESTATE (invalid state) until
 * implemented in later phases. This allows Phase 0 to compile while keeping
 * the full API surface.
 *===========================================================================*/

tl_status_t tl_append(tl_timelog_t* tl, tl_ts_t ts, tl_handle_t handle) {
    (void)tl; (void)ts; (void)handle;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_append_batch(tl_timelog_t* tl, const tl_record_t* records,
                            size_t n, uint32_t flags) {
    (void)tl; (void)records; (void)n; (void)flags;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_delete_range(tl_timelog_t* tl, tl_ts_t t1, tl_ts_t t2) {
    (void)tl; (void)t1; (void)t2;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_delete_before(tl_timelog_t* tl, tl_ts_t cutoff) {
    (void)tl; (void)cutoff;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_flush(tl_timelog_t* tl) {
    (void)tl;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_compact(tl_timelog_t* tl) {
    (void)tl;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_snapshot_acquire(const tl_timelog_t* tl, tl_snapshot_t** out) {
    (void)tl; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

void tl_snapshot_release(tl_snapshot_t* s) {
    (void)s;
    /* Not yet implemented */
}

tl_status_t tl_iter_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                          tl_iter_t** out) {
    (void)snap; (void)t1; (void)t2; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_iter_since(const tl_snapshot_t* snap, tl_ts_t t1,
                          tl_iter_t** out) {
    (void)snap; (void)t1; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_iter_until(const tl_snapshot_t* snap, tl_ts_t t2,
                          tl_iter_t** out) {
    (void)snap; (void)t2; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_iter_equal(const tl_snapshot_t* snap, tl_ts_t ts,
                          tl_iter_t** out) {
    (void)snap; (void)ts; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_iter_point(const tl_snapshot_t* snap, tl_ts_t ts,
                          tl_iter_t** out) {
    (void)snap; (void)ts; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_iter_next(tl_iter_t* it, tl_record_t* out) {
    (void)it; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

void tl_iter_destroy(tl_iter_t* it) {
    (void)it;
    /* Not yet implemented */
}

tl_status_t tl_scan_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                          tl_scan_fn fn, void* ctx) {
    (void)snap; (void)t1; (void)t2; (void)fn; (void)ctx;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_min_ts(const tl_snapshot_t* snap, tl_ts_t* out) {
    (void)snap; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_max_ts(const tl_snapshot_t* snap, tl_ts_t* out) {
    (void)snap; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_next_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out) {
    (void)snap; (void)ts; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_prev_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out) {
    (void)snap; (void)ts; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_maint_start(tl_timelog_t* tl) {
    (void)tl;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_maint_stop(tl_timelog_t* tl) {
    (void)tl;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_maint_step(tl_timelog_t* tl) {
    (void)tl;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_stats(const tl_snapshot_t* snap, tl_stats_t* out) {
    (void)snap; (void)out;
    return TL_ESTATE; /* Not yet implemented */
}

tl_status_t tl_validate(const tl_snapshot_t* snap) {
    (void)snap;
    return TL_ESTATE; /* Not yet implemented */
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
