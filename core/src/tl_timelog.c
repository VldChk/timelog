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
#include "query/tl_count.h"
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

/** Return default window size (1 hour) in the given time unit. */
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

    cfg->time_unit           = TL_TIME_MS;
    cfg->target_page_bytes   = TL_DEFAULT_TARGET_PAGE_BYTES;
    cfg->memtable_max_bytes  = TL_DEFAULT_MEMTABLE_MAX_BYTES;
    cfg->ooo_budget_bytes    = 0;  /* derived: memtable_max_bytes / 10 */
    cfg->sealed_max_runs     = TL_DEFAULT_SEALED_MAX_RUNS;
    cfg->sealed_wait_ms      = TL_DEFAULT_SEALED_WAIT_MS;
    cfg->maintenance_wakeup_ms = 0;  /* 0 = default (100ms) in normalize */
    cfg->max_delta_segments     = TL_DEFAULT_MAX_DELTA_SEGMENTS;
    cfg->window_size            = 0;    /* 0 = default based on time_unit */
    cfg->window_origin          = 0;
    cfg->delete_debt_threshold  = 0.0;  /* disabled */
    cfg->compaction_target_bytes = 0;
    cfg->max_compaction_inputs   = 0;
    cfg->max_compaction_windows  = 0;
    cfg->maintenance_mode = TL_MAINT_BACKGROUND;
    cfg->log_level = TL_LOG_INFO;

    return TL_OK;
}

/* struct tl_timelog is defined in tl_timelog_internal.h */

/*===========================================================================
 * Internal Validation
 *===========================================================================*/

/** Validate configuration values. Enum casts to int catch negative values. */
static tl_status_t validate_config(const tl_config_t* cfg) {
    TL_ASSERT(cfg != NULL);

    if ((int)cfg->time_unit < (int)TL_TIME_S ||
        (int)cfg->time_unit > (int)TL_TIME_NS) {
        return TL_EINVAL;
    }

    if (cfg->target_page_bytes > 0 &&
        cfg->target_page_bytes < TL_RECORD_SIZE * TL_MIN_PAGE_ROWS) {
        return TL_EINVAL;
    }

    if ((int)cfg->maintenance_mode < (int)TL_MAINT_DISABLED ||
        (int)cfg->maintenance_mode > (int)TL_MAINT_BACKGROUND) {
        return TL_EINVAL;
    }

    if (cfg->delete_debt_threshold < 0.0 || cfg->delete_debt_threshold > 1.0) {
        return TL_EINVAL;
    }

    if (cfg->window_size < 0) {
        return TL_EINVAL;
    }

    if (cfg->log_level != TL_LOG_NONE &&
        ((int)cfg->log_level < (int)TL_LOG_ERROR ||
         (int)cfg->log_level > (int)TL_LOG_TRACE)) {
        return TL_EINVAL;
    }

    tl_status_t adapt_st = tl_adaptive_config_validate(&cfg->adaptive);
    if (adapt_st != TL_OK) {
        return adapt_st;
    }

    /* Custom allocator requires realloc_fn (used by heap, recvec, intervals) */
    if (cfg->allocator.malloc_fn != NULL && cfg->allocator.realloc_fn == NULL) {
        return TL_EINVAL;
    }

    return TL_OK;
}

/**
 * Apply default values where zero means "use default".
 * Order matters: derived values (window, OOO budget) depend on base values.
 */
static void normalize_config(tl_timelog_t* tl) {
    tl_config_t* cfg = &tl->config;

    /* Base config defaults */
    if (cfg->target_page_bytes == 0)
        cfg->target_page_bytes = TL_DEFAULT_TARGET_PAGE_BYTES;
    if (cfg->memtable_max_bytes == 0)
        cfg->memtable_max_bytes = TL_DEFAULT_MEMTABLE_MAX_BYTES;
    if (cfg->sealed_max_runs == 0)
        cfg->sealed_max_runs = TL_DEFAULT_SEALED_MAX_RUNS;
    if (cfg->max_delta_segments == 0)
        cfg->max_delta_segments = TL_DEFAULT_MAX_DELTA_SEGMENTS;

    /* Derived values (depend on base config above) */
    tl->effective_window_size = (cfg->window_size == 0)
        ? default_window_size(cfg->time_unit) : cfg->window_size;
    tl->effective_ooo_budget = (cfg->ooo_budget_bytes == 0)
        ? cfg->memtable_max_bytes / 10 : cfg->ooo_budget_bytes;

    if (cfg->maintenance_wakeup_ms == 0)
        cfg->maintenance_wakeup_ms = TL_DEFAULT_MAINTENANCE_WAKEUP_MS;
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

tl_status_t tl_open(const tl_config_t* cfg, tl_timelog_t** out) {
    tl_status_t status;
    tl_timelog_t* tl = NULL;
    tl_config_t default_cfg;

    if (out == NULL) {
        return TL_EINVAL;
    }
    *out = NULL;

    if (cfg == NULL) {
        tl_config_init_defaults(&default_cfg);
        cfg = &default_cfg;
    }

    status = validate_config(cfg);
    if (status != TL_OK) {
        return status;
    }

    tl_alloc_ctx_t temp_alloc;
    tl__alloc_init(&temp_alloc, &cfg->allocator);

    tl = TL_NEW(&temp_alloc, tl_timelog_t);
    if (tl == NULL) {
        tl__alloc_destroy(&temp_alloc);
        return TL_ENOMEM;
    }

    memset(tl, 0, sizeof(*tl));
    tl->config = *cfg;
    tl__alloc_init(&tl->alloc, &cfg->allocator);
    tl__log_init(&tl->log, cfg->log_fn, cfg->log_ctx, cfg->log_level);
    normalize_config(tl);

    status = init_locks(tl);
    if (status != TL_OK) {
        tl__alloc_destroy(&tl->alloc);
        temp_alloc.alloc.free_fn(temp_alloc.alloc.ctx, tl);
        return status;
    }

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

    status = tl_manifest_create(&tl->alloc, &tl->manifest);
    if (status != TL_OK) {
        tl_memtable_destroy(&tl->memtable);
        destroy_locks(tl);
        tl__alloc_destroy(&tl->alloc);
        temp_alloc.alloc.free_fn(temp_alloc.alloc.ctx, tl);
        return status;
    }
    tl->next_gen = 1;
    tl->memview_cache = NULL;
    tl->memview_cache_epoch = 0;

#ifdef TL_DEBUG
    tl_atomic_init_u32(&tl->snapshot_count, 0);
#endif

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

    tl->is_open = true;
    tl->maint_state = TL_WORKER_STOPPED;
    tl->maint_shutdown = false;
    tl->flush_pending = false;
    tl->compact_pending = false;
    tl_adaptive_state_init(&tl->adaptive);

    /* Freeze the window grid once L1 exists to keep window boundaries stable. */
    tl->window_grid_frozen = (tl_manifest_l1_count(tl->manifest) > 0);

    /* Auto-start background worker (default mode) */
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

    /* Stop worker first; abort if join fails (worker may still hold locks) */
    tl_status_t stop_st = tl_maint_stop(tl);
    if (stop_st == TL_EINTERNAL) {
        TL_LOG_ERROR("tl_close: worker join failed, aborting to prevent corruption");
        abort();
    }

    tl->is_open = false;

#ifdef TL_DEBUG
    uint32_t outstanding = tl_atomic_load_relaxed_u32(&tl->snapshot_count);
    TL_ASSERT_MSG(outstanding == 0,
        "tl_close() called with outstanding snapshots - caller must release all snapshots first");
#endif

    /* on_drop_handle is not invoked for records still present at close. */
    if (tl->manifest != NULL) {
        tl_manifest_release(tl->manifest);
        tl->manifest = NULL;
    }

    if (tl->memview_cache != NULL) {
        tl_memview_shared_release(tl->memview_cache);
        tl->memview_cache = NULL;
    }

    tl_memtable_destroy(&tl->memtable);
    destroy_locks(tl);

    /* Save allocator before destroying it (needed to free tl itself) */
    tl_alloc_ctx_t alloc = tl->alloc;

    tl__alloc_destroy(&tl->alloc);
    alloc.alloc.free_fn(alloc.alloc.ctx, tl);
}

/*===========================================================================
 * Write Path Implementation
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

    if (!tl_memtable_should_seal(&tl->memtable)) {
        return TL_OK;
    }

    if (tl_memtable_ooo_budget_exceeded(&tl->memtable)) {
        tl_atomic_inc_u64(&tl->ooo_budget_hits);
    }

    tl_record_t* dropped = NULL;
    size_t dropped_len = 0;
    tl_status_t seal_st = tl_memtable_seal_ex(&tl->memtable,
                                               &tl->memtable_mu,
                                               NULL,
                                               tl->op_seq,
                                               &dropped,
                                               &dropped_len);
    if (seal_st == TL_OK) {
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
        /* Non-queue-full failure (e.g., ENOMEM); remap to EBUSY since
         * the write already succeeded and must not be retried. */
        return TL_EBUSY;
    }

    if (tl->config.maintenance_mode == TL_MAINT_DISABLED) {
        return TL_EBUSY;
    }

    /* Background mode: drop writer_mu, wait for space, retry seal */
    tl_atomic_inc_u64(&tl->backpressure_waits);
    TL_UNLOCK_WRITER(tl);

    TL_LOCK_MEMTABLE(tl);
    bool have_space = tl_memtable_wait_for_space(&tl->memtable,
                                                   &tl->memtable_mu,
                                                   &tl->memtable_cond,
                                                   tl->config.sealed_wait_ms);
    TL_UNLOCK_MEMTABLE(tl);

    TL_LOCK_WRITER(tl);

    if (!have_space) {
        return TL_EBUSY;
    }

    /* Retry seal after space freed */
    dropped = NULL;
    dropped_len = 0;
    seal_st = tl_memtable_seal_ex(&tl->memtable,
                                   &tl->memtable_mu,
                                   NULL,
                                   tl->op_seq,
                                   &dropped,
                                   &dropped_len);
    if (seal_st == TL_OK) {
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

    /* Write succeeded but seal failed; EBUSY prevents caller retry */
    return TL_EBUSY;
}

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

    TL_LOCK_WRITER(tl);

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

    /* Deferred signal (lock ordering: writer_mu before maint_mu) */
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

    TL_LOCK_WRITER(tl);

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
        /* All-or-nothing: failure means no records were inserted. */
        return insert_st;
    }
    tl_status_t seal_st = handle_seal_with_backpressure(tl, &need_signal,
                                                        &dropped, &dropped_len);

    TL_UNLOCK_WRITER(tl);

    /* Deferred signal (lock ordering: writer_mu before maint_mu) */
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

    if (t1 == t2) {
        return TL_OK;  /* empty range */
    }
    if (t1 > t2) {
        return TL_EINVAL;
    }

    tl_status_t st;
    bool need_signal = false;
    tl_record_t* dropped = NULL;
    size_t dropped_len = 0;

    TL_LOCK_WRITER(tl);

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

    st = handle_seal_with_backpressure(tl, &need_signal, &dropped, &dropped_len);
    TL_UNLOCK_WRITER(tl);

    /* Deferred signal (lock ordering: writer_mu before maint_mu) */
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

    TL_LOCK_WRITER(tl);

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

    /* Deferred signal (lock ordering: writer_mu before maint_mu) */
    if (need_signal) {
        tl__maint_request_flush(tl);
    }
    tl__emit_drop_callbacks(tl, dropped, dropped_len);

    return st;
}

/*===========================================================================
 * Compaction Delegation
 *===========================================================================*/

static bool tl__compaction_needed(const tl_timelog_t* tl) {
    return tl_compact_needed(tl);
}

static tl_status_t tl__compact_one_step(tl_timelog_t* tl) {
    return tl_compact_one(tl, 3);  /* 3 bounded publish retries */
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

    /* Step 1: Pin base manifest under writer_mu (prevents ABA/UAF) */
    TL_LOCK_WRITER(tl);
    tl_manifest_t* base = tl->manifest;
    tl_manifest_acquire(base);
    TL_UNLOCK_WRITER(tl);

    /* Step 2: Build new manifest OFF-LOCK */
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

    /* Step 3: Validate base unchanged, then swap under seqlock */
    TL_LOCK_WRITER(tl);

    if (tl->manifest != base) {
        TL_UNLOCK_WRITER(tl);
        tl_manifest_release(new_manifest);
        tl_manifest_release(base);
        return TL_EBUSY;  /* seg NOT released -- caller retries */
    }

    tl_seqlock_write_begin(&tl->view_seq);
    tl_manifest_t* old = tl->manifest;
    tl->manifest = new_manifest;

    /* Pop memrun inside seqlock so no snapshot sees both segment and memrun */
    TL_LOCK_MEMTABLE(tl);
    tl_memtable_pop_oldest(&tl->memtable, &tl->memtable_cond);
    TL_UNLOCK_MEMTABLE(tl);

    tl_seqlock_write_end(&tl->view_seq);
    TL_UNLOCK_WRITER(tl);

    tl_manifest_release(base);
    tl_manifest_release(old);
    tl_memrun_release(mr);
    tl_segment_release(seg);  /* Builder acquired its own ref */

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
 * Flush a single memrun to L0 segment and publish via rebase-publish pattern.
 * On success, mr is released. On failure, caller must release mr.
 */
static tl_status_t flush_one_memrun(tl_timelog_t* tl, tl_memrun_t* mr) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(mr != NULL);

    tl_status_t st;

    /* Acquire unique generation under writer_mu */
    TL_LOCK_WRITER(tl);
    uint32_t gen = tl->next_gen++;
    TL_UNLOCK_WRITER(tl);

    /* Capture tombstone snapshot for filtering */
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

    /* Build L0 segment OFF-LOCK */
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

    /* Publish with retry (3 attempts, same as compaction) */
    for (int attempt = 0; attempt < 3; attempt++) {
        st = flush_publish(tl, mr, seg);
        if (st != TL_EBUSY) {
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
    }

    /* Retries exhausted; release segment, caller releases mr */
    tl_segment_release(seg);
    if (dropped != NULL) {
        tl__free(&tl->alloc, dropped);
    }
    return TL_EBUSY;
}

/*===========================================================================
 * tl__flush_one - Flush one sealed memrun (maintenance thread path).
 * Also updates adaptive density metrics after successful flush.
 *===========================================================================*/
static tl_status_t tl__flush_one(tl_timelog_t* tl) {
    TL_ASSERT(tl != NULL);

    TL_LOCK_FLUSH(tl);

    tl_memrun_t* mr = NULL;
    TL_LOCK_MEMTABLE(tl);
    tl_status_t st = tl_memtable_peek_oldest(&tl->memtable, &mr);
    TL_UNLOCK_MEMTABLE(tl);

    if (st != TL_OK || mr == NULL) {
        TL_UNLOCK_FLUSH(tl);
        return TL_EOF;  /* No work */
    }

    /* Capture flush metrics before flush (record-only bounds, no tombstones) */
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

            /* run is sorted; OOO has precomputed min/max */
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

    st = flush_one_memrun(tl, mr);
    if (st != TL_OK) {
        tl_memrun_release(mr);
    }

    TL_UNLOCK_FLUSH(tl);

    /* Update adaptive density after flush_mu release (lock ordering) */
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

    TL_LOCK_FLUSH(tl);

    /* Loop: seal active + flush all sealed until nothing remains */
    for (;;) {
        TL_LOCK_WRITER(tl);
        bool need_seal = !tl_memtable_is_active_empty(&tl->memtable);
        if (need_seal) {
            st = tl_memtable_seal(&tl->memtable,
                                   &tl->memtable_mu,
                                   NULL,
                                   tl->op_seq);
            if (st != TL_OK && st != TL_EBUSY) {
                TL_UNLOCK_WRITER(tl);
                TL_UNLOCK_FLUSH(tl);
                return st;
            }
        }
        TL_UNLOCK_WRITER(tl);

        tl_memrun_t* mr = NULL;
        TL_LOCK_MEMTABLE(tl);
        st = tl_memtable_peek_oldest(&tl->memtable, &mr);
        TL_UNLOCK_MEMTABLE(tl);

        if (st != TL_OK || mr == NULL) {
            TL_LOCK_WRITER(tl);
            bool active_empty = tl_memtable_is_active_empty(&tl->memtable);
            TL_UNLOCK_WRITER(tl);

            if (active_empty) {
                break;
            }
            continue;
        }

        st = flush_one_memrun(tl, mr);
        if (st != TL_OK) {
            tl_memrun_release(mr);
            TL_UNLOCK_FLUSH(tl);
            return st;
        }
    }

    TL_UNLOCK_FLUSH(tl);
    return TL_OK;
}

/*===========================================================================
 * Maintenance Request Helpers
 *
 * These functions implement the deferred signaling pattern:
 * - Set flag UNDER maint_mu (atomically with respect to worker)
 * - Signal condvar only if worker is RUNNING
 * - MUST be called AFTER releasing writer_mu (lock ordering)
 *
 * CRITICAL: Always set the flag, but only signal if worker is RUNNING.
 * This ensures work isn't lost if writes happen before tl_maint_start().
 *===========================================================================*/

static void tl__maint_request_flush(tl_timelog_t* tl) {
    TL_ASSERT(tl != NULL);

    if (tl->config.maintenance_mode != TL_MAINT_BACKGROUND) {
        return;
    }

    TL_LOCK_MAINT(tl);
    tl->flush_pending = true;

    if (tl->maint_state == TL_WORKER_RUNNING) {
        tl_cond_signal(&tl->maint_cond);
    }

    TL_UNLOCK_MAINT(tl);
}

static void tl__maint_request_compact(tl_timelog_t* tl) {
    TL_ASSERT(tl != NULL);

    TL_LOCK_MAINT(tl);
    tl->compact_pending = true;

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

    tl__maint_request_compact(tl);

    return TL_OK;
}

/*===========================================================================
 * Snapshot API Implementation
 *===========================================================================*/

tl_status_t tl_snapshot_acquire(const tl_timelog_t* tl, tl_snapshot_t** out) {
    if (tl == NULL || out == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }

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

/** Build plan + k-way merge + tombstone filter for the given range. */
static tl_status_t iter_create_internal(tl_snapshot_t* snap,
                                         tl_ts_t t1, tl_ts_t t2,
                                         bool t2_unbounded,
                                         tl_iter_t** out) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    tl_alloc_ctx_t* alloc = snap->alloc;
    tl_status_t st;

    tl_iter_t* it = TL_NEW(alloc, tl_iter_t);
    if (it == NULL) {
        return TL_ENOMEM;
    }
    memset(it, 0, sizeof(*it));
    it->snapshot = snap;
    it->alloc = alloc;

    st = tl_plan_build(&it->plan, snap, alloc, t1, t2, t2_unbounded);
    if (st != TL_OK) {
        tl__free(alloc, it);
        return st;
    }

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
 * Iterator API Implementation
 *===========================================================================*/

tl_status_t tl_iter_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                          tl_iter_t** out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }
    if (t1 >= t2) {
        /* Empty/invalid range: return exhausted iterator */
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

    return iter_create_internal((tl_snapshot_t*)snap, t1, 0, true, out);
}

tl_status_t tl_iter_until(const tl_snapshot_t* snap, tl_ts_t t2,
                          tl_iter_t** out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

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
    tl_iter_t* it = TL_NEW(alloc, tl_iter_t);
    if (it == NULL) {
        return TL_ENOMEM;
    }
    memset(it, 0, sizeof(*it));
    it->snapshot = (tl_snapshot_t*)snap;
    it->alloc = alloc;
    it->point_mode = true;
    it->point_idx = 0;

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

    if (it->point_mode) {
        tl_point_result_destroy(&it->point_result);
        tl_alloc_ctx_t* alloc = it->alloc;
        tl__free(alloc, it);
        return;
    }

    /* Range mode: destroy in reverse order of creation (filter has no destroy) */

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
    return (st == TL_EOF) ? TL_OK : st;
}



tl_status_t tl_count_range(const tl_timelog_t* tl, tl_ts_t t1, tl_ts_t t2,
                           uint64_t* out) {
    if (tl == NULL || out == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    tl_snapshot_t* snap = NULL;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    if (st != TL_OK) {
        return st;
    }

    st = tl_snapshot_count_range_internal(snap, t1, t2, false, out);
    tl_snapshot_release(snap);
    return st;
}

tl_status_t tl_count(const tl_timelog_t* tl, uint64_t* out) {
    if (tl == NULL || out == NULL) {
        return TL_EINVAL;
    }
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    tl_snapshot_t* snap = NULL;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    if (st != TL_OK) {
        return st;
    }

    st = tl_snapshot_count_range_internal(snap, TL_TS_MIN, 0, true, out);
    tl_snapshot_release(snap);
    return st;
}

tl_status_t tl_snapshot_count_range(const tl_snapshot_t* snap,
                                     tl_ts_t t1, tl_ts_t t2,
                                     int t2_unbounded,
                                     uint64_t* out) {
    return tl_snapshot_count_range_internal(snap, t1, t2, t2_unbounded != 0, out);
}

/*===========================================================================
 * Timestamp Navigation
 *===========================================================================*/

tl_status_t tl_min_ts(const tl_snapshot_t* snap, tl_ts_t* out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    if (!snap->has_data) {
        return TL_EOF;
    }

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

    /* O(N) scan: LSM iterators are forward-only */
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
        return TL_EOF;
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

    tl_iter_t* it = NULL;
    tl_status_t st = tl_iter_since(snap, next, &it);
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

tl_status_t tl_prev_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    if (!snap->has_data) {
        return TL_EOF;
    }

    if (ts == TL_TS_MIN) {
        return TL_EOF;
    }

    /* O(N) scan of [TL_TS_MIN, ts) to find the last timestamp */
    tl_iter_t* it = NULL;
    tl_status_t st = tl_iter_range(snap, TL_TS_MIN, ts, &it);
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
        return TL_EOF;
    }

    *out = last_ts;
    return TL_OK;
}

/*===========================================================================
 * Background Maintenance Worker
 *
 * The worker thread loop:
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

        /* Wait for work or shutdown (timed wait catches missed signals) */
        TL_LOCK_MAINT(tl);
        while (!tl->maint_shutdown &&
               !tl->flush_pending &&
               !tl->compact_pending) {
            tl_cond_timedwait(&tl->maint_cond, &tl->maint_mu,
                              tl->config.maintenance_wakeup_ms);
        }

        if (tl->maint_shutdown) {
            TL_UNLOCK_MAINT(tl);
            break;
        }

        /* Copy and clear flags atomically (under maint_mu) */
        if (tl->flush_pending) {
            work |= TL_WORK_FLUSH;
        }
        if (tl->compact_pending) {
            work |= TL_WORK_COMPACT_EXPLICIT;
        }

        tl->flush_pending = false;
        tl->compact_pending = false;

        TL_UNLOCK_MAINT(tl);

        /* Check sealed queue to detect missed signals */
        TL_LOCK_MEMTABLE(tl);
        size_t sealed_len = tl_memtable_sealed_len(&tl->memtable);
        TL_UNLOCK_MEMTABLE(tl);
        if (sealed_len > 0) {
            work |= TL_WORK_FLUSH;
        }

        /* Only check compaction heuristic when flush work exists (compaction
         * triggers only change after flush creates new L0 segments). */
        if (!(work & TL_WORK_COMPACT_EXPLICIT) && (work & TL_WORK_FLUSH)) {
            if (tl__compaction_needed(tl)) {
                work |= TL_WORK_COMPACT_HEURISTIC;
            }
        }

        /* Execute flush work (fairness: flush one, check compaction) */
        if (work & TL_WORK_FLUSH) {
            tl_status_t st;
            while ((st = tl__flush_one(tl)) == TL_OK) {
                if (tl__compaction_needed(tl)) {
                    work |= TL_WORK_COMPACT_HEURISTIC;
                    break;
                }
            }

            /* Transient errors: backoff to prevent CPU spin */
            if (st == TL_ENOMEM || st == TL_EBUSY || st == TL_EINTERNAL) {
                tl_sleep_ms(backoff_ms);
                backoff_ms = (backoff_ms * 2 > TL_MAINT_BACKOFF_MAX_MS)
                           ? TL_MAINT_BACKOFF_MAX_MS : backoff_ms * 2;

                /* Log transient error (once per backoff cycle) */
                {
                    tl_log_ctx_t* log = &tl->log;
                    TL_LOG_WARN("Flush failed (%s), retrying after %u ms backoff",
                                tl_strerror(st), backoff_ms);
                    (void)log;  /* Silence unused warning if logging disabled */
                }
            } else {
                backoff_ms = TL_MAINT_BACKOFF_INIT_MS;  /* Reset on success */
            }

            /* Re-set flush_pending if more sealed memruns exist */
            if (st != TL_EOF) {
                TL_LOCK_MEMTABLE(tl);
                bool more_work = tl_memtable_has_sealed(&tl->memtable);
                TL_UNLOCK_MEMTABLE(tl);
                if (more_work) {
                    TL_LOCK_MAINT(tl);
                    tl->flush_pending = true;
                    TL_UNLOCK_MAINT(tl);
                }
            }
        }

        /* Execute compaction work */
        if (work & (TL_WORK_COMPACT_EXPLICIT | TL_WORK_COMPACT_HEURISTIC)) {
            tl_status_t st = tl__compact_one_step(tl);

            if (st == TL_ENOMEM || st == TL_EBUSY || st == TL_EINTERNAL) {
                tl_sleep_ms(backoff_ms);
                backoff_ms = (backoff_ms * 2 > TL_MAINT_BACKOFF_MAX_MS)
                           ? TL_MAINT_BACKOFF_MAX_MS : backoff_ms * 2;

                /* Log transient error (once per backoff cycle) */
                {
                    tl_log_ctx_t* log = &tl->log;
                    TL_LOG_WARN("Compaction failed (%s), retrying after %u ms backoff",
                                tl_strerror(st), backoff_ms);
                    (void)log;  /* Silence unused warning if logging disabled */
                }

                TL_LOCK_MAINT(tl);
                tl->compact_pending = true;
                TL_UNLOCK_MAINT(tl);
            } else if (st == TL_EOVERFLOW) {
                /* Non-retryable: window span overflow */
                tl_log_ctx_t* log = &tl->log;
                TL_LOG_ERROR("Compaction failed: window span overflow (TL_EOVERFLOW)");
                (void)log;  /* Silence unused warning if logging disabled */
                backoff_ms = TL_MAINT_BACKOFF_INIT_MS;
            } else if (st == TL_OK) {
                backoff_ms = TL_MAINT_BACKOFF_INIT_MS;
            }
        }
    }

    return NULL;
}

/*===========================================================================
 * tl_maint_start - STOPPED -> RUNNING (idempotent if already RUNNING)
 *===========================================================================*/

tl_status_t tl_maint_start(tl_timelog_t* tl) {
    if (tl == NULL) {
        return TL_EINVAL;
    }

    if (!tl->is_open) {
        return TL_ESTATE;
    }
    if (tl->config.maintenance_mode != TL_MAINT_BACKGROUND) {
        return TL_ESTATE;
    }

    TL_LOCK_MAINT(tl);

    switch (tl->maint_state) {
        case TL_WORKER_RUNNING:
            TL_UNLOCK_MAINT(tl);
            return TL_OK;
        case TL_WORKER_STOPPING:
            TL_UNLOCK_MAINT(tl);
            return TL_EBUSY;
        case TL_WORKER_STOPPED:
            break;
    }

    tl->maint_shutdown = false;

    tl_status_t st = tl_thread_create(&tl->maint_thread,
                                       tl__maint_worker_entry,
                                       tl);
    if (st != TL_OK) {
        TL_UNLOCK_MAINT(tl);
        return TL_EINTERNAL;
    }

    tl->maint_state = TL_WORKER_RUNNING;

    /* Wake worker if work was queued before start */
    if (tl->flush_pending || tl->compact_pending) {
        tl_cond_signal(&tl->maint_cond);
    }

    TL_UNLOCK_MAINT(tl);
    return TL_OK;
}

/*===========================================================================
 * tl_maint_stop - RUNNING -> STOPPING -> STOPPED
 * Join happens OUTSIDE maint_mu (worker may hold lower-priority locks).
 * Mode not checked (allows tl_close to call unconditionally).
 *===========================================================================*/

tl_status_t tl_maint_stop(tl_timelog_t* tl) {
    if (tl == NULL) {
        return TL_EINVAL;
    }

    TL_LOCK_MAINT(tl);

    switch (tl->maint_state) {
        case TL_WORKER_STOPPED:
        case TL_WORKER_STOPPING:
            TL_UNLOCK_MAINT(tl);
            return TL_OK;  /* Idempotent; prevents double-join */
        case TL_WORKER_RUNNING:
            break;
    }

    tl->maint_state = TL_WORKER_STOPPING;
    tl->maint_shutdown = true;
    tl_cond_signal(&tl->maint_cond);
    TL_UNLOCK_MAINT(tl);

    /* Join OUTSIDE maint_mu; must use original struct member (not a copy) */
    tl_status_t st = tl_thread_join(&tl->maint_thread, NULL);

    TL_LOCK_MAINT(tl);
    if (st == TL_OK) {
        tl->maint_state = TL_WORKER_STOPPED;
        tl->maint_shutdown = false;
    }
    /* On join failure: stay in STOPPING, don't clear shutdown */
    TL_UNLOCK_MAINT(tl);

    return (st == TL_OK) ? TL_OK : TL_EINTERNAL;
}

/*===========================================================================
 * tl_maint_step - Manual mode: flush one sealed memrun, else compact one step.
 *===========================================================================*/

tl_status_t tl_maint_step(tl_timelog_t* tl) {
    if (tl == NULL) {
        return TL_EINVAL;
    }

    if (!tl->is_open) {
        return TL_ESTATE;
    }
    if (tl->config.maintenance_mode != TL_MAINT_DISABLED) {
        return TL_ESTATE;
    }

    TL_LOCK_MEMTABLE(tl);
    bool has_sealed = tl_memtable_has_sealed(&tl->memtable);
    TL_UNLOCK_MEMTABLE(tl);

    if (has_sealed) {
        tl_status_t st = tl__flush_one(tl);
        if (st == TL_OK || st == TL_ENOMEM) {
            return st;
        }
    }

    /* Compaction: explicit request OR automatic heuristic */
    bool was_explicit = false;
    TL_LOCK_MAINT(tl);
    if (tl->compact_pending) {
        was_explicit = true;
    }
    TL_UNLOCK_MAINT(tl);

    bool do_compact = was_explicit || tl__compaction_needed(tl);

    if (do_compact) {
        tl_status_t st = tl__compact_one_step(tl);

        /* Clear on success/no-work/fatal; preserve on transient errors */
        if (was_explicit && (st == TL_OK || st == TL_EOF || st == TL_EOVERFLOW)) {
            TL_LOCK_MAINT(tl);
            tl->compact_pending = false;
            TL_UNLOCK_MAINT(tl);
        }

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
 *===========================================================================*/

tl_status_t tl_stats(const tl_snapshot_t* snap, tl_stats_t* out) {
    if (snap == NULL || out == NULL) {
        return TL_EINVAL;
    }

    memset(out, 0, sizeof(*out));

    const tl_manifest_t* manifest = tl_snapshot_manifest(snap);
    const tl_memview_t* memview = tl_snapshot_memview(snap);

    out->segments_l0 = tl_manifest_l0_count(manifest);
    out->segments_l1 = tl_manifest_l1_count(manifest);

    /* Count pages and visible records (watermark-aware, no row scans) */
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

    /* Active buffers: use per-record tombstone filtering. */
    total_records += tl__count_active_visible_range(memview, skyline_imm,
                                                     TL_TS_MIN, 0, true);

    /* Sealed memruns use watermark-aware immutable counting. */
    for (size_t i = 0; i < tl_memview_sealed_len(memview); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(memview, i);
        total_records += tl__visible_records_in_memrun(mr,
                                                        skyline_data,
                                                        skyline_len);
    }

    out->records_estimate = total_records;
    tl_intervals_destroy(&skyline);

    /* RAW bounds (pre-tombstone). Use tl_min_ts/tl_max_ts for visible bounds. */
    if (tl_snapshot_has_data(snap)) {
        out->min_ts = tl_snapshot_min_ts(snap);
        out->max_ts = tl_snapshot_max_ts(snap);
    } else {
        out->min_ts = TL_TS_MAX;
        out->max_ts = TL_TS_MIN;
    }

    /* Tombstone count: sum across all sources (not deduplicated) */
    uint64_t tombstone_count = 0;
    tombstone_count += tl_memview_tomb_len(memview);

    for (size_t i = 0; i < tl_memview_sealed_len(memview); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(memview, i);
        tl_intervals_imm_t mr_tombs = tl_memrun_tombs_imm(mr);
        tombstone_count += mr_tombs.len;
    }

    for (uint32_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);
        if (tl_segment_has_tombstones(seg)) {
            tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
            tombstone_count += seg_tombs.len;
        }
    }

    out->tombstone_count = tombstone_count;

    /* Memtable metrics (snapshot-time values) */
    out->memtable_active_records = (uint64_t)tl_memview_run_len(memview);
    out->memtable_ooo_records = (uint64_t)tl_memview_ooo_total_len(memview);
    out->memtable_sealed_runs = (uint64_t)tl_memview_sealed_len(memview);

    /* Operational counters (relaxed load, monotonically increasing) */
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

        /* Adaptive metrics (under maint_mu; zero when disabled) */
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
    if (snap == NULL) {
        return TL_EINVAL;
    }

#ifndef TL_DEBUG
    (void)snap;
    return TL_OK;  /* No-op in release builds */
#else
    /* Debug: validate bottom-up (manifest -> memview -> snapshot bounds) */
    const tl_manifest_t* manifest = tl_snapshot_manifest(snap);
    const tl_memview_t* memview = tl_snapshot_memview(snap);

    if (!tl_manifest_validate(manifest)) {
        return TL_EINTERNAL;
    }

    if (!tl_memview_validate(memview)) {
        return TL_EINTERNAL;
    }

    if (snap->has_data) {
        if (snap->min_ts > snap->max_ts) {
            return TL_EINTERNAL;
        }
    }

    return TL_OK;
#endif /* TL_DEBUG */
}

/* Publication uses separate LOCK_WRITER + seqlock_write_begin (not a combined
 * helper) because manifest validation must occur between the two steps. */
