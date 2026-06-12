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

/* Common precondition check for public API functions. */
#define TL_CHECK_OPEN(tl) \
    do { \
        if ((tl) == NULL) return TL_EINVAL; \
        if (!(tl)->is_open) return TL_ESTATE; \
    } while (0)

/*===========================================================================
 * Iterator Structure
 *
 * Wraps the query plan, K-way merge, and tombstone filter behind a single
 * forward iterator. Range mode uses the plan/kmerge/filter trio; point mode
 * skips them in favour of an eager lookup result.
 *===========================================================================*/

struct tl_iter {
    /* Range-mode state: plan owns sources and tombstones. */
    tl_plan_t           plan;
    tl_kmerge_iter_t    kmerge;
    tl_filter_iter_t    filter;

    /* Point-mode state: eagerly materialised match set. */
    tl_point_result_t   point_result;
    size_t              point_idx;

    /* Snapshot pins the underlying manifest/memview for the iterator's life. */
    tl_snapshot_t*      snapshot;
    tl_alloc_ctx_t*     alloc;

    bool                done;
    bool                initialized;
    bool                point_mode;
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

/** Default window size of one hour, expressed in the configured time unit. */
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

/** Validate configuration values. Enums are cast to int so that negative
 *  values supplied via the C ABI are rejected rather than coerced. */
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

    /* Custom allocators must provide realloc; heap, recvec, and intervals all
     * grow via realloc and cannot fall back to a malloc/copy/free dance. */
    if (cfg->allocator.malloc_fn != NULL && cfg->allocator.realloc_fn == NULL) {
        return TL_EINVAL;
    }

    return TL_OK;
}

/**
 * Resolve zero-valued fields to their defaults. Base fields must be filled in
 * before derived ones (window size and OOO budget read from them).
 */
static void normalize_config(tl_timelog_t* tl) {
    tl_config_t* cfg = &tl->config;

    if (cfg->target_page_bytes == 0)
        cfg->target_page_bytes = TL_DEFAULT_TARGET_PAGE_BYTES;
    if (cfg->memtable_max_bytes == 0)
        cfg->memtable_max_bytes = TL_DEFAULT_MEMTABLE_MAX_BYTES;
    if (cfg->sealed_max_runs == 0)
        cfg->sealed_max_runs = TL_DEFAULT_SEALED_MAX_RUNS;
    if (cfg->max_delta_segments == 0)
        cfg->max_delta_segments = TL_DEFAULT_MAX_DELTA_SEGMENTS;

    /* Derived defaults (depend on base config resolved above). */
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

    /* Once any L1 segment exists the window grid must be frozen: L1 segments
     * partition the time domain into non-overlapping windows, so changing the
     * window size after the fact would break that partitioning. */
    tl->window_grid_frozen = (tl_manifest_l1_count(tl->manifest) > 0);

    if (tl->config.maintenance_mode == TL_MAINT_BACKGROUND) {
        status = tl_maint_start(tl);
        if (status != TL_OK) {
            /* Worker startup failed: tear everything we just built back down
             * so tl_open() leaves no half-initialised state behind. */
            tl_manifest_release(tl->manifest);
            tl_memtable_destroy(&tl->memtable);
            destroy_locks(tl);
            tl__alloc_destroy(&tl->alloc);
            temp_alloc.alloc.free_fn(temp_alloc.alloc.ctx, tl);
            return status;
        }
    }

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

    /* Stop the background worker before tearing down state it might touch.
     * tl_close() is not thread-safe; TL_EBUSY here means another thread is
     * already stopping the worker, so continuing would free state before
     * quiescence. Any non-OK stop result is therefore a hard lifecycle
     * violation, not a recoverable close outcome. */
    tl_status_t stop_st = tl_maint_stop(tl);
    if (stop_st != TL_OK) {
        TL_LOG_ERROR("tl_close: worker stop failed (%s), aborting to prevent corruption",
                     tl_strerror(stop_st));
        abort();
    }

    tl->is_open = false;

#ifdef TL_DEBUG
    uint32_t outstanding = tl_atomic_load_relaxed_u32(&tl->snapshot_count);
    TL_ASSERT_MSG(outstanding == 0,
        "tl_close() called with outstanding snapshots - caller must release all snapshots first");
#endif

    /* Contract: on_drop_handle fires only for tombstone-driven physical
     * deletes during flush/compaction. Records still present at close are NOT
     * surfaced; the binding layer must track its own owned references. */
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

    /* Copy the allocator out before destroying the embedded context: we need
     * a valid free_fn to release the tl_timelog_t struct itself. */
    tl_alloc_ctx_t alloc = tl->alloc;

    tl__alloc_destroy(&tl->alloc);
    alloc.alloc.free_fn(alloc.alloc.ctx, tl);
}

/*===========================================================================
 * Write Path Implementation
 *===========================================================================*/

/* Forward declaration: the write path requests flushes after dropping
 * writer_mu, but the definition lives with the maintenance plumbing below. */
static void tl__maint_request_flush(tl_timelog_t* tl);
static void tl__maint_request_compact(tl_timelog_t* tl);

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
 * Seal the active run if the memtable is full, applying backpressure when
 * the sealed-run queue has no room.
 *
 * Called with writer_mu held; returns with writer_mu held. May temporarily
 * drop writer_mu to wait on memtable_cond — this respects the lock order
 * (writer_mu must never be held while acquiring memtable_mu for a wait).
 *
 * Signalling is deferred: the worker is woken only after writer_mu is
 * released, because maint_mu sits to the left of writer_mu in the lock
 * order. The caller must observe *need_signal and call
 * tl__maint_request_flush() outside the writer_mu critical section.
 *
 * @param tl          Engine instance.
 * @param need_signal Out: true if the caller should wake the worker.
 * @return TL_OK on success or no-op; TL_EBUSY signals that the original write
 *         already succeeded but back-end work could not be enqueued — the
 *         caller must not retry the write, as the record is already in the log.
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
        /* Any non-queue-full failure (e.g. ENOMEM during the seal) is
         * remapped to EBUSY: the write itself already succeeded, so we
         * must not let the caller retry it. EBUSY is the contractual
         * signal for "the record is in, but back-end work is degraded". */
        return TL_EBUSY;
    }

    if (tl->config.maintenance_mode == TL_MAINT_DISABLED) {
        return TL_EBUSY;
    }

    /* Background mode: release writer_mu, wait for the worker to free a
     * sealed-queue slot, then re-acquire writer_mu and retry. Dropping the
     * writer lock is mandatory — the worker needs to publish a flushed
     * segment, which itself requires writer_mu. */
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

    /* Write succeeded but seal could not complete. Return EBUSY rather than
     * the inner error so the caller does not retry an already-applied write. */
    return TL_EBUSY;
}

tl_status_t tl_append(tl_timelog_t* tl, tl_ts_t ts, tl_handle_t handle) {
    TL_CHECK_OPEN(tl);

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

    /* Seal/backpressure decisions happen under writer_mu but condvar
     * signalling and user callbacks must run after we release it (the lock
     * order forbids taking maint_mu under writer_mu, and on_drop_handle may
     * call into arbitrary user code). */
    tl_status_t seal_st = handle_seal_with_backpressure(tl, &need_signal,
                                                        &dropped, &dropped_len);

    TL_UNLOCK_WRITER(tl);

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
    TL_CHECK_OPEN(tl);
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
        /* All-or-nothing batch semantics: on failure no records are inserted,
         * so the caller may safely retry the entire batch. */
        return insert_st;
    }
    tl_status_t seal_st = handle_seal_with_backpressure(tl, &need_signal,
                                                        &dropped, &dropped_len);

    TL_UNLOCK_WRITER(tl);

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
    TL_CHECK_OPEN(tl);

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

    if (need_signal) {
        tl__maint_request_flush(tl);
    }
    tl__emit_drop_callbacks(tl, dropped, dropped_len);

    return st;
}

tl_status_t tl_delete_before(tl_timelog_t* tl, tl_ts_t cutoff) {
    TL_CHECK_OPEN(tl);

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

    st = handle_seal_with_backpressure(tl, &need_signal, &dropped, &dropped_len);

    TL_UNLOCK_WRITER(tl);

    if (need_signal) {
        tl__maint_request_flush(tl);
    }
    tl__emit_drop_callbacks(tl, dropped, dropped_len);

    return st;
}

/*===========================================================================
 * Compaction Delegation
 *===========================================================================*/

/* Cap on publish retries when a concurrent writer races us during compaction:
 * we rebuild and try again, but bound the loop so a runaway producer cannot
 * starve the maintenance worker. */
#define TL_COMPACT_MAX_RETRIES 3

/*===========================================================================
 * Flush Implementation
 *
 * Flush uses the rebase-publish pattern (shared with compaction) to keep the
 * writer_mu critical section to a pointer compare and pointer swap. All page
 * and segment construction happens off-lock; only manifest publication and
 * the seqlock transition run while writers are blocked.
 *===========================================================================*/

/**
 * Publish a pre-built L0 segment.
 *
 * Three phases ensure readers see a coherent manifest at all times:
 *   1. Pin the current manifest under writer_mu to obtain a stable base
 *      reference (prevents the manifest pointer from being recycled while
 *      we work off-lock).
 *   2. Build the new manifest off-lock using the manifest builder; all
 *      allocations happen here.
 *   3. Under writer_mu, confirm the manifest pointer still equals our base
 *      (no concurrent compaction published in the meantime); if so, swap
 *      atomically inside a seqlock write critical section so snapshots
 *      either see the old or new manifest, never a torn intermediate.
 *
 * @return TL_OK     swap succeeded; seg and mr ownership released here.
 *         TL_EBUSY  manifest moved underneath us; seg and mr NOT released
 *                   so the caller can retry against the new base.
 *         Other     allocation/build failure; seg released here, mr retained.
 */
static tl_status_t flush_publish(tl_timelog_t* tl, tl_memrun_t* mr, tl_segment_t* seg) {
    tl_status_t st;

    /* Pin the current manifest so it cannot be freed by a racing publisher
     * while we use it as the build base. The acquired ref is released once
     * we either succeed or have decided to abort the publication attempt. */
    TL_LOCK_WRITER(tl);
    tl_manifest_t* base = tl->manifest;
    tl_manifest_acquire(base);
    TL_UNLOCK_WRITER(tl);

    /* Build the new manifest off-lock. All allocation lives here, so writers
     * remain unblocked and the eventual swap is allocation-free. */
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

    /* Compare-and-swap publication: a concurrent compaction may have moved
     * the manifest pointer while we built our delta off-lock. If so, abort
     * and let the caller rebuild against the new base. */
    TL_LOCK_WRITER(tl);

    if (tl->manifest != base) {
        TL_UNLOCK_WRITER(tl);
        tl_manifest_release(new_manifest);
        tl_manifest_release(base);
        return TL_EBUSY;
    }

    tl_seqlock_write_begin(&tl->view_seq);
    tl_manifest_t* old = tl->manifest;
    tl->manifest = new_manifest;

    /* The memrun pop happens inside the same seqlock write window as the
     * manifest swap. This is the invariant that prevents a reader from
     * counting a record twice (once in the new segment and once in the
     * still-queued memrun) or zero times (segment not yet visible, memrun
     * already popped). Both transitions are observed atomically. */
    TL_LOCK_MEMTABLE(tl);
    tl_memtable_pop_oldest(&tl->memtable, &tl->memtable_cond);
    TL_UNLOCK_MEMTABLE(tl);

    tl_seqlock_write_end(&tl->view_seq);
    TL_UNLOCK_WRITER(tl);

    tl_manifest_release(base);
    tl_manifest_release(old);
    tl_memrun_release(mr);
    tl_segment_release(seg);  /* Builder retained its own reference. */

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
 * Build an L0 segment from a single memrun and publish it.
 *
 * Ownership: on success the memrun is released here (its data is now in the
 * published segment). On failure the caller is responsible for releasing mr.
 */
static tl_status_t flush_one_memrun(tl_timelog_t* tl, tl_memrun_t* mr) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(mr != NULL);

    tl_status_t st;

    /* Generation numbers must be globally unique and monotonically increasing
     * to give the merge iterator a deterministic tie-break. Allocate under
     * writer_mu so concurrent flush/compact paths see a consistent counter. */
    TL_LOCK_WRITER(tl);
    uint32_t gen = tl->next_gen++;
    TL_UNLOCK_WRITER(tl);

    /* Acquire a snapshot to read the current tombstone set: records covered
     * by tombstones are physically dropped during flush rather than copied
     * into the new segment. */
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

    /* Segment construction runs entirely off-lock; only the final manifest
     * swap in flush_publish() re-enters writer_mu. */
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
        return st;  /* mr retained for the caller to release. */
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

    /* Bounded retry: a concurrent compaction may move the manifest while we
     * publish. Rebuild and try again, but cap the loop so a heavy writer
     * cannot starve the flusher. */
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

    /* Retries exhausted: discard the segment we built and surface EBUSY so
     * the caller (or worker loop) can rebuild against a newer manifest. */
    tl_segment_release(seg);
    if (dropped != NULL) {
        tl__free(&tl->alloc, dropped);
    }
    return TL_EBUSY;
}

/*===========================================================================
 * tl__flush_one
 *
 * Maintenance-thread entry point: pop the oldest sealed memrun, build an L0
 * segment, publish it, and feed the resulting size into the adaptive window
 * sizer so future segments can be tuned.
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
        return TL_EOF;
    }

    /* Capture the memrun's raw bounds before flushing so the adaptive sizer
     * sees pre-tombstone metrics (post-tombstone counts are not yet known). */
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

            /* The in-order run is sorted; the OOO portion carries
             * precomputed min/max so we avoid a second pass. */
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

    /* Adaptive update runs after dropping flush_mu: it acquires maint_mu,
     * which sits to the left of flush_mu in the lock order. */
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
    TL_CHECK_OPEN(tl);

    tl_status_t st;

    TL_LOCK_FLUSH(tl);

    /* Drain semantics: seal the active run if non-empty, then flush every
     * sealed memrun. Repeat until both the active run and the sealed queue
     * are empty, so on return all data is durably in segments. */
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

    /* A user-driven flush publishes L0 segments outside the worker loop, so
     * nudge the worker if that pushed a compaction trigger over threshold.
     * Runs after flush_mu is released (lock order: maint_mu -> flush_mu).
     * The worker's periodic wake-up also re-evaluates triggers now; this
     * nudge just removes up to maintenance_wakeup_ms of latency. */
    if (tl->config.maintenance_mode == TL_MAINT_BACKGROUND &&
        tl_compact_needed(tl)) {
        tl__maint_request_compact(tl);
    }
    return TL_OK;
}

/*===========================================================================
 * Maintenance Request Helpers
 *
 * Deferred signalling pattern:
 *   - Always set the pending flag under maint_mu, so the worker's predicate
 *     check is race-free against the signal.
 *   - Signal the condvar only when the worker is RUNNING; a flag set before
 *     tl_maint_start() will be picked up immediately when the worker
 *     finishes initialisation.
 *   - Must be invoked after releasing writer_mu — maint_mu sits to its left
 *     in the lock order.
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
    TL_CHECK_OPEN(tl);

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

/**
 * Construct the plan/kmerge/filter pipeline for a half-open range query.
 * The plan owns the segment and memview sources; the kmerge produces a
 * merged sorted stream; the filter elides records covered by tombstones.
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

    st = tl_kmerge_iter_init(&it->kmerge, &it->plan, alloc);
    if (st != TL_OK) {
        tl_plan_destroy(&it->plan);
        tl__free(alloc, it);
        return st;
    }

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
        /* Half-open [t1, t2) with t1 >= t2 is empty. Return a valid but
         * already-exhausted iterator so callers can use a single code path. */
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

    /* Tear down range-mode resources in reverse order of acquisition.
     * The filter iterator is a thin view over the kmerge and owns no state
     * of its own, so it has no explicit destroy. */
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

    /* The merge iterator is forward-only, so finding max requires walking
     * the entire visible set. Cheaper than maintaining a reverse iterator
     * for an infrequent operation. */
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

    /* Forward-only iteration over [TL_TS_MIN, ts): the last record yielded
     * is the predecessor of ts. */
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
 * Worker loop:
 *   1. Block on maint_cond until a pending flag is set or shutdown is
 *      requested. A timed wait acts as a safety net for any signal that
 *      raced the predicate check.
 *   2. Sample and clear the pending flags under maint_mu so a write that
 *      arrives mid-iteration is not lost (the next signal re-arms the flag).
 *   3. Perform flush and/or compaction work with maint_mu released — both
 *      acquire locks that sit to its right in the lock order.
 *
 * Lock order within the loop: maint_mu (only during wait + flag sampling)
 *  -> flush_mu (inside tl__flush_one) -> writer_mu (inside publish).
 *
 * Pending flags are plain bools guarded by maint_mu rather than atomics:
 * the mutex doubles as the predicate barrier for the condition variable,
 * eliminating the classic lost-wakeup race between set-flag and signal.
 *===========================================================================*/

/* Exponential backoff bounds for transient maintenance failures. Keeps the
 * worker from busy-spinning on persistent ENOMEM/EBUSY conditions. */
#define TL_MAINT_BACKOFF_INIT_MS   10
#define TL_MAINT_BACKOFF_MAX_MS    100

typedef enum tl_work_t {
    TL_WORK_NONE               = 0,
    TL_WORK_FLUSH              = 1u << 0,
    TL_WORK_COMPACT_EXPLICIT   = 1u << 1,
    TL_WORK_COMPACT_HEURISTIC  = 1u << 2,
    TL_WORK_RESHAPE_L0         = 1u << 3  /* Reserved for future use. */
} tl_work_t;

static void* tl__maint_worker_entry(void* arg) {
    tl_timelog_t* tl = (tl_timelog_t*)arg;
    uint32_t backoff_ms = TL_MAINT_BACKOFF_INIT_MS;

    for (;;) {
        tl_work_t work = TL_WORK_NONE;

        /* Predicate-guarded wait. The timed wait is defensive — under
         * correct signalling we'd be woken explicitly, but timing out
         * lets the worker recover from any missed wake-up. */
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

        /* Sample then clear under maint_mu so any new request set after we
         * release the lock will arm the flag again and trigger another loop. */
        if (tl->flush_pending) {
            work |= TL_WORK_FLUSH;
        }
        if (tl->compact_pending) {
            work |= TL_WORK_COMPACT_EXPLICIT;
        }

        tl->flush_pending = false;
        tl->compact_pending = false;

        TL_UNLOCK_MAINT(tl);

        /* Belt-and-braces: even if the flush flag was clear, a non-empty
         * sealed queue means there is work to do (e.g. wake-up without
         * an explicit signal). */
        TL_LOCK_MEMTABLE(tl);
        size_t sealed_len = tl_memtable_sealed_len(&tl->memtable);
        TL_UNLOCK_MEMTABLE(tl);
        if (sealed_len > 0) {
            work |= TL_WORK_FLUSH;
        }

        /* Evaluate the compaction heuristic on EVERY wake-up, not only when
         * this worker is about to flush. Triggers can change without worker
         * flush activity: a user-called tl_flush() publishes L0 segments
         * directly, and delete-debt grows from tombstone insertion alone
         * (delete-heavy retention workloads with no new writes). The check
         * is cheap (manifest counters + cursor sweep) and runs at most once
         * per maintenance_wakeup_ms when idle. Previously this was gated on
         * pending flush work, which let user-flushed L0 grow unboundedly and
         * left delete_debt_threshold inert on idle instances (v1.3 usability
         * lab findings). */
        if (!(work & TL_WORK_COMPACT_EXPLICIT)) {
            if (tl_compact_needed(tl)) {
                work |= TL_WORK_COMPACT_HEURISTIC;
            }
        }

        /* Drain flushes but break out as soon as compaction becomes due.
         * This keeps L0 from growing unboundedly when ingest is heavy: we
         * interleave flush and compaction rather than starving compaction. */
        if (work & TL_WORK_FLUSH) {
            tl_status_t st;
            while ((st = tl__flush_one(tl)) == TL_OK) {
                if (tl_compact_needed(tl)) {
                    work |= TL_WORK_COMPACT_HEURISTIC;
                    break;
                }
            }

            /* Transient failure (allocator pressure, manifest contention):
             * sleep with exponential backoff so we don't peg a CPU core. */
            if (st == TL_ENOMEM || st == TL_EBUSY || st == TL_EINTERNAL) {
                tl_sleep_ms(backoff_ms);
                backoff_ms = (backoff_ms * 2 > TL_MAINT_BACKOFF_MAX_MS)
                           ? TL_MAINT_BACKOFF_MAX_MS : backoff_ms * 2;

                {
                    tl_log_ctx_t* log = &tl->log;
                    TL_LOG_WARN("Flush failed (%s), retrying after %u ms backoff",
                                tl_strerror(st), backoff_ms);
                    (void)log;
                }
            } else {
                backoff_ms = TL_MAINT_BACKOFF_INIT_MS;
            }

            /* Anything other than TL_EOF means we stopped early (compaction
             * cut-in, or transient error); ensure the worker will revisit
             * the flush queue on the next iteration. */
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

        if (work & (TL_WORK_COMPACT_EXPLICIT | TL_WORK_COMPACT_HEURISTIC)) {
            tl_status_t st = tl_compact_one(tl, TL_COMPACT_MAX_RETRIES);

            if (st == TL_ENOMEM || st == TL_EBUSY || st == TL_EINTERNAL) {
                tl_sleep_ms(backoff_ms);
                backoff_ms = (backoff_ms * 2 > TL_MAINT_BACKOFF_MAX_MS)
                           ? TL_MAINT_BACKOFF_MAX_MS : backoff_ms * 2;

                {
                    tl_log_ctx_t* log = &tl->log;
                    TL_LOG_WARN("Compaction failed (%s), retrying after %u ms backoff",
                                tl_strerror(st), backoff_ms);
                    (void)log;
                }

                TL_LOCK_MAINT(tl);
                tl->compact_pending = true;
                TL_UNLOCK_MAINT(tl);
            } else if (st == TL_EOVERFLOW) {
                /* Window span exceeds tl_ts_t range — not retryable.
                 * Reset the backoff and let any pending request stay clear. */
                tl_log_ctx_t* log = &tl->log;
                TL_LOG_ERROR("Compaction failed: window span overflow (TL_EOVERFLOW)");
                (void)log;
                backoff_ms = TL_MAINT_BACKOFF_INIT_MS;
            } else if (st == TL_OK) {
                backoff_ms = TL_MAINT_BACKOFF_INIT_MS;
            }
        }
    }

    return NULL;
}

/*===========================================================================
 * tl_maint_start
 *
 * Transition the worker from STOPPED to RUNNING. Idempotent when already
 * RUNNING; rejected with EBUSY while a previous stop is still in flight to
 * avoid spawning a second worker on top of the joining one.
 *===========================================================================*/

tl_status_t tl_maint_start(tl_timelog_t* tl) {
    TL_CHECK_OPEN(tl);
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

    /* If any writer queued work before the worker was started, deliver the
     * wake-up now so we don't sleep on a non-empty work set. */
    if (tl->flush_pending || tl->compact_pending) {
        tl_cond_signal(&tl->maint_cond);
    }

    TL_UNLOCK_MAINT(tl);
    return TL_OK;
}

/*===========================================================================
 * tl_maint_stop
 *
 * Transition the worker through RUNNING -> STOPPING -> STOPPED. The join
 * itself happens after releasing maint_mu, because the worker may briefly
 * acquire locks that sit to the right of maint_mu in the lock order, and
 * blocking on join while holding maint_mu would deadlock.
 *
 * The maintenance-mode check is intentionally omitted so tl_close() can
 * call this unconditionally without first inspecting the configuration.
 *===========================================================================*/

tl_status_t tl_maint_stop(tl_timelog_t* tl) {
    if (tl == NULL) {
        return TL_EINVAL;
    }

    TL_LOCK_MAINT(tl);

    switch (tl->maint_state) {
        case TL_WORKER_STOPPED:
            TL_UNLOCK_MAINT(tl);
            return TL_OK;
        case TL_WORKER_STOPPING:
            TL_UNLOCK_MAINT(tl);
            return TL_EBUSY;  /* Another thread is joining; TL_OK means quiesced. */
        case TL_WORKER_RUNNING:
            break;
    }

    tl->maint_state = TL_WORKER_STOPPING;
    tl->maint_shutdown = true;
    tl_cond_signal(&tl->maint_cond);
    TL_UNLOCK_MAINT(tl);

    /* Join the worker thread itself — must reference the struct member, not
     * a copy, since pthread_join consumes the handle in place. */
    tl_status_t st = tl_thread_join(&tl->maint_thread, NULL);

    TL_LOCK_MAINT(tl);
    if (st == TL_OK) {
        tl->maint_state = TL_WORKER_STOPPED;
        tl->maint_shutdown = false;
    }
    /* On join failure leave state == STOPPING and shutdown == true so the
     * worker is not erroneously considered restartable. */
    TL_UNLOCK_MAINT(tl);

    return (st == TL_OK) ? TL_OK : TL_EINTERNAL;
}

/*===========================================================================
 * tl_maint_step
 *
 * Manual-mode entry point: perform exactly one unit of maintenance work
 * (flush a sealed memrun if any is pending, otherwise advance compaction
 * by one step). Returns TL_EOF when no work is currently due.
 *===========================================================================*/

tl_status_t tl_maint_step(tl_timelog_t* tl) {
    TL_CHECK_OPEN(tl);
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

    /* A user-issued tl_compact() sets compact_pending; otherwise fall back
     * to the heuristic that asks whether compaction is structurally due. */
    bool was_explicit = false;
    TL_LOCK_MAINT(tl);
    if (tl->compact_pending) {
        was_explicit = true;
    }
    TL_UNLOCK_MAINT(tl);

    bool do_compact = was_explicit || tl_compact_needed(tl);

    if (do_compact) {
        tl_status_t st = tl_compact_one(tl, TL_COMPACT_MAX_RETRIES);

        /* For explicit requests, consume the flag on success, on no-work, or
         * on non-retryable failure. On transient errors we leave it armed so
         * the next tl_maint_step() will pick the request up again. */
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

    return TL_EOF;
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

    /* Count pages and tombstone-visible records without scanning rows:
     * each segment carries enough metadata for an O(pages + tombstones)
     * estimate, which is good enough for diagnostic stats. */
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

    for (uint32_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);
        total_pages += seg->page_count;
        immutable_visible_records += tl__visible_records_in_segment(seg,
                                                                    skyline_data,
                                                                    skyline_len);
    }

    for (uint32_t i = 0; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);
        total_pages += seg->page_count;
        immutable_visible_records += tl__visible_records_in_segment(seg,
                                                                    skyline_data,
                                                                    skyline_len);
    }

    out->pages_total = total_pages;

    uint64_t total_records = immutable_visible_records;

    /* The active and OOO buffers are mutable, so we must filter record by
     * record against the live tombstone skyline. */
    total_records += tl__count_active_visible_range(memview, skyline_imm,
                                                     TL_TS_MIN, 0, true);

    /* Sealed memruns are immutable; the watermark-aware counter can short
     * circuit using their precomputed page bounds. */
    for (size_t i = 0; i < tl_memview_sealed_len(memview); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(memview, i);
        total_records += tl__visible_records_in_memrun(mr,
                                                        skyline_data,
                                                        skyline_len);
    }

    out->records_estimate = total_records;
    tl_intervals_destroy(&skyline);

    /* Reports the raw, pre-tombstone min/max stored on the snapshot. For
     * the bounds of currently-visible records call tl_min_ts/tl_max_ts. */
    if (tl_snapshot_has_data(snap)) {
        out->min_ts = tl_snapshot_min_ts(snap);
        out->max_ts = tl_snapshot_max_ts(snap);
    } else {
        out->min_ts = TL_TS_MAX;
        out->max_ts = TL_TS_MIN;
    }

    /* Aggregate raw tombstone counts from every component. Not deduplicated
     * across components: overlapping intervals are still counted separately. */
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

    /* Memtable metrics reflect the snapshot's frozen view, not the live
     * memtable, so they remain consistent for the snapshot's lifetime. */
    out->memtable_active_records = (uint64_t)tl_memview_run_len(memview);
    out->memtable_ooo_records = (uint64_t)tl_memview_ooo_total_len(memview);
    out->memtable_sealed_runs = (uint64_t)tl_memview_sealed_len(memview);

    /* Operational counters are monotonically increasing; relaxed loads are
     * sufficient because we never read a derived quantity that requires
     * cross-counter consistency. The cast drops const to satisfy the lock
     * macros, but we only read atomic counters with no state mutation. */
    tl_timelog_t* tl = (tl_timelog_t*)snap->parent;
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

        /* Adaptive metrics live behind maint_mu; when adaptive sizing is
         * disabled the fields are left at zero. */
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
    return TL_OK;
#else
    /* Debug builds validate from the leaves up: each component checks its
     * own invariants, then we verify cross-component bounds at the top. */
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

/* Manifest publication keeps writer_mu acquisition and seqlock entry as
 * separate steps rather than a combined helper: validation that the base
 * manifest is still current must happen between acquiring writer_mu and
 * opening the seqlock window, and bailing out cleanly across both is
 * easier with explicit calls. */
