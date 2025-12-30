#include "../include/timelog/timelog.h"
#include "../src/internal/tl_defs.h"
#include "../src/internal/tl_status.h"
#include "../src/internal/tl_config.h"
#include "../src/internal/tl_alloc.h"
#include "../src/internal/tl_log.h"
#include "../src/internal/tl_atomic.h"
#include "../src/internal/tl_thread.h"
#include "../src/internal/tl_memtable.h"
#include "../src/internal/tl_manifest.h"
#include "../src/internal/tl_flush.h"
#include "../src/internal/tl_snapshot.h"
#include "../src/internal/tl_plan.h"
#include "../src/internal/tl_merge.h"
#include "../src/internal/tl_filter.h"
#include "../src/internal/tl_iter.h"

#include <string.h>

/*
 * Forward declarations for compaction (defined later in file).
 */
static bool compaction_needed(tl_timelog_t* tl);
static tl_status_t compact_one_step(tl_timelog_t* tl);

/*
 * Public iterator structure.
 *
 * Wraps the internal query components:
 * - Query plan (owns component iterators)
 * - Merge iterator (k-way merge)
 * - Filtered iterator (tombstone filtering)
 */
struct tl_iter {
    const tl_allocator_t*  alloc;
    const tl_snapshot_t*   snap;        /* Not owned */
    tl_qplan_t*            plan;        /* Owned */
    tl_merge_iter_t*       merge;       /* Owned */
    tl_filtered_iter_t*    filtered;    /* Owned */
};

/*
 * Internal timelog structure.
 */
struct tl_timelog {
    /* Configuration (copied at open) */
    tl_config_t     cfg;

    /* Logger (derived from config) */
    tl_logger_t     logger;

    /* Publication protocol */
    tl_atomic_u64_t view_seq;         /* Seqlock for snapshot consistency */

    /* Current manifest (protected by writer_mu) */
    tl_manifest_t*  manifest_current;

    /* Delta layer */
    tl_memtable_t*  memtable;

    /* Generation counter for segments */
    tl_atomic_u32_t next_generation;

    /* Writer coordination */
    tl_mutex_t      writer_mu;        /* Serializes write operations */

    /* Flush serialization (protects flush_one_and_publish build+publish) */
    tl_mutex_t      flush_mu;

    /* State flags */
    bool            is_open;

    /*
     * Maintenance subsystem
     *
     * Lock ordering: maint_mu -> flush_mu -> writer_mu (never reverse)
     * memtable->mu is internal and may be taken while holding writer_mu.
     */
    tl_mutex_t      maint_mu;         /* Protects maintenance state */
    tl_cond_t       maint_cond;       /* Signal to wake worker */
    bool            maint_running;    /* Is background thread active? */
    bool            maint_shutdown;   /* Shutdown requested? */
    tl_thread_t     maint_thread;     /* Background worker handle */

    /* Work pending flags (protected by maint_mu) */
    bool            flush_pending;    /* Sealed memruns need flushing */
    bool            compact_pending;  /* Compaction requested */
};

/*===========================================================================
 * Publication Protocol Helpers
 *===========================================================================*/

/*
 * Publication protocol helpers.
 *
 * The view_seq counter uses even/odd protocol:
 * - Even: stable state, snapshots can acquire
 * - Odd: update in progress, snapshots must retry
 */

/**
 * Begin a publication-critical update.
 * Makes view_seq odd to signal readers to wait/retry.
 */
static void publication_begin(tl_timelog_t* tl) {
    tl_atomic_u64_fetch_add(&tl->view_seq, 1);  /* Now odd */
    tl_atomic_thread_fence_release();
}

/**
 * End a publication-critical update.
 * Makes view_seq even to signal stable state.
 */
static void publication_end(tl_timelog_t* tl) {
    tl_atomic_thread_fence_release();
    tl_atomic_u64_fetch_add(&tl->view_seq, 1);  /* Now even */
}

/*===========================================================================
 * Internal Accessor Functions (for snapshot.c)
 *===========================================================================*/

/**
 * Load view_seq atomically.
 */
uint64_t tl_timelog_view_seq_load(const tl_timelog_t* tl) {
    tl_atomic_thread_fence_acquire();
    return tl_atomic_u64_load(&((tl_timelog_t*)tl)->view_seq);
}

/**
 * Acquire manifest reference (increments refcount).
 * Caller must hold writer_mu.
 */
tl_manifest_t* tl_timelog_manifest_acquire(tl_timelog_t* tl) {
    tl_manifest_t* m = tl->manifest_current;
    if (m != NULL) {
        tl_manifest_acquire(m);
    }
    return m;
}

/**
 * Capture memview snapshot.
 * Caller must hold writer_mu.
 */
tl_status_t tl_timelog_memview_capture(tl_timelog_t* tl, tl_memview_t** out) {
    return tl_memtable_snapshot(tl->memtable, out);
}

/**
 * Get allocator.
 */
const tl_allocator_t* tl_timelog_allocator(const tl_timelog_t* tl) {
    return &tl->cfg.allocator;
}

/**
 * Lock/unlock writer mutex (used by snapshot acquisition).
 */
void tl_timelog_writer_lock(tl_timelog_t* tl) {
    tl_mutex_lock(&tl->writer_mu);
}

void tl_timelog_writer_unlock(tl_timelog_t* tl) {
    tl_mutex_unlock(&tl->writer_mu);
}

/*===========================================================================
 * Flush and Publish
 *===========================================================================*/

/**
 * Flush one memrun and publish to manifest.
 *
 * This is the core publication transaction:
 * 1. Build segment from oldest sealed memrun
 * 2. Begin publication (view_seq odd)
 * 3. Build new manifest with segment
 * 4. Publish manifest (atomic swap)
 * 5. Remove memrun from sealed queue
 * 6. End publication (view_seq even)
 *
 * @return TL_OK on success, TL_EOF if no memruns to flush
 */
static tl_status_t flush_one_and_publish(tl_timelog_t* tl) {
    tl_status_t st;

    /* Serialize flush operations to avoid double-flush of the same memrun */
    tl_mutex_lock(&tl->flush_mu);

    /* Get oldest sealed memrun */
    tl_memrun_t* mr = tl_memtable_peek_oldest_sealed(tl->memtable);
    if (mr == NULL) {
        tl_mutex_unlock(&tl->flush_mu);
        return TL_EOF;
    }

    /* Build segment from memrun (expensive, outside publication lock) */
    tl_segment_t* seg = NULL;
    uint32_t gen = tl_atomic_u32_fetch_add(&tl->next_generation, 1);
    st = tl_flush_memrun(&tl->cfg.allocator, mr,
                         tl->cfg.target_page_bytes,
                         gen,
                         &seg);
    if (st != TL_OK && st != TL_EOF) {
        tl_mutex_unlock(&tl->flush_mu);
        return st;
    }

    /* Handle tombstone-only or empty memrun */
    if (seg == NULL && st == TL_EOF) {
        /* Empty memrun: just remove from queue */
        tl_memrun_t* removed = tl_memtable_pop_oldest_sealed(tl->memtable);
        if (removed != NULL) {
            tl_memrun_release(removed);
        }
        tl_mutex_unlock(&tl->flush_mu);
        return TL_OK;
    }

    /*
     * Publication transaction (short critical section).
     * writer_mu ensures no concurrent snapshot capture or other publication.
     */
    tl_mutex_lock(&tl->writer_mu);

    /* Begin: view_seq becomes odd */
    publication_begin(tl);

    /* Build new manifest */
    tl_manifest_t* old_manifest = tl->manifest_current;
    tl_manifest_t* new_manifest = NULL;

    st = tl_manifest_build(&tl->cfg.allocator, old_manifest,
                           seg,      /* add_delta */
                           NULL,     /* add_main */
                           NULL, 0,  /* remove_delta */
                           NULL, 0,  /* remove_main */
                           &new_manifest);

    if (st != TL_OK) {
        publication_end(tl);
        tl_mutex_unlock(&tl->writer_mu);
        tl_segment_release(seg);
        tl_mutex_unlock(&tl->flush_mu);
        return st;
    }

    /* Manifest swap (serialized by writer_mu) */
    tl->manifest_current = new_manifest;

    /* Remove memrun from sealed queue (marks as published) */
    tl_memrun_t* removed = tl_memtable_pop_oldest_sealed(tl->memtable);

    /* End: view_seq becomes even */
    publication_end(tl);

    tl_mutex_unlock(&tl->writer_mu);

    /* Release old manifest (may still be pinned by snapshots) */
    if (old_manifest != NULL) {
        tl_manifest_release(old_manifest);
    }

    /* Release segment reference (manifest now owns it) */
    tl_segment_release(seg);

    /* Release removed memrun (may still be pinned by snapshots) */
    if (removed != NULL) {
        tl_memrun_release(removed);
    }

    tl_mutex_unlock(&tl->flush_mu);
    return TL_OK;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_open(const tl_config_t* cfg, tl_timelog_t** out) {
    if (out == NULL) {
        return TL_EINVAL;
    }
    *out = NULL;

    /* Use provided config or defaults */
    tl_config_t local_cfg;
    if (cfg == NULL) {
        tl_config_init_defaults(&local_cfg);
        cfg = &local_cfg;
    }

    /* Validate configuration */
    tl_status_t st = tl_config_validate(cfg);
    if (st != TL_OK) {
        return st;
    }

    /* Allocate instance */
    tl_timelog_t* tl = tl__calloc(&cfg->allocator, 1, sizeof(tl_timelog_t));
    if (tl == NULL) {
        return TL_ENOMEM;
    }

    /* Copy configuration */
    memcpy(&tl->cfg, cfg, sizeof(tl_config_t));

    /* Initialize logger (disabled for now) */
    tl_logger_init_noop(&tl->logger);
    (void)cfg->log_fn;
    (void)cfg->log_ctx;

    /* Initialize atomics */
    tl_atomic_u64_store(&tl->view_seq, 0);

    /* Initialize mutex */
    if (tl_mutex_init(&tl->writer_mu) != 0) {
        tl__free(&cfg->allocator, tl);
        return TL_EINTERNAL;
    }

    /* Initialize flush mutex */
    if (tl_mutex_init(&tl->flush_mu) != 0) {
        tl_mutex_destroy(&tl->writer_mu);
        tl__free(&cfg->allocator, tl);
        return TL_EINTERNAL;
    }

    /* Create empty manifest
     * NOTE: Use &tl->cfg.allocator (the copy) since cfg may point to
     * a stack-local config that will be deallocated after tl_open returns.
     */
    st = tl_manifest_create_empty(&tl->cfg.allocator, 0, &tl->manifest_current);
    if (st != TL_OK) {
        tl_mutex_destroy(&tl->flush_mu);
        tl_mutex_destroy(&tl->writer_mu);
        tl__free(&tl->cfg.allocator, tl);
        return st;
    }

    /* Create memtable
     * NOTE: Same as above - use &tl->cfg.allocator.
     */
    st = tl_memtable_create(&tl->cfg.allocator,
                            tl->cfg.memtable_max_bytes,
                            tl->cfg.target_page_bytes,
                            &tl->memtable);
    if (st != TL_OK) {
        tl_manifest_release(tl->manifest_current);
        tl_mutex_destroy(&tl->flush_mu);
        tl_mutex_destroy(&tl->writer_mu);
        tl__free(&tl->cfg.allocator, tl);
        return st;
    }

    /* Initialize maintenance subsystem */
    if (tl_mutex_init(&tl->maint_mu) != 0) {
        tl_memtable_destroy(tl->memtable);
        tl_manifest_release(tl->manifest_current);
        tl_mutex_destroy(&tl->flush_mu);
        tl_mutex_destroy(&tl->writer_mu);
        tl__free(&tl->cfg.allocator, tl);
        return TL_EINTERNAL;
    }

    if (tl_cond_init(&tl->maint_cond) != 0) {
        tl_mutex_destroy(&tl->maint_mu);
        tl_memtable_destroy(tl->memtable);
        tl_manifest_release(tl->manifest_current);
        tl_mutex_destroy(&tl->flush_mu);
        tl_mutex_destroy(&tl->writer_mu);
        tl__free(&tl->cfg.allocator, tl);
        return TL_EINTERNAL;
    }

    tl->maint_running = false;
    tl->maint_shutdown = false;
    tl->flush_pending = false;
    tl->compact_pending = false;

    tl_atomic_u32_store(&tl->next_generation, 1);
    tl->is_open = true;

    TL_LOG_INFO(&tl->logger, "timelog opened (time_unit=%d, page_bytes=%zu)",
                (int)cfg->time_unit, cfg->target_page_bytes);

    *out = tl;
    return TL_OK;
}

void tl_close(tl_timelog_t* tl) {
    if (tl == NULL) {
        return;
    }

    TL_LOG_INFO(&tl->logger, "timelog closing");

    /*
     * CRITICAL: Stop background maintenance FIRST.
     * This ensures the worker thread is not accessing any resources
     * when we start destroying them.
     */
    tl_maint_stop(tl);

    /* Mark as closed to catch use-after-close in debug */
    tl->is_open = false;

    /* Destroy maintenance primitives */
    tl_cond_destroy(&tl->maint_cond);
    tl_mutex_destroy(&tl->maint_mu);

    /* Destroy memtable */
    if (tl->memtable != NULL) {
        tl_memtable_destroy(tl->memtable);
    }

    /* Release manifest */
    if (tl->manifest_current != NULL) {
        tl_manifest_release(tl->manifest_current);
    }

    /* Destroy mutex */
    tl_mutex_destroy(&tl->flush_mu);
    tl_mutex_destroy(&tl->writer_mu);

    /* Free instance using its own allocator */
    tl_allocator_t alloc = tl->cfg.allocator;
    tl__free(&alloc, tl);
}

/*===========================================================================
 * Write API
 *===========================================================================*/

/**
 * Signal the maintenance thread that there's work to do.
 *
 * IMPORTANT: This must be called AFTER releasing writer_mu to respect
 * the lock ordering (maint_mu -> flush_mu -> writer_mu, never reverse).
 */
static void signal_maintenance_flush(tl_timelog_t* tl) {
    tl_mutex_lock(&tl->maint_mu);
    tl->flush_pending = true;
    tl_cond_signal(&tl->maint_cond);
    tl_mutex_unlock(&tl->maint_mu);
}

tl_status_t tl_append(tl_timelog_t* tl, tl_ts_t ts, tl_handle_t handle) {
    if (tl == NULL || !tl->is_open) return TL_EINVAL;

    bool sealed = false;

    tl_mutex_lock(&tl->writer_mu);

    tl_status_t st = tl_memtable_insert(tl->memtable, ts, handle);
    if (st != TL_OK) {
        tl_mutex_unlock(&tl->writer_mu);
        return st;
    }

    /* Check if sealing is needed */
    if (tl_memtable_should_seal(tl->memtable)) {
        if (!tl_memtable_can_seal(tl->memtable)) {
            tl_mutex_unlock(&tl->writer_mu);
            return TL_EBUSY;  /* Backpressure: caller should flush */
        }

        st = tl_memtable_seal_active(tl->memtable);
        if (st != TL_OK && st != TL_EOF) {
            tl_mutex_unlock(&tl->writer_mu);
            return st;
        }
        sealed = (st == TL_OK);  /* TL_EOF means empty seal */
    }

    tl_mutex_unlock(&tl->writer_mu);

    /* Signal maintenance thread if we sealed (outside writer_mu) */
    if (sealed) {
        signal_maintenance_flush(tl);
    }

    return TL_OK;
}

tl_status_t tl_append_batch(tl_timelog_t* tl, const tl_record_t* records,
                            size_t n, uint32_t flags) {
    if (tl == NULL || !tl->is_open) return TL_EINVAL;
    if (n == 0) return TL_OK;
    if (records == NULL) return TL_EINVAL;

    bool sealed = false;

    tl_mutex_lock(&tl->writer_mu);

    tl_status_t st = tl_memtable_insert_batch(tl->memtable, records, n, flags);
    if (st != TL_OK) {
        tl_mutex_unlock(&tl->writer_mu);
        return st;
    }

    /* Check sealing */
    if (tl_memtable_should_seal(tl->memtable)) {
        if (!tl_memtable_can_seal(tl->memtable)) {
            tl_mutex_unlock(&tl->writer_mu);
            return TL_EBUSY;
        }

        st = tl_memtable_seal_active(tl->memtable);
        if (st != TL_OK && st != TL_EOF) {
            tl_mutex_unlock(&tl->writer_mu);
            return st;
        }
        sealed = (st == TL_OK);
    }

    tl_mutex_unlock(&tl->writer_mu);

    /* Signal maintenance thread if we sealed (outside writer_mu) */
    if (sealed) {
        signal_maintenance_flush(tl);
    }

    return TL_OK;
}

tl_status_t tl_delete_range(tl_timelog_t* tl, tl_ts_t t1, tl_ts_t t2) {
    if (tl == NULL || !tl->is_open) return TL_EINVAL;
    if (t2 < t1) return TL_EINVAL;
    if (t1 == t2) return TL_OK;  /* Empty range */

    bool sealed = false;

    tl_mutex_lock(&tl->writer_mu);

    tl_status_t st = tl_memtable_add_tombstone(tl->memtable, t1, t2);
    if (st != TL_OK) {
        tl_mutex_unlock(&tl->writer_mu);
        return st;
    }

    /* Check sealing */
    if (tl_memtable_should_seal(tl->memtable)) {
        if (!tl_memtable_can_seal(tl->memtable)) {
            tl_mutex_unlock(&tl->writer_mu);
            return TL_EBUSY;
        }

        st = tl_memtable_seal_active(tl->memtable);
        if (st == TL_OK) {
            sealed = true;
        }
        /* Ignore TL_EOF (empty seal is fine) */
    }

    tl_mutex_unlock(&tl->writer_mu);

    /* Signal maintenance thread if we sealed (outside writer_mu) */
    if (sealed) {
        signal_maintenance_flush(tl);
    }

    return TL_OK;
}

tl_status_t tl_delete_before(tl_timelog_t* tl, tl_ts_t cutoff) {
    if (tl == NULL || !tl->is_open) return TL_EINVAL;

    /* delete_before(cutoff) is delete_range(TL_TS_MIN, cutoff) */
    return tl_delete_range(tl, TL_TS_MIN, cutoff);
}

tl_status_t tl_flush(tl_timelog_t* tl) {
    if (tl == NULL || !tl->is_open) return TL_EINVAL;

    /* First seal active if non-empty */
    tl_mutex_lock(&tl->writer_mu);
    tl_status_t st = tl_memtable_seal_active(tl->memtable);
    tl_mutex_unlock(&tl->writer_mu);

    /* Ignore TL_EOF (empty seal) */
    if (st != TL_OK && st != TL_EOF) {
        return st;
    }

    /* Flush all sealed memruns */
    while (true) {
        st = flush_one_and_publish(tl);
        if (st == TL_EOF) break;  /* No more sealed memruns */
        if (st != TL_OK) return st;
    }

    return TL_OK;
}

tl_status_t tl_compact(tl_timelog_t* tl) {
    if (tl == NULL || !tl->is_open) return TL_EINVAL;

    /*
     * Request compaction.
     *
     * If background maintenance is running, signal it to perform compaction.
     * Otherwise, perform compaction synchronously.
     */
    tl_mutex_lock(&tl->maint_mu);
    bool bg_running = tl->maint_running;
    if (bg_running) {
        tl->compact_pending = true;
        tl_cond_signal(&tl->maint_cond);
    }
    tl_mutex_unlock(&tl->maint_mu);

    if (bg_running) {
        /* Background thread will handle it */
        return TL_OK;
    }

    /* Perform compaction synchronously */
    if (!compaction_needed(tl)) {
        return TL_EOF;  /* Nothing to compact */
    }

    tl_status_t st = compact_one_step(tl);
    if (st == TL_EBUSY) {
        /* Manifest changed during build, retry once */
        st = compact_one_step(tl);
    }

    return st;
}

/*===========================================================================
 * Snapshot API
 *===========================================================================*/

tl_status_t tl_snapshot_acquire(const tl_timelog_t* tl, tl_snapshot_t** out) {
    if (tl == NULL || out == NULL) return TL_EINVAL;
    if (!tl->is_open) return TL_ESTATE;

    /* Cast away const for internal access (writer_mu protects capture) */
    return tl_snapshot_acquire_internal((struct tl_timelog*)tl, out);
}

void tl_snapshot_release(tl_snapshot_t* s) {
    tl_snapshot_release_internal(s);
}

/*===========================================================================
 * Read API - Iterator Creation
 *===========================================================================*/

/*
 * Internal helper: create iterator for range [t1, t2).
 */
static tl_status_t iter_create_range(const tl_snapshot_t* snap,
                                      tl_ts_t t1,
                                      tl_ts_t t2,
                                      tl_iter_t** out) {
    if (snap == NULL || out == NULL) return TL_EINVAL;
    *out = NULL;

    if (t2 < t1) return TL_EINVAL;

    const tl_allocator_t* alloc = snap->alloc;

    /* Allocate iterator */
    tl_iter_t* it = tl__calloc(alloc, 1, sizeof(tl_iter_t));
    if (it == NULL) return TL_ENOMEM;

    it->alloc = alloc;
    it->snap = snap;

    tl_status_t st;

    /* Build query plan */
    st = tl_qplan_build(alloc, snap, t1, t2, &it->plan);
    if (st != TL_OK) {
        tl__free(alloc, it);
        return st;
    }

    /* Create merge iterator */
    st = tl_merge_iter_create(alloc, it->plan, &it->merge);
    if (st != TL_OK) {
        tl_qplan_destroy(it->plan);
        tl__free(alloc, it);
        return st;
    }

    /* Create filtered iterator (with tombstones from plan) */
    st = tl_filtered_iter_create(alloc, it->merge, it->plan->eff_tombs, &it->filtered);
    if (st != TL_OK) {
        tl_merge_iter_destroy(it->merge);
        tl_qplan_destroy(it->plan);
        tl__free(alloc, it);
        return st;
    }

    *out = it;
    return TL_OK;
}

tl_status_t tl_iter_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                          tl_iter_t** out) {
    return iter_create_range(snap, t1, t2, out);
}

tl_status_t tl_iter_since(const tl_snapshot_t* snap, tl_ts_t t1,
                          tl_iter_t** out) {
    /* since(t1) = range(t1, TL_TS_MAX) */
    return iter_create_range(snap, t1, TL_TS_MAX, out);
}

tl_status_t tl_iter_until(const tl_snapshot_t* snap, tl_ts_t t2,
                          tl_iter_t** out) {
    /* until(t2) = range(TL_TS_MIN, t2) */
    return iter_create_range(snap, TL_TS_MIN, t2, out);
}

tl_status_t tl_iter_equal(const tl_snapshot_t* snap, tl_ts_t ts,
                          tl_iter_t** out) {
    /* equal(ts) = range(ts, ts+1) */
    if (ts == TL_TS_MAX) {
        /* Edge case: ts+1 would overflow */
        return iter_create_range(snap, ts, ts, out);
    }
    return iter_create_range(snap, ts, ts + 1, out);
}

/*===========================================================================
 * Read API - Iterator Operations
 *===========================================================================*/

tl_status_t tl_iter_next(tl_iter_t* it, tl_record_t* out) {
    if (it == NULL) return TL_EINVAL;

    /* Check if exhausted */
    if (tl_filtered_iter_state(it->filtered) != TL_ITER_READY) {
        return TL_EOF;
    }

    /* Get current record */
    const tl_record_t* rec = tl_filtered_iter_peek(it->filtered);
    if (rec == NULL) {
        return TL_EOF;
    }

    /* Copy to output if provided */
    if (out != NULL) {
        *out = *rec;
    }

    /* Advance to next */
    tl_filtered_iter_advance(it->filtered);

    return TL_OK;
}

void tl_iter_destroy(tl_iter_t* it) {
    if (it == NULL) return;

    const tl_allocator_t* alloc = it->alloc;

    /* Destroy in reverse order of creation */
    if (it->filtered != NULL) {
        tl_filtered_iter_destroy(it->filtered);
    }
    if (it->merge != NULL) {
        tl_merge_iter_destroy(it->merge);
    }
    if (it->plan != NULL) {
        tl_qplan_destroy(it->plan);
    }

    tl__free(alloc, it);
}

/*===========================================================================
 * Scan API
 *===========================================================================*/

tl_status_t tl_scan_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                          tl_scan_fn fn, void* ctx) {
    if (snap == NULL || fn == NULL) return TL_EINVAL;

    /* Create iterator for range */
    tl_iter_t* it = NULL;
    tl_status_t st = iter_create_range(snap, t1, t2, &it);
    if (st != TL_OK) {
        return st;
    }

    /* Iterate and call visitor */
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        tl_scan_decision_t decision = fn(ctx, &rec);
        if (decision == TL_SCAN_STOP) {
            break;
        }
    }

    tl_iter_destroy(it);
    return TL_OK;
}

/*===========================================================================
 * Timestamp Navigation
 *===========================================================================*/

tl_status_t tl_min_ts(const tl_snapshot_t* snap, tl_ts_t* out) {
    if (snap == NULL || out == NULL) return TL_EINVAL;

    if (!snap->has_bounds) {
        return TL_EOF;  /* Empty snapshot */
    }

    *out = snap->min_ts;
    return TL_OK;
}

tl_status_t tl_max_ts(const tl_snapshot_t* snap, tl_ts_t* out) {
    if (snap == NULL || out == NULL) return TL_EINVAL;

    if (!snap->has_bounds) {
        return TL_EOF;  /* Empty snapshot */
    }

    *out = snap->max_ts;
    return TL_OK;
}

tl_status_t tl_next_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out) {
    if (snap == NULL || out == NULL) return TL_EINVAL;

    /*
     * Find the first timestamp > ts.
     * Strategy: use iter_since(ts+1) and peek first record.
     */
    if (ts == TL_TS_MAX) {
        return TL_EOF;  /* No timestamp after MAX */
    }

    tl_iter_t* it = NULL;
    tl_status_t st = iter_create_range(snap, ts + 1, TL_TS_MAX, &it);
    if (st != TL_OK) {
        return st;
    }

    /* Check if there's a record */
    if (tl_filtered_iter_state(it->filtered) != TL_ITER_READY) {
        tl_iter_destroy(it);
        return TL_EOF;
    }

    const tl_record_t* rec = tl_filtered_iter_peek(it->filtered);
    if (rec == NULL) {
        tl_iter_destroy(it);
        return TL_EOF;
    }

    *out = rec->ts;
    tl_iter_destroy(it);
    return TL_OK;
}

tl_status_t tl_prev_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out) {
    if (snap == NULL || out == NULL) return TL_EINVAL;

    /*
     * Find the last timestamp < ts.
     * Strategy: iterate range [min_ts, ts) and track the last seen timestamp.
     *
     * This is O(n) but correct. For O(log n), we'd need a reverse iterator
     * or segment-level max tracking. This is acceptable for V1.
     */
    if (!snap->has_bounds || ts <= snap->min_ts) {
        return TL_EOF;  /* No timestamp before ts */
    }

    tl_iter_t* it = NULL;
    tl_status_t st = iter_create_range(snap, snap->min_ts, ts, &it);
    if (st != TL_OK) {
        return st;
    }

    tl_ts_t last_ts = TL_TS_MIN;
    bool found = false;

    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        if (rec.ts < ts) {
            last_ts = rec.ts;
            found = true;
        }
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
 *===========================================================================*/

/**
 * Background maintenance worker thread function.
 *
 * This thread:
 * - Waits for work signals (flush_pending, compact_pending)
 * - Performs maintenance work outside the main path
 * - Respects shutdown requests for clean termination
 *
 * Thread safety:
 * - Uses maint_mu to protect state access
 * - Uses flush_mu to serialize flush build+publish
 * - Uses writer_mu only during publication (short critical section)
 * - Never holds maint_mu while doing actual work
 */
static void* maint_worker_fn(void* arg) {
    tl_timelog_t* tl = (tl_timelog_t*)arg;

    tl_mutex_lock(&tl->maint_mu);

    while (!tl->maint_shutdown) {
        /*
         * Wait for work signal or shutdown.
         * Use timed wait with 100ms timeout to periodically check shutdown
         * even if no signal is received (defensive against missed signals).
         */
        while (!tl->maint_shutdown &&
               !tl->flush_pending &&
               !tl->compact_pending) {
            tl_cond_timedwait(&tl->maint_cond, &tl->maint_mu, 100);
        }

        if (tl->maint_shutdown) {
            break;
        }

        /* Capture pending work and clear flags under lock */
        bool do_flush = tl->flush_pending;
        bool do_compact = tl->compact_pending;
        tl->flush_pending = false;
        tl->compact_pending = false;

        tl_mutex_unlock(&tl->maint_mu);

        /*
         * Do actual work outside lock.
         * Priority: flush > compaction (per Write LLD §8.3)
         */
        if (do_flush) {
            /* Flush all sealed memruns */
            while (flush_one_and_publish(tl) == TL_OK) {
                /* Continue flushing until no more sealed memruns */
            }
        }

        if (do_compact && compaction_needed(tl)) {
            /* Perform compaction */
            tl_status_t cst = compact_one_step(tl);
            if (cst == TL_EBUSY) {
                /* Manifest changed during build, retry once */
                compact_one_step(tl);
            }
        }

        tl_mutex_lock(&tl->maint_mu);
    }

    tl_mutex_unlock(&tl->maint_mu);
    return NULL;
}

tl_status_t tl_maint_start(tl_timelog_t* tl) {
    if (tl == NULL || !tl->is_open) return TL_EINVAL;

    tl_mutex_lock(&tl->maint_mu);

    if (tl->maint_running) {
        /* Already running - idempotent success */
        tl_mutex_unlock(&tl->maint_mu);
        return TL_OK;
    }

    /* Reset shutdown flag in case of restart */
    tl->maint_shutdown = false;

    /* Create worker thread */
    int rc = tl_thread_create(&tl->maint_thread, maint_worker_fn, tl);
    if (rc != 0) {
        tl_mutex_unlock(&tl->maint_mu);
        return TL_EINTERNAL;
    }

    tl->maint_running = true;

    tl_mutex_unlock(&tl->maint_mu);

    TL_LOG_INFO(&tl->logger, "maintenance thread started");
    return TL_OK;
}

tl_status_t tl_maint_stop(tl_timelog_t* tl) {
    if (tl == NULL) return TL_EINVAL;

    tl_mutex_lock(&tl->maint_mu);

    if (!tl->maint_running) {
        /* Not running - idempotent success */
        tl_mutex_unlock(&tl->maint_mu);
        return TL_OK;
    }

    /* Signal shutdown */
    tl->maint_shutdown = true;
    tl_cond_signal(&tl->maint_cond);

    tl_mutex_unlock(&tl->maint_mu);

    /* Wait for thread to exit (outside lock to avoid deadlock) */
    tl_thread_join(tl->maint_thread, NULL);

    tl_mutex_lock(&tl->maint_mu);
    tl->maint_running = false;
    tl_mutex_unlock(&tl->maint_mu);

    TL_LOG_INFO(&tl->logger, "maintenance thread stopped");
    return TL_OK;
}

/*===========================================================================
 * Compaction Implementation (Phase 6B)
 *===========================================================================*/

/**
 * Check if compaction is needed.
 *
 * V1 simple policy: compact when delta segment count exceeds threshold.
 */
static bool compaction_needed(tl_timelog_t* tl) {
    bool needed = false;

    tl_mutex_lock(&tl->writer_mu);
    const tl_manifest_t* m = tl->manifest_current;
    if (m != NULL) {
        needed = (m->n_delta >= tl->cfg.max_delta_segments);
    }
    tl_mutex_unlock(&tl->writer_mu);

    return needed;
}

/**
 * Merge node for K-way compaction merge.
 */
typedef struct compact_merge_node {
    tl_record_t          record;
    tl_segment_iter_t*   iter;
    uint32_t             seg_idx;
} compact_merge_node_t;

/**
 * Compare merge nodes for min-heap (by timestamp, then segment index).
 */
static bool compact_heap_less(const compact_merge_node_t* a,
                               const compact_merge_node_t* b) {
    if (a->record.ts != b->record.ts) {
        return a->record.ts < b->record.ts;
    }
    return a->seg_idx < b->seg_idx;
}

/**
 * Swap two compact merge nodes.
 */
static void compact_heap_swap(compact_merge_node_t* a, compact_merge_node_t* b) {
    compact_merge_node_t tmp = *a;
    *a = *b;
    *b = tmp;
}

/**
 * Sift up after insertion.
 */
static void compact_heap_sift_up(compact_merge_node_t* heap, uint32_t idx) {
    while (idx > 0) {
        uint32_t parent = (idx - 1) / 2;
        if (compact_heap_less(&heap[idx], &heap[parent])) {
            compact_heap_swap(&heap[idx], &heap[parent]);
            idx = parent;
        } else {
            break;
        }
    }
}

/**
 * Sift down after extraction.
 */
static void compact_heap_sift_down(compact_merge_node_t* heap,
                                    uint32_t size,
                                    uint32_t idx) {
    while (true) {
        uint32_t smallest = idx;
        uint32_t left = 2 * idx + 1;
        uint32_t right = 2 * idx + 2;

        if (left < size && compact_heap_less(&heap[left], &heap[smallest])) {
            smallest = left;
        }
        if (right < size && compact_heap_less(&heap[right], &heap[smallest])) {
            smallest = right;
        }

        if (smallest != idx) {
            compact_heap_swap(&heap[idx], &heap[smallest]);
            idx = smallest;
        } else {
            break;
        }
    }
}

/**
 * Push a node onto the compact heap.
 */
static void compact_heap_push(compact_merge_node_t* heap,
                               uint32_t* size,
                               const compact_merge_node_t* node) {
    heap[*size] = *node;
    compact_heap_sift_up(heap, *size);
    (*size)++;
}

/**
 * Pop the minimum node from the compact heap.
 */
static void compact_heap_pop(compact_merge_node_t* heap, uint32_t* size) {
    if (*size == 0) return;
    (*size)--;
    if (*size > 0) {
        heap[0] = heap[*size];
        compact_heap_sift_down(heap, *size, 0);
    }
}

/**
 * Perform one compaction step.
 *
 * V1 simple strategy: merge all delta segments into one main segment.
 *
 * Algorithm:
 * 1. BUILD PHASE (expensive, outside seqlock):
 *    - Acquire current manifest
 *    - Collect all tombstones from delta segments
 *    - K-way merge delta segments, filtering tombstoned records
 *    - Build output main segment
 *
 * 2. PUBLISH PHASE (short, seqlock-protected):
 *    - Re-verify manifest hasn't changed
 *    - Build new manifest (remove deltas, add main)
 *    - Atomic swap
 *
 * @return TL_OK if compaction performed, TL_EOF if nothing to compact,
 *         TL_EBUSY if manifest changed during build (retry needed)
 */
static tl_status_t compact_one_step(tl_timelog_t* tl) {
    const tl_allocator_t* alloc = &tl->cfg.allocator;
    tl_status_t st;

    /*=========================================================================
     * BUILD PHASE (expensive, outside seqlock)
     *=========================================================================*/

    /*
     * Acquire current manifest reference.
     * This ensures the manifest (and its segments) remain valid during build.
     */
    tl_manifest_t* old_manifest = NULL;
    tl_mutex_lock(&tl->writer_mu);
    old_manifest = tl->manifest_current;
    if (old_manifest != NULL) {
        tl_manifest_acquire(old_manifest);
    }
    tl_mutex_unlock(&tl->writer_mu);

    if (old_manifest == NULL || old_manifest->n_delta == 0) {
        if (old_manifest != NULL) {
            tl_manifest_release(old_manifest);
        }
        return TL_EOF;  /* Nothing to compact */
    }

    uint32_t n_delta = old_manifest->n_delta;

    /*
     * Step 1: Collect all tombstones from delta segments.
     * These will be used to filter out deleted records during merge.
     */
    tl_intervals_t merged_tombs;
    tl_intervals_init(&merged_tombs, alloc);

    for (uint32_t i = 0; i < n_delta; i++) {
        tl_segment_t* seg = old_manifest->delta[i];
        if (seg->tombstones != NULL) {
            for (uint32_t j = 0; j < seg->tombstones->n; j++) {
                st = tl_intervals_insert(&merged_tombs,
                                          seg->tombstones->v[j].start,
                                          seg->tombstones->v[j].end);
                if (st != TL_OK) {
                    tl_intervals_destroy(&merged_tombs);
                    tl_manifest_release(old_manifest);
                    return st;
                }
            }
        }
    }

    /*
     * Step 2: Create segment iterators for all delta segments.
     */
    tl_segment_iter_t** iters = tl__malloc(alloc,
                                            n_delta * sizeof(tl_segment_iter_t*));
    if (iters == NULL) {
        tl_intervals_destroy(&merged_tombs);
        tl_manifest_release(old_manifest);
        return TL_ENOMEM;
    }

    for (uint32_t i = 0; i < n_delta; i++) {
        iters[i] = NULL;
    }

    for (uint32_t i = 0; i < n_delta; i++) {
        st = tl_segment_iter_create(alloc, old_manifest->delta[i],
                                     TL_TS_MIN, TL_TS_MAX, &iters[i]);
        if (st != TL_OK) {
            /* Cleanup on error */
            for (uint32_t j = 0; j < n_delta; j++) {
                if (iters[j] != NULL) {
                    tl_segment_iter_destroy(iters[j]);
                }
            }
            tl__free(alloc, iters);
            tl_intervals_destroy(&merged_tombs);
            tl_manifest_release(old_manifest);
            return st;
        }
    }

    /*
     * Step 3: Build min-heap for K-way merge.
     */
    compact_merge_node_t* heap = tl__malloc(alloc,
                                             n_delta * sizeof(compact_merge_node_t));
    if (heap == NULL) {
        for (uint32_t i = 0; i < n_delta; i++) {
            tl_segment_iter_destroy(iters[i]);
        }
        tl__free(alloc, iters);
        tl_intervals_destroy(&merged_tombs);
        tl_manifest_release(old_manifest);
        return TL_ENOMEM;
    }

    uint32_t heap_size = 0;

    /* Initialize heap with first record from each iterator */
    for (uint32_t i = 0; i < n_delta; i++) {
        if (tl_segment_iter_state(iters[i]) == TL_ITER_READY) {
            const tl_record_t* rec = tl_segment_iter_peek(iters[i]);
            if (rec != NULL) {
                compact_merge_node_t node;
                node.record = *rec;
                node.iter = iters[i];
                node.seg_idx = i;
                compact_heap_push(heap, &heap_size, &node);
            }
        }
    }

    /*
     * Step 4: K-way merge with tombstone filtering into segment builder.
     */
    uint32_t page_capacity = (uint32_t)((tl->cfg.target_page_bytes - 64) /
                                         (sizeof(tl_ts_t) + sizeof(tl_handle_t)));
    if (page_capacity < 128) page_capacity = 128;

    tl_segment_builder_t builder;
    uint32_t gen = tl_atomic_u32_fetch_add(&tl->next_generation, 1);
    st = tl_segment_builder_init(&builder, alloc, page_capacity,
                                  TL_SEG_MAIN, gen);
    if (st != TL_OK) {
        tl__free(alloc, heap);
        for (uint32_t i = 0; i < n_delta; i++) {
            tl_segment_iter_destroy(iters[i]);
        }
        tl__free(alloc, iters);
        tl_intervals_destroy(&merged_tombs);
        tl_manifest_release(old_manifest);
        return st;
    }

    uint64_t records_added = 0;

    while (heap_size > 0) {
        /* Get minimum record */
        tl_record_t rec = heap[0].record;
        tl_segment_iter_t* min_iter = heap[0].iter;

        /* Advance the iterator that produced this record */
        st = tl_segment_iter_advance(min_iter);

        if (st == TL_OK) {
            /* Update heap with new record from this iterator */
            const tl_record_t* next_rec = tl_segment_iter_peek(min_iter);
            if (next_rec != NULL) {
                heap[0].record = *next_rec;
                compact_heap_sift_down(heap, heap_size, 0);
            } else {
                /* Iterator exhausted unexpectedly */
                compact_heap_pop(heap, &heap_size);
            }
        } else {
            /* Iterator exhausted */
            compact_heap_pop(heap, &heap_size);
        }

        /* Filter: skip record if covered by tombstone */
        if (tl_intervals_contains(&merged_tombs, rec.ts)) {
            continue;  /* Record deleted, skip it */
        }

        /* Add record to output segment */
        st = tl_segment_builder_add(&builder, rec.ts, rec.handle);
        if (st != TL_OK) {
            tl_segment_builder_destroy(&builder);
            tl__free(alloc, heap);
            for (uint32_t i = 0; i < n_delta; i++) {
                tl_segment_iter_destroy(iters[i]);
            }
            tl__free(alloc, iters);
            tl_intervals_destroy(&merged_tombs);
            tl_manifest_release(old_manifest);
            return st;
        }

        records_added++;
    }

    /* Cleanup iterators and heap */
    tl__free(alloc, heap);
    for (uint32_t i = 0; i < n_delta; i++) {
        tl_segment_iter_destroy(iters[i]);
    }
    tl__free(alloc, iters);

    /*
     * Step 5: Finish building segment.
     * Note: Tombstones are NOT carried forward to main segment since they've
     * been applied. The records they deleted are already filtered out.
     */
    tl_segment_t* output_seg = NULL;
    st = tl_segment_builder_finish(&builder, &output_seg);
    tl_segment_builder_destroy(&builder);

    tl_intervals_destroy(&merged_tombs);

    /* Handle case where all records were tombstoned */
    if (st == TL_EOF) {
        /* No records survived - still need to remove delta segments */
        output_seg = NULL;
    } else if (st != TL_OK) {
        tl_manifest_release(old_manifest);
        return st;
    }

    /*=========================================================================
     * PUBLISH PHASE (short, seqlock-protected)
     *=========================================================================*/

    tl_mutex_lock(&tl->writer_mu);

    /*
     * Re-verify manifest hasn't changed during build phase.
     * If it has, abort and let caller retry.
     */
    if (tl->manifest_current != old_manifest) {
        tl_mutex_unlock(&tl->writer_mu);
        if (output_seg != NULL) {
            tl_segment_release(output_seg);
        }
        tl_manifest_release(old_manifest);
        return TL_EBUSY;  /* Manifest changed, retry */
    }


    publication_begin(tl);

    /*
     * Build new manifest:
     * - Remove all delta segments
     * - Add output main segment (if non-empty)
     */
    tl_manifest_t* new_manifest = NULL;
    st = tl_manifest_build(alloc, old_manifest,
                            NULL,                        /* add_delta: none */
                            output_seg,                  /* add_main */
                            old_manifest->delta,         /* remove_delta: all */
                            old_manifest->n_delta,
                            NULL, 0,                     /* remove_main: none */
                            &new_manifest);

    if (st != TL_OK) {
        publication_end(tl);
        tl_mutex_unlock(&tl->writer_mu);
        if (output_seg != NULL) {
            tl_segment_release(output_seg);
        }
        tl_manifest_release(old_manifest);
        return st;
    }

    /* Atomic manifest swap */
    tl->manifest_current = new_manifest;

    publication_end(tl);

    tl_mutex_unlock(&tl->writer_mu);

    /* Release old manifest (may still be pinned by snapshots) */
    tl_manifest_release(old_manifest);

    /* Release output segment reference (manifest now owns it) */
    if (output_seg != NULL) {
        tl_segment_release(output_seg);
    }

    TL_LOG_INFO(&tl->logger, "compaction completed: merged %u delta segments, "
                "%llu records", n_delta, (unsigned long long)records_added);

    return TL_OK;
}

/**
 * Signal the maintenance thread that compaction may be needed.
 */
static void signal_maintenance_compact(tl_timelog_t* tl) {
    tl_mutex_lock(&tl->maint_mu);
    tl->compact_pending = true;
    tl_cond_signal(&tl->maint_cond);
    tl_mutex_unlock(&tl->maint_mu);
}

tl_status_t tl_maint_step(tl_timelog_t* tl) {
    if (tl == NULL || !tl->is_open) return TL_EINVAL;

    /*
     * Manual maintenance: perform one unit of work.
     *
     * Priority order per Write LLD §8.3:
     * 1. Flush sealed memruns (highest priority - bounds memory)
     * 2. Compaction (bounds read amplification)
     */

    /* Try to flush one sealed memrun */
    tl_status_t st = flush_one_and_publish(tl);
    if (st == TL_OK) {
        return TL_OK;  /* Did work */
    }
    if (st != TL_EOF) {
        return st;  /* Error */
    }

    /* No memruns to flush; try compaction if needed */
    if (compaction_needed(tl)) {
        st = compact_one_step(tl);
        if (st == TL_OK || st == TL_EBUSY) {
            return TL_OK;  /* Did work (or need retry) */
        }
        if (st != TL_EOF) {
            return st;  /* Error */
        }
    }

    return TL_EOF;  /* No work to do */
}

/*===========================================================================
 * Statistics and Diagnostics
 *===========================================================================*/

tl_status_t tl_stats(const tl_snapshot_t* snap, tl_stats_t* out) {
    if (snap == NULL || out == NULL) return TL_EINVAL;

    memset(out, 0, sizeof(tl_stats_t));

    /* Manifest statistics */
    if (snap->manifest != NULL) {
        out->segments_main = snap->manifest->n_main;
        out->segments_delta = snap->manifest->n_delta;

        /* Count pages and records */
        for (uint32_t i = 0; i < snap->manifest->n_main; i++) {
            const tl_segment_t* seg = snap->manifest->main[i];
            out->pages_total += seg->page_count;
            out->records_estimate += seg->record_count;
            if (seg->tombstones != NULL) {
                out->tombstone_count += seg->tombstones->n;
            }
        }
        for (uint32_t i = 0; i < snap->manifest->n_delta; i++) {
            const tl_segment_t* seg = snap->manifest->delta[i];
            out->pages_total += seg->page_count;
            out->records_estimate += seg->record_count;
            if (seg->tombstones != NULL) {
                out->tombstone_count += seg->tombstones->n;
            }
        }
    }

    /* Memview statistics */
    if (snap->memview != NULL) {
        out->records_estimate += snap->memview->active_run_len;
        out->records_estimate += snap->memview->active_ooo_len;
        out->tombstone_count += snap->memview->active_tombs_len;

        for (size_t i = 0; i < snap->memview->sealed_len; i++) {
            const tl_memrun_t* mr = snap->memview->sealed[i];
            out->records_estimate += mr->run_len + mr->ooo_len;
            out->tombstone_count += mr->tombs_len;
        }
    }

    /* Bounds */
    if (snap->has_bounds) {
        out->min_ts = snap->min_ts;
        out->max_ts = snap->max_ts;
    } else {
        out->min_ts = 0;
        out->max_ts = 0;
    }

    return TL_OK;
}

/*
 * Helper: validate a tombstone array (tl_interval_t[]).
 * Checks: each interval has start < end, intervals are sorted, non-overlapping.
 */
static tl_status_t validate_tombstone_array(const tl_interval_t* tombs, size_t len) {
    if (tombs == NULL || len == 0) return TL_OK;

    tl_ts_t prev_end = TL_TS_MIN;
    for (size_t i = 0; i < len; i++) {
        /* S7: Each interval must have start < end */
        if (tombs[i].start >= tombs[i].end) {
            return TL_EINTERNAL;  /* Invalid tombstone: start >= end */
        }
        /* S8/W4: Intervals must be sorted and non-overlapping */
        if (tombs[i].start < prev_end) {
            return TL_EINTERNAL;  /* Overlapping or unsorted tombstones */
        }
        prev_end = tombs[i].end;
    }
    return TL_OK;
}

tl_status_t tl_validate(const tl_snapshot_t* snap) {
    if (snap == NULL) return TL_EINVAL;

    tl_status_t st;

    /*
     * Phase 5 Validation - Full Invariant Coverage
     *
     * From HLD/LLDs:
     * - I1/R1: Sortedness per component (pages, segments, memview)
     * - S2: Per-page ts[] sortedness
     * - S3: Page bounds correctness (min_ts == ts[0], max_ts == ts[n-1])
     * - S4: Catalog sortedness
     * - S5: Segment bounds match page bounds
     * - S7: Tombstone validity (start < end)
     * - S8/W4: Tombstone canonicalization (disjoint, sorted)
     */

    /*=======================================================================
     * 1. Manifest Segment Validation
     *=======================================================================*/
    if (snap->manifest != NULL) {
        /*
         * Main segments: should be sorted by min_ts
         * (Per LLD: main segments are sorted, delta segments are in flush order)
         */
        for (uint32_t i = 1; i < snap->manifest->n_main; i++) {
            if (snap->manifest->main[i]->min_ts < snap->manifest->main[i-1]->min_ts) {
                return TL_EINTERNAL;  /* Main segments not sorted */
            }
        }

        /*
         * NOTE: Delta segments are NOT sorted by min_ts.
         * Per Read LLD: "For delta segments (small, possibly unsorted)"
         * They are in flush order, not timestamp order.
         * The k-way merge handles this correctly.
         */

        /*
         * Validate each main segment using comprehensive tl_segment_validate().
         * This checks: catalog sorted, each page valid (bounds, sortedness),
         * segment bounds match pages.
         */
        for (uint32_t i = 0; i < snap->manifest->n_main; i++) {
            const tl_segment_t* seg = snap->manifest->main[i];

            /* Use comprehensive segment validation (S2, S3, S4, S5) */
            st = tl_segment_validate(seg);
            if (st != TL_OK) return st;

            /* S7/S8: Validate segment tombstones */
            if (seg->tombstones != NULL && seg->tombstones->n > 0) {
                st = validate_tombstone_array(seg->tombstones->v, seg->tombstones->n);
                if (st != TL_OK) return st;
            }
        }

        /*
         * Validate each delta segment
         */
        for (uint32_t i = 0; i < snap->manifest->n_delta; i++) {
            const tl_segment_t* seg = snap->manifest->delta[i];

            /* Use comprehensive segment validation (S2, S3, S4, S5) */
            st = tl_segment_validate(seg);
            if (st != TL_OK) return st;

            /* S7/S8: Validate segment tombstones */
            if (seg->tombstones != NULL && seg->tombstones->n > 0) {
                st = validate_tombstone_array(seg->tombstones->v, seg->tombstones->n);
                if (st != TL_OK) return st;
            }
        }
    }

    /*=======================================================================
     * 2. Memview Validation
     *=======================================================================*/
    if (snap->memview != NULL) {
        /*
         * W2: Active run should be sorted (in-order buffer invariant)
         */
        for (size_t i = 1; i < snap->memview->active_run_len; i++) {
            if (snap->memview->active_run[i].ts < snap->memview->active_run[i-1].ts) {
                return TL_EINTERNAL;  /* Active run not sorted */
            }
        }

        /*
         * W3: Active OOO should be sorted (sorted at snapshot capture time)
         */
        for (size_t i = 1; i < snap->memview->active_ooo_len; i++) {
            if (snap->memview->active_ooo[i].ts < snap->memview->active_ooo[i-1].ts) {
                return TL_EINTERNAL;  /* Active OOO not sorted */
            }
        }

        /*
         * S7/S8: Active tombstones should be valid and canonical
         */
        st = validate_tombstone_array(snap->memview->active_tombs,
                                       snap->memview->active_tombs_len);
        if (st != TL_OK) return st;

        /*
         * Sealed memruns: each run/ooo array sorted, tombs valid
         */
        for (size_t k = 0; k < snap->memview->sealed_len; k++) {
            const tl_memrun_t* mr = snap->memview->sealed[k];

            /* Run array sorted */
            for (size_t i = 1; i < mr->run_len; i++) {
                if (mr->run[i].ts < mr->run[i-1].ts) {
                    return TL_EINTERNAL;  /* Sealed run not sorted */
                }
            }

            /* OOO array sorted (sorted at seal time) */
            for (size_t i = 1; i < mr->ooo_len; i++) {
                if (mr->ooo[i].ts < mr->ooo[i-1].ts) {
                    return TL_EINTERNAL;  /* Sealed OOO not sorted */
                }
            }

            /* S7/S8: Sealed memrun tombstones */
            st = validate_tombstone_array(mr->tombs, mr->tombs_len);
            if (st != TL_OK) return st;
        }
    }

    /*=======================================================================
     * 3. Snapshot Bounds Validation (optional consistency check)
     *=======================================================================*/
    if (snap->has_bounds) {
        /* Basic sanity: min <= max when bounds are present */
        if (snap->min_ts > snap->max_ts) {
            return TL_EINTERNAL;  /* Invalid snapshot bounds */
        }
    }

    return TL_OK;
}
