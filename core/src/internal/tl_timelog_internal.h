#ifndef TL_TIMELOG_INTERNAL_H
#define TL_TIMELOG_INTERNAL_H

/*===========================================================================
 * Internal Timelog Structure Definition
 *
 * This header contains the SINGLE authoritative definition of struct tl_timelog.
 * It is included by:
 * - tl_timelog.c (main implementation)
 * - tl_snapshot.c (snapshot acquisition needs field access)
 * - Any future internal module that needs field access
 *
 * IMPORTANT: This is an INTERNAL header. External code must only use the
 * opaque tl_timelog_t pointer from timelog.h.
 *===========================================================================*/

#include "tl_defs.h"
#include "tl_alloc.h"
#include "tl_log.h"
#include "tl_sync.h"
#include "tl_seqlock.h"
#include "../delta/tl_memtable.h"
#include "../storage/tl_manifest.h"
#include "../maint/tl_adaptive.h"

/* Forward declaration to avoid heavy include dependencies. */
struct tl_memview_shared;
typedef struct tl_memview_shared tl_memview_shared_t;

/*===========================================================================
 * Maintenance Worker State Machine (Phase 7)
 *
 * Protected by maint_mu. State transitions:
 *   STOPPED  -> RUNNING  (tl_maint_start)
 *   RUNNING  -> STOPPING (tl_maint_stop initiated)
 *   STOPPING -> STOPPED  (tl_maint_stop completed)
 *
 * The 3-state machine prevents:
 * - Double-spawn: start during RUNNING returns TL_OK (idempotent)
 * - Double-join: start/stop during STOPPING returns TL_EBUSY/TL_OK
 *===========================================================================*/
typedef enum tl_worker_state {
    TL_WORKER_STOPPED  = 0,  /* No worker thread */
    TL_WORKER_RUNNING  = 1,  /* Worker thread active */
    TL_WORKER_STOPPING = 2   /* Stop requested, join in progress */
} tl_worker_state_t;

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
     * Lifecycle Flag
     *
     * is_open is only modified at open/close boundaries when no other
     * threads should be accessing the instance.
     *-----------------------------------------------------------------------*/
    bool            is_open;

    /*-----------------------------------------------------------------------
     * Maintenance State (Phase 7)
     *
     * CRITICAL: All fields in this section are protected by maint_mu.
     * NO atomics are used. This eliminates the lost-work race condition
     * that exists with load-then-store patterns on atomic flags.
     *
     * The state machine + plain bools pattern from plan_phase7.md:
     * - State machine prevents double-spawn/double-join races
     * - Mutex-protected flags ensure work is never lost
     * - Flag set always happens (even if worker not RUNNING)
     * - Signal gated on state (only when RUNNING)
     *-----------------------------------------------------------------------*/
    tl_worker_state_t maint_state;      /* State machine: STOPPED/RUNNING/STOPPING */
    bool              maint_shutdown;   /* Signal worker to exit */
    bool              flush_pending;    /* Sealed memruns exist */
    bool              compact_pending;  /* Compaction requested */
    tl_thread_t       maint_thread;     /* Worker thread handle (valid when RUNNING) */

    /*-----------------------------------------------------------------------
     * Adaptive Segmentation State (V-Next)
     *
     * Protected by maint_mu. Single writer: maintenance thread only.
     * Tracks EWMA density and failure counters for window adaptation.
     * The authoritative window is `effective_window_size` (above).
     *-----------------------------------------------------------------------*/
    tl_adaptive_state_t adaptive;

    /*-----------------------------------------------------------------------
     * Delta Layer (Phase 4)
     *-----------------------------------------------------------------------*/

    /* Memtable: mutable write buffer for inserts and tombstones */
    tl_memtable_t   memtable;

    /* Snapshot memview cache (for reuse when memtable epoch unchanged) */
    tl_memview_shared_t* memview_cache;
    uint64_t             memview_cache_epoch;

    /*-----------------------------------------------------------------------
     * Storage Layer (Phase 5)
     *
     * The manifest is the atomic publication root for storage.
     * Swapped atomically under writer_mu + seqlock during flush/compaction.
     *-----------------------------------------------------------------------*/
    tl_manifest_t*  manifest;       /* Current manifest (atomic publication root) */
    uint32_t        next_gen;       /* Monotonic generation for new segments */

    /*-----------------------------------------------------------------------
     * Operational Counters (cumulative since open)
     *
     * These are atomic because they may be incremented by the writer thread
     * (seals, ooo_budget_hits, backpressure) or the maintenance thread
     * (flushes, compactions) while being read by stats queries.
     *-----------------------------------------------------------------------*/
    tl_atomic_u64   seals_total;        /* Memtable seals performed */
    tl_atomic_u64   ooo_budget_hits;    /* OOO budget exceeded (forced sort) */
    tl_atomic_u64   backpressure_waits; /* Writer blocked on sealed queue */
    tl_atomic_u64   flushes_total;      /* Flush operations completed */
    tl_atomic_u64   compactions_total;  /* Compaction operations completed */

#ifdef TL_DEBUG
    /*-----------------------------------------------------------------------
     * Debug-Only Snapshot Tracking
     *
     * Counts outstanding snapshots to detect leaks at close time.
     * Atomic because snapshots can be acquired/released from multiple threads.
     *-----------------------------------------------------------------------*/
    tl_atomic_u32   snapshot_count; /* Outstanding snapshot count */
#endif
};

#endif /* TL_TIMELOG_INTERNAL_H */
