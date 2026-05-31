#ifndef TL_TIMELOG_INTERNAL_H
#define TL_TIMELOG_INTERNAL_H

/*===========================================================================
 * Internal Timelog Structure
 *
 * Sole authoritative definition of struct tl_timelog. External callers see
 * only the opaque tl_timelog_t pointer from timelog.h; this header is
 * shared between internal translation units (the main implementation, the
 * snapshot module, and any other internal module that needs field access).
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
 * Maintenance Worker State Machine
 *
 * Three states under maint_mu. Transitions:
 *   STOPPED  -> RUNNING  via tl_maint_start
 *   RUNNING  -> STOPPING via tl_maint_stop
 *   STOPPING -> STOPPED  on successful join
 *
 * The intermediate STOPPING state prevents two dangerous races:
 *   - Double-spawn: tl_maint_start during RUNNING is idempotent (TL_OK).
 *   - Double-join: start/stop while STOPPING returns TL_EBUSY so we never
 *     pthread_join the same handle twice and never report TL_OK before the
 *     worker is quiesced.
 *===========================================================================*/
typedef enum tl_worker_state {
    TL_WORKER_STOPPED  = 0,
    TL_WORKER_RUNNING  = 1,
    TL_WORKER_STOPPING = 2
} tl_worker_state_t;

/**
 * Core engine instance.
 *
 * Field ordering groups frequently-accessed members to reduce cache-line
 * bouncing; config is stored inline so the hot path does not pay for a
 * pointer chase. Mutability and lock ownership are documented per field
 * below.
 */
struct tl_timelog {
    /*-----------------------------------------------------------------------
     * Configuration (immutable after init)
     *-----------------------------------------------------------------------*/
    tl_config_t     config;

    /*-----------------------------------------------------------------------
     * Effective Values
     *
     * Both fields are derived from config at open. effective_ooo_budget is
     * immutable for the lifetime of the instance. effective_window_size is
     * mutable: adaptive segmentation may resize it during compaction
     * (under maint_mu) until window_grid_frozen latches it in place.
     *-----------------------------------------------------------------------*/
    tl_ts_t         effective_window_size;
    size_t          effective_ooo_budget;

    /*-----------------------------------------------------------------------
     * Subsystem Contexts
     *-----------------------------------------------------------------------*/
    tl_alloc_ctx_t  alloc;
    tl_log_ctx_t    log;

    /*-----------------------------------------------------------------------
     * Synchronisation
     *
     * Strict lock order, leftmost acquired first:
     *   maint_mu -> flush_mu -> writer_mu -> memtable_mu
     *
     * Acquiring a lock to the left of one you already hold is forbidden
     * and would deadlock against the worker thread.
     *-----------------------------------------------------------------------*/

    /* Serialises manifest publication and snapshot capture. The critical
     * section is intentionally short — all expensive work happens
     * off-lock and only the final pointer swap is performed here. */
    tl_mutex_t      writer_mu;

    /* Serialises flush build+publish so there is only ever one flusher. */
    tl_mutex_t      flush_mu;

    /* Protects the maintenance state machine and the pending-work flags. */
    tl_mutex_t      maint_mu;
    tl_cond_t       maint_cond;

    /* Protects the memtable's sealed-memrun ring buffer. */
    tl_mutex_t      memtable_mu;
    tl_cond_t       memtable_cond;  /* Signalled when sealed queue gains space. */

    /* Seqlock published with even/odd parity around manifest swaps so
     * snapshot readers can detect torn captures and retry. */
    tl_seqlock_t    view_seq;

    /*-----------------------------------------------------------------------
     * Lifecycle Flag
     *
     * Mutated only on the open/close boundary, when no other thread can
     * be touching the instance.
     *-----------------------------------------------------------------------*/
    bool            is_open;

    /*-----------------------------------------------------------------------
     * Maintenance State
     *
     * Every field in this block is protected by maint_mu and stored as a
     * plain bool, never an atomic. The mutex doubles as the predicate
     * barrier for maint_cond, which closes the classic lost-wakeup race
     * that arises with naked atomic flags: a writer can set the flag while
     * the worker is between predicate check and wait.
     *
     * Signalling rule: always set the flag, but only signal the condvar
     * when the worker is RUNNING. A flag set before tl_maint_start() is
     * picked up automatically once the worker enters its loop.
     *-----------------------------------------------------------------------*/
    tl_worker_state_t maint_state;
    bool              maint_shutdown;   /* Request the worker to exit. */
    bool              flush_pending;    /* Sealed memrun(s) await flushing. */
    bool              compact_pending;  /* Explicit compaction was requested. */
    tl_thread_t       maint_thread;     /* Valid while maint_state == RUNNING. */

    /*-----------------------------------------------------------------------
     * Adaptive Segmentation State
     *
     * Tracks the EWMA of segment density plus a consecutive-failure counter
     * that the adaptive sizer uses to retune effective_window_size. Owned
     * solely by the maintenance thread; readers acquire maint_mu.
     *-----------------------------------------------------------------------*/
    tl_adaptive_state_t adaptive;

    /*-----------------------------------------------------------------------
     * Window Grid Freeze
     *
     * Once any L1 segment exists, the partitioning of the time domain into
     * non-overlapping windows is fixed for that L1's bounds; resizing the
     * window after that point would let new L1 segments overlap their
     * predecessors. This flag latches that condition: set true either at
     * open (if the manifest already contains L1 segments) or the first
     * time compaction promotes a segment to L1. Once true it remains true.
     *-----------------------------------------------------------------------*/
    bool window_grid_frozen;

    /*-----------------------------------------------------------------------
     * Delta Layer
     *-----------------------------------------------------------------------*/

    /* Mutable write buffer that absorbs inserts and tombstones until the
     * active run is sealed and handed off to the flusher. */
    tl_memtable_t   memtable;

    /* Monotonic operation sequence, written under writer_mu. Drives the
     * sequence numbers stamped onto records and tombstones. */
    tl_seq_t        op_seq;

    /* Shared cached memview reused across snapshot acquisitions when the
     * memtable epoch has not changed; saves a deep copy on the hot path. */
    tl_memview_shared_t* memview_cache;
    uint64_t             memview_cache_epoch;

    /*-----------------------------------------------------------------------
     * Storage Layer
     *
     * The manifest pointer is the engine's atomic publication root.
     * Every flush and compaction swaps it under writer_mu and inside a
     * seqlock write window so readers see either the pre-publish or
     * post-publish state, never an intermediate.
     *-----------------------------------------------------------------------*/
    tl_manifest_t*  manifest;
    uint32_t        next_gen;       /* Monotonic generation handed to new segments. */

    /*-----------------------------------------------------------------------
     * Operational Counters
     *
     * Cumulative since open. Stored as atomics because the writer thread
     * updates the ingest-side counters concurrently with the maintenance
     * thread updating the flush/compact counters, and tl_stats() may
     * sample any of them at any time. Relaxed loads are sufficient since
     * each counter is independent of the others.
     *-----------------------------------------------------------------------*/
    tl_atomic_u64   seals_total;
    tl_atomic_u64   ooo_budget_hits;            /* OOO budget exceeded (forced sort). */
    tl_atomic_u64   backpressure_waits;         /* Writer waited on the sealed queue. */
    tl_atomic_u64   flushes_total;
    tl_atomic_u64   compactions_total;
    tl_atomic_u64   compaction_retries;         /* Interim publish retries. */
    tl_atomic_u64   compaction_publish_ebusy;   /* Publish gave up with EBUSY. */
    tl_atomic_u64   compaction_select_calls;
    tl_atomic_u64   compaction_select_l0_inputs;
    tl_atomic_u64   compaction_select_l1_inputs;
    tl_atomic_u64   compaction_select_no_work;

#ifdef TL_DEBUG
    /*-----------------------------------------------------------------------
     * Debug-only outstanding snapshot count, used by tl_close() to fire
     * an assertion when callers forget to release their snapshots before
     * tearing the engine down. Atomic because snapshots can be acquired
     * and released from arbitrary threads.
     *-----------------------------------------------------------------------*/
    tl_atomic_u32   snapshot_count;
#endif
};

#endif /* TL_TIMELOG_INTERNAL_H */
