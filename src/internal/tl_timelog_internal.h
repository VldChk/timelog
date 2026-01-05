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
#include "tl_atomic.h"
#include "tl_seqlock.h"
#include "../delta/tl_memtable.h"
#include "../storage/tl_manifest.h"

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
     * Delta Layer (Phase 4)
     *-----------------------------------------------------------------------*/

    /* Memtable: mutable write buffer for inserts and tombstones */
    tl_memtable_t   memtable;

    /*-----------------------------------------------------------------------
     * Storage Layer (Phase 5)
     *
     * The manifest is the atomic publication root for storage.
     * Swapped atomically under writer_mu + seqlock during flush/compaction.
     *-----------------------------------------------------------------------*/
    tl_manifest_t*  manifest;       /* Current manifest (atomic publication root) */
    uint32_t        next_gen;       /* Monotonic generation for new segments */
};

#endif /* TL_TIMELOG_INTERNAL_H */
