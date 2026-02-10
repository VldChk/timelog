#ifndef TL_COMPACTION_H
#define TL_COMPACTION_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_intervals.h"
#include "../storage/tl_segment.h"
#include "../storage/tl_manifest.h"

/*===========================================================================
 * Compaction Module
 *
 * Implements L0 -> L1 compaction for the LSM-style storage layer.
 *
 * Goals (Compaction Policy LLD Section 1):
 * 1. Bound read amplification: L0 count <= max_delta_segments
 * 2. Enforce L1 non-overlap: L1 segments aligned to time windows
 * 3. Fold tombstones: L1 segments are tombstone-free
 * 4. Preserve snapshot isolation: atomic manifest publication
 * 5. Support handle drop callback: notify when records retired
 *
 * Phases:
 * 1. Trigger check (tl_compact_needed)
 * 2. Selection (tl_compact_select)
 * 3. Merge (tl_compact_merge)
 * 4. Publication (tl_compact_publish)
 *
 * Thread Safety:
 * - Compaction is serialized externally by maint_mu (one compaction at a time)
 * - writer_mu held only during short publication phase
 * - Long-running merge happens without locks
 *
 * Trigger Coupling with Flush (Background Mode):
 * - tl_compact_needed() is only called when flush work is pending
 * - This is safe because compaction triggers depend on segment state
 * - See tl_compact_needed() documentation for full details
 *
 * Handle Drop Callback Semantics:
 * - Callbacks are DEFERRED until AFTER successful publication
 * - During merge, dropped records are collected but NOT fired
 * - Only after publish succeeds are callbacks invoked for all dropped records
 * - If compaction fails/retries, pending drops are discarded (will be re-collected)
 * - IMPORTANT: This is a "retire" notification, NOT a "safe to free" signal
 * - Existing snapshots may still reference the dropped record until released
 * - User must implement their own epoch/RCU/hazard-pointer scheme if they
 *   need safe payload reclamation (see tl_on_drop_fn docs in timelog.h)
 *
 * Reference: timelog_v1_lld_compaction_policy.md
 *===========================================================================*/

/* Forward declarations */
struct tl_timelog;
typedef struct tl_timelog tl_timelog_t;
struct tl_snapshot;
typedef struct tl_snapshot tl_snapshot_t;

/*===========================================================================
 * Compaction Context
 *
 * Holds all state for a single compaction operation.
 * Created by select, populated by merge, consumed by publish.
 *===========================================================================*/

typedef struct tl_compact_ctx {
    tl_timelog_t*       tl;              /* Parent instance */
    tl_alloc_ctx_t*     alloc;           /* Allocator */

    /* Input segments (pinned during compaction) */
    tl_segment_t**      input_l0;        /* Selected L0 segments */
    size_t              input_l0_len;
    tl_segment_t**      input_l1;        /* Selected L1 segments */
    size_t              input_l1_len;

    /* Manifest snapshot at selection time */
    tl_manifest_t*      base_manifest;   /* Pinned base manifest */
    tl_snapshot_t*      snapshot;        /* Pinned snapshot (for tombs + seq) */
    tl_seq_t            applied_seq;     /* Tombstone watermark for outputs */

    /* Effective tombstone set */
    tl_intervals_t      tombs;           /* Union of all tombstones (unclipped) */
    tl_intervals_t      tombs_clipped;   /* Tombstones clipped to output range */

    /* Output segments */
    tl_segment_t**      output_l1;       /* New L1 segments */
    size_t              output_l1_len;
    size_t              output_l1_cap;

    tl_segment_t*       residual_tomb;   /* Tombstone-only L0 for residuals */

    /* Configuration (copied from tl) */
    tl_ts_t             window_size;
    tl_ts_t             window_origin;
    size_t              target_page_bytes;
    uint32_t            generation;

    /* Handle drop callback (matches tl_config_t naming) */
    tl_on_drop_fn       on_drop_handle;
    void*               on_drop_ctx;

    /* Deferred drop records - collected during merge, fired after publish.
     *
     * CRITICAL CORRECTNESS INVARIANT: If compaction fails (ENOMEM/EBUSY)
     * or retries, callbacks MUST NOT fire for records still visible in
     * the manifest. This would violate the on_drop_handle contract and
     * can cause double-free/UAF in user code that treats it as final
     * reclamation.
     *
     * Solution: Collect dropped (ts, handle) pairs during merge, but only
     * invoke callbacks after successful publish. On failure/retry, the
     * drops are discarded when ctx is destroyed; re-merge re-collects them.
     *
     * Uses tl_record_t for storage since it has (ts, handle) pair. */
    tl_record_t*        dropped_records;
    size_t              dropped_len;
    size_t              dropped_cap;

    /* Output range (computed from input selection) */
    tl_ts_t             output_min_ts;
    tl_ts_t             output_max_ts;
    int64_t             output_min_wid;  /* First output window ID */
    int64_t             output_max_wid;  /* Last output window ID (inclusive) */
} tl_compact_ctx_t;

/*===========================================================================
 * Context Lifecycle
 *===========================================================================*/

/**
 * Initialize compaction context.
 * Does NOT select segments - call tl_compact_select() next.
 *
 * @param window_size Effective window size (caller must read under maint_mu)
 */
void tl_compact_ctx_init(tl_compact_ctx_t* ctx,
                          tl_timelog_t* tl,
                          tl_alloc_ctx_t* alloc,
                          tl_ts_t window_size);

/**
 * Destroy compaction context and release all pinned resources.
 * Safe to call at any point (partial initialization cleanup).
 */
void tl_compact_ctx_destroy(tl_compact_ctx_t* ctx);

/*===========================================================================
 * Compaction Phases
 *===========================================================================*/

/**
 * Phase 1: Check if compaction is needed.
 *
 * Returns true if:
 * - L0 count >= max_delta_segments
 * - compact_pending flag is set (checked by caller)
 * - Delete debt threshold exceeded (optional)
 *
 * Briefly acquires writer_mu to pin manifest (prevents UAF).
 * This is an advisory check; selection re-validates.
 *
 * Flush/Compaction Trigger Coupling (Background Mode):
 * =====================================================
 * In background mode, the worker loop only calls this function when:
 *   - do_flush is true (flush work pending), AND
 *   - do_compact is false (compact_pending was NOT already set)
 *
 * See tl_timelog.c:1749: `if (!do_compact && do_flush)`
 *
 * This is an optimization based on the invariant:
 *
 *   "Compaction triggers can only change when segments change"
 *
 * Segment state changes only via:
 * - Flush: creates new L0 segments (increases L0 count, adds tombstones)
 * - Compaction: removes L0/L1, creates L1 (decreases L0 count)
 *
 * On idle periodic wakes with no pending work, calling this is wasteful
 * because triggers are unchanged from the previous check.
 *
 * When compact_pending is already set (explicit tl_compact() request), this
 * function is SKIPPED because we already know compaction should run.
 *
 * IMPORTANT: This coupling means delete-debt compaction won't be triggered
 * on pure idle wakes without write activity. Users wanting prompt delete-debt
 * response should either:
 * - Use tl_compact() for explicit compaction requests
 * - Ensure continued write activity
 *
 * This coupling does NOT affect:
 * - Explicit requests via compact_pending flag (bypasses this check entirely)
 * - Manual mode (tl_maint_step always checks triggers unconditionally)
 *
 * Reference: tl_timelog.c worker loop (tl__maint_worker_entry)
 */
bool tl_compact_needed(const tl_timelog_t* tl);

/**
 * Phase 2: Select segments for compaction.
 *
 * Implements baseline policy (Compaction Policy LLD Section 6.1):
 * 1. Pin current manifest
 * 2. Select all L0 segments
 * 3. Compute covered time range (records + tombstones)
 * 4. Select overlapping L1 segments
 *
 * IMPORTANT: Caller MUST call tl_compact_ctx_destroy() regardless of
 * return status. This function acquires resources (manifest pin, segment
 * refs) that are cleaned up by destroy. This follows the init/destroy
 * lifecycle pattern - select may partially succeed before failing.
 *
 * @param ctx  Initialized compaction context
 * @return TL_OK on success (inputs selected and pinned)
 *         TL_EOF if no work needed
 *         TL_ENOMEM on allocation failure
 *         TL_EOVERFLOW if window ID computation overflows
 */
tl_status_t tl_compact_select(tl_compact_ctx_t* ctx);

/**
 * Phase 3: Execute compaction merge.
 *
 * Implements merge algorithm (Compaction Policy LLD Section 7):
 * 1. Build effective tombstone set
 * 2. K-way merge all input segments
 * 3. Skip deleted records (tombstone filtering)
 * 4. Partition output by window boundaries
 * 5. Build L1 segments for windows with live records
 * 6. Build residual tombstone segment if needed
 *
 * Deleted records are COLLECTED but callbacks are NOT fired here.
 * See header comment for deferred callback semantics - callbacks
 * are only invoked after successful publish in tl_compact_one().
 *
 * @param ctx  Context with selected inputs
 * @return TL_OK on success (outputs built)
 *         TL_ENOMEM on allocation failure
 *         TL_EOVERFLOW if window span too large
 */
tl_status_t tl_compact_merge(tl_compact_ctx_t* ctx);

/**
 * Phase 4: Publish compaction results.
 *
 * Implements publication protocol (Compaction Policy LLD Section 8):
 * 1. Build new manifest (OFF-LOCK - this is the expensive part)
 * 2. Acquire writer_mu + seqlock
 * 3. Verify manifest unchanged (abort if changed)
 * 4. Swap manifest pointer (O(1))
 * 5. Release locks
 * 6. Release old manifest
 *
 * @param ctx  Context with built outputs
 * @return TL_OK on success
 *         TL_EBUSY if manifest changed (caller should retry)
 *         TL_ENOMEM on allocation failure
 */
tl_status_t tl_compact_publish(tl_compact_ctx_t* ctx);

/**
 * Complete compaction (all phases).
 *
 * Convenience function that runs select -> merge -> publish.
 * On TL_EBUSY from publish, retries up to max_retries times.
 *
 * @param tl          Timelog instance
 * @param max_retries Max publish retries (default 3)
 * @return TL_OK on success
 *         TL_EOF if no work needed
 *         TL_EBUSY if all retries exhausted
 *         TL_ENOMEM on allocation failure
 *         TL_EOVERFLOW if window span too large
 */
tl_status_t tl_compact_one(tl_timelog_t* tl, int max_retries);

#ifdef TL_TEST_HOOKS
/**
 * Test-only: compute delete debt ratio for a manifest.
 * Exposes internal heuristic for unit testing.
 */
double tl_test_compute_delete_debt(const tl_timelog_t* tl,
                                   const tl_manifest_t* m);
#endif

#endif /* TL_COMPACTION_H */
