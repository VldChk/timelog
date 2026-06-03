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
 * L0 -> L1 compaction for the LSM-style storage layer.
 *
 * Goals:
 * 1. Bound read amplification: L0 count <= max_delta_segments
 * 2. Enforce L1 non-overlap: L1 segments aligned to time windows
 * 3. Fold tombstones: L1 segments are tombstone-free
 * 4. Preserve snapshot isolation: atomic manifest publication
 * 5. Support a handle-drop callback when records are retired
 *
 * Stages (run sequentially per compaction):
 *   tl_compact_needed   -- cheap trigger check
 *   tl_compact_select   -- pin manifest, choose input segments
 *   tl_compact_merge    -- k-way merge with tombstone filtering (off-lock)
 *   tl_compact_publish  -- atomically swap to a new manifest
 *
 * Bounded selection for OOO workloads
 * -----------------------------------
 * Out-of-order ingestion can produce wide L0 spans that, if compacted in
 * one shot, would rewrite huge L1 ranges. To keep work bounded:
 *
 * - Selection is anchored on the oldest backlog and capped at
 *   max_compaction_windows windows, max_compaction_inputs L0 segments,
 *   and compaction_target_bytes estimated output.
 * - L1 segments are pulled in only when their window bounds overlap the
 *   bounded output range.
 * - On a manifest race, publish returns TL_EBUSY and tl_compact_one()
 *   re-selects and re-merges from the new manifest (bounded retries).
 *
 * Thread Safety:
 * - Compaction is serialised externally by maint_mu (one at a time).
 * - writer_mu is held only for the short publication phase; the long
 *   merge runs without locks.
 *
 * Trigger coupling with flush (background mode):
 * In background mode the worker only calls tl_compact_needed() when flush
 * work is also pending. This is safe because compaction triggers only
 * change when segment state changes (flush adds L0; compaction removes
 * L0/L1 and adds L1). On idle wakes with no writes the trigger state is
 * unchanged and there is nothing to evaluate. See tl_compact_needed()
 * for the full explanation.
 *
 * Handle-drop callback semantics:
 * - Callbacks are DEFERRED until AFTER a successful publish. During merge,
 *   dropped (ts, handle) pairs are collected but not fired.
 * - On failure/retry, pending drops are discarded and will be re-collected
 *   from the next merge.
 * - The callback is a "retired" notification, NOT a "safe to free" signal:
 *   existing snapshots may still reference the dropped record. Users who
 *   need safe payload reclamation must layer their own epoch / RCU /
 *   hazard-pointer scheme on top (see tl_on_drop_fn docs in timelog.h).
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

    /* Effective tombstone sets (two distinct sets with different purposes)
     *
     * tombs:         Union of tombstones from INPUT segments only (unclipped).
     *                Used for: residual tombstone computation (tombstones that
     *                extend beyond the merged output window range).
     *
     * tombs_clipped: Tombstones from snapshot (global), clipped to output
     *                window range [first_window_start, last_window_end).
     *                Used for: record filtering during the K-way merge.
     *
     * Using the wrong set causes incorrect results:
     * - tombs_clipped for residuals → misses tombstones outside window
     * - tombs for filtering → applies tombstones from outside compaction scope
     */
    tl_intervals_t      tombs;           /* From input segments, unclipped */
    tl_intervals_t      tombs_clipped;   /* From snapshot, clipped to output range */

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

    /* (ts, handle) pairs of records tombstoned during merge, queued
     * here so that the on_drop_handle callback fires only AFTER a
     * successful publish.
     *
     * Firing before publish would let user code free a payload while
     * the record is still visible in the manifest if merge or publish
     * later fails, producing UAF/double-free. On failure or retry the
     * queue is discarded; the next merge will re-collect the same
     * drops from the freshly selected inputs. */
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
 * Returns true if compaction should run.
 *
 * Triggers:
 * - L0 count >= max_delta_segments
 * - Delete-debt fraction exceeds delete_debt_threshold (when configured)
 *
 * Briefly acquires writer_mu to pin the manifest (prevents UAF on a
 * concurrent swap). This is an advisory check; the selection phase
 * re-validates from the live manifest.
 *
 * Background mode trigger coupling
 * --------------------------------
 * The background worker only calls this function on wakes that already
 * have flush work pending, and only when compact_pending is not already
 * set. The invariant "compaction triggers can only change when segments
 * change" makes idle re-checks pointless: only flush or compaction
 * itself can move the L0 count or alter the tombstone set.
 *
 * Side effect: delete-debt compaction will NOT fire on pure idle wakes
 * without write activity. Callers that need prompt delete-debt response
 * should either invoke tl_compact() explicitly or generate write
 * activity. Manual maintenance mode is unaffected (the manual stepper
 * always evaluates triggers unconditionally).
 */
bool tl_compact_needed(const tl_timelog_t* tl);

/**
 * Select inputs for the next compaction.
 *
 * Pins the current manifest, greedily picks L0 segments (subject to
 * input/window/byte caps), computes their covered time range, and pulls
 * in every L1 segment whose window overlaps that range.
 *
 * The caller MUST call tl_compact_ctx_destroy() regardless of the
 * return value: this function acquires manifest pins and segment refs
 * that even a partial failure leaves attached to the context.
 *
 * @param ctx  Initialised compaction context
 * @return TL_OK on success (inputs selected and pinned)
 *         TL_EOF if no work needed
 *         TL_ENOMEM on allocation failure
 *         TL_EOVERFLOW if window ID computation overflows
 */
tl_status_t tl_compact_select(tl_compact_ctx_t* ctx);

/**
 * Run the K-way merge over the selected inputs and produce output
 * segments.
 *
 * The merge filters out records covered by the snapshot tombstone set
 * (clipped to the output window range), partitions surviving records
 * along window boundaries to form L1 segments, and builds a residual
 * tombstone-only L0 segment for any tombstone portions that extend
 * outside the output range.
 *
 * Dropped records are queued onto ctx->dropped_records for the
 * callback that fires later, AFTER publish succeeds (see the
 * dropped_records comment above for why).
 *
 * @param ctx  Context with selected inputs
 * @return TL_OK on success (outputs built)
 *         TL_ENOMEM on allocation failure
 *         TL_EOVERFLOW if window span too large
 */
tl_status_t tl_compact_merge(tl_compact_ctx_t* ctx);

/**
 * Atomically swap the manifest to one that includes the compaction
 * outputs.
 *
 * The expensive manifest builder runs OFF-LOCK; writer_mu is then taken
 * only for an O(1) pointer swap protected by the seqlock so concurrent
 * readers see either the old or new manifest. If the live manifest no
 * longer matches the base used during merge (a concurrent flush
 * published in the meantime), TL_EBUSY is returned and the caller must
 * re-select and re-merge.
 *
 * @param ctx  Context with built outputs
 * @return TL_OK on success
 *         TL_EBUSY if manifest changed (caller should retry)
 *         TL_ENOMEM on allocation failure
 */
tl_status_t tl_compact_publish(tl_compact_ctx_t* ctx);

/**
 * Run select -> merge -> publish as one operation, retrying up to
 * max_retries times when publish returns TL_EBUSY.
 *
 * @param tl          Timelog instance
 * @param max_retries Max publish retries (>= 1)
 * @return TL_OK on success
 *         TL_EOF if no work needed
 *         TL_EBUSY if all retries exhausted
 *         TL_ENOMEM on allocation failure
 *         TL_EOVERFLOW if window span too large
 */
tl_status_t tl_compact_one(tl_timelog_t* tl, int max_retries);

#ifdef TL_TEST_HOOKS
/**
 * Test-only: exposes the delete-debt heuristic for unit testing.
 */
double tl_test_compute_delete_debt(const tl_timelog_t* tl,
                                   const tl_manifest_t* m);
#endif

#endif /* TL_COMPACTION_H */
