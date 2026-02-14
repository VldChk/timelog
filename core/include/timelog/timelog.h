#ifndef TIMELOG_H
#define TIMELOG_H

/**
 * @file timelog.h
 * @brief Timelog V1 Public API
 *
 * Timelog is an in-memory, time-indexed multimap optimized for:
 * - Fast time-range selection: [t1, t2), since(t), until(t)
 * - Fast time-based eviction: drop everything older than T
 * - Out-of-order ingestion via LSM-style L0 delta layer
 *
 * Key concepts:
 * - Timestamps are int64_t in a chosen resolution (s/ms/us/ns)
 * - Handles are opaque uint64_t tokens for payloads
 * - Duplicates (same timestamp) are allowed; tie order is unspecified
 * - Reads use snapshot isolation; writes require external single-writer coordination
 *
 * Timestamp Range Semantics:
 * - Timestamps span the FULL int64 range: TL_TS_MIN to TL_TS_MAX are valid data values
 * - TL_TS_MAX (INT64_MAX) is NOT a sentinel; records at TL_TS_MAX are fully supported
 * - All range APIs use half-open intervals [t1, t2) where t1 is inclusive, t2 exclusive
 * - Unbounded queries (since/until) use explicit API functions, not sentinel values
 *
 * Example - querying at timestamp boundaries:
 *   tl_iter_t* it;
 *   tl_iter_equal(snap, TL_TS_MAX, &it);   // All records at INT64_MAX
 *   tl_iter_point(snap, TL_TS_MAX, &it);   // First record at INT64_MAX
 *   tl_iter_since(snap, TL_TS_MAX, &it);   // Records from INT64_MAX to +inf
 */

#include <stdint.h>
#include <stddef.h>

#include "tl_export.h"

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * Thread-Safety Model (consolidated)
 *
 * Concurrency contract:
 * - Writes (tl_append*, tl_delete*, tl_flush, tl_compact):
 *   Single-writer required. Caller must serialize writes externally.
 *
 * - Reads (tl_snapshot_acquire, tl_iter_*, tl_scan_*, tl_min/max/next/prev_ts):
 *   Thread-safe. Multiple concurrent readers are supported via snapshots.
 *
 * - Snapshots:
 *   Iterators derived from a snapshot must be destroyed before releasing it.
 *
 * - Maintenance (tl_maint_start, tl_maint_stop):
 *   Thread-safe. See function docs for mode constraints and idempotency.
 *   tl_maint_step is NOT thread-safe (manual mode only).
 *
 * - Lifecycle (tl_close):
 *   NOT thread-safe. tl_close() must not race with any other API call on
 *   the same instance. Caller must ensure exclusive access during close.
 *===========================================================================*/

/*===========================================================================
 * Forward declarations (opaque types)
 *===========================================================================*/

typedef struct tl_timelog  tl_timelog_t;
typedef struct tl_snapshot tl_snapshot_t;
typedef struct tl_iter     tl_iter_t;

/*===========================================================================
 * Fundamental types
 *===========================================================================*/

/** Timestamp type (unit determined by configuration) */
typedef int64_t  tl_ts_t;

/**
 * Timestamp boundary constants.
 *
 * IMPORTANT: These are valid data values, NOT sentinels.
 * Records with ts == TL_TS_MAX are fully supported and can be:
 * - Appended via tl_append()
 * - Queried via tl_iter_equal(snap, TL_TS_MAX, &it)
 * - Deleted via tl_delete_range(): use a range ending before TL_TS_MAX.
 *   The public API does NOT expose unbounded delete-to-infinity; that is
 *   reserved for internal maintenance paths.
 *
 * NOTE: The half-open interval [TL_TS_MAX, TL_TS_MAX+1) cannot be expressed
 * in signed int64 arithmetic without overflow. For records at exactly TL_TS_MAX,
 * use either an unbounded tombstone or avoid storing critical data at this boundary.
 *
 * For unbounded queries, use the explicit API functions:
 * - tl_iter_since(snap, t1, &it)  for [t1, +inf)
 * - tl_iter_until(snap, t2, &it)  for (-inf, t2)
 */
#define TL_TS_MIN  INT64_MIN
#define TL_TS_MAX  INT64_MAX

/** Opaque payload handle */
typedef uint64_t tl_handle_t;

/** Record returned by reads and accepted by batch writes */
typedef struct tl_record {
    tl_ts_t     ts;
    tl_handle_t handle;
} tl_record_t;

/*===========================================================================
 * Status codes
 *
 * Error code semantics:
 * - TL_OK:        Operation succeeded
 * - TL_EOF:       End of iteration, or no work to do (not an error)
 * - TL_EINVAL:    Invalid argument (NULL pointer, invalid range t1>=t2,
 *                 invalid config value, out-of-bounds index)
 * - TL_ESTATE:    Invalid state (e.g., instance not open, wrong maint mode)
 * - TL_EBUSY:     Resource temporarily busy. Context-dependent:
 *                 - Write APIs (tl_append*, tl_delete*): Write WAS accepted,
 *                   but a seal/maintenance issue occurred:
 *                   (a) Sealed queue full (backpressure), OR
 *                   (b) Seal allocation failed (rare TL_ENOMEM remapped), OR
 *                   (c) OOO head flush failed after insert (runset allocation/backpressure).
 *                   DO NOT RETRY - would cause duplicates. In manual mode
 *                   call flush(); in background mode worker handles it.
 *                 - Maintenance/flush APIs (tl_flush, tl_maint_step):
 *                   Publish retry exhausted due to concurrent manifest change.
 *                   NO data loss; safe to retry after a short delay.
 *                 - tl_maint_start(): Stop in progress - retry later.
 * - TL_ENOMEM:    Memory allocation failed. For write APIs (tl_append*),
 *                 this means NO data was inserted - caller can rollback
 *                 (e.g., DECREF handles) and retry later.
 * - TL_EOVERFLOW: Arithmetic overflow (extreme timestamp calculations,
 *                 array size overflow). For write APIs, this means NO
 *                 data was inserted - caller can rollback and retry.
 * - TL_EINTERNAL: Internal error (thread creation failed, invariant violation
 *                 - should not occur in normal operation)
 *
 * Retryability guide:
 * - TL_EBUSY for writes: NOT retryable (data is already in log)
 * - TL_EBUSY for maintenance/flush: Retryable (publish conflict)
 * - TL_EBUSY for tl_maint_start: Retryable after short delay
 * - TL_ENOMEM/TL_EOVERFLOW for writes: Retryable (no data was inserted)
 * - TL_EINVAL, TL_ESTATE: Not retryable without caller fix
 * - TL_EINTERNAL: Usually indicates a bug; may or may not be retryable
 *===========================================================================*/

typedef enum tl_status {
    TL_OK        = 0,   /* Success */
    TL_EOF       = 1,   /* End of iteration / no work */
    TL_EINVAL    = 10,  /* Invalid argument */
    TL_ESTATE    = 20,  /* Invalid state */
    TL_EBUSY     = 21,  /* Resource busy - see status code docs for context */
    TL_ENOMEM    = 30,  /* Out of memory (often retryable) */
    TL_EOVERFLOW = 31,  /* Arithmetic overflow */
    TL_EINTERNAL = 90   /* Internal error (bug or system failure) */
} tl_status_t;

/** Get human-readable description of status code. */
TL_API const char* tl_strerror(tl_status_t s);

/*===========================================================================
 * Configuration
 *===========================================================================*/

typedef enum tl_time_unit {
    TL_TIME_S  = 0,
    TL_TIME_MS = 1,
    TL_TIME_US = 2,
    TL_TIME_NS = 3
} tl_time_unit_t;

typedef enum tl_maint_mode {
    TL_MAINT_DISABLED   = 0,
    TL_MAINT_BACKGROUND = 1
} tl_maint_mode_t;

/**
 * Log verbosity levels (passed to log_fn callback).
 * Use TL_LOG_NONE in config to disable all logging.
 */
typedef enum tl_log_level {
    TL_LOG_ERROR = 0,   /* Critical errors only */
    TL_LOG_WARN  = 1,   /* Warnings and errors */
    TL_LOG_INFO  = 2,   /* Informational messages */
    TL_LOG_DEBUG = 3,   /* Debug output */
    TL_LOG_TRACE = 4,   /* Verbose tracing */
    TL_LOG_NONE  = -1   /* Disable all logging */
} tl_log_level_t;

/** Custom allocator interface */
typedef struct tl_allocator {
    void* ctx;
    void* (*malloc_fn)(void* ctx, size_t size);
    void* (*calloc_fn)(void* ctx, size_t count, size_t size);
    void* (*realloc_fn)(void* ctx, void* ptr, size_t new_size);
    void  (*free_fn)(void* ctx, void* ptr);
} tl_allocator_t;

/** Log callback */
typedef void (*tl_log_fn)(void* ctx, int level, const char* msg);

/**
 * Handle drop callback (invoked after physical deletes during compaction
 * and during flush when tombstones remove sealed records).
 *
 * WHEN INVOKED:
 * - Only for records PHYSICALLY dropped during compaction or flush
 *   (tombstone application)
 * - NOT called for logical tombstone insertion (tl_delete_range/tl_delete_before)
 * - NOT called during tl_close() - caller retains ownership of all remaining handles
 * - Callbacks are DEFERRED until after successful manifest publish, ensuring
 *   that only truly committed drops trigger the callback
 *
 * SNAPSHOT SAFETY (read carefully):
 * This callback indicates a record is being RETIRED from the newest manifest,
 * NOT that it's safe to free immediately. Existing snapshots acquired before
 * compaction may still reference this handle until those snapshots are released.
 * CONTRACT:
 * - Called ONLY when a record is physically deleted during compaction or flush
 *   (tombstone coverage).
 * - Called ONLY after successful manifest publish (never speculatively).
 * - NOT called by tl_close() or segment release.
 * - Handles not covered by tombstones are never reported here; callers
 *   must track them if cleanup-at-close is required.
 *
 * THREADING:
 * - May be called from the maintenance worker thread (background mode)
 * - May be called from the thread invoking tl_maint_step(), tl_flush(),
 *   or any API path that publishes physical drops
 *
 * Treat this as a "retire" notification, not a "free now" signal.
 *
 * SAFE usage patterns:
 * - Epoch-based reclamation: track callback timestamp, defer free until all
 *   snapshots older than that epoch are released
 * - Reference counting: callback decrements refcount, actual free when zero
 * - Grace period: callback adds to deferred-free queue with timestamp
 *
 * UNSAFE usage (can cause use-after-free):
 * - Immediately freeing user payload in this callback
 *
 * The callback is invoked after manifest publish completes, without holding
 * timelog internal locks. It must not call back into timelog APIs.
 * If compaction/flush/seal fails before publish/commit, callbacks from that
 * attempt are not emitted.
 *
 * LIFETIME (H-05 contract clarification):
 * - Caller retains ownership of handles not covered by tombstones
 * - At tl_close(), records in the log are NOT notified via this callback
 * - If cleanup-at-close is needed, caller must track inserted handles independently
 *
 * @param ctx    User-provided context (from tl_config_t.on_drop_ctx)
 * @param ts     Timestamp of the dropped record
 * @param handle Handle of the dropped record
 */
typedef void (*tl_on_drop_fn)(void* ctx, tl_ts_t ts, tl_handle_t handle);

/**
 * Adaptive segmentation configuration.
 * Embedded in tl_config_t as `tl_config_t.adaptive`.
 * All zeros = disabled (preserves existing behavior).
 *
 * Adaptive segmentation dynamically adjusts compaction window sizes based on
 * data density to maintain approximately constant segment sizes.
 *
 * Field naming: Uses short names inside nested struct.
 * LLD's `adaptive_target_records` == `config.adaptive.target_records`
 */
typedef struct tl_adaptive_config {
    uint64_t    target_records;             /**< 0 = disabled, >0 = target records per segment */
    tl_ts_t     min_window;                 /**< Minimum window size (guardrail) */
    tl_ts_t     max_window;                 /**< Maximum window size (guardrail) */
    uint32_t    hysteresis_pct;             /**< Min % change to apply (e.g., 10) */
    tl_ts_t     window_quantum;             /**< Snap to multiples (0 = no snapping) */
    double      alpha;                      /**< EWMA smoothing factor [0.0, 1.0] */
    uint32_t    warmup_flushes;             /**< Flushes before adapting */
    uint32_t    stale_flushes;              /**< Flushes without update = stale (0 = infinite) */
    uint32_t    failure_backoff_threshold;  /**< Failures before backoff */
    uint32_t    failure_backoff_pct;        /**< % to grow window on backoff */
} tl_adaptive_config_t;

/** Configuration for tl_open() */
typedef struct tl_config {
    tl_time_unit_t  time_unit;

    size_t          target_page_bytes;      /* 0 => default (64 KiB) */
    size_t          memtable_max_bytes;     /* 0 => default (1 MiB) */
    size_t          ooo_budget_bytes;       /* 0 => memtable_max_bytes / 10 */

    size_t          sealed_max_runs;        /* 0 => default (4) */
    uint32_t        sealed_wait_ms;         /* default: 100ms. Backpressure wait timeout.
                                             * NOTE: 0 = no waiting (immediate TL_EBUSY).
                                             * Unlike other fields, 0 is NOT "use default". */

    /* Maintenance timing */
    uint32_t        maintenance_wakeup_ms;  /* 0 => default (100ms). Periodic wake interval. */

    size_t          max_delta_segments;     /* 0 => default (8). L0 segment bound. */

    tl_ts_t         window_size;            /* 0 => default window (1 hour) */
    tl_ts_t         window_origin;          /* default: 0 */

    double          delete_debt_threshold;  /* 0.0 => disabled */
    size_t          compaction_target_bytes;/* optional cap */
    uint32_t        max_compaction_inputs;  /* optional cap */
    uint32_t        max_compaction_windows; /* default: 0 (unlimited) */

    tl_adaptive_config_t adaptive;          /* Adaptive segmentation (zeros = disabled) */

    tl_maint_mode_t maintenance_mode;

    tl_allocator_t  allocator;
    tl_log_fn       log_fn;
    void*           log_ctx;
    tl_log_level_t  log_level;              /* max log level (default: TL_LOG_INFO) */
    tl_on_drop_fn   on_drop_handle;         /* physical delete callback */
    void*           on_drop_ctx;
} tl_config_t;

TL_API tl_status_t tl_config_init_defaults(tl_config_t* cfg);

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Create a new timelog instance.
 *
 * @param cfg Configuration, or NULL to use defaults from tl_config_init_defaults().
 *            The config is copied; it need not persist after this call.
 * @param out Output pointer for new instance (must not be NULL)
 * @return TL_OK on success; TL_EINVAL if out is NULL or config is invalid;
 *         TL_ENOMEM on allocation failure; TL_EINTERNAL if worker thread fails
 *
 * Maintenance:
 * - When maintenance_mode == TL_MAINT_BACKGROUND (the default), the background
 *   maintenance worker is automatically started during tl_open(). No separate
 *   call to tl_maint_start() is needed for normal operation.
 * - When maintenance_mode == TL_MAINT_DISABLED, no worker is started and the
 *   caller must call tl_flush() and tl_maint_step() manually.
 *
 * If a log_fn callback is configured, informational messages may be logged
 * during open (and close) operations.
 */
TL_API tl_status_t tl_open(const tl_config_t* cfg, tl_timelog_t** out);

/**
 * Destroy a timelog instance and release all resources.
 *
 * @param tl Instance to close (NULL is safe)
 *
 * DATA LOSS WARNING:
 * tl_close() does NOT flush/materialize unflushed records from the memtable.
 * Any records appended after the last tl_flush() call will be dropped.
 * To materialize all data before close:
 *   tl_flush(tl);   // Flush remaining memtable records
 *   tl_close(tl);   // Now safe to close
 *
 * Preconditions:
 * - All snapshots and iterators must be released before calling tl_close()
 *   (tl_close reads snapshot counters without locking).
 * - Background maintenance (if enabled) will be stopped automatically
 *
 * Thread Safety:
 * - tl_close() must NOT race with any other API call on the same instance.
 *   The caller must ensure no other thread is calling tl_append, tl_flush,
 *   tl_snapshot_acquire, tl_maint_start, tl_maint_stop, or any other API
 *   while tl_close() is executing.
 * - This is consistent with the single-writer model: external coordination
 *   is required for lifecycle transitions.
 * - If worker join fails (TL_EINTERNAL from internal tl_maint_stop), close
 *   will abort in debug builds to prevent memory corruption.
 */
TL_API void tl_close(tl_timelog_t* tl);

/*===========================================================================
 * Write API (single-writer externally required)
 *===========================================================================*/

/*
 * Backpressure and Error Semantics:
 *
 * TL_EBUSY (backpressure):
 * - Write calls may return TL_EBUSY when:
 *   (a) Sealed queue full (sealed_max_runs reached, maintenance can't keep up)
 *   (b) Seal allocation failed (rare - memrun struct allocation failed)
 *   (c) OOO head flush failed after insert (runset allocation/backpressure)
 * - CRITICAL: TL_EBUSY means ALL data WAS accepted. DO NOT RETRY.
 *   Retrying would create duplicate records. In manual mode, call tl_flush()
 *   to relieve pressure. In background mode, wait for maintenance to catch up.
 *
 * TL_ENOMEM / TL_EOVERFLOW (true failures):
 * - These mean NO data was inserted - operation has all-or-nothing semantics.
 * - For tl_append_batch: either ALL records were inserted, or NONE were.
 * - Caller can safely rollback (e.g., DECREF all handles) and retry later.
 *
 * Summary: TL_EBUSY = data accepted (don't retry), other errors = no data (can retry).
 */

/** Append flags */
typedef enum tl_append_flags {
    TL_APPEND_NONE               = 0,
    TL_APPEND_HINT_MOSTLY_IN_ORDER = 1 << 0,
    TL_APPEND_HINT_MOSTLY_ORDER  = TL_APPEND_HINT_MOSTLY_IN_ORDER /* alias */
} tl_append_flags_t;

TL_API tl_status_t tl_append(tl_timelog_t* tl, tl_ts_t ts, tl_handle_t handle);

/*
 * Batch sequencing contract:
 * a single internal operation sequence is assigned to the whole batch.
 */
TL_API tl_status_t tl_append_batch(tl_timelog_t* tl, const tl_record_t* records,
                                   size_t n, uint32_t flags);

/*
 * Delete range [t1, t2). Unbounded delete-to-infinity is not exposed publicly.
 * Note: half-open ranges cannot represent a single-point delete at TL_TS_MAX.
 */
TL_API tl_status_t tl_delete_range(tl_timelog_t* tl, tl_ts_t t1, tl_ts_t t2);

/* Delete [MIN_TS, cutoff) */
TL_API tl_status_t tl_delete_before(tl_timelog_t* tl, tl_ts_t cutoff);

/**
 * Synchronous flush of active + sealed memruns; publishes L0 before return.
 *
 * Returns:
 * - TL_OK: All flushable data published
 * - TL_EBUSY: Publish retries exhausted due to concurrent manifest change
 *             (no data loss; safe to retry)
 * - TL_ENOMEM/TL_EOVERFLOW: Build failed (inputs preserved; retry later)
 * - TL_ESTATE/TL_EINVAL: Invalid state/args
 */
TL_API tl_status_t tl_flush(tl_timelog_t* tl);

/* Request compaction; actual work performed by maintenance. */
TL_API tl_status_t tl_compact(tl_timelog_t* tl);

/*===========================================================================
 * Snapshot API (read isolation)
 *===========================================================================*/

TL_API tl_status_t tl_snapshot_acquire(const tl_timelog_t* tl, tl_snapshot_t** out);

/* Release snapshot; all iterators derived from it must be destroyed first. */
TL_API void tl_snapshot_release(tl_snapshot_t* s);

/*===========================================================================
 * Read API (iterators)
 *===========================================================================*/

/* Iterate records in [t1, t2). */
TL_API tl_status_t tl_iter_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                                 tl_iter_t** out);

/* Iterate records in [t1, +inf). */
TL_API tl_status_t tl_iter_since(const tl_snapshot_t* snap, tl_ts_t t1,
                                 tl_iter_t** out);

/* Iterate records in [MIN_TS, t2). */
TL_API tl_status_t tl_iter_until(const tl_snapshot_t* snap, tl_ts_t t2,
                                 tl_iter_t** out);

/*
 * Iterate all records with timestamp == ts (range form with overflow guard).
 * A row is filtered only when max_tombstone_seq(ts) > row_watermark.
 */
TL_API tl_status_t tl_iter_equal(const tl_snapshot_t* snap, tl_ts_t ts,
                                 tl_iter_t** out);

/**
 * Create an iterator over all records with timestamp == ts.
 *
 * Duplicates are returned; tie order is unspecified.
 * A row is filtered only when max_tombstone_seq(ts) > row_watermark.
 */
TL_API tl_status_t tl_iter_point(const tl_snapshot_t* snap, tl_ts_t ts,
                                 tl_iter_t** out);

TL_API tl_status_t tl_iter_next(tl_iter_t* it, tl_record_t* out);

TL_API void tl_iter_destroy(tl_iter_t* it);

/*===========================================================================
 * Scan API (visitor pattern)
 *===========================================================================*/

typedef enum tl_scan_decision {
    TL_SCAN_CONTINUE = 0,
    TL_SCAN_STOP     = 1
} tl_scan_decision_t;

typedef tl_scan_decision_t (*tl_scan_fn)(void* ctx, const tl_record_t* rec);

TL_API tl_status_t tl_scan_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                                 tl_scan_fn fn, void* ctx);

/*===========================================================================
 * Count API
 *===========================================================================*/

/* Count visible records in full snapshot range [MIN_TS, +inf). */
TL_API tl_status_t tl_count(const tl_timelog_t* tl, uint64_t* out);

/* Count visible records in [t1, t2). */
TL_API tl_status_t tl_count_range(const tl_timelog_t* tl, tl_ts_t t1, tl_ts_t t2,
                                  uint64_t* out);

/**
 * Count visible records in a snapshot range [t1, t2) or [t1, +inf).
 *
 * @param snap         Snapshot to query
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ignored if t2_unbounded
 * @param t2_unbounded If nonzero, treat range as [t1, +inf)
 * @param out          Output count
 * @return TL_OK on success
 */
TL_API tl_status_t tl_snapshot_count_range(const tl_snapshot_t* snap,
                                            tl_ts_t t1, tl_ts_t t2,
                                            int t2_unbounded,
                                            uint64_t* out);

/*===========================================================================
 * Timestamp navigation
 *
 * Convenience functions for finding min/max timestamps and navigating between
 * adjacent timestamps. These are intended for diagnostic/debugging use cases.
 *
 * **Performance note**: Forward navigation (tl_min_ts, tl_next_ts) is efficient
 * at O(K log P), but backward navigation (tl_max_ts, tl_prev_ts) requires full
 * dataset scan at O(N) due to LSM architecture. For performance-critical paths,
 * use iterators directly or maintain your own bounds tracking.
 *
 * Where: K = component count, P = pages/component, N = total visible records.
 *===========================================================================*/

/**
 * Get the minimum timestamp in the snapshot (first visible record).
 *
 * @param snap Snapshot to query
 * @param out  Output parameter for minimum timestamp
 * @return TL_OK   Success, *out contains minimum timestamp
 *         TL_EOF  No visible records (empty or all deleted)
 *         TL_EINVAL  snap or out is NULL
 *         TL_ENOMEM  Iterator allocation failed
 *
 * Complexity: O(K log P) typical - creates iterator and fetches first record.
 * However, if tombstones delete early records, the function must scan past
 * them to find the first VISIBLE record, degrading to O(N) in tombstone-heavy
 * edge cases. For truly performance-critical paths with heavy deletes,
 * consider maintaining your own min tracker.
 */
TL_API tl_status_t tl_min_ts(const tl_snapshot_t* snap, tl_ts_t* out);

/**
 * Get the maximum timestamp in the snapshot (last visible record).
 *
 * @param snap Snapshot to query
 * @param out  Output parameter for maximum timestamp
 * @return TL_OK   Success, *out contains maximum timestamp
 *         TL_EOF  No visible records (empty or all deleted)
 *         TL_EINVAL  snap or out is NULL
 *         TL_ENOMEM  Iterator allocation failed
 *
 * **WARNING: O(N) COMPLEXITY** - This function scans ALL visible records
 * because LSM iterators only support forward traversal. For large datasets,
 * consider maintaining your own max tracker during append operations.
 */
TL_API tl_status_t tl_max_ts(const tl_snapshot_t* snap, tl_ts_t* out);

/**
 * Find the next timestamp strictly greater than the given timestamp.
 *
 * @param snap Snapshot to query
 * @param ts   Reference timestamp
 * @param out  Output parameter for next timestamp
 * @return TL_OK   Success, *out contains next timestamp after ts
 *         TL_EOF  No visible records after ts
 *         TL_EINVAL  snap or out is NULL
 *         TL_ENOMEM  Iterator allocation failed
 *
 * Complexity: O(K log P) typical - creates iterator at ts+1 and fetches first.
 * However, if tombstones delete records after ts, the function must scan past
 * them to find the first VISIBLE record, degrading to O(N) in tombstone-heavy
 * edge cases.
 *
 * Note: If ts == TL_TS_MAX, returns TL_EOF (no overflow).
 */
TL_API tl_status_t tl_next_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out);

/**
 * Find the previous timestamp strictly less than the given timestamp.
 *
 * @param snap Snapshot to query
 * @param ts   Reference timestamp
 * @param out  Output parameter for previous timestamp
 * @return TL_OK   Success, *out contains previous timestamp before ts
 *         TL_EOF  No visible records before ts
 *         TL_EINVAL  snap or out is NULL
 *         TL_ENOMEM  Iterator allocation failed
 *
 * **WARNING: O(N) COMPLEXITY** - This function scans ALL visible records
 * in [TL_TS_MIN, ts) to find the last one, because LSM iterators only
 * support forward traversal. For large datasets, consider using iterators
 * directly or implementing reverse navigation in your application layer.
 *
 * Note: If ts == TL_TS_MIN, returns TL_EOF (no underflow).
 */
TL_API tl_status_t tl_prev_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out);

/*===========================================================================
 * Maintenance control
 *===========================================================================*/

/**
 * Start the background maintenance worker thread.
 *
 * In TL_MAINT_BACKGROUND mode, the worker is automatically started by
 * tl_open(), so this function is typically only needed to restart the
 * worker after calling tl_maint_stop().
 *
 * @param tl Timelog instance
 * @return TL_OK       Worker started successfully (or already running)
 *         TL_EINVAL   tl is NULL
 *         TL_ESTATE   Not open, or mode is not TL_MAINT_BACKGROUND
 *         TL_EBUSY    Stop in progress (STOPPING state) - retry later
 *         TL_EINTERNAL Thread creation failed
 *
 * Thread Safety: Safe to call from any thread.
 * Idempotency: If already running, returns TL_OK without action.
 */
TL_API tl_status_t tl_maint_start(tl_timelog_t* tl);

/**
 * Stop the background maintenance worker thread.
 *
 * Signals the worker to exit and blocks until it terminates.
 * Safe to call regardless of mode (allows cleanup in tl_close).
 *
 * @param tl Timelog instance
 * @return TL_OK       Worker stopped (or already stopped, or stop in progress)
 *         TL_EINVAL   tl is NULL
 *         TL_EINTERNAL Thread join failed (severe error)
 *
 * Thread Safety: Safe to call from any thread.
 * Idempotency: Returns TL_OK if already stopped or if another thread is
 *              stopping. In the latter case, TL_OK does NOT guarantee the
 *              worker has fully exited - only that a stop is in progress.
 *
 * @warning Do not call from the worker thread itself (deadlock on join).
 */
TL_API tl_status_t tl_maint_stop(tl_timelog_t* tl);

/**
 * Perform one unit of maintenance work (manual mode only).
 *
 * Priority: flush one sealed memrun, else compact one step.
 *
 * @param tl Timelog instance
 * @return TL_OK       Work was performed
 *         TL_EOF      No work to do
 *         TL_EINVAL   tl is NULL
 *         TL_ESTATE   Not open, or mode is not TL_MAINT_DISABLED
 *         TL_ENOMEM   Build failed (inputs preserved, retry later)
 *         TL_EBUSY    Publish retries exhausted (retry later)
 *
 * Thread Safety: NOT thread-safe. Caller must ensure single-threaded access.
 */
TL_API tl_status_t tl_maint_step(tl_timelog_t* tl);

/*===========================================================================
 * Statistics and diagnostics
 *===========================================================================*/

typedef struct tl_stats {
    /* Storage layer metrics */
    uint64_t segments_l0;       /* L0 (delta) segments */
    uint64_t segments_l1;       /* L1 (main) segments */
    uint64_t pages_total;       /* Total pages across all segments */
    uint64_t records_estimate;  /* Snapshot-time tombstone-aware visible record count */
    tl_ts_t  min_ts;            /* Minimum timestamp (TL_TS_MAX if empty) */
    tl_ts_t  max_ts;            /* Maximum timestamp (TL_TS_MIN if empty) */
    uint64_t tombstone_count;   /* Number of tombstone intervals */

    /* Memtable/delta layer metrics (snapshot-time values) */
    uint64_t memtable_active_records;  /* Records in active run buffer */
    uint64_t memtable_ooo_records;     /* Records in OOO buffer */
    uint64_t memtable_sealed_runs;     /* Sealed memruns pending flush */

    /* Operational counters (cumulative since open) */
    uint64_t seals_total;              /* Total memtable seals performed */
    uint64_t ooo_budget_hits;          /* Times OOO budget was exceeded */
    uint64_t backpressure_waits;       /* Times writer blocked on sealed queue */
    uint64_t flushes_total;            /* Total flush operations completed */
    uint64_t compactions_total;        /* Total compaction operations completed */
    uint64_t compaction_retries;       /* Compaction publish retries */
    uint64_t compaction_publish_ebusy; /* Publish attempts returning TL_EBUSY */
    /* Compaction selection observability (M-23) */
    uint64_t compaction_select_calls;      /* Selection attempts */
    uint64_t compaction_select_l0_inputs;  /* Total L0 inputs selected */
    uint64_t compaction_select_l1_inputs;  /* Total L1 inputs selected */
    uint64_t compaction_select_no_work;    /* Selections with no L0s */

    /* Adaptive segmentation metrics (V-Next)
     * Only populated when adaptive.target_records > 0 in config. */
    tl_ts_t  adaptive_window;          /* Current effective window size */
    double   adaptive_ewma_density;    /* EWMA density (records per time unit) */
    uint64_t adaptive_flush_count;     /* Flush count for density tracking */
    uint32_t adaptive_failures;        /* Consecutive compaction failures */
} tl_stats_t;

TL_API tl_status_t tl_stats(const tl_snapshot_t* snap, tl_stats_t* out);

TL_API tl_status_t tl_validate(const tl_snapshot_t* snap);

#ifdef __cplusplus
}
#endif

#endif /* TIMELOG_H */
