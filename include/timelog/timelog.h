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
 */

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

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

/** Opaque payload handle */
typedef uint64_t tl_handle_t;

/** Record returned by reads and accepted by batch writes */
typedef struct tl_record {
    tl_ts_t     ts;
    tl_handle_t handle;
} tl_record_t;

/*===========================================================================
 * Status codes
 *===========================================================================*/

typedef enum tl_status {
    TL_OK        = 0,
    TL_EOF       = 1,
    TL_EINVAL    = 10,
    TL_ESTATE    = 20,
    TL_EBUSY     = 21,
    TL_ENOMEM    = 30,
    TL_EOVERFLOW = 31,  /* Arithmetic overflow (extreme timestamp values) */
    TL_EINTERNAL = 90
} tl_status_t;

const char* tl_strerror(tl_status_t s);

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

/** Handle drop callback (for payload reclamation on physical delete) */
typedef void (*tl_on_drop_fn)(void* ctx, tl_ts_t ts, tl_handle_t handle);

/** Configuration for tl_open() */
typedef struct tl_config {
    tl_time_unit_t  time_unit;

    size_t          target_page_bytes;
    size_t          memtable_max_bytes;
    size_t          ooo_budget_bytes;       /* 0 => memtable_max_bytes / 10 */

    size_t          sealed_max_runs;        /* default: 4 */
    uint32_t        sealed_wait_ms;         /* default: 100 */

    size_t          max_delta_segments;     /* L0 bound */

    tl_ts_t         window_size;            /* 0 => default window (1 hour) */
    tl_ts_t         window_origin;          /* default: 0 */

    double          delete_debt_threshold;  /* 0.0 => disabled */
    size_t          compaction_target_bytes;/* optional cap */
    uint32_t        max_compaction_inputs;  /* optional cap */
    uint32_t        max_compaction_windows; /* optional cap */

    tl_maint_mode_t maintenance_mode;

    tl_allocator_t  allocator;
    tl_log_fn       log_fn;
    void*           log_ctx;
    tl_on_drop_fn   on_drop_handle;         /* physical delete callback */
    void*           on_drop_ctx;
} tl_config_t;

tl_status_t tl_config_init_defaults(tl_config_t* cfg);

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
 *         TL_ENOMEM on allocation failure
 *
 * If a log_fn callback is configured, informational messages may be logged
 * during open (and close) operations.
 */
tl_status_t tl_open(const tl_config_t* cfg, tl_timelog_t** out);

/**
 * Destroy a timelog instance and release all resources.
 *
 * @param tl Instance to close (NULL is safe)
 *
 * The caller must ensure all snapshots and iterators are released before
 * calling tl_close().
 */
void tl_close(tl_timelog_t* tl);

/*===========================================================================
 * Write API (single-writer externally required)
 *===========================================================================*/

/*
 * Backpressure:
 * - Write calls may return TL_EBUSY if sealed_max_runs is reached and
 *   maintenance cannot make progress within sealed_wait_ms.
 */

/** Append flags */
typedef enum tl_append_flags {
    TL_APPEND_NONE               = 0,
    TL_APPEND_HINT_MOSTLY_IN_ORDER = 1 << 0,
    TL_APPEND_HINT_MOSTLY_ORDER  = TL_APPEND_HINT_MOSTLY_IN_ORDER /* alias */
} tl_append_flags_t;

tl_status_t tl_append(tl_timelog_t* tl, tl_ts_t ts, tl_handle_t handle);

tl_status_t tl_append_batch(tl_timelog_t* tl, const tl_record_t* records,
                            size_t n, uint32_t flags);

tl_status_t tl_delete_range(tl_timelog_t* tl, tl_ts_t t1, tl_ts_t t2);

/* Delete [MIN_TS, cutoff) */
tl_status_t tl_delete_before(tl_timelog_t* tl, tl_ts_t cutoff);

/* Synchronous flush of active + sealed memruns; publishes L0 before return. */
tl_status_t tl_flush(tl_timelog_t* tl);

/* Request compaction; actual work performed by maintenance. */
tl_status_t tl_compact(tl_timelog_t* tl);

/*===========================================================================
 * Snapshot API (read isolation)
 *===========================================================================*/

tl_status_t tl_snapshot_acquire(const tl_timelog_t* tl, tl_snapshot_t** out);

/* Release snapshot; all iterators derived from it must be destroyed first. */
void tl_snapshot_release(tl_snapshot_t* s);

/*===========================================================================
 * Read API (iterators)
 *===========================================================================*/

/* Iterate records in [t1, t2). */
tl_status_t tl_iter_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                          tl_iter_t** out);

/* Iterate records in [t1, +inf). */
tl_status_t tl_iter_since(const tl_snapshot_t* snap, tl_ts_t t1,
                          tl_iter_t** out);

/* Iterate records in [MIN_TS, t2). */
tl_status_t tl_iter_until(const tl_snapshot_t* snap, tl_ts_t t2,
                          tl_iter_t** out);

/*
 * Iterate all records with timestamp == ts (range form with overflow guard).
 * If any tombstone in the snapshot covers ts, the iterator is empty.
 */
tl_status_t tl_iter_equal(const tl_snapshot_t* snap, tl_ts_t ts,
                          tl_iter_t** out);

/**
 * Create an iterator over all records with timestamp == ts.
 *
 * Duplicates are returned; tie order is unspecified. If any tombstone in the
 * snapshot covers ts, the iterator is empty.
 */
tl_status_t tl_iter_point(const tl_snapshot_t* snap, tl_ts_t ts,
                          tl_iter_t** out);

tl_status_t tl_iter_next(tl_iter_t* it, tl_record_t* out);

void tl_iter_destroy(tl_iter_t* it);

/*===========================================================================
 * Scan API (visitor pattern)
 *===========================================================================*/

typedef enum tl_scan_decision {
    TL_SCAN_CONTINUE = 0,
    TL_SCAN_STOP     = 1
} tl_scan_decision_t;

typedef tl_scan_decision_t (*tl_scan_fn)(void* ctx, const tl_record_t* rec);

tl_status_t tl_scan_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2,
                          tl_scan_fn fn, void* ctx);

/*===========================================================================
 * Timestamp navigation
 *===========================================================================*/

tl_status_t tl_min_ts(const tl_snapshot_t* snap, tl_ts_t* out);

tl_status_t tl_max_ts(const tl_snapshot_t* snap, tl_ts_t* out);

tl_status_t tl_next_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out);

tl_status_t tl_prev_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out);

/*===========================================================================
 * Maintenance control
 *===========================================================================*/

/*
 * Background mode:
 * - tl_maint_start must be called to start the worker (tl_open does not start
 *   threads).
 */
tl_status_t tl_maint_start(tl_timelog_t* tl);

tl_status_t tl_maint_stop(tl_timelog_t* tl);

/* Manual mode: performs one unit of work, returns TL_EOF if idle. */
tl_status_t tl_maint_step(tl_timelog_t* tl);

/*===========================================================================
 * Statistics and diagnostics
 *===========================================================================*/

typedef struct tl_stats {
    uint64_t segments_l0;
    uint64_t segments_l1;
    uint64_t pages_total;
    uint64_t records_estimate;
    tl_ts_t  min_ts;
    tl_ts_t  max_ts;
    uint64_t tombstone_count;
} tl_stats_t;

tl_status_t tl_stats(const tl_snapshot_t* snap, tl_stats_t* out);

tl_status_t tl_validate(const tl_snapshot_t* snap);

#ifdef __cplusplus
}
#endif

#endif /* TIMELOG_H */
