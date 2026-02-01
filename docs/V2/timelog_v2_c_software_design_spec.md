# Timelog V2 C Software Design Spec (Refined)

This document consolidates the current Timelog V2 design decisions from:
- docs/V2/timelog_v2_c_hld.md
- docs/V2/timelog_v2_lld_background_maintenance.md
- docs/V2/timelog_v2_lld_compaction_policy.md
- docs/V2/timelog_v2_lld_read_path.md
- docs/V2/timelog_v2_lld_storage_pages.md
- docs/V2/timelog_v2_lld_write_path.md

It defines the public API contracts, configuration, module boundaries, and
critical concurrency/publication protocols. It is written to be implementation
ready and consistent across all docs.

---

## 0. Scope

This spec covers:
- Public API surface and semantics.
- Configuration schema and defaults.
- High-level architecture and module boundaries.
- Concurrency model, snapshot isolation, and publication protocols.

It does not re-specify low-level layout details that are already defined in the
LLDs; those are referenced by name.

---

## 1. Non-negotiable invariants

- Timelog stores (ts:int64, handle:opaque) and does not interpret payloads.
- Range semantics are half-open: [t1, t2).
- Duplicates are preserved; tie order is deterministic by source priority/handle
  but not a public contract.
- All writes go to L0 first (memtable); segments are immutable after publish.
- L0 segments may overlap; L1 segments are non-overlapping by time window.
- Deletes are time-range tombstones; per-page masks remain a future optimization.
- Reads are snapshot-based: manifest + memview captured via seqlock protocol.
- Single writer externally; multiple readers supported.

---

## 2. Terminology

- L0: delta layer (memtable flush outputs), may overlap in time.
- L1: main layer (compaction outputs), non-overlapping by time window.
- Memtable: mutable ingest buffer for writes and tombstones.
- Memrun: sealed, immutable memtable snapshot queued for flush.
- Memview: immutable snapshot view of active + sealed memruns.
- Manifest: immutable catalog of L0/L1 segments published via atomic swap.
- Tombstones: coalesced half-open intervals [t1, t2) representing deletes.
- Window: fixed partition [window_start, window_end) for L1 non-overlap.

---

## 3. Architecture overview

1) L0 intake (memtable)
   - Writes and tombstones enter the memtable first.
   - In-order records (active_run) are always sorted by timestamp.
   - Out-of-order records append into ooo_head (may be unsorted during append).
   - OOO head is flushed into immutable sorted OOO runs at chunk threshold or seal.
   - OOO head is sorted off-lock during memview capture if still unsorted.

2) Flush to L0
   - Sealed memruns are flushed to immutable L0 segments.
   - L0 segments may overlap; tombstones are attached to L0 segments.

3) L1 compaction
   - L0 and overlapping L1 segments are merged into window-aligned L1 outputs.
   - L1 segments are tombstone-free and non-overlapping by window.

4) Read path
   - Snapshot acquisition pins manifest + memview.
   - Query planning prunes segments/pages, then merges iterators.
   - Tombstones are applied as a filter at read time.

5) Maintenance
   - Background worker (or manual step) performs flush + compaction.
   - Publication is atomic via manifest pointer swap and view_seq seqlock.

---

## 4. Concurrency and publication protocols

### 4.1 Locks and ordering

Locks:
- writer_mu: serializes manifest publication (flush/compaction).
- flush_mu: serializes flush build + publish (single flusher at a time).
- maint_mu: protects maintenance state and signaling.
- memtable.mu: protects sealed memrun queue.
- memtable.cond: backpressure waiters for sealed queue space (paired with memtable.mu).
- view_seq: atomic seqlock counter for snapshot consistency.

Lock ordering (strict):
maint_mu -> flush_mu -> writer_mu -> memtable.mu

### 4.2 Snapshot acquisition protocol

Snapshots must capture a consistent manifest + memview:
1) lock(writer_mu)
2) atomic_load view_seq (must be even)
3) acquire manifest ref
4) capture memview
5) atomic_load view_seq again
6) unlock(writer_mu)
7) if values differ or odd: retry

### 4.3 Flush publication protocol

1) Build phase (off-lock):
   - lock(flush_mu)
   - peek + pin oldest sealed memrun (memtable.mu)
   - build L0 segment from memrun
2) Publish phase (short critical section):
   - lock(writer_mu)
   - view_seq = atomic_fetch_add(+1) (odd)
   - swap manifest pointer to include new L0 segment
   - remove memrun from sealed queue (memtable.mu)
   - view_seq = atomic_fetch_add(+1) (even)
   - unlock(writer_mu)
   - unpin memrun, unlock(flush_mu)

Invariant: no snapshot sees both memrun and its flushed segment, and no
snapshot misses data.

### 4.4 Compaction publication protocol

1) Build L1 outputs off-lock (merge + tombstone folding).
2) lock(writer_mu)
3) view_seq = atomic_fetch_add(+1) (odd)
4) verify manifest unchanged (else retry up to 3 times)
5) swap manifest pointer
6) view_seq = atomic_fetch_add(+1) (even)
7) unlock(writer_mu)

### 4.5 Backpressure and fairness

- sealed_max_runs bounds the sealed memrun queue.
- In background mode, wait up to sealed_wait_ms before TL_EBUSY.
- Compaction fairness: after each flush, if L0 exceeds threshold, run one
  compaction step to prevent starvation.

---

## 5. Configuration (tl_config_t)

### 5.1 Enumerations

```c
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

typedef enum tl_log_level {
    TL_LOG_ERROR = 0,   /* Critical errors only */
    TL_LOG_WARN  = 1,   /* Warnings and errors */
    TL_LOG_INFO  = 2,   /* Informational messages */
    TL_LOG_DEBUG = 3,   /* Debug output */
    TL_LOG_TRACE = 4,   /* Verbose tracing */
    TL_LOG_NONE  = -1   /* Disable all logging */
} tl_log_level_t;
```

### 5.2 Configuration struct

```c
typedef struct tl_allocator {
    void* ctx;
    void* (*malloc_fn)(void* ctx, size_t n);
    void* (*calloc_fn)(void* ctx, size_t count, size_t size);
    void* (*realloc_fn)(void* ctx, void* p, size_t n);
    void  (*free_fn)(void* ctx, void* p);
} tl_allocator_t;

typedef void (*tl_log_fn)(void* ctx, int level, const char* msg);
typedef void (*tl_on_drop_fn)(void* ctx, tl_ts_t ts, tl_handle_t h);

/* Adaptive segmentation configuration (all zeros = disabled) */
typedef struct tl_adaptive_config {
    uint64_t    target_records;             /* 0 = disabled, >0 = target records per segment */
    tl_ts_t     min_window;                 /* Minimum window size (guardrail) */
    tl_ts_t     max_window;                 /* Maximum window size (guardrail) */
    uint32_t    hysteresis_pct;             /* Min % change to apply (e.g., 10) */
    tl_ts_t     window_quantum;             /* Snap to multiples (0 = no snapping) */
    double      alpha;                      /* EWMA smoothing factor [0.0, 1.0] */
    uint32_t    warmup_flushes;             /* Flushes before adapting */
    uint32_t    stale_flushes;              /* Flushes without update = stale (0 = infinite) */
    uint32_t    failure_backoff_threshold;  /* Failures before backoff */
    uint32_t    failure_backoff_pct;        /* % to grow window on backoff */
} tl_adaptive_config_t;

/* Note: For adaptive segmentation, consider setting stale_flushes > 0
 * to bound how long EWMA density can remain stale after long gaps. */

typedef struct tl_config {
    tl_time_unit_t  time_unit;

    size_t          target_page_bytes;      /* default: 64 KiB */
    size_t          memtable_max_bytes;     /* flush threshold, default: 1 MiB */
    size_t          ooo_budget_bytes;       /* 0 => memtable_max_bytes / 10 */

    size_t          sealed_max_runs;        /* default: 4 */
    uint32_t        sealed_wait_ms;         /* default: 100 */

    uint32_t        maintenance_wakeup_ms;  /* default: 100 (periodic wake interval) */

    size_t          max_delta_segments;     /* L0 bound, default: 8 */

    tl_ts_t         window_size;            /* 0 => default window (1 hour) */
    tl_ts_t         window_origin;          /* default: 0 */

    double          delete_debt_threshold;  /* 0.0 => disabled */
    size_t          compaction_target_bytes;/* optional cap, 0 = unlimited */
    uint32_t        max_compaction_inputs;  /* optional cap, 0 = unlimited */
    uint32_t        max_compaction_windows; /* default: 0 (unlimited greedy selection) */

    tl_adaptive_config_t adaptive;          /* Adaptive segmentation (zeros = disabled) */

    tl_maint_mode_t maintenance_mode;       /* default: TL_MAINT_BACKGROUND */

    tl_allocator_t  allocator;              /* optional; defaults to libc */
    tl_log_fn       log_fn;                 /* optional */
    void*           log_ctx;
    tl_log_level_t  log_level;              /* max log level, default: TL_LOG_INFO */

    tl_on_drop_fn   on_drop_handle;         /* physical delete callback */
    void*           on_drop_ctx;
} tl_config_t;

tl_status_t tl_config_init_defaults(tl_config_t* cfg);
```

Defaults are documented in tl_config_init_defaults().

Delete debt metric:
- delete_debt_ratio = tombstone_covered_span / window_size (window-scoped).
- If delete_debt_ratio >= delete_debt_threshold, compaction is requested.

on_drop_handle:
- Optional callback invoked when records are physically reclaimed during
  compaction (not on logical tombstone insert).
- May run on a background maintenance thread; keep it fast and thread-safe.

---

## 6. Public API contracts

### 6.1 Opaque types and values

```c
typedef struct tl_timelog  tl_timelog_t;
typedef struct tl_snapshot tl_snapshot_t;
typedef struct tl_iter     tl_iter_t;

typedef int64_t  tl_ts_t;
typedef uint64_t tl_handle_t;

typedef struct tl_record {
    tl_ts_t     ts;
    tl_handle_t handle;
} tl_record_t;
```

### 6.2 Status codes

```c
typedef enum tl_status {
    TL_OK        = 0,   /* Success */
    TL_EOF       = 1,   /* End of iteration / no work */
    TL_EINVAL    = 10,  /* Invalid argument */
    TL_ESTATE    = 20,  /* Invalid state */
    TL_EBUSY     = 21,  /* Resource busy (context-dependent) */
    TL_ENOMEM    = 30,  /* Out of memory (often retryable) */
    TL_EOVERFLOW = 31,  /* Arithmetic overflow */
    TL_EINTERNAL = 90   /* Internal error (bug or system failure) */
} tl_status_t;

const char* tl_strerror(tl_status_t s);
```

Error semantics (context-dependent):
- TL_EBUSY: For write APIs, indicates data accepted; do not retry. For tl_maint_start, retryable after short delay.
- TL_ENOMEM/TL_EOVERFLOW: Allocation/overflow failures; for writes, no data inserted, retryable after delay.
- TL_EINVAL/TL_ESTATE: Not retryable without caller fix.
- TL_EINTERNAL: Usually indicates a bug; may or may not be retryable.

### 6.3 Lifecycle

```c
tl_status_t tl_open(const tl_config_t* cfg, tl_timelog_t** out);
void        tl_close(tl_timelog_t* tl);
```

### 6.4 Write API (single writer externally)

```c
tl_status_t tl_append(tl_timelog_t* tl, tl_ts_t ts, tl_handle_t handle);

typedef enum tl_append_flags {
    TL_APPEND_NONE = 0,
    TL_APPEND_HINT_MOSTLY_IN_ORDER = 1 << 0,
    TL_APPEND_HINT_MOSTLY_ORDER = TL_APPEND_HINT_MOSTLY_IN_ORDER
} tl_append_flags_t;

tl_status_t tl_append_batch(
    tl_timelog_t* tl,
    const tl_record_t* records,
    size_t n,
    uint32_t flags
);

tl_status_t tl_delete_range(tl_timelog_t* tl, tl_ts_t t1, tl_ts_t t2);
tl_status_t tl_delete_before(tl_timelog_t* tl, tl_ts_t cutoff);

tl_status_t tl_flush(tl_timelog_t* tl);
tl_status_t tl_compact(tl_timelog_t* tl);
```

Semantics:
- Duplicates are allowed.
- Deletes are tombstones applied at read time.
- tl_delete_before is equivalent to delete [MIN_TS, cutoff).
- Write calls may return TL_EBUSY if sealed_max_runs is reached and
  maintenance cannot make progress within sealed_wait_ms.
- For writes, TL_EBUSY means data accepted; do not retry.
- For writes, TL_ENOMEM/TL_EOVERFLOW mean no data inserted (all-or-nothing).
- tl_flush performs a synchronous flush of active + sealed memruns and
  publishes the resulting L0 segments before returning.
- tl_compact requests compaction; actual work is performed by maintenance
  (background worker or tl_maint_step).

### 6.5 Snapshot API

```c
tl_status_t tl_snapshot_acquire(const tl_timelog_t* tl, tl_snapshot_t** out);
void        tl_snapshot_release(tl_snapshot_t* s);
```

Snapshots pin the manifest and a memview; all iterators are bound to the
snapshot lifetime.
Iterators must be destroyed before their snapshot is released. The caller
must release all snapshots before tl_close().

### 6.6 Read API (iterators)

```c
tl_status_t tl_iter_range(const tl_snapshot_t* snap, tl_ts_t t1, tl_ts_t t2, tl_iter_t** out);
tl_status_t tl_iter_since(const tl_snapshot_t* snap, tl_ts_t t1, tl_iter_t** out);
tl_status_t tl_iter_until(const tl_snapshot_t* snap, tl_ts_t t2, tl_iter_t** out);

tl_status_t tl_iter_equal(const tl_snapshot_t* snap, tl_ts_t ts, tl_iter_t** out);
tl_status_t tl_iter_point(const tl_snapshot_t* snap, tl_ts_t ts, tl_iter_t** out);

tl_status_t tl_iter_next(tl_iter_t* it, tl_record_t* out);
void        tl_iter_destroy(tl_iter_t* it);
```

Semantics:
- tl_iter_equal uses range semantics [ts, ts+1) and guards overflow.
- tl_iter_point uses direct equality to avoid overflow.
- tl_iter_since returns [t1, +inf).
- tl_iter_until returns [MIN_TS, t2).
- point/equal return all visible records with ts; duplicates preserved.
- If any tombstone covers ts in the snapshot, point/equal return empty.

Optional scan interface:

```c
typedef enum tl_scan_decision {
    TL_SCAN_CONTINUE = 0,
    TL_SCAN_STOP = 1
} tl_scan_decision_t;

typedef tl_scan_decision_t (*tl_scan_fn)(void* ctx, const tl_record_t* rec);

tl_status_t tl_scan_range(
    const tl_snapshot_t* snap,
    tl_ts_t t1,
    tl_ts_t t2,
    tl_scan_fn fn,
    void* ctx
);
```

### 6.7 Timestamp navigation

```c
tl_status_t tl_min_ts(const tl_snapshot_t* snap, tl_ts_t* out);
tl_status_t tl_max_ts(const tl_snapshot_t* snap, tl_ts_t* out);

tl_status_t tl_next_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out);
tl_status_t tl_prev_ts(const tl_snapshot_t* snap, tl_ts_t ts, tl_ts_t* out);
```

These reflect visible (non-deleted) records in the snapshot.

### 6.8 Maintenance control

```c
tl_status_t tl_maint_start(tl_timelog_t* tl);
tl_status_t tl_maint_stop(tl_timelog_t* tl);
tl_status_t tl_maint_step(tl_timelog_t* tl);
```

**tl_maint_start** (TL_MAINT_BACKGROUND mode only):
- Starts the background worker thread for flush and compaction.
- tl_open() does NOT start the worker; explicit call required.
- Returns:
  - TL_OK: Worker started (or already running - idempotent)
  - TL_EINVAL: tl is NULL
  - TL_ESTATE: Not open, or mode is not TL_MAINT_BACKGROUND
  - TL_EBUSY: Stop in progress (another thread is stopping) - retry later
  - TL_EINTERNAL: Thread creation failed

**tl_maint_stop**:
- Signals worker to exit and waits for termination.
- Safe to call regardless of mode (allows unconditional cleanup in tl_close).
- Returns:
  - TL_OK: Worker stopped, or already stopped, or stop in progress by another thread
  - TL_EINVAL: tl is NULL
  - TL_EINTERNAL: Thread join failed (severe error)
- **Important**: When another thread is stopping the worker, TL_OK does NOT
  guarantee the worker has fully exited - only that a stop is in progress.

**tl_maint_step** (TL_MAINT_DISABLED mode only):
- Performs one unit of maintenance work synchronously.
- Priority: flush one sealed memrun, else compact one step.
- Returns:
  - TL_OK: Work was performed
  - TL_EOF: No work pending
  - TL_EINVAL: tl is NULL
  - TL_ESTATE: Not open, or mode is not TL_MAINT_DISABLED
  - TL_ENOMEM: Build failed (inputs preserved, retry later)

### 6.9 Diagnostics

```c
typedef struct tl_stats {
    /* Storage layer metrics */
    uint64_t segments_l0;           /* L0 (delta) segments */
    uint64_t segments_l1;           /* L1 (main) segments */
    uint64_t pages_total;           /* Total pages across all segments */
    uint64_t records_estimate;      /* Estimated total records (may include deleted) */
    tl_ts_t  min_ts;                /* Minimum timestamp (TL_TS_MAX if empty) */
    tl_ts_t  max_ts;                /* Maximum timestamp (TL_TS_MIN if empty) */
    uint64_t tombstone_count;       /* Number of tombstone intervals */

    /* Memtable/delta layer metrics (snapshot-time values) */
    uint64_t memtable_active_records;  /* Records in active run buffer */
    uint64_t memtable_ooo_records;     /* Records in OOO head + runs */
    uint64_t memtable_sealed_runs;     /* Sealed memruns pending flush */

    /* Operational counters (cumulative since open) */
    uint64_t seals_total;              /* Total memtable seals performed */
    uint64_t ooo_budget_hits;          /* Times OOO budget was exceeded */
    uint64_t backpressure_waits;       /* Times writer blocked on sealed queue */
    uint64_t flushes_total;            /* Total flush operations completed */
    uint64_t compactions_total;        /* Total compaction operations completed */

    /* Adaptive segmentation metrics (only populated if adaptive.target_records > 0) */
    tl_ts_t  adaptive_window;          /* Current effective window size */
    double   adaptive_ewma_density;    /* EWMA density (records per time unit) */
    uint64_t adaptive_flush_count;     /* Flush count for density tracking */
    uint32_t adaptive_failures;        /* Consecutive compaction failures */
} tl_stats_t;

tl_status_t tl_stats(const tl_snapshot_t* snap, tl_stats_t* out);
tl_status_t tl_validate(const tl_snapshot_t* snap);
```

---

## 7. Internal module boundaries (conceptual)

Core:
- tl_timelog: top-level orchestrator (config, locks, API routing).

Storage:
- tl_page, tl_segment, tl_manifest (immutable storage + catalog).

Delta:
- tl_memtable (mutable ingest), tl_memview (immutable snapshot view),
  tl_flush (build L0 segments from memruns).

Deletes:
- tl_tombstones (interval sets + helpers).

Query:
- tl_snapshot (snapshot object), tl_plan (pruning), tl_iter/merge/filter.

Maintenance:
- tl_compaction_policy (selection + rules), tl_compactor (merge + publish),
  tl_scheduler (background worker and signaling).

Utilities:
- tl_atomic, tl_thread, tl_alloc, tl_log.

---

## 8. Storage and compaction invariants (summary)

- Pages and segments are immutable after publish.
- L0 segments may overlap; L1 segments are window-aligned and non-overlapping.
- L1 outputs are tombstone-free.
- Tombstone-only L0 segments are allowed to preserve residual intervals.
- Manifest version increments on each publish.
- Per-page row bitsets are reserved for future versions (defensive read support only).

---

## 9. Testing and validation hooks

- tl_validate checks invariants on a snapshot (debug builds).
- Maintenance and read-path correctness are validated against the LLDs.

---

This spec is the implementation-ready contract for Timelog V2. Any changes to
protocols or public APIs must be reflected here and in the LLDs to preserve
cross-document consistency.

