# Python API

Source of truth for Python behavior: `python/timelog/__init__.py`.

## Core Class

- `Timelog`
- Exceptions: `TimelogError`, `TimelogBusyError`
- Iterator/span types: `TimelogIter`, `PageSpan`, `PageSpanIter`, `PageSpanObjectsView`

## Runtime Support

- Regular CPython 3.12-3.14 builds are supported.
- Isolated subinterpreters with a per-interpreter GIL are supported (Layer A complete).
- Free-threaded CPython 3.14t (Py_GIL_DISABLED=1) is supported (Layer B complete).
  The extension declares `Py_mod_gil = Py_MOD_GIL_NOT_USED` and synchronizes all
  mutable state with per-object critical sections, an explicit live_lock, and
  atomic refcounts on the engine/handle contexts and the core pagespan owner.
- The public buffer/analytics surface is intentionally narrow: `bulk_append()`
  consumes contiguous native-endian int64 timestamp buffers, and
  `PageSpan.timestamps` exposes a read-only memoryview.

## Lifecycle

- `Timelog(**kwargs)`
- `reopen(...)`
- `configure(...)` (alias for `reopen`)
- `close()` for deterministic explicit cleanup
- Context manager is supported, but optional.

`Contract`
- `close()` discards all data; Timelog is in-memory and nothing survives close.
  `flush()` matters while the log is open: it materializes pending writes into
  immutable segments so zero-copy `views()` readers can see them.
- `close()` can raise while active iterators, `PageSpan` objects, memoryview exports, or other snapshot pins are still alive. Release those readers first, then close again.
- Lifecycle calls (`close()`, `reopen()`, `configure()`) are not synchronization barriers. Serialize them externally against append/query users of the same instance.
- Non-context-manager usage (`log = Timelog()`) is supported. If explicit `close()` is omitted, the finalizer auto-closes on collection as a best-effort cleanup path.
- Live `Timelog` objects keep using their originating module state across manual reload/reimport of `timelog._timelog`.

## Write API

- `append(obj)`
- `append(obj, ts=...)`
- `append(ts, obj)`
- `extend([(ts, obj), ...], mostly_ordered=..., insert_on_error=...)`
- `bulk_append(timestamps, objects, mostly_ordered=None)`
- `log[ts] = obj`

`Contract`
- On write-path backpressure, `TimelogBusyError` indicates data was accepted by the engine; do not blind-retry append/delete calls.
- `extend(..., insert_on_error=True)` (the default) SKIPS records whose
  timestamp is type-invalid (e.g. a string or bool) and emits a
  `RuntimeWarning` with the skip count; pass `insert_on_error=False` to
  pre-validate the whole batch and insert all-or-nothing. A timestamp below
  the `min_ts` floor always aborts the whole batch with `ValueError`
  regardless of `insert_on_error` (floor violations are pre-validated, not
  skippable).
- `mostly_ordered` (and the instance-level `mostly_ordered_default`) is
  accepted for compatibility and currently ignored: the engine always
  verifies sortedness itself, so the hint has no effect today.
- `bulk_append(timestamps, objects)` is the typed-buffer fast path for bulk ingest:
  `timestamps` must be a contiguous 1-D native-endian int64 buffer (a NumPy `int64`
  array, `array.array("q")`, or a memoryview of either); `objects` must be a concrete
  ordered sequence (list/tuple) of the same length. The whole batch is a single
  all-or-nothing append that respects `min_ts`; `mostly_ordered=None` uses the
  instance's `mostly_ordered_default`. Rejected inputs raise before any insert:
  non-native byte order, non-int64 item size or format, multi-dimensional or
  misaligned buffers, length mismatch (`ValueError`); non-contiguous buffers
  (`ValueError` or `BufferError`, depending on the buffer producer); non-buffer
  timestamps, str/bytes payload containers, generators/iterators/sets as
  `objects` (`TypeError`).
  It is an ingest fast path, not a general interop surface: it does not change what
  `extend()` accepts, and a `TimelogBusyError` still means the records WERE committed.

## Read API

- `log[t1:t2]` -> iterator over `[t1, t2)`
- `log[t1:]` -> iterator over `[t1, +inf)`
- `log[:t2]` -> iterator over `(-inf, t2)`
- `log[:]` -> full iterator
- `log[ts]` -> list of objects at exact timestamp
- `at(ts)` -> alias for exact timestamp lookup
- `ts in log` -> True if any record exists at exactly `ts` (O(log n) point check)
- `__iter__()` -> full iterator
- `__len__()` -> tombstone-aware estimated visible count from `stats()`

Named query methods (equivalent to the slice forms, useful when passing
callables around): `range(t1, t2)`, `since(t1)`, `until(t2)`, `all()`,
`point(ts)` / `equal(ts)` (iterators over one timestamp's records).

Timestamp navigation: `min_ts()` / `max_ts()` return the smallest/largest
visible data timestamp or `None` when empty (`max_ts()` is O(n) — prefer
`stats()["storage"]["max_ts"]` for monitoring); `next_ts(ts)` / `prev_ts(ts)`
return the nearest strictly-greater / strictly-smaller visible timestamp.
For "first timestamp >= x", use `next_ts(x - 1)` (guard `x > TL_TS_MIN`).

`Contract`
- Slices return SINGLE-USE iterators: a second `list(it)` yields `[]`.
  `len(it)` reports remaining rows without consuming them (and counts down
  as you iterate). Materialize with `list(...)` if you need re-iteration.
- Reversed slice bounds follow sequence semantics: `log[100:10]` is an empty
  iterator (like `lst[100:10] == []`). The explicit `range(t1, t2)` method
  raises `ValueError` on reversed bounds instead.
- `reversed(log)` raises `TypeError` (the LSM read path is forward-only);
  iterate a bounded window and reverse the materialized list, or walk
  backwards with `prev_ts()`.
- `log[ts] = obj` APPENDS — it never replaces (multimap semantics). For
  upsert behavior, `del log[ts]` first.

## Delete API

- `cutoff(ts)` -> delete before `ts`
- `delete(ts)` -> point delete via half-open range
- `delete(t1, t2)` -> delete range `[t1, t2)`
- `del log[ts]`
- `del log[t1:t2]`

`Contract`
- Point delete at `TL_TS_MAX` is not representable as `[ts, ts+1)` and raises `ValueError`.
- Deletes are logical and immediate for readers; physical memory reclaim
  happens via compaction (see `docs/operations.md`, "Space Reclaim After
  Deletes").

## Presets

- `Timelog.for_streaming(**overrides)` — background maintenance + `busy_policy="flush"`.
- `Timelog.for_bulk_ingest(**overrides)` — `maintenance="disabled"` + 16 MiB memtable +
  `busy_policy="flush"`; flush/compact manually after the load.
- `Timelog.for_low_latency(**overrides)` — small memtable, `sealed_wait_ms=0`,
  `busy_policy="raise"`.

## Maintenance API

- `flush()` — synchronously seal + materialize all pending writes into segments.
- `compact()` — request compaction (background worker performs it; in
  `maintenance="disabled"` follow with `maint_step()`).
- `maint_step()` — perform one unit of maintenance manually (disabled mode).
- `start_maintenance()` / `stop_maintenance()` — control the background worker.
- `maintenance_mode` (property) — `"background"` or `"disabled"`.

## Introspection

- `stats()` -> nested dict: `storage` / `memtable` / `operational` /
  `compaction_selection` / `adaptive` / `config`. Empty-log bounds read as
  `None`; `operational.busy_events` counts write-path backpressure under
  EVERY `busy_policy` (including `"silent"`); `config` echoes the effective
  instance configuration (`time_unit`, `maintenance`, `busy_policy`,
  `min_ts`, `mostly_ordered_default`) for dashboards.
- `busy_events` (property) -> cumulative backpressure events.
- `extend_skipped` (property; also `stats()['operational']['extend_skipped']`) ->
  total records dropped by `extend(insert_on_error=True)` skips. The
  RuntimeWarning is deduplicated per call site by Python's warning machinery;
  this counter is the monitorable signal for recurring drops.
- `alloc_failures` (property) -> allocation failures in the drop callback
  (each one is a deliberately leaked object, never a UAF).
- `min_ts_floor` (property) -> the configured `min_ts` retention floor or
  `None`. Distinct from `min_ts()`, which reports the smallest timestamp in
  the data.
- `retired_queue_len` (property) -> objects awaiting deferred release.

## Export API

- `to_dict(t1=None, t2=None)` -> `{timestamp: object}`
- `to_numpy(t1=None, t2=None, dtype=None)` -> `(timestamps, values)` numpy arrays

`Contract`
- Bounds behave exactly like `log[t1:t2]` slicing: `None` = open end,
  half-open `[t1, t2)`, reversed bounds yield an empty result. A record at
  `TL_TS_MAX` is exported only when `t2` is `None` (no bounded `t2` can
  include it).
- Both exports are snapshot-isolated and hold a reader pin for their whole
  duration: a concurrent `close()` raises until the export finishes.
- `to_dict` collapses duplicate timestamps to ONE value (the last in
  iteration order). Which record wins is deterministic for a given storage
  state but otherwise unspecified — out-of-order ingestion and background
  compaction can reorder equal-timestamp records. Need a specific winner?
  Avoid duplicate timestamps or pick explicitly from `point(ts)`.
- `to_numpy` returns two fresh contiguous 1-D arrays: `int64` timestamps and
  `float64` values unless `dtype` overrides it. `dtype` must be a scalar
  numeric dtype (integer/float kind); anything else raises `TypeError`.
  Value conversion follows numpy: `bool` → 1.0/0.0, `None` → NaN under float
  dtypes (TypeError under integer dtypes), ints beyond 2^53 lose precision
  under the default — pass `dtype=np.int64` for exact big-int payloads.
  Duplicate timestamps are all exported (multimap). A non-convertible value
  raises its original exception with the failing row index attached as a
  note (PEP 678). The output is shape-compatible with `bulk_append`
  (values come back converted, not as the original objects).
- numpy is an optional dependency, imported lazily by `to_numpy` only;
  `to_dict` works without it.

## Zero-Copy Views

- `views(t1=None, t2=None, kind="segment")`

`Implementation note`
- Views expose physical storage spans and are not a semantic replacement for tombstone-filtered logical iterators.
- Views only see FLUSHED segments: on a freshly-written log, call `flush()`
  first or `views()` yields nothing while `len(log)` is non-zero.
- `PageSpan.objects()` returns a lazy view tied to the parent span. Once the parent `PageSpan` is closed, indexing, iteration, `len()`, and `copy()` on the view raise `ValueError`.
