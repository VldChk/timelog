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

## Lifecycle

- `Timelog(**kwargs)`
- `reopen(...)`
- `configure(...)` (alias for `reopen`)
- `close()` for deterministic explicit cleanup
- Context manager is supported, but optional.

`Contract`
- `close()` drops unflushed data. Use `flush()` before close if persistence of in-memory state to immutable segments is required.
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
- `bulk_append(timestamps, objects)` is the typed-buffer fast path for bulk ingest:
  `timestamps` must be a contiguous 1-D native-endian int64 buffer (a NumPy `int64`
  array, `array.array("q")`, or a memoryview of either); `objects` must be a concrete
  ordered sequence (list/tuple) of the same length. The whole batch is a single
  all-or-nothing append that respects `min_ts`; `mostly_ordered=None` uses the
  instance's `mostly_ordered_default`. Rejected inputs raise before any insert:
  non-native byte order, non-int64 item size or format, multi-dimensional or
  non-contiguous buffers, length mismatch (`ValueError`); non-buffer timestamps,
  str/bytes payload containers, generators/iterators/sets as `objects` (`TypeError`).
  It is an ingest fast path, not a general interop surface: it does not change what
  `extend()` accepts, and a `TimelogBusyError` still means the records WERE committed.

## Read API

- `log[t1:t2]` -> iterator over `[t1, t2)`
- `log[t1:]` -> iterator over `[t1, +inf)`
- `log[:t2]` -> iterator over `(-inf, t2)`
- `log[:]` -> full iterator
- `log[ts]` -> list of objects at exact timestamp
- `at(ts)` -> alias for exact timestamp lookup
- `__iter__()` -> full iterator
- `__len__()` -> tombstone-aware estimated visible count from `stats()`

## Delete API

- `cutoff(ts)` -> delete before `ts`
- `delete(ts)` -> point delete via half-open range
- `delete(t1, t2)` -> delete range `[t1, t2)`
- `del log[ts]`
- `del log[t1:t2]`

`Contract`
- Point delete at `TL_TS_MAX` is not representable as `[ts, ts+1)` and raises `ValueError`.

## Zero-Copy Views

- `views(t1=None, t2=None, kind="segment")`

`Implementation note`
- Views expose physical storage spans and are not a semantic replacement for tombstone-filtered logical iterators.
- `PageSpan.objects()` returns a lazy view tied to the parent span. Once the parent `PageSpan` is closed, indexing, iteration, `len()`, and `copy()` on the view raise `ValueError`.
