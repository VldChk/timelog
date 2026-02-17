# Python API

Source of truth for Python behavior: `python/timelog/__init__.py`.

## Core Class

- `Timelog`
- Exceptions: `TimelogError`, `TimelogBusyError`
- Iterator/span types: `TimelogIter`, `PageSpan`, `PageSpanIter`, `PageSpanObjectsView`

## Lifecycle

- `Timelog(**kwargs)`
- `reopen(...)`
- `configure(...)` (alias for `reopen`)
- Context manager is supported.

`Contract`
- `close()` drops unflushed data. Use `flush()` before close if persistence of in-memory state to immutable segments is required.

## Write API

- `append(obj)`
- `append(obj, ts=...)`
- `append(ts, obj)`
- `extend([(ts, obj), ...], mostly_ordered=..., insert_on_error=...)`
- `log[ts] = obj`

`Contract`
- On write-path backpressure, `TimelogBusyError` indicates data was accepted by the engine; do not blind-retry append/delete calls.

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
