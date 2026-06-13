# Getting Started

## Install

Install from PyPI:

```bash
pip install timelog-lib
```

or with `uv`:

```bash
uv add timelog-lib
```

The distribution name is `timelog-lib`, but import paths stay unchanged:

```python
from timelog import Timelog
```

Runtime support:

- CPython 3.12-3.14 regular builds.
- Isolated subinterpreters with per-interpreter GIL.
- CPython 3.14t free-threaded builds (`Py_GIL_DISABLED=1`) on supported wheels.

## Source Build (Development)

For local source builds, use CMake and the CPython binding target:

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --target timelog_e2e_build -j 2
```

For Python tests:

```bash
cmake -E env PYTHONPATH="$PWD/python" python -m pytest python/tests -q
```

## Quick Python Example

```python
from timelog import Timelog

log = Timelog.for_streaming(time_unit="ms")
log.append({"event": "start"})     # auto timestamp
log[1700000000000] = {"event": "a"}
log.extend([
    (1700000000100, {"event": "b"}),
    (1700000000200, {"event": "c"}),
])

rows = list(log[1700000000000:1700000000300])
at_t = log.at(1700000000100)

log.cutoff(1700000000050)            # delete before timestamp
log.flush()                           # materialize pending writes for views/readers
log.close()                           # deterministic cleanup; data is discarded
```

Timelog is in-memory. `close()` discards all records, flushed or not. `flush()`
is still useful while the instance is open because it moves pending writes into
immutable segments that zero-copy `views()` can expose.

## Bulk Ingest

Use `bulk_append()` when timestamps already live in a contiguous int64 buffer
and payloads are in a concrete Python sequence:

```python
from array import array
from timelog import Timelog

log = Timelog.for_bulk_ingest(time_unit="ms")
timestamps = array("q", [100, 101, 102])
objects = [{"event": "a"}, {"event": "b"}, {"event": "c"}]

log.bulk_append(timestamps, objects)
log.flush()
print(list(log[100:103]))
log.close()
```

`bulk_append()` is all-or-nothing for rejected inputs: native-endian int64,
1-D contiguous timestamp buffer, same-length list/tuple payload sequence.

## Zero-Copy Timestamp Views

For timestamp-heavy scans, flush first and use `views()`:

```python
log = Timelog()
for ts in range(1_000):
    log.append(ts, {"value": ts})

log.flush()
for span in log.views():
    ts_view = span.timestamps       # read-only memoryview over int64 timestamps
    first = span.start_ts
    count = len(span)
    span.close()

log.close()
```

Views expose physical storage spans, not tombstone-filtered logical query
results. Use normal iterators for semantic reads and views for span-oriented
timestamp access.

## Recommended Constructor Presets

- `Timelog.for_streaming(...)`
- `Timelog.for_bulk_ingest(...)`
- `Timelog.for_low_latency(...)`

See `docs/configuration.md` for detailed tuning.
