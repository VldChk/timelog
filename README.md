# Timelog

In-memory, LSM-inspired, time-indexed multimap for Python.

Timelog stores many Python objects per timestamp, supports out-of-order ingest,
and answers timestamp/range queries from a native C17 engine through a CPython
extension. Current package version: **1.3.0**.

[![License](https://img.shields.io/github/license/VldChk/timelog)](LICENSE)
[![PyPI version](https://img.shields.io/pypi/v/timelog-lib.svg)](https://pypi.org/project/timelog-lib/)
[![Python versions](https://img.shields.io/pypi/pyversions/timelog-lib.svg)](https://pypi.org/project/timelog-lib/)
[![Tests (PR)](https://github.com/VldChk/timelog/actions/workflows/tests-pr.yml/badge.svg)](https://github.com/VldChk/timelog/actions/workflows/tests-pr.yml)
[![Packaging (PR)](https://github.com/VldChk/timelog/actions/workflows/packaging-pr.yml/badge.svg)](https://github.com/VldChk/timelog/actions/workflows/packaging-pr.yml)
[![Dependency Review](https://github.com/VldChk/timelog/actions/workflows/dependency-review.yml/badge.svg)](https://github.com/VldChk/timelog/actions/workflows/dependency-review.yml)
[![Release (PyPI)](https://github.com/VldChk/timelog/actions/workflows/release-pypi.yml/badge.svg)](https://github.com/VldChk/timelog/actions/workflows/release-pypi.yml)
[![Coverage](https://codecov.io/gh/VldChk/timelog/branch/main/graph/badge.svg)](https://codecov.io/gh/VldChk/timelog)
[![CodeQL](https://github.com/VldChk/timelog/actions/workflows/codeql.yml/badge.svg)](https://github.com/VldChk/timelog/actions/workflows/codeql.yml)
[![Sanitizers](https://github.com/VldChk/timelog/actions/workflows/sanitizers.yml/badge.svg)](https://github.com/VldChk/timelog/actions/workflows/sanitizers.yml)
[![OpenSSF Scorecard](https://api.securityscorecards.dev/projects/github.com/VldChk/timelog/badge)](https://securityscorecards.dev/viewer/?uri=github.com/VldChk/timelog)
[![Python 3.12+](https://img.shields.io/badge/python-3.12%2B-blue)](https://github.com/VldChk/timelog)

## Why Timelog

Timelog is built for timestamp-first workloads where the core operation is "everything in `[t1, t2)`".  
It provides a native in-memory index with snapshot-consistent reads, out-of-order ingestion support, and sequenced range deletes.

At a high level, writes flow through mutable ingest state into immutable layers (memrun, L0, L1), while reads merge across layers with tombstone-aware filtering.  
The design is LSM-inspired, but explicitly scoped to an embedded in-memory engine.

Use it when you want a local Python object index optimized for:

- append-heavy event streams,
- range scans over integer timestamps,
- retention via logical deletes/tombstones,
- concurrent snapshot readers over live Python objects,
- zero-copy timestamp views for analytics-style scans.

## Installation

Install from PyPI:

```bash
pip install timelog-lib
```

Or with `uv`:

```bash
uv add timelog-lib
```

Distribution name is `timelog-lib`, import namespace stays `timelog`:

```python
from timelog import Timelog
```

## Runtime Support

- Regular CPython **3.12-3.14**.
- Isolated subinterpreters with a per-interpreter GIL.
- Free-threaded CPython **3.14t** (`Py_GIL_DISABLED=1`) on the supported wheel set;
  importing Timelog does not re-enable the GIL.
- Typed package metadata is included (`py.typed` and `_timelog.pyi`).

The Python API remains single-writer at the instance level: writes and lifecycle
operations must be externally serialized. Independent snapshot readers can run
concurrently.

## What Changed in 1.2 and 1.3

`1.2.0` rebuilt the CPython runtime boundary: `_timelog` now uses
multi-phase module initialization, module-local exceptions and heap types,
per-interpreter-safe state recovery, and explicit synchronization for the
supported free-threaded wheel family.

`1.3.0` keeps that runtime contract and focuses on the hot user paths:
auto-timestamp `append(obj)` moved from Python into C, common positional
methods use lower-overhead dispatch, `bulk_append()` ingests typed timestamp
buffers directly, and core lower/upper-bound searches use a measured
size-gated branchless path.

## Quickstart: Streaming

```python
from timelog import Timelog

log = Timelog.for_streaming(time_unit="ms")

# Auto-timestamp append
log.append({"event": "boot"})

# Operator-style explicit timestamp append
log[1_700_000_000_000] = {"event": "tick"}

# Half-open range query [t1, t2)
rows = list(log[1_700_000_000_000:1_700_000_000_001])
print(rows)

log.close()  # deterministic cleanup; finalizer cleanup is best-effort
```

## Quickstart: Correctness Semantics

```python
from timelog import Timelog

log = Timelog(time_unit="ms")
log[10] = "A"
del log[5:15]              # delete [5, 15)
log[10] = "B"              # later insert at same ts

print(log[10])             # ['B']
print(list(log[0:20]))     # [(10, 'B')]

log.close()  # optional explicit cleanup
```

Timelog uses sequenced tombstones, so later inserts are not hidden by earlier deletes.

## Core Guarantees

- Time ranges are half-open: `[t1, t2)`.
- Reads are snapshot-consistent.
- Concurrency model is single writer plus concurrent readers.
- Duplicate timestamps are allowed (multimap semantics).
- Write-path backpressure (`TimelogBusyError`) indicates the write was accepted; do not blind-retry the same write.
- `close()` discards all data. Timelog is in-memory; `flush()` improves open-instance visibility for readers, not durability.

## What Timelog Is (and Isn’t)

Timelog is:

- an embedded, in-memory timestamp index,
- optimized for append-heavy ingest and time-range retrieval,
- implemented in C17 with first-party CPython bindings.

Timelog is not:

- a durable storage engine,
- a distributed TSDB,
- a SQL query engine.

`close()` discards all data — the engine is in-memory, so nothing survives it.
`flush()` matters while the log is OPEN: it materializes pending writes into
immutable segments so zero-copy `views()` readers can see them.

## API Snapshot

Core Python facade surface:

- Constructors: `Timelog(...)`, `for_streaming(...)`, `for_bulk_ingest(...)`,
  `for_low_latency(...)`.
- Writes:
  - `append(obj)`, `append(obj, ts=...)`, `append(ts, obj)`.
  - `extend([(ts, obj), ...], mostly_ordered=..., insert_on_error=...)`.
  - `bulk_append(timestamps, objects)` for contiguous native-endian int64 buffers
    plus a same-length list/tuple of payloads.
  - `log[ts] = obj`, `delete(t1, t2)`, `delete(ts)`, `cutoff(ts)`.
- Reads:
  - `log[t1:t2]`, `log[t1:]`, `log[:t2]`, `log[:]`.
  - `log[ts]` / `at(ts)`.
  - named iterators: `range`, `since`, `until`, `all`, `point` / `equal`.
  - iterator helpers: `len(it)`, `next_batch(n)`, and `it.view()`.
- Introspection and views:
  - `stats()`, `busy_events`, `extend_skipped`, `retired_queue_len`.
  - `views(...)` / `page_spans(...)` for zero-copy timestamp spans.
  - `PageSpan.timestamps` is a read-only memoryview; `PageSpan.objects()` lazily
    exposes the corresponding Python payloads.

See `docs/python-api.md` for the full behavior contract.

## Lifecycle, Threading, and Backpressure

- Most users should write `log = Timelog(...)` or use a preset constructor and
  keep the object for the required scope. A context manager is available but not
  required.
- Explicit `close()` gives deterministic cleanup. If omitted, collection
  auto-closes on a best-effort basis.
- Do not call `close()` concurrently with other operations on the same instance.
- Release active iterators, `PageSpan` objects, object views, and exported
  memoryviews before closing; they hold snapshot pins.
- Background maintenance can run automatically (`maintenance="background"`) or
  be controlled manually (`maintenance="disabled"` + `flush()` / `compact()` /
  `maint_step()`).
- `TimelogBusyError` on write operations means accepted write + pressure signal,
  not "write lost".

## Architecture

```text
Write Path                               Read Path
----------                               ---------
append/extend/delete                     snapshot + query([t1, t2))
      |                                           |
      v                                           v
  Memtable (mutable)  <--------------------  Snapshot view
      | seal
      v
  Memrun (immutable)
      | flush
      v
  L0 Segments (overlap)
      | compact
      v
  L1 Segments (windowed, non-overlap)
```

Reads plan sources across active + immutable layers, then run k-way merge with tombstone filtering based on sequencing/watermark state.  
Flush and compaction bound read fan-out over time.  
Deletes are logical tombstones; physical cleanup is deferred to maintenance.

`flush()` is a visibility operation, not durability: it publishes pending
writes into immutable in-memory segments so readers and zero-copy `views()` can
see them. `close()` always tears down the in-memory engine and discards all
records.

## Performance at a Glance

Same-harness v1.3 A/B against the v1.2.0 wheel, Linux x86_64, pinned CPU,
CPython `3.13.12`, median of 5:

| Operation | v1.2.0 | v1.3.0 | Change |
|---|---:|---:|---:|
| `append(obj)` | 513.9 ns | 117.1 ns | 4.39x faster |
| `append(ts, obj)` | 352.1 ns | 103.9 ns | 3.39x faster |
| `append(obj, ts=...)` | 364.7 ns | 109.6 ns | 3.33x faster |
| `point(ts)` | 457.1 ns | 337.1 ns | 1.36x faster |
| `equal(ts)` | 548.8 ns | 429.3 ns | 1.28x faster |
| `next_ts(ts)` | 393.8 ns | 299.8 ns | 1.31x faster |
| `range(t1, t2)` | 575.9 ns | 458.0 ns | 1.26x faster |
| `delete_range(t1, t2)` | 18,059.6 ns | 13,289.3 ns | 1.36x faster |
| `delete_before(ts)` | 109.7 ns | 80.8 ns | 1.36x faster |

New v1.3 ingest fast path:

- `bulk_append(np.int64 array, list)`: **113.3 ns/record** on a 200k-record
  measured batch.
- In that benchmark, `bulk_append` was **2.23x** faster than a post-v1.3
  per-record append loop and **3.51x** faster than `extend(zip(...))`.

Search-path optimization:

- Size-gated branchless lower/upper-bound search measured **1.9x-5.0x faster**
  at gated sizes up to 262,144 records, and falls back to the neutral path for
  very large arrays where it no longer wins.

Historical scale snapshot (`2026-02-15`, Linux x86_64, CPython `3.13.12`,
dataset `11,550,000` rows):

- Batch ingest (`A2`): `191,105` records/sec.
- Full scan (`B4`): `18,088,679` records/sec.
- Append latency (`K1`, background): `p99 = 672 ns`.
- PageSpan iteration (`F1`): `1.48B` timestamps/sec on the timestamp-only span path.

Results are workload-, configuration-, and hardware-dependent.
The current publishable benchmark framing is `docs/performance.md`; older
reports are retained as historical snapshots.

Methodology and context:

- `docs/PERFORMANCE_METHODOLOGY.md`
- `docs/performance.md`
- `docs/benchmarks/bulk_append.md`
- `docs/benchmarks/max_delta_segments.md`
- `docs/BENCHMARK_1GB_7PCT_OOO_UNIX.md`
- `docs/BENCHMARK_REPORT.md`

Complexity claims should be interpreted with stated assumptions. In practice:

- append path is amortized O(1) at memtable layer,
- point/range behavior approaches logarithmic seek + linear output scan when source fan-out is bounded by maintenance,
- delete cost depends on tombstone interval state.

## Documentation

- Index: `docs/index.md`
- Release notes: `docs/release-notes.md`
- Python API: `docs/python-api.md`
- Configuration: `docs/configuration.md`
- Error and retry semantics: `docs/errors-and-retry-semantics.md`
- Performance methodology: `docs/PERFORMANCE_METHODOLOGY.md`
- PyPI/release operations: `docs/pypi-release.md`

## License

MIT. See `LICENSE`.

## Contributing

PRs are welcome. Run core validation locally:

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DTIMELOG_BUILD_PYTHON=ON -DTIMELOG_BUILD_PY_TESTS=ON
cmake --build build --target timelog_e2e_build --config Release -j 2
ctest --test-dir build -C Release --output-on-failure -R '^py_.*_tests$'
cmake -E env PYTHONPATH="$PWD/python" python -m pytest python/tests -q
```

Package build sanity:

```bash
python -m build
python -m twine check dist/*
```
