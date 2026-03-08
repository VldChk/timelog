# Timelog

In-memory, LSM-inspired, time-indexed multimap for Python (C17 core + CPython extension).

[![License](https://img.shields.io/github/license/VldChk/timelog)](LICENSE)
[![PyPI version](https://img.shields.io/pypi/v/timelog-lib.svg)](https://pypi.org/project/timelog-lib/)
[![Python versions](https://img.shields.io/pypi/pyversions/timelog-lib.svg)](https://pypi.org/project/timelog-lib/)
[![Tests (PR)](https://github.com/VldChk/timelog/actions/workflows/tests-pr.yml/badge.svg)](https://github.com/VldChk/timelog/actions/workflows/tests-pr.yml)
[![Packaging (PR)](https://github.com/VldChk/timelog/actions/workflows/packaging-pr.yml/badge.svg)](https://github.com/VldChk/timelog/actions/workflows/packaging-pr.yml)
[![Coverage](https://codecov.io/gh/VldChk/timelog/branch/main/graph/badge.svg)](https://codecov.io/gh/VldChk/timelog)
[![CodeQL](https://github.com/VldChk/timelog/actions/workflows/codeql.yml/badge.svg)](https://github.com/VldChk/timelog/actions/workflows/codeql.yml)
[![Sanitizers](https://github.com/VldChk/timelog/actions/workflows/sanitizers.yml/badge.svg)](https://github.com/VldChk/timelog/actions/workflows/sanitizers.yml)
[![Python 3.12+](https://img.shields.io/badge/python-3.12%2B-blue)](https://github.com/VldChk/timelog)

## Why Timelog

Timelog is built for timestamp-first workloads where the core operation is "everything in `[t1, t2)`".  
It provides a native in-memory index with snapshot-consistent reads, out-of-order ingestion support, and sequenced range deletes.

At a high level, writes flow through mutable ingest state into immutable layers (memrun, L0, L1), while reads merge across layers with tombstone-aware filtering.  
The design is LSM-inspired, but explicitly scoped to an embedded in-memory engine.

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

log.close()  # optional explicit cleanup
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

## What Timelog Is (and Isn’t)

Timelog is:

- an embedded, in-memory timestamp index,
- optimized for append-heavy ingest and time-range retrieval,
- implemented in C17 with first-party CPython bindings.

Timelog is not:

- a durable storage engine,
- a distributed TSDB,
- a SQL query engine.

`close()` does not materialize unflushed writes. Call `flush()` first if you need all pending data materialized into immutable segments before shutdown.

## API Snapshot

Core Python facade surface:

- Constructors:
  - `Timelog(...)`
  - `Timelog.for_streaming(...)`
  - `Timelog.for_bulk_ingest(...)`
  - `Timelog.for_low_latency(...)`
- Writes:
  - `append(...)`
  - `extend(...)`
  - `log[ts] = obj`
  - `delete(t1, t2)` / `delete(ts)`
  - `cutoff(ts)`
- Reads:
  - `log[t1:t2]`, `log[t1:]`, `log[:t2]`, `log[:]`
  - `log[ts]` / `at(ts)`
- Introspection and views:
  - `stats()`
  - `views(...)`

See `docs/python-api.md` for the full behavior contract.

## Threading and Backpressure

- Writes and lifecycle operations must be externally serialized.
- Snapshot iterators are safe for concurrent reads.
- Background maintenance can run automatically (`maintenance="background"`) or be controlled manually.
- `TimelogBusyError` on write operations means accepted write + pressure signal, not "write lost".
- Do not call `close()` concurrently with other operations on the same instance.

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

## Performance at a Glance

Historical snapshot (`2026-02-15`, Linux x86_64, Python `3.13.12`, dataset `11,550,000` rows):

- Batch ingest (`A2`): `191,105` records/sec
- Full scan (`B4`): `18,088,679` records/sec
- Append latency (`K1`, background): `p99 = 672 ns`

Results are workload-, configuration-, and hardware-dependent.

Methodology and context:

- `docs/PERFORMANCE_METHODOLOGY.md`
- `docs/BENCHMARK_1GB_7PCT_OOO_UNIX.md`
- `docs/BENCHMARK_REPORT.md`
- `docs/performance.md`

Complexity claims should be interpreted with stated assumptions. In practice:

- append path is amortized O(1) at memtable layer,
- point/range behavior approaches logarithmic seek + linear output scan when source fan-out is bounded by maintenance,
- delete cost depends on tombstone interval state.

## Documentation

- Index: `docs/index.md`
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
