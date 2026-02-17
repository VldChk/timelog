# Getting Started

## Install

Timelog packaging instructions are evolving with CI/wheel integration. For source builds, use CMake and the CPython binding target.

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

with Timelog.for_streaming(time_unit="ms") as log:
    log.append({"event": "start"})     # auto timestamp
    log[1700000000000] = {"event": "a"}
    log.extend([
        (1700000000100, {"event": "b"}),
        (1700000000200, {"event": "c"}),
    ])

    rows = list(log[1700000000000:1700000000300])
    at_t = log.at(1700000000100)

    log.cutoff(1700000000050)            # delete before timestamp
    log.flush()                           # materialize pending writes
```

## Recommended Constructor Presets

- `Timelog.for_streaming(...)`
- `Timelog.for_bulk_ingest(...)`
- `Timelog.for_low_latency(...)`

See `docs/configuration.md` for detailed tuning.
