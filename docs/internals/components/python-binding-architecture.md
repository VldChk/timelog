# Internals: Python Binding Architecture

Sources:
- `bindings/cpython/include/timelogpy/*`
- `bindings/cpython/src/*`
- `python/timelog/__init__.py`

## Layers

1. C engine (`timelog`)
2. CPython extension (`_timelog`)
3. Python facade (`timelog` package API)

## Handle and Lifetime Model

`Contract`
- Engine stores opaque handles; payload interpretation is outside core engine.

`Implementation note`
- Binding uses handle encode/decode and retirement draining patterns.
- GIL discipline is required for Python C-API interactions.

## Iterators and Views

- Snapshot-backed iterator types map to Python iteration APIs.
- PageSpan interfaces expose high-throughput timestamp access patterns.

## Error Surface

- C status codes map into Python exception hierarchy.
- Busy/error semantics must preserve engine retry contracts.
