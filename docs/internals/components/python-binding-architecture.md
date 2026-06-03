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
- Python C-API interactions require an attached Python thread state. On
  regular builds that also coincides with the active interpreter's GIL;
  on per-interpreter-GIL builds the lock is interpreter-local; on
  free-threaded (Py_GIL_DISABLED) builds the GIL is absent and the
  attached thread state is the only precondition the binding relies on.
  All mutable extension state is explicitly synchronized — see LLD §5.4
  for the synchronization matrix.

## Iterators and Views

- Snapshot-backed iterator types map to Python iteration APIs.
- PageSpan interfaces expose high-throughput timestamp access patterns.

## Error Surface

- C status codes map into Python exception hierarchy.
- Busy/error semantics must preserve engine retry contracts.
