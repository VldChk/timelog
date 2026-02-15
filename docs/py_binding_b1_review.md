# Review: CPython py_handle/py_errors vs Binding Design

## Findings (ordered by severity)

### High
- Spec mismatch in error mapping: header comments promise specialized mapping for `TL_ESTATE`/`TL_EBUSY`, but implementation paths map broadly to `TimelogError` in some cases. This can mislead users and tests. Evidence: `bindings/cpython/include/timelogpy/py_errors.h` `bindings/cpython/src/py_errors.c`.
- Memory-ordering contract drift: design comments describe stronger ordering than the current atomic mode in `tl_py_pins_enter`. This is a future-maintenance risk if code assumes stronger ordering later. Evidence: `bindings/cpython/src/py_handle.c`.

### Medium
- GIL discipline is documented but not fully enforced by runtime guards on every path that may drain retired nodes.
- Thread/GIL test coverage is narrow for non-main-thread callback scenarios.

### Low
- Exception qualified names should remain aligned with final packaging/module naming to avoid repr/pickling surprises.

## Alignment Highlights
- Core handle-lifetime approach is coherent: no Python C-API in on-drop callback, deferred drain under GIL, pin-count gating.

## Open Questions
- Should busy conditions consistently map to a dedicated `TimelogBusyError` path for all user-facing write outcomes?
- Should debug-mode runtime assertions enforce GIL preconditions in drain-sensitive paths?

## Sources reviewed
- `bindings/cpython/include/timelogpy/py_errors.h`
- `bindings/cpython/include/timelogpy/py_handle.h`
- `bindings/cpython/src/py_errors.c`
- `bindings/cpython/src/py_handle.c`
- `bindings/cpython/tests/test_py_handle.c`
- `docs/internals/components/python-binding-architecture.md`
- `docs/errors-and-retry-semantics.md`
