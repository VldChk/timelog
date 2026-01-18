# Review: CPython py_handle/py_errors vs LLD-B1 + Python HLD

## Findings (ordered by severity)

### High
- Spec mismatch in error mapping: header comment promises TL_ESTATE -> RuntimeError and TL_EBUSY -> ResourceWarning, but implementation maps both to TimelogError; this diverges from the Python HLD error model (TimelogBusyError or RuntimeError) and can mislead users and tests. Evidence: `bindings/cpython/include/timelogpy/py_errors.h:11` `bindings/cpython/include/timelogpy/py_errors.h:12` `bindings/cpython/src/py_errors.c:67` `bindings/cpython/src/py_errors.c:89`.
- Memory-ordering contract drift: file-level design comment says pin increment is ACQUIRE, but tl_py_pins_enter uses RELAXED. This conflicts with LLD-B1’s stated ordering and the file’s own contract, risking future changes relying on the stronger order. Evidence: `bindings/cpython/src/py_handle.c:15` `bindings/cpython/src/py_handle.c:125`.

### Medium
- GIL discipline is documented but not enforced: tl_py_pins_exit_and_maybe_drain can call tl_py_drain_retired without any runtime GIL check; a caller mistake would run Py_DECREF without the GIL. This is a correctness hazard for the binding surface and should be guarded or asserted. Evidence: `bindings/cpython/include/timelogpy/py_handle.h:179` `bindings/cpython/src/py_handle.c:128` `bindings/cpython/src/py_handle.c:140`.
- Test coverage gaps for thread/GIL constraints: tests only run on the main thread and call on_drop directly, so they do not exercise the “no Python C-API in on_drop” guarantee under a non-Python thread or validate GIL requirements. Evidence: `bindings/cpython/tests/test_py_handle.c:249` `bindings/cpython/tests/test_py_handle.c:294`.

### Low
- Exception type naming may not match the final module path: TimelogError is created with the qualified name "timelog.TimelogError" without evidence that the extension module is `timelog` (often `_timelog`). This can affect exception repr/pickling and should be aligned with packaging decisions. Evidence: `bindings/cpython/src/py_errors.c:30`.

## Alignment highlights (non-blocking)
- LLD-B1 invariants are largely respected: on_drop enqueues with no Python C-API, pins gate drain, and drain performs Py_DECREF under the GIL. Evidence: `bindings/cpython/include/timelogpy/py_handle.h:162` `bindings/cpython/src/py_handle.c:163` `bindings/cpython/src/py_handle.c:243`.

## Open questions to resolve before implementation
- Should the error surface include a dedicated TimelogBusyError per HLD, or is TimelogError sufficient? Evidence: `bindings/cpython/include/timelogpy/py_errors.h:33` `bindings/cpython/src/py_errors.c:67`.
- Do we want to enforce GIL preconditions at runtime (PyGILState_Check) in debug builds to catch misuse early? Evidence: `bindings/cpython/src/py_handle.c:128`.

## Sources reviewed
- `bindings/cpython/include/timelogpy/py_errors.h`
- `bindings/cpython/include/timelogpy/py_handle.h`
- `bindings/cpython/src/py_errors.c`
- `bindings/cpython/src/py_handle.c`
- `bindings/cpython/tests/test_py_handle.c`
- `docs/timelog_python_north_star_hld.md`
- `docs/timelog_v1_lld_B1_python_handle_lifetime.md`