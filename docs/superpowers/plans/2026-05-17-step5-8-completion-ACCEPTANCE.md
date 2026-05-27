# Layer B Acceptance Checklist Evidence

This document walks the LLD §10 acceptance checklist and pins each item to a concrete code or test artifact. Generated after Steps 5 (Layer B synchronization), 6 (Py_mod_gil), and 8 (docs + packaging + CI) landed.

| # | Acceptance item | Status | Evidence |
|---|---|---|---|
| 1 | no `m_size = -1` | ✅ | `bindings/cpython/src/module.c:478` — `sizeof(tl_py_module_state_t)` |
| 2 | multi-phase initialization | ✅ | `module.c:456` — `{Py_mod_exec, timelog_exec}` slot |
| 3 | idempotent exec + partial-init unwind | ✅ | `bindings/cpython/tests/test_py_module_exec.c:523` `same_module_second_exec_is_noop_success`, `:765` `retry_after_each_failpoint` |
| 4 | no process-global Python objects | ✅ | `grep -rE 'extern PyObject\* ' bindings/cpython/src/` returns zero hits |
| 5 | all exceptions are per-module | ✅ | `bindings/cpython/include/timelogpy/py_module_state.h:18-19` — `exc_timelog_error`, `exc_timelog_busy_error` |
| 6 | all reachable extension types are heap types | ✅ | 6 `PyType_FromModuleAndSpec` creation sites across `py_timelog.c`, `py_iter.c`, `py_span.c`, `py_span_iter.c`, `py_span_objects.c` (2 in the last for view + view-iter) |
| 7 | no reachable production static binding `PyTypeObject` | ✅ | `python demo/ci/check_layer_a_static.py` → `Layer A static regression check passed.` |
| 8 | core `tl_pagespan_owner.refcnt` is atomic | ✅ | `core/src/query/tl_pagespan_iter.c:43` — `tl_atomic_u32 refcnt;` |
| 9 | no correctness-critical path relies on the GIL as a lock | ✅ | `tl_py_attached_to_interp` uses `PyThreadState_GetUnchecked` (3.13+) for attached-thread-state probe, not `PyGILState_Check` for correctness. See `bindings/cpython/src/py_handle.c:59-76`. |
| 10 | no decref / warning / callback-capable work under `core_lock`, `live_lock`, or object critical sections | ✅ | Collect-unlock-execute pattern applied in `tl_py_live_release_all` (`py_handle.c:611+`), `tl_py_handle_ctx_traverse` (`py_handle.c:691+`), `pytimelogiter_cleanup` (split into `detach_locked` + `release_resources`, `py_iter.c:95+`), `pagespan_cleanup` (`py_span.c:93+`), `pagespaniter_cleanup` (`py_span_iter.c:213+`) |
| 11 | live tracking and object-local mutable state are explicitly synchronized | ✅ | L2: `live_lock` field in `tl_py_handle_ctx_t` + `tl_py_mutex_t` (`py_handle.h:173`). L4: per-object critical sections — 51 `TL_PY_OBJ_LOCK` / `tl_py_mutex_t` / `live_lock` sites across `bindings/cpython/src/` |
| 12 | maintenance thread never calls Python C API | ✅ | `grep -rE 'Py[A-Z][a-zA-Z]+\|PyObject' core/src/maint/` returns zero hits |
| 13 | `Py_mod_multiple_interpreters = Py_MOD_PER_INTERPRETER_GIL_SUPPORTED` | ✅ | `module.c:458` |
| 14 | `Py_mod_gil = Py_MOD_GIL_NOT_USED` | ✅ | `module.c:469` (3.13+ guarded) |
| 15 | free-threaded import does not enable the GIL | ✅ | `PYTHON_GIL=0 python3.14t -c "import sys, timelog; print(sys._is_gil_enabled())"` → `False`. Also gated by `python/tests/test_free_threading.py::test_import_does_not_enable_gil` (hard assert, no xfail) |
| 16 | subinterpreter smoke and independence tests pass | ✅ | `pytest python/tests/test_subinterpreters.py` on 3.14t → 7 passed in 0.44s |
| 17 | concurrent stress tests and PageSpan cross-thread release tests pass on free-threaded 3.14 | ✅ | `python/tests/test_freethreaded_stress.py` covers §7.5 (concurrent reads + writer), §7.6 (PageSpan cross-thread release), §7.7 (mutable state overlap on close/buffer/iter), §7.8 (drop/drain with reentrant `__del__`), §7.9 (close+reopen, GC finalization). Local 3.14t run with `TIMELOG_SHORT_STRESS=1`: 7/7 passed |
| 18 | public docs and Python facade no longer make blanket CPython-GIL-required support claims | ✅ | Cleanup landed in `python/timelog/__init__.py:69+`, `bindings/cpython/include/timelogpy/py_timelog.h:9-32`, `docs/python-api.md:11-19`, `docs/internals/components/python-binding-architecture.md:19+`. Static check enforces (`check_layer_a_static.py` `stale GIL-only claim` rule) |
| 19 | dual wheel families build in CI | ✅ | `pyproject.toml:54` — `build = "cp312-* cp313-* cp314-* cp314t-*"`. `.github/workflows/packaging-pr.yml` matrix builds + smoke-tests cp313 and cp314t (with `PYTHON_GIL=0` assertion on cp314t leg). |

## Layer-B-specific CI gates added

- `compatibility-baseline-pr.yml` / `compatibility-baseline-main.yml`: `freethreading-3.14t-ubuntu` leg now runs `test_free_threading` + `test_freethreaded_stress` with `TIMELOG_SHORT_STRESS=1`. Pre-test sanity check fails the leg if `setup-python` returns a non-free-threaded fallback.
- `sanitizers.yml`: new `thread-sanitizer-freethreaded (ubuntu-latest, 3.14t)` job runs the freethreading leg under TSan + libtsan LD_PRELOAD, fails if any `(WARNING|ERROR): ThreadSanitizer` line appears in the log (independent of pytest exit code).
- `packaging-pr.yml`: cp314t wheel install smoke runs `PYTHON_GIL=0 python -c "import timelog"` and asserts `sys._is_gil_enabled()` stays False after import.

## Layer B local validation summary

- **3.13 regular** (build-step2): `ctest` 9/9 + `pytest python/tests` 97/16-skipped.
- **3.14t free-threaded** (build-py314t): `pytest python/tests` 111/2-skipped + `pytest test_freethreaded_stress.py` (TIMELOG_SHORT_STRESS=1) 7/7 passed.
- **Static regression**: `python demo/ci/check_layer_a_static.py` passed.
- **Docs consistency**: `python demo/ci/check_docs_consistency.py` passed.

## Open items (intentional)

These are explicit non-goals or future-phase work, not regressions:

- **`cp313t` (free-threaded 3.13)** is NOT in the wheel build set. Spec §6.10: "explicitly tested only." 3.13t is structurally compatible (the same synchronization primitives back-compat to 3.13 via the `PyMutex` fallback path) but not gated by CI.
- **TSan-on-3.14t is `continue-on-error: true`** initially while runner availability and TSan-vs-CPython noise are characterized. Promoted to required once consistently green.
- **Subscription / pickling preservation tests** not formally added; spec did not require them.

Every spec acceptance bullet has a concrete file:line or test-name pointer above. Layer B is complete.
