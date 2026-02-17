# timelog
Native C17 time-series engine with first-party CPython bindings.

## Unified End-to-End Build
Use one build tree for core + bindings + tests.

```bash
cmake -S . -B build-e2e -DTIMELOG_BUILD_PYTHON=ON -DTIMELOG_BUILD_PY_TESTS=ON
cmake --build build-e2e --config Release --target timelog_e2e_build
cmake --build build-e2e --config Release --target timelog_e2e_test
```

What this gives you in one flow:
1. Core library and core tests.
2. CPython extension module `_timelog`.
3. C-level binding tests.
4. Automatic staging of `_timelog` into `python/timelog/` (no manual copy).

## Optional Python Facade Tests
If `pytest` is installed:

```bash
cmake -S . -B build-e2e -DTIMELOG_BUILD_PYTHON=ON -DTIMELOG_BUILD_PY_FACADE_TESTS=ON
cmake --build build-e2e --config Release --target timelog_python_facade_tests
```
