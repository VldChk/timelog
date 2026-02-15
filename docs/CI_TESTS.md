# PR Test CI

This repository includes a dedicated PR workflow at `.github/workflows/tests-pr.yml` that runs on every pull request on both Linux and Windows.

## What It Runs

1. Pure C core tests (`timelog_tests`) split by `TL_TEST_GROUPS`.
2. C-level CPython binding tests via `ctest -R ^py_.*_tests$`.
3. Python facade tests in `python/tests` via `pytest`.
4. Demo/methodology/correctness tests in `demo/tests` via `unittest`.

## Core Group List

The grouped core run uses these 13 groups from `core/tests/test_main.c`:

1. `internal_sync`
2. `internal_data`
3. `storage`
4. `delta`
5. `compaction`
6. `pagespan`
7. `adaptive`
8. `functional`
9. `api_semantics`
10. `snapshot_lifetime`
11. `invariants`
12. `concurrency`
13. `stress`

## Required Branch Protection Checks

Set these GitHub checks as required:

1. `Tests (PR) / test (ubuntu-latest, 3.13)`
2. `Tests (PR) / test (windows-latest, 3.13)`

## Local Dry-Run Commands

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DTIMELOG_BUILD_PYTHON=ON -DTIMELOG_BUILD_PY_TESTS=ON
cmake --build build --target timelog_e2e_build -j 2
python demo/ci/run_core_test_groups.py --build-dir build --config Release --summary-json demo/benchmark_runs/core.local.json --summary-md demo/benchmark_runs/core.local.md
ctest --test-dir build -C Release --output-on-failure -R '^py_.*_tests$'
cmake -E env PYTHONPATH="$PWD/python" python -m pytest python/tests -q
python -m unittest discover -s demo/tests -p "test_*.py" -v
```
