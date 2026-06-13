# PR Test CI

This repository includes a dedicated PR workflow at `.github/workflows/tests-pr.yml` that runs on every pull request on Linux and Windows for CPython 3.12 and 3.13. It also has a required Linux CPython 3.14 subinterpreter job for Layer A.

## What It Runs

1. Pure C core tests (`timelog_tests`) split by `TL_TEST_GROUPS`.
2. Production-source Layer A static regression check.
3. C-level CPython binding tests via `ctest -R ^py_.*_tests$`.
4. Python facade tests in `python/tests` via `pytest`.
5. Demo/methodology/correctness tests in `demo/tests` via `unittest`.
6. Layer A subinterpreter tests on CPython 3.14 via `demo/ci/run_compat_baseline.py --legs subinterpreters`.

## Compatibility Baseline

The repository also includes compatibility workflows at
`.github/workflows/compatibility-baseline-pr.yml` and
`.github/workflows/compatibility-baseline-main.yml`.

Purpose:
1. Mirror Layer A subinterpreter behavior on additional compatibility hosts, including Windows CPython 3.14.
2. Gate Layer B free-threaded behavior on a genuine CPython 3.14t host with `Py_GIL_DISABLED=1`.
3. Preserve permanent baseline coverage so future regressions fail against existing tests instead of adding new tests late.

Current policy:
1. Missing host capability is reported as `SKIP`, but a leg that collects no passing or expected-failing tests is a failure.
2. Layer A subinterpreter tests are required to pass on hosts with `concurrent.interpreters`.
3. Layer B free-threaded import and short-stress tests are required to pass on the `freethreading-3.14t-ubuntu` compatibility leg.
4. `XPASS`, `FAIL`, `ERROR`, and all-skip capability legs fail the compatibility job.

Compatibility markers:
1. `subinterpreters`
2. `freethreading`
3. `stress`

## Synthetic Data Contracts

1. `demo/timelog_demo.py` defaults to `demo/generated_5pct.csv` and auto-generates missing `generated_*.csv` files with `demo/hft_synthetic.py`.
2. `demo/timelog_benchmark.py --generate-data` guarantees both the primary generated dataset and its A6 comparison pair (`generated_5pct.csv` <-> `generated_20pct.csv`).
3. Large committed CSV fixtures are not required for CI benchmark/correctness flows.

## Correctness Source Contracts

1. `demo/correctness_checker.py --source-mode csv` is strict and fails when no valid `--csv` files are provided.
2. `--source-mode mixed` never silently degrades to single-source synthetic behavior:
   - With CSV paths: `mixed_csv_syn`.
   - Without CSV paths: `mixed_syn_syn` (primary + alternate synthetic OOO streams).
3. Nightly correctness CI includes:
   - synthetic 5% OOO leg
   - synthetic 20% OOO leg
   - mixed synthetic leg (5% primary + 20% alternate)

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

1. `Tests (PR) / test (ubuntu-latest, 3.12)`
2. `Tests (PR) / test (ubuntu-latest, 3.13)`
3. `Tests (PR) / test (windows-latest, 3.12)`
4. `Tests (PR) / test (windows-latest, 3.13)`
5. `Tests (PR) / subinterpreters (ubuntu-latest, 3.14)`
6. `Packaging (PR) / packaging-pr (cp313)`
7. `Packaging (PR) / packaging-pr (cp314t)`
8. `Packaging (PR) / packaging-pr (cp314t-aarch64)`
9. `Compatibility Baseline (PR) / compatibility-baseline (subinterpreters-3.14-ubuntu)`
10. `Compatibility Baseline (PR) / compatibility-baseline (subinterpreters-3.14-windows)`
11. `Compatibility Baseline (PR) / compatibility-baseline (freethreading-3.14t-ubuntu)`
12. `Docs Check (PR) / docs-check`
13. `Dependency Review / dependency-review`

The dedicated TSan free-threaded job remains advisory until runner stability is
characterized.

## Packaging and Release Workflows

1. PR packaging validation: `.github/workflows/packaging-pr.yml`
2. Dependency policy gate: `.github/workflows/dependency-review.yml`
3. Manual TestPyPI release: `.github/workflows/release-testpypi.yml`
4. Tag-triggered PyPI release: `.github/workflows/release-pypi.yml`

See `docs/pypi-release.md` for publish runbooks and OIDC setup.

## Local Dry-Run Commands

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DTIMELOG_BUILD_PYTHON=ON -DTIMELOG_BUILD_PY_TESTS=ON
cmake --build build --target timelog_e2e_build -j 2
python demo/ci/check_layer_a_static.py
python demo/ci/run_core_test_groups.py --build-dir build --config Release --summary-json demo/benchmark_runs/core.local.json --summary-md demo/benchmark_runs/core.local.md
ctest --test-dir build -C Release --output-on-failure -R '^py_.*_tests$'
cmake -E env PYTHONPATH="$PWD/python" python -m pytest python/tests -q
python -m unittest discover -s demo/tests -p "test_*.py" -v
```

## Local Compatibility Baseline Commands

Regular Python 3.14+ host:

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DTIMELOG_BUILD_PYTHON=ON -DTIMELOG_BUILD_PY_TESTS=ON
cmake --build build --target timelog_e2e_build -j 2
ctest --test-dir build -C Release --output-on-failure -R '^py_module_tests$'
cmake -E env PYTHONPATH="$PWD/python" python -m pytest python/tests/test_subinterpreters.py -q -rA
cmake -E env PYTHONPATH="$PWD/python" TIMELOG_STRESS_TESTS=1 TIMELOG_SHORT_STRESS=1 python -m pytest python/tests/test_compat_stress.py -q -rA
cmake -E env PYTHONPATH="$PWD/python" TIMELOG_STRESS_TESTS=1 TIMELOG_SHORT_STRESS=1 python demo/ci/run_compat_baseline.py --legs subinterpreters,stress --summary-json demo/benchmark_runs/compat.local.json --summary-md demo/benchmark_runs/compat.local.md
```

Free-threaded `t` build host:

```bash
cmake -E env PYTHONPATH="$PWD/python" PYTHON_GIL=0 python -m pytest python/tests/test_free_threading.py -q -rA
cmake -E env PYTHONPATH="$PWD/python" PYTHON_GIL=0 python demo/ci/run_compat_baseline.py --legs freethreading --summary-json demo/benchmark_runs/compat-ft.local.json --summary-md demo/benchmark_runs/compat-ft.local.md
```

## Local Packaging Dry-Run Commands

```bash
python -m pip install --upgrade pip build twine
python -m build
python -m twine check dist/*

python -m venv .venv-wheel-smoke
source .venv-wheel-smoke/bin/activate
python -m pip install --upgrade pip
python -m pip install dist/timelog_lib-*.whl
python -m pytest python/tests -q
```
