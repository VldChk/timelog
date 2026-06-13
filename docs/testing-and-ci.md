# Testing and CI

## Test Layers

1. Core C tests (`timelog_tests`) including grouped runs.
2. C-level CPython binding tests (CTest `py_*_tests`).
3. Python facade tests (`python/tests`).
4. Demo/methodology/correctness tests (`demo/tests`).
5. Compatibility legs for subinterpreters and free-threaded CPython.

## CI Workflows

- PR cross-platform test workflow: `.github/workflows/tests-pr.yml`
- PR packaging workflow: `.github/workflows/packaging-pr.yml`
- Compatibility baseline workflows:
  `.github/workflows/compatibility-baseline-pr.yml` and
  `.github/workflows/compatibility-baseline-main.yml`
- Correctness E2E workflows: `.github/workflows/correctness-e2e-*.yml`
- Methodology benchmark workflows: `.github/workflows/benchmark-methodology-*.yml`
- Docs consistency workflow: `.github/workflows/docs-check.yml`
- TestPyPI release workflow: `.github/workflows/release-testpypi.yml`
- PyPI release workflow: `.github/workflows/release-pypi.yml`

Detailed test commands and branch-protection checks are in `docs/CI_TESTS.md`.
Packaging and publishing runbook is in `docs/pypi-release.md`.

Current release support gates:

- regular CPython 3.12 and 3.13 on Linux/Windows in `tests-pr.yml`;
- CPython 3.14 subinterpreter compatibility;
- CPython 3.14t free-threaded compatibility with `PYTHON_GIL=0`;
- packaging smoke for regular and free-threaded wheel families.

## Demo/Verifier Runtime Behavior

1. `demo/timelog_demo.py` bootstrap:
   - Uses `demo/generated_5pct.csv` by default.
   - Auto-generates missing `generated_*.csv` inputs via `demo/hft_synthetic.py`.
2. Correctness checker source modes:
   - `synthetic`: single synthetic stream.
   - `csv`: strict CSV-only mode; requires valid `--csv` inputs.
   - `mixed`: explicit dual-source mode (`mixed_csv_syn` or `mixed_syn_syn`).
3. Correctness summaries include `source_contract` and `source_counters` for CI triage.
