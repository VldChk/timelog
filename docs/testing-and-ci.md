# Testing and CI

## Test Layers

1. Core C tests (`timelog_tests`) including grouped runs.
2. C-level CPython binding tests (CTest `py_*_tests`).
3. Python facade tests (`python/tests`).
4. Demo/methodology/correctness tests (`demo/tests`).

## CI Workflows

- PR cross-platform test workflow: `.github/workflows/tests-pr.yml`
- Correctness E2E workflows: `.github/workflows/correctness-e2e-*.yml`
- Methodology benchmark workflows: `.github/workflows/benchmark-methodology-*.yml`
- Docs consistency workflow: `.github/workflows/docs-check.yml`

Detailed test commands and branch-protection checks are in `docs/CI_TESTS.md`.

## Demo/Verifier Runtime Behavior

1. `demo/timelog_demo.py` bootstrap:
   - Uses `demo/generated_5pct.csv` by default.
   - Auto-generates missing `generated_*.csv` inputs via `demo/hft_synthetic.py`.
2. Correctness checker source modes:
   - `synthetic`: single synthetic stream.
   - `csv`: strict CSV-only mode; requires valid `--csv` inputs.
   - `mixed`: explicit dual-source mode (`mixed_csv_syn` or `mixed_syn_syn`).
3. Correctness summaries include `source_contract` and `source_counters` for CI triage.
