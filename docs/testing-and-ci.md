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
