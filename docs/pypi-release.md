# PyPI Release Guide (`timelog-lib`)

This guide covers packaging, testing, and publishing Timelog as the
distribution `timelog-lib` while preserving runtime imports:

```python
from timelog import Timelog
```

## Package Identity

1. Distribution name: `timelog-lib`
2. Import package: `timelog`
3. Initial published version: `1.0.0`

## Local Packaging Commands

Build source + wheel artifacts:

```bash
python -m pip install --upgrade pip build twine
python -m build
python -m twine check dist/*
```

Build only source distribution:

```bash
python -m build --sdist
```

Build only wheel:

```bash
python -m build --wheel
```

## Local Install Validation

Wheel install smoke test:

```bash
python -m venv .venv-wheel-smoke
source .venv-wheel-smoke/bin/activate
python -m pip install --upgrade pip
python -m pip install dist/timelog_lib-*.whl
python -c "import timelog; from timelog import Timelog; print(timelog.__version__)"
```

Quick runtime check:

```bash
python - <<'PY'
from timelog import Timelog
with Timelog() as log:
    log.append(1, "ok")
    assert list(log[1:2]) == [(1, "ok")]
print("smoke-pass")
PY
```

Source distribution install smoke test:

```bash
python -m venv .venv-sdist-smoke
source .venv-sdist-smoke/bin/activate
python -m pip install --upgrade pip
python -m pip install dist/timelog_lib-*.tar.gz
python -c "import timelog; from timelog import Timelog; print('sdist-pass')"
```

## CI Workflows

1. `.github/workflows/packaging-pr.yml`
2. `.github/workflows/release-testpypi.yml`
3. `.github/workflows/release-pypi.yml`

### Packaging PR Workflow

`packaging-pr.yml` runs on pull requests and performs:

1. `python -m build --sdist`
2. representative Linux wheel build via `cibuildwheel` (`cp313-manylinux_x86_64`)
3. `twine check dist/*`
4. wheel install + `python/tests` + smoke script

### TestPyPI Release Workflow

Trigger `.github/workflows/release-testpypi.yml` manually (`workflow_dispatch`):

1. build sdist on Ubuntu
2. build wheels on Linux/macOS/Windows
3. collect artifacts into `dist/`
4. run `twine check dist/*`
5. publish to TestPyPI with OIDC trusted publishing

### PyPI Release Workflow

`release-pypi.yml` triggers on git tags `v*`.

1. verify tag version matches `pyproject.toml` (`vX.Y.Z` <-> `project.version`)
2. build sdist + full wheel matrix
3. run `twine check dist/*`
4. publish to PyPI with OIDC trusted publishing

## Wheel Policy

Build matrix is defined in `pyproject.toml` under `[tool.cibuildwheel]`.

1. Python: `cp312`, `cp313`, `cp314`
2. Skip: `cp313t`, `cp314t`, `pp*`, `*-musllinux_*`
3. Linux arches: `x86_64`, `aarch64`
4. macOS arches: `x86_64`, `arm64`
5. Windows arch: `AMD64`

## Trusted Publishing Checklist

Complete these once per registry:

1. Ensure your PyPI and TestPyPI accounts have verified email and 2FA enabled.
2. In each index project settings, configure GitHub trusted publisher:
   - owner: `VldChk`
   - repository: `timelog`
   - workflow:
     - `release-testpypi.yml` for TestPyPI
     - `release-pypi.yml` for PyPI
   - environment (if enforced):
     - `testpypi`
     - `pypi`
3. Confirm GitHub workflow permissions include `id-token: write`.
4. Perform first publish to TestPyPI and validate install.
5. Publish tag `v1.0.0` to claim `timelog-lib` on PyPI.

## Release Operator Commands

Create and push a release tag:

```bash
git tag v1.0.0
git push origin v1.0.0
```

Run TestPyPI release before first production publish:

1. Open Actions in GitHub.
2. Run `Release (TestPyPI)` workflow manually.
3. Validate `pip install -i https://test.pypi.org/simple timelog-lib`.
