"""Compatibility-baseline tests for free-threaded import behavior."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from textwrap import dedent

import pytest


pytestmark = [pytest.mark.freethreading]

_LAYER_B_XFAIL_REASON = (
    "Layer B is not implemented yet: timelog does not declare no-GIL support "
    "and still relies on GIL-era binding assumptions."
)


def test_import_does_not_enable_gil(compat_runtime, compat_package_root):
    compat_runtime.require_free_threaded_build()

    script = dedent(
        """
        import json
        import sys

        before = sys._is_gil_enabled()

        try:
            import timelog
        except Exception as exc:
            print(
                json.dumps(
                    {
                        "before": before,
                        "after": None,
                        "error_type": type(exc).__name__,
                        "error": str(exc),
                    }
                )
            )
            raise

        after = sys._is_gil_enabled()
        print(json.dumps({"before": before, "after": after}))
        """
    )

    env = os.environ.copy()
    existing = env.get("PYTHONPATH", "")
    if existing:
        env["PYTHONPATH"] = compat_package_root + os.pathsep + existing
    else:
        env["PYTHONPATH"] = compat_package_root
    env["PYTHON_GIL"] = "0"

    try:
        completed = subprocess.run(
            [sys.executable, "-c", script],
            check=True,
            capture_output=True,
            env=env,
            text=True,
        )
    except subprocess.CalledProcessError as exc:
        payload = json.loads(exc.stdout.strip().splitlines()[-1])
        assert payload["before"] is False
        pytest.xfail(_LAYER_B_XFAIL_REASON)

    payload = json.loads(completed.stdout.strip().splitlines()[-1])
    assert payload["before"] is False
    if payload["after"] != payload["before"]:
        pytest.xfail(_LAYER_B_XFAIL_REASON)
