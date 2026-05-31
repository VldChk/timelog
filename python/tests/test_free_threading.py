"""Compatibility-baseline tests for free-threaded import behavior.

Importing the timelog C extension on a free-threaded CPython build
(Py_GIL_DISABLED=1) must NOT cause the runtime to re-enable the GIL.
The module's PyModuleDef declares Py_mod_gil = Py_MOD_GIL_NOT_USED,
which the runtime honors only when the extension is correctly
synchronized for genuine parallelism.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from textwrap import dedent

import pytest


pytestmark = [pytest.mark.freethreading]


def test_import_does_not_enable_gil(compat_runtime, compat_package_root):
    compat_runtime.require_free_threaded_build()

    script = dedent(
        """
        import json
        import sys

        before = sys._is_gil_enabled()
        import timelog  # noqa: F401
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

    completed = subprocess.run(
        [sys.executable, "-c", script],
        check=True,
        capture_output=True,
        env=env,
        text=True,
    )

    payload = json.loads(completed.stdout.strip().splitlines()[-1])
    assert payload["before"] is False, "PYTHON_GIL=0 should disable GIL before import"
    assert payload["after"] is False, (
        "Importing timelog re-enabled the GIL on a free-threaded build. "
        "This indicates Py_mod_gil = Py_MOD_GIL_NOT_USED was not set, or "
        "the runtime refused the declaration."
    )
