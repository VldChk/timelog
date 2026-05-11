"""Shared helpers for compatibility baseline tests."""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
import sys
import sysconfig
from types import ModuleType
from typing import Any

import pytest


def _env_flag(name: str) -> bool:
    value = os.environ.get(name, "")
    return value.strip().lower() in {"1", "true", "yes", "on"}


@dataclass(frozen=True)
class CompatRuntime:
    """Runtime capability probes shared by compatibility tests."""

    python_version: tuple[int, int, int]
    concurrent_interpreters: ModuleType | None
    free_threaded_build: bool
    has_gil_probe: bool
    stress_enabled: bool
    short_stress: bool

    @classmethod
    def detect(cls) -> "CompatRuntime":
        interpreters_mod: ModuleType | None
        try:
            import concurrent.interpreters as interpreters_mod
        except ImportError:
            interpreters_mod = None

        return cls(
            python_version=sys.version_info[:3],
            concurrent_interpreters=interpreters_mod,
            free_threaded_build=sysconfig.get_config_var("Py_GIL_DISABLED") == 1,
            has_gil_probe=hasattr(sys, "_is_gil_enabled"),
            stress_enabled=_env_flag("TIMELOG_STRESS_TESTS"),
            short_stress=_env_flag("TIMELOG_SHORT_STRESS"),
        )

    def require_subinterpreters(self) -> ModuleType:
        if self.python_version < (3, 14, 0):
            pytest.skip("requires Python 3.14+ for concurrent.interpreters")
        if self.concurrent_interpreters is None:
            pytest.skip("concurrent.interpreters is unavailable on this host")
        return self.concurrent_interpreters

    def require_free_threaded_build(self) -> None:
        if not self.free_threaded_build:
            pytest.skip("requires a free-threaded CPython build")
        if not self.has_gil_probe:
            pytest.skip("sys._is_gil_enabled() is unavailable on this host")

    def require_stress_enabled(self) -> bool:
        if not self.stress_enabled:
            pytest.skip("compatibility stress tests disabled (set TIMELOG_STRESS_TESTS=1)")
        return self.short_stress


_COMPAT_RUNTIME = CompatRuntime.detect()


@pytest.fixture(scope="session")
def compat_runtime() -> CompatRuntime:
    return _COMPAT_RUNTIME


@pytest.fixture(scope="session")
def compat_package_root() -> str:
    return str(Path(__file__).resolve().parents[1])


@pytest.fixture(scope="session")
def compat_repo_root() -> str:
    return str(Path(__file__).resolve().parents[2])


@pytest.fixture(scope="session")
def compat_env() -> dict[str, Any]:
    runtime = _COMPAT_RUNTIME
    return {
        "package_root": str(Path(__file__).resolve().parents[1]),
        "repo_root": str(Path(__file__).resolve().parents[2]),
        "python_version": runtime.python_version,
        "free_threaded_build": runtime.free_threaded_build,
        "has_gil_probe": runtime.has_gil_probe,
        "stress_enabled": runtime.stress_enabled,
        "short_stress": runtime.short_stress,
        "has_subinterpreters": runtime.concurrent_interpreters is not None,
    }
