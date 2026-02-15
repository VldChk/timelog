#!/usr/bin/env python3
"""Methodology benchmark profile definitions."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

PR_SCENARIOS = [
    "A2",
    "A2B",
    "B4",
    "B5",
    "D3",
    "D4",
    "E3",
    "E4",
    "F4",
    "I3",
    "J1",
    "J2",
    "J3",
    "K1",
]


@dataclass
class BenchmarkProfile:
    name: str
    scenarios: list[str] | str  # "all" or explicit list
    warmup_runs: int
    measured_runs: int
    quick: bool
    data_paths: list[str]


def default_profile(profile_name: str, data_path: str) -> BenchmarkProfile:
    if profile_name == "pr":
        return BenchmarkProfile(
            name="pr",
            scenarios=PR_SCENARIOS,
            warmup_runs=1,
            measured_runs=3,
            quick=True,
            data_paths=[data_path],
        )
    if profile_name == "full":
        return BenchmarkProfile(
            name="full",
            scenarios="all",
            warmup_runs=3,
            measured_runs=10,
            quick=False,
            data_paths=[data_path],
        )

    # custom default fallback (can be replaced via config file)
    return BenchmarkProfile(
        name="custom",
        scenarios="all",
        warmup_runs=3,
        measured_runs=10,
        quick=False,
        data_paths=[data_path],
    )


def load_custom_profile(config_path: Path, default_data_path: str) -> BenchmarkProfile:
    with config_path.open() as f:
        raw = json.load(f)

    return BenchmarkProfile(
        name=str(raw.get("name", "custom")),
        scenarios=raw.get("scenarios", "all"),
        warmup_runs=int(raw.get("warmup_runs", 3)),
        measured_runs=int(raw.get("measured_runs", 10)),
        quick=bool(raw.get("quick", False)),
        data_paths=list(raw.get("data_paths", [default_data_path])),
    )


def profile_to_dict(profile: BenchmarkProfile) -> dict[str, Any]:
    return {
        "name": profile.name,
        "scenarios": profile.scenarios,
        "warmup_runs": profile.warmup_runs,
        "measured_runs": profile.measured_runs,
        "quick": profile.quick,
        "data_paths": profile.data_paths,
    }
