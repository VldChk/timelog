#!/usr/bin/env python3
"""Baseline I/O and regression classification for methodology benchmarks."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from benchmark_schema import BenchmarkScenarioSpec

SCHEMA_VERSION = "methodology_v1"
THROUGHPUT_REGRESSION_THRESHOLD = 0.10  # 10%


def detect_platform_bucket(platform_name: str) -> str:
    p = platform_name.lower()
    if "windows" in p:
        return "windows"
    return "linux"


def default_baseline_path(platform_name: str) -> Path:
    bucket = detect_platform_bucket(platform_name)
    return Path("benchmarks") / "baselines" / bucket / "methodology_v1.json"


def apples_contract(spec: BenchmarkScenarioSpec, dataset_id: str, quick: bool) -> dict[str, Any]:
    return {
        "measurement_type": spec.measurement_type,
        "primary_unit": spec.primary_unit,
        "timing_boundary": spec.timing_boundary,
        "state_profile": spec.state_profile,
        "dataset_id": dataset_id,
        "quick": bool(quick),
    }


def load_baseline(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {"schema_version": SCHEMA_VERSION, "scenarios": {}}
    with path.open() as f:
        data = json.load(f)
    if data.get("schema_version") != SCHEMA_VERSION:
        return {"schema_version": SCHEMA_VERSION, "scenarios": {}}
    data.setdefault("scenarios", {})
    return data


def save_baseline(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as f:
        json.dump(payload, f, indent=2)


def compare_to_baseline(
    baseline: dict[str, Any],
    scenario_id: str,
    contract: dict[str, Any],
    median_rate: float,
    primary_unit: str | None = None,
) -> tuple[str, dict[str, Any]]:
    """Return throughput gate outcome and details.

    Outcomes:
    - pass: matched baseline and no >10% regression
    - warn: matched baseline with >10% regression (advisory gate)
    - na: no matching baseline
    """
    entries = baseline.get("scenarios", {}).get(scenario_id, [])
    for entry in entries:
        if entry.get("apples_contract") != contract:
            continue
        base = float(entry.get("median_rate", 0.0))
        if base <= 0.0 or median_rate <= 0.0:
            return "na", {"reason": "non-positive baseline or median", "baseline_median_rate": base}
        delta = (median_rate - base) / base
        if primary_unit == "ms_per_op":
            # Lower is better for ms/op metrics.
            regressed = median_rate > (base * (1.0 + THROUGHPUT_REGRESSION_THRESHOLD))
        else:
            regressed = delta < -THROUGHPUT_REGRESSION_THRESHOLD
        return (
            "warn" if regressed else "pass",
            {
                "baseline_median_rate": base,
                "current_median_rate": median_rate,
                "delta_ratio": delta,
                "threshold_ratio": -THROUGHPUT_REGRESSION_THRESHOLD,
                "regressed": regressed,
            },
        )

    return "na", {"reason": "no apples-to-apples baseline match"}


def build_baseline_from_results(
    schema_version: str,
    platform_name: str,
    timestamp: str,
    scenarios: list[dict[str, Any]],
) -> dict[str, Any]:
    out: dict[str, Any] = {
        "schema_version": schema_version,
        "platform": detect_platform_bucket(platform_name),
        "generated_at": timestamp,
        "scenarios": {},
    }
    for s in scenarios:
        sid = s["scenario_id"]
        out["scenarios"].setdefault(sid, [])
        out["scenarios"][sid].append(
            {
                "apples_contract": s.get("apples_contract", {}),
                "median_rate": s.get("stats", {}).get("median_rate", 0.0),
            }
        )
    return out
