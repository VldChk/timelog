#!/usr/bin/env python3
"""Statistics and model-fitting utilities (stdlib-only)."""

from __future__ import annotations

import math
import random
import statistics
from typing import Any

from benchmark_schema import ComplexityFitResult, ScenarioStats


def percentile(values: list[float], p: float) -> float:
    if not values:
        return 0.0
    if len(values) == 1:
        return values[0]
    s = sorted(values)
    pos = (len(s) - 1) * p
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return s[lo]
    w = pos - lo
    return s[lo] * (1.0 - w) + s[hi] * w


def mad(values: list[float]) -> float:
    if not values:
        return 0.0
    med = statistics.median(values)
    deviations = [abs(v - med) for v in values]
    return statistics.median(deviations)


def bootstrap_ci95(values: list[float], seed: int, samples: int = 500) -> tuple[float, float]:
    if not values:
        return (0.0, 0.0)
    if len(values) == 1:
        return (values[0], values[0])
    rng = random.Random(seed)
    n = len(values)
    boots = []
    for _ in range(samples):
        draw = [values[rng.randrange(n)] for _ in range(n)]
        boots.append(statistics.median(draw))
    boots.sort()
    lo = boots[max(0, int(0.025 * (samples - 1)))]
    hi = boots[min(samples - 1, int(0.975 * (samples - 1)))]
    return (lo, hi)


def compute_scenario_stats(rates: list[float], latencies_ns: list[float], seed: int) -> ScenarioStats:
    ci_lo, ci_hi = bootstrap_ci95(rates, seed=seed)
    return ScenarioStats(
        samples=len(rates),
        median_rate=statistics.median(rates) if rates else 0.0,
        p95_rate=percentile(rates, 0.95),
        p99_rate=percentile(rates, 0.99),
        mad_rate=mad(rates),
        ci95_low_rate=ci_lo,
        ci95_high_rate=ci_hi,
        median_latency_ns=statistics.median(latencies_ns) if latencies_ns else 0.0,
        p95_latency_ns=percentile(latencies_ns, 0.95),
        p99_latency_ns=percentile(latencies_ns, 0.99),
    )


def fit_loglog_exponent(xs: list[float], ys: list[float]) -> dict[str, float]:
    points = [(x, y) for x, y in zip(xs, ys) if x > 0 and y > 0]
    if len(points) < 2:
        return {"slope": 0.0, "intercept": 0.0, "r2": 0.0}

    logx = [math.log(x) for x, _ in points]
    logy = [math.log(y) for _, y in points]
    n = len(points)

    sx = sum(logx)
    sy = sum(logy)
    sxx = sum(v * v for v in logx)
    sxy = sum(x * y for x, y in zip(logx, logy))

    denom = (n * sxx) - (sx * sx)
    if denom == 0:
        return {"slope": 0.0, "intercept": 0.0, "r2": 0.0}

    slope = ((n * sxy) - (sx * sy)) / denom
    intercept = (sy - slope * sx) / n

    yhat = [slope * x + intercept for x in logx]
    ybar = sy / n
    ss_res = sum((yy - yh) ** 2 for yy, yh in zip(logy, yhat))
    ss_tot = sum((yy - ybar) ** 2 for yy in logy)
    r2 = 1.0 - (ss_res / ss_tot) if ss_tot > 0 else 1.0

    return {"slope": slope, "intercept": intercept, "r2": r2}


def fit_linear_slope(xs: list[float], ys: list[float]) -> dict[str, float]:
    points = [(x, y) for x, y in zip(xs, ys)]
    if len(points) < 2:
        return {"slope": 0.0, "intercept": 0.0, "r2": 0.0}
    n = len(points)
    sx = sum(x for x, _ in points)
    sy = sum(y for _, y in points)
    sxx = sum(x * x for x, _ in points)
    sxy = sum(x * y for x, y in points)

    denom = (n * sxx) - (sx * sx)
    if denom == 0:
        return {"slope": 0.0, "intercept": 0.0, "r2": 0.0}

    slope = ((n * sxy) - (sx * sy)) / denom
    intercept = (sy - slope * sx) / n
    yhat = [slope * x + intercept for x, _ in points]
    ybar = sy / n
    ss_res = sum((y - yh) ** 2 for (_, y), yh in zip(points, yhat))
    ss_tot = sum((y - ybar) ** 2 for _, y in points)
    r2 = 1.0 - (ss_res / ss_tot) if ss_tot > 0 else 1.0
    return {"slope": slope, "intercept": intercept, "r2": r2}


def evaluate_complexity_from_result(scenario_id: str, result: dict[str, Any]) -> ComplexityFitResult:
    """Evaluate complexity gate from per-scenario output payload when available."""
    if scenario_id == "J1":
        ok = bool(result.get("all_correct", False)) and result.get("complexity_verified") == "O(M)"
        return ComplexityFitResult(
            gate="pass" if ok else "fail",
            summary="J1 iteration/result cardinality check",
            metrics={"all_correct": result.get("all_correct"), "complexity_verified": result.get("complexity_verified")},
        )

    if scenario_id == "J2":
        ok = bool(result.get("complexity_verified", False))
        return ComplexityFitResult(
            gate="pass" if ok else "fail",
            summary="J2 scaling exponent check",
            metrics={"scaling_exponent": result.get("scaling_exponent"), "verdict": result.get("verdict")},
        )

    if scenario_id == "J3":
        ok = bool(result.get("complexity_verified", False))
        return ComplexityFitResult(
            gate="pass" if ok else "fail",
            summary="J3 quadratic behavior detection",
            metrics={"avg_ratio": result.get("avg_ratio"), "is_quadratic": result.get("is_quadratic")},
        )

    return ComplexityFitResult(gate="na", summary="No complexity gate for this scenario", metrics={})
