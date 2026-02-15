#!/usr/bin/env python3
"""Core execution engine for methodology benchmarks."""

from __future__ import annotations

import platform
import time
from dataclasses import asdict, replace
from pathlib import Path
from typing import Any

from benchmark_baseline import apples_contract, compare_to_baseline, load_baseline
from benchmark_models import compute_scenario_stats, evaluate_complexity_from_result
from benchmark_schema import (
    BenchmarkCaseContext,
    BenchmarkScenarioSpec,
    GateStatus,
    PhaseTiming,
    RunSample,
)

_DATASET_ROW_CACHE: dict[str, int] = {}


def _extract_primary_count(result: dict[str, Any], primary_unit: str) -> float:
    if primary_unit == "records_in_per_sec":
        return float(result.get("records_in", result.get("records", 0)))
    if primary_unit == "records_out_per_sec":
        return float(result.get("records_out", result.get("records", 0)))
    if primary_unit == "queries_per_sec":
        return float(result.get("queries", result.get("records", 0)))
    if primary_unit == "ops_per_sec":
        return float(result.get("ops", result.get("records", 0)))
    if primary_unit == "timestamps_per_sec":
        return float(result.get("timestamps", result.get("records", 0)))
    if primary_unit == "objects_per_sec":
        return float(result.get("objects", result.get("records", 0)))
    if primary_unit == "bytes_per_sec":
        return float(result.get("bytes", 0))
    if primary_unit == "ms_per_op":
        return float(result.get("ops", 1))
    return float(result.get("records", 0))


def _extract_primary_rate(primary_unit: str, primary_count: float, measure_time_s: float) -> float:
    if measure_time_s <= 0:
        return 0.0
    if primary_unit == "ms_per_op":
        if primary_count <= 0:
            return 0.0
        return (measure_time_s * 1000.0) / primary_count
    return primary_count / measure_time_s


def _latency_ns_from_count(primary_count: float, measure_time_s: float) -> float:
    if primary_count <= 0 or measure_time_s <= 0:
        return 0.0
    return (measure_time_s * 1e9) / primary_count


def _dataset_rows_fast(path: Path) -> int:
    key = str(path)
    if key in _DATASET_ROW_CACHE:
        return _DATASET_ROW_CACHE[key]
    if not path.exists():
        _DATASET_ROW_CACHE[key] = 0
        return 0
    with path.open("rb") as f:
        line_count = 0
        chunk = f.read(1024 * 1024)
        while chunk:
            line_count += chunk.count(b"\n")
            chunk = f.read(1024 * 1024)
    # Exclude header when present.
    rows = max(0, line_count - 1)
    _DATASET_ROW_CACHE[key] = rows
    return rows


def run_scenario(
    spec: BenchmarkScenarioSpec,
    ctx: BenchmarkCaseContext,
    warmup_runs: int,
    measured_runs: int,
    baseline: dict[str, Any] | None,
) -> dict[str, Any]:
    warmup_runs = max(0, warmup_runs)
    measured_runs = max(1, measured_runs)

    phase = PhaseTiming()
    samples: list[RunSample] = []
    correctness_failures: list[str] = []
    complexity_failures: list[str] = []

    # Warmup passes
    for _ in range(warmup_runs):
        t0 = time.perf_counter()
        state = spec.setup_fn(ctx)
        t1 = time.perf_counter()
        spec.warmup_fn(ctx, state)
        t2 = time.perf_counter()
        spec.teardown_fn(ctx, state)
        t3 = time.perf_counter()

        phase.setup_time_s += t1 - t0
        phase.warmup_time_s += t2 - t1
        phase.teardown_time_s += t3 - t2

    last_result: dict[str, Any] = {}

    for i in range(measured_runs):
        t0 = time.perf_counter()
        state = spec.setup_fn(ctx)
        t1 = time.perf_counter()

        m0 = time.perf_counter()
        result = spec.measure_fn(ctx, state)
        m1 = time.perf_counter()

        td0 = time.perf_counter()
        spec.teardown_fn(ctx, state)
        td1 = time.perf_counter()

        setup_s = t1 - t0
        measure_s = m1 - m0
        teardown_s = td1 - td0

        phase.setup_time_s += setup_s
        phase.measure_time_s += measure_s
        phase.teardown_time_s += teardown_s

        primary_count = _extract_primary_count(result, spec.primary_unit)
        primary_rate = _extract_primary_rate(spec.primary_unit, primary_count, measure_s)
        primary_latency_ns = _latency_ns_from_count(primary_count, measure_s)

        samples.append(
            RunSample(
                run_index=i,
                measure_time_s=measure_s,
                primary_count=primary_count,
                primary_rate=primary_rate,
                primary_latency_ns=primary_latency_ns,
                result=result,
            )
        )

        ok, msg = (True, "ok")
        if spec.correctness_assert_fn is not None:
            ok, msg = spec.correctness_assert_fn(result)
        if not ok:
            correctness_failures.append(msg)

        last_result = result

    rates = [s.primary_rate for s in samples]
    latencies = [s.primary_latency_ns for s in samples]
    stats = compute_scenario_stats(rates, latencies, seed=ctx.seed)

    complexity_eval = evaluate_complexity_from_result(spec.scenario_id, last_result)
    if spec.complexity_assert_fn is not None:
        cok, cmsg = spec.complexity_assert_fn(last_result)
        if not cok:
            complexity_failures.append(cmsg)
    if complexity_eval.gate == "fail":
        complexity_failures.append(complexity_eval.summary)

    correctness_gate = "fail" if correctness_failures else "pass"
    if spec.scenario_id.startswith("J"):
        complexity_gate = "fail" if complexity_failures else "pass"
    else:
        complexity_gate = "na"

    dataset_id = Path(ctx.data_path).name
    contract = apples_contract(spec, dataset_id=dataset_id, quick=ctx.quick)

    throughput_gate = "na"
    throughput_detail: dict[str, Any] = {"reason": "baseline unavailable"}
    if baseline is not None:
        throughput_gate, throughput_detail = compare_to_baseline(
            baseline,
            spec.scenario_id,
            contract,
            stats.median_rate,
            primary_unit=spec.primary_unit,
        )

    gate_status = GateStatus(
        correctness=correctness_gate,
        complexity=complexity_gate,
        throughput=throughput_gate,
        details={
            "correctness_failures": correctness_failures,
            "complexity_failures": complexity_failures,
            "throughput": throughput_detail,
            "complexity_model": asdict(complexity_eval),
        },
    )

    # Best-effort scenario metadata extracted from final result.
    n_rows = _dataset_rows_fast(Path(ctx.data_path))
    metadata = {
        "dataset_id": dataset_id,
        "N": n_rows,
        "M": last_result.get("records", 0),
        "K": last_result.get("K"),
        "T": last_result.get("T"),
        "ooo_ratio": last_result.get("ooo_rate"),
        "duplicate_rate": last_result.get("duplicate_rate"),
        "maintenance_mode": ctx.log_overrides.get("maintenance", "default"),
    }

    return {
        "scenario_id": spec.scenario_id,
        "name": spec.name,
        "category": spec.category,
        "measurement_type": spec.measurement_type,
        "primary_unit": spec.primary_unit,
        "timing_boundary": spec.timing_boundary,
        "state_profile": spec.state_profile,
        "expected_model": spec.expected_model,
        # Flat aliases for schema consumers.
        "dataset_id": metadata["dataset_id"],
        "N": metadata["N"],
        "M": metadata["M"],
        "K": metadata["K"],
        "T": metadata["T"],
        "ooo_ratio": metadata["ooo_ratio"],
        "duplicate_rate": metadata["duplicate_rate"],
        "maintenance_mode": metadata["maintenance_mode"],
        "setup_time_s": phase.setup_time_s,
        "warmup_time_s": phase.warmup_time_s,
        "measure_time_s": phase.measure_time_s,
        "teardown_time_s": phase.teardown_time_s,
        "total_time_s": phase.total_time_s,
        "median": stats.median_rate,
        "p95": stats.p95_rate,
        "p99": stats.p99_rate,
        "mad": stats.mad_rate,
        "apples_contract": contract,
        "phase_timing": {
            "setup_time_s": phase.setup_time_s,
            "warmup_time_s": phase.warmup_time_s,
            "measure_time_s": phase.measure_time_s,
            "teardown_time_s": phase.teardown_time_s,
            "total_time_s": phase.total_time_s,
        },
        "stats": asdict(stats),
        "samples": [asdict(s) for s in samples],
        "last_result": last_result,
        "gates": asdict(gate_status),
        "metadata": metadata,
    }


def run_benchmark_suite(
    specs: list[BenchmarkScenarioSpec],
    base_ctx: BenchmarkCaseContext,
    warmup_runs: int,
    measured_runs: int,
    baseline_path: Path | None,
) -> list[dict[str, Any]]:
    baseline = None
    if baseline_path is not None:
        baseline = load_baseline(baseline_path)

    out: list[dict[str, Any]] = []
    for spec in specs:
        ctx = replace(base_ctx)
        ctx.feature_code = spec.scenario_id
        out.append(run_scenario(spec, ctx, warmup_runs, measured_runs, baseline))
    return out


def summarize_gate_counts(scenarios: list[dict[str, Any]]) -> dict[str, Any]:
    counts = {
        "correctness": {"pass": 0, "fail": 0, "na": 0, "warn": 0},
        "complexity": {"pass": 0, "fail": 0, "na": 0, "warn": 0},
        "throughput": {"pass": 0, "fail": 0, "na": 0, "warn": 0},
    }
    for s in scenarios:
        gates = s.get("gates", {})
        for gate_name in ("correctness", "complexity", "throughput"):
            state = gates.get(gate_name, "na")
            counts[gate_name][state] = counts[gate_name].get(state, 0) + 1

    return {
        "platform": platform.platform(),
        "scenario_count": len(scenarios),
        "gate_counts": counts,
    }
