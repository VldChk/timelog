#!/usr/bin/env python3
"""Methodology scenario registry built on top of timelog_demo features."""

from __future__ import annotations

import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import timelog_demo as td

from benchmark_schema import BenchmarkCaseContext, BenchmarkScenarioSpec


@dataclass
class ScenarioState:
    runner: td.DemoRunner
    feature: dict[str, Any]
    log: td.Timelog | None = None
    records: list[tuple[int, td.Order]] | None = None
    extra: dict[str, Any] | None = None


def _runner_from_ctx(ctx: BenchmarkCaseContext) -> td.DemoRunner:
    return td.DemoRunner(
        data_path=ctx.data_path,
        quick=ctx.quick,
        verbose=False,
        no_perf=True,
        csv_mode=ctx.csv_mode,
        ingest_mode=ctx.ingest_mode,
        preload_csv=ctx.preload_csv,
        reuse_obj=ctx.reuse_obj,
        track_memory=ctx.track_memory,
        track_gc=ctx.track_gc,
        repeat_min_seconds=0.0,
        repeat_max_runs=1,
        log_overrides=ctx.log_overrides,
    )


def _default_setup(ctx: BenchmarkCaseContext) -> ScenarioState:
    assert ctx.feature_code is not None
    feature = td.FEATURES[ctx.feature_code]
    runner = _runner_from_ctx(ctx)
    log = None
    if feature["category"] in td.SHARED_LOG_CATEGORIES:
        log = td.Timelog.for_streaming(time_unit="ns")
        runner.log = log
        # Methodology boundary: pre-load shared read-path data in setup.
        runner.ensure_data_loaded()
    return ScenarioState(runner=runner, feature=feature, log=log)


def _default_measure(ctx: BenchmarkCaseContext, state: ScenarioState) -> dict[str, Any]:
    _ = ctx
    return state.feature["func"](state.runner)


def _default_warmup(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = _default_measure(ctx, state)


def _default_teardown(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = ctx
    if state.log is not None:
        state.log.close()


# -------------------------
# Corrected boundary cases
# -------------------------

def _a2b_setup(ctx: BenchmarkCaseContext) -> ScenarioState:
    runner = _runner_from_ctx(ctx)
    limit = runner.limit if runner.limit else 0
    records = list(td.load_orders(ctx.data_path, limit=limit))
    log = td.Timelog.for_streaming(time_unit="ns")
    return ScenarioState(runner=runner, feature=td.FEATURES["A2B"], log=log, records=records)


def _a2b_measure(ctx: BenchmarkCaseContext, state: ScenarioState) -> dict[str, Any]:
    _ = ctx
    assert state.log is not None
    assert state.records is not None
    batch_size = 10_000
    total = 0
    for i in range(0, len(state.records), batch_size):
        batch = state.records[i : i + batch_size]
        state.log.extend(batch)
        total += len(batch)
    return {"records": total, "records_in": total}


def _a2b_warmup(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = _a2b_measure(ctx, state)


def _a2b_teardown(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = ctx
    if state.log is not None:
        state.log.close()


def _a6_setup(ctx: BenchmarkCaseContext) -> ScenarioState:
    runner = _runner_from_ctx(ctx)
    alt_path = td._alternate_dataset_path(ctx.data_path)
    if alt_path is None:
        paired = td.paired_dataset_path(ctx.data_path)
        if paired is not None and Path(paired).exists():
            alt_path = paired
    if alt_path is None:
        alt_path = ctx.data_path
    return ScenarioState(
        runner=runner,
        feature=td.FEATURES["A6"],
        extra={"primary_path": ctx.data_path, "alternate_path": alt_path},
    )


def _a6_measure(ctx: BenchmarkCaseContext, state: ScenarioState) -> dict[str, Any]:
    _ = ctx
    assert state.extra is not None
    primary_path = state.extra["primary_path"]
    alternate_path = state.extra["alternate_path"]
    limit = min(state.runner.limit or 50_000, 20_000)
    cases: dict[str, dict[str, Any]] = {}
    for label, path in [("primary", primary_path), ("alternate", alternate_path)]:
        records = list(td.load_orders(path, limit=limit))
        start = time.perf_counter_ns()
        log = td.Timelog.for_streaming(time_unit="ns")
        try:
            batch_size = 10_000
            for i in range(0, len(records), batch_size):
                log.extend(records[i : i + batch_size])
        finally:
            log.close()
        elapsed = time.perf_counter_ns() - start
        wall_s = elapsed / 1e9
        rps = len(records) / wall_s if wall_s > 0 else 0.0
        cases[label] = {
            "path": path,
            "records": len(records),
            "wall_time_s": wall_s,
            "records_per_sec": rps,
        }
    total_records = sum(v["records"] for v in cases.values())
    return {"records": total_records, "records_in": total_records, "cases": cases}


def _a6_warmup(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = _a6_measure(ctx, state)


def _a6_teardown(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = (ctx, state)


def _d3_setup(ctx: BenchmarkCaseContext) -> ScenarioState:
    runner = _runner_from_ctx(ctx)
    limit = min(runner.limit, 10_000) if runner.limit else 10_000
    records = list(td.load_orders(ctx.data_path, limit=limit))
    log = td.Timelog.for_bulk_ingest(time_unit="ns")
    log.extend(records)
    target_ts = records[100][0] if len(records) > 100 else records[0][0]
    return ScenarioState(
        runner=runner,
        feature=td.FEATURES["D3"],
        log=log,
        records=records,
        extra={"target_ts": target_ts},
    )


def _d3_measure(ctx: BenchmarkCaseContext, state: ScenarioState) -> dict[str, Any]:
    _ = ctx
    assert state.log is not None
    assert state.records is not None
    assert state.extra is not None
    target_ts = state.extra["target_ts"]
    before = list(state.log.at(target_ts))
    state.log.delete(target_ts, target_ts + 1)
    after = list(state.log.at(target_ts))
    return {
        "records": len(state.records),
        "ops": 1,
        "target_ts": target_ts,
        "before_count": len(before),
        "after_count": len(after),
    }


def _d3_assert(result: dict[str, Any]) -> tuple[bool, str]:
    ok = result.get("before_count", 0) >= 1 and result.get("after_count", 1) == 0
    return ok, "before>=1 and after==0"


def _d3_teardown(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = ctx
    if state.log is not None:
        state.log.close()


def _d4_setup(ctx: BenchmarkCaseContext) -> ScenarioState:
    runner = _runner_from_ctx(ctx)
    limit = min(runner.limit, 50_000) if runner.limit else 50_000
    records = list(td.load_orders(ctx.data_path, limit=limit))
    log = td.Timelog.for_bulk_ingest(time_unit="ns")
    log.extend(records)
    first = next(iter(log))[0]
    query_start = first
    query_end = first + 60_000_000_000
    del_start = first + 20_000_000_000
    del_end = first + 40_000_000_000
    return ScenarioState(
        runner=runner,
        feature=td.FEATURES["D4"],
        log=log,
        records=records,
        extra={
            "query_start": query_start,
            "query_end": query_end,
            "del_start": del_start,
            "del_end": del_end,
        },
    )


def _d4_measure(ctx: BenchmarkCaseContext, state: ScenarioState) -> dict[str, Any]:
    _ = ctx
    assert state.log is not None
    assert state.extra is not None
    del_start = state.extra["del_start"]
    del_end = state.extra["del_end"]
    state.log.delete(del_start, del_end)
    results = list(state.log[state.extra["query_start"] : state.extra["query_end"]])
    in_deleted = sum(1 for ts, _ in results if del_start <= ts < del_end)
    return {
        "records": len(results),
        "records_out": len(results),
        "ops": 2,
        "in_deleted_range": in_deleted,
    }


def _d4_assert(result: dict[str, Any]) -> tuple[bool, str]:
    ok = result.get("in_deleted_range", 1) == 0
    return ok, "in_deleted_range==0"


def _d4_teardown(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = ctx
    if state.log is not None:
        state.log.close()


def _e3_setup(ctx: BenchmarkCaseContext) -> ScenarioState:
    runner = _runner_from_ctx(ctx)
    limit = min(runner.limit, 50_000) if runner.limit else 50_000
    records = list(td.load_orders(ctx.data_path, limit=limit))
    log = td.Timelog.for_streaming(time_unit="ns")
    return ScenarioState(runner=runner, feature=td.FEATURES["E3"], log=log, records=records)


def _e3_measure(ctx: BenchmarkCaseContext, state: ScenarioState) -> dict[str, Any]:
    _ = ctx
    assert state.log is not None
    assert state.records is not None
    count = 0
    for ts, order in state.records:
        state.log.append(ts, order)
        count += 1
    return {"records": count, "records_in": count}


def _e3_teardown(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = ctx
    if state.log is not None:
        state.log.close()


def _e4_setup(ctx: BenchmarkCaseContext) -> ScenarioState:
    runner = _runner_from_ctx(ctx)
    limit = min(runner.limit, 20_000) if runner.limit else 20_000
    records = list(td.load_orders(ctx.data_path, limit=limit))
    log = td.Timelog.for_streaming(time_unit="ns")
    return ScenarioState(runner=runner, feature=td.FEATURES["E4"], log=log, records=records)


def _e4_measure(ctx: BenchmarkCaseContext, state: ScenarioState) -> dict[str, Any]:
    _ = ctx
    assert state.log is not None
    assert state.records is not None
    count = 0
    for ts, order in state.records:
        state.log.append(ts, order)
        count += 1
    state.log.stop_maintenance()
    state.log.start_maintenance()
    for ts, order in state.records:
        state.log.append(ts, order)
        count += 1
    state.log.stop_maintenance()
    return {"records": count, "records_in": count, "ops": 3}


def _e4_teardown(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = ctx
    if state.log is not None:
        state.log.close()


def _f4_setup(ctx: BenchmarkCaseContext) -> ScenarioState:
    runner = _runner_from_ctx(ctx)
    log = td.Timelog.for_streaming(time_unit="ns")
    runner.log = log
    runner.ensure_data_loaded()
    runner.log.flush()
    first = next(iter(runner.log))[0]
    window = 10_000_000_000
    return ScenarioState(
        runner=runner,
        feature=td.FEATURES["F4"],
        log=log,
        extra={"first": first, "window": window},
    )


def _f4_measure(ctx: BenchmarkCaseContext, state: ScenarioState) -> dict[str, Any]:
    _ = ctx
    if td.np is None:
        return {"records": 0, "error": "numpy not installed"}
    assert state.log is not None
    assert state.extra is not None
    total_timestamps = 0
    avg_gap = 0.0
    first = state.extra["first"]
    window = state.extra["window"]
    with state.log.views(first, first + window) as spans:
        for span in spans:
            with span as live_span:
                arr = td.np.asarray(live_span.timestamps)
                total_timestamps += len(arr)
                if len(arr) > 1:
                    avg_gap = float(td.np.mean(td.np.diff(arr)))
                del arr
            break
    return {
        "records": total_timestamps,
        "timestamps": total_timestamps,
        "dtype": "int64",
        "avg_gap_ns": avg_gap,
    }


def _f4_teardown(ctx: BenchmarkCaseContext, state: ScenarioState) -> None:
    _ = ctx
    if state.log is not None:
        state.log.close()


# -------------------------
# Metadata mapping
# -------------------------

_MEASUREMENT_TYPE_BY_CATEGORY = {
    "A": "e2e",
    "B": "engine_only",
    "C": "engine_only",
    "D": "api_overhead",
    "E": "api_overhead",
    "F": "engine_only",
    "G": "engine_only",
    "H": "engine_only",
    "I": "engine_only",
    "J": "engine_only",
    "K": "mixed_workload",
}

_PRIMARY_UNIT_OVERRIDES = {
    "A0": "records_in_per_sec",
    "A1": "records_in_per_sec",
    "A2": "records_in_per_sec",
    "A2B": "records_in_per_sec",
    "A3": "records_in_per_sec",
    "A4": "records_in_per_sec",
    "A5": "records_in_per_sec",
    "A6": "records_in_per_sec",
    "B5": "queries_per_sec",
    "B6": "queries_per_sec",
    "B7": "ops_per_sec",
    "B8": "ops_per_sec",
    "D1": "ops_per_sec",
    "D2": "ops_per_sec",
    "D3": "ops_per_sec",
    "D4": "records_out_per_sec",
    "E1": "ms_per_op",
    "E2": "ms_per_op",
    "E3": "records_in_per_sec",
    "E4": "records_in_per_sec",
    "F1": "timestamps_per_sec",
    "F2": "timestamps_per_sec",
    "F3": "objects_per_sec",
    "F4": "timestamps_per_sec",
    "F5": "timestamps_per_sec",
    "H4": "queries_per_sec",
}

_DEFAULT_PRIMARY_BY_CATEGORY = {
    "A": "records_in_per_sec",
    "B": "records_out_per_sec",
    "C": "records_out_per_sec",
    "D": "ops_per_sec",
    "E": "ops_per_sec",
    "F": "timestamps_per_sec",
    "G": "records_out_per_sec",
    "H": "records_out_per_sec",
    "I": "records_out_per_sec",
    "J": "ops_per_sec",
    "K": "ops_per_sec",
}

_TIMING_BOUNDARY_BY_MEASUREMENT = {
    "e2e": "full_stack",
    "engine_only": "python_api",
    "api_overhead": "python_api",
    "mixed_workload": "mixed",
}

_STATE_BY_CATEGORY = {
    "A": "mixed",
    "B": "warm",
    "C": "warm",
    "D": "mixed",
    "E": "mixed",
    "F": "warm",
    "G": "warm",
    "H": "warm",
    "I": "mixed",
    "J": "na",
    "K": "mixed",
}

_EXPECTED_MODEL_BY_CATEGORY = {
    "A": "append/extend throughput",
    "B": "range/point retrieval",
    "C": "scan + analytics",
    "D": "tombstone + query filtering",
    "E": "maintenance control/ops",
    "F": "zero-copy buffer operations",
    "G": "iterator behavior",
    "H": "domain analytics workload",
    "I": "tiered read comparison",
    "J": "complexity validation",
    "K": "production mixed workload",
}


def _default_correctness_assert(result: dict[str, Any]) -> tuple[bool, str]:
    if "error" in result:
        return False, str(result["error"])
    return True, "ok"


def _numpy_optional_correctness_assert(result: dict[str, Any]) -> tuple[bool, str]:
    if result.get("error") == "numpy not installed":
        return True, "optional dependency missing: numpy"
    return _default_correctness_assert(result)


def _default_complexity_assert(result: dict[str, Any]) -> tuple[bool, str]:
    if "complexity_verified" in result:
        v = result["complexity_verified"]
        ok = bool(v) if not isinstance(v, str) else v.upper().startswith("O(")
        return ok, f"complexity_verified={v}"
    return True, "na"


def _spec_from_code(code: str, feature: dict[str, Any]) -> BenchmarkScenarioSpec:
    category = feature["category"]
    measurement_type = _MEASUREMENT_TYPE_BY_CATEGORY[category]
    primary_unit = _PRIMARY_UNIT_OVERRIDES.get(code, _DEFAULT_PRIMARY_BY_CATEGORY[category])
    timing_boundary = _TIMING_BOUNDARY_BY_MEASUREMENT[measurement_type]
    state_profile = _STATE_BY_CATEGORY[category]
    expected_model = _EXPECTED_MODEL_BY_CATEGORY[category]

    setup_fn = _default_setup
    warmup_fn = _default_warmup
    measure_fn = _default_measure
    teardown_fn = _default_teardown
    correctness_assert_fn = _default_correctness_assert
    complexity_assert_fn = _default_complexity_assert if code.startswith("J") else None

    if code == "A2B":
        setup_fn = _a2b_setup
        warmup_fn = _a2b_warmup
        measure_fn = _a2b_measure
        teardown_fn = _a2b_teardown
    elif code == "A6":
        setup_fn = _a6_setup
        warmup_fn = _a6_warmup
        measure_fn = _a6_measure
        teardown_fn = _a6_teardown
    elif code == "D3":
        setup_fn = _d3_setup
        warmup_fn = _default_warmup
        measure_fn = _d3_measure
        teardown_fn = _d3_teardown
        correctness_assert_fn = _d3_assert
    elif code == "D4":
        setup_fn = _d4_setup
        warmup_fn = _default_warmup
        measure_fn = _d4_measure
        teardown_fn = _d4_teardown
        correctness_assert_fn = _d4_assert
    elif code == "E3":
        setup_fn = _e3_setup
        warmup_fn = _default_warmup
        measure_fn = _e3_measure
        teardown_fn = _e3_teardown
    elif code == "E4":
        setup_fn = _e4_setup
        warmup_fn = _default_warmup
        measure_fn = _e4_measure
        teardown_fn = _e4_teardown
    elif code == "F4":
        setup_fn = _f4_setup
        warmup_fn = _default_warmup
        measure_fn = _f4_measure
        teardown_fn = _f4_teardown

    if code in {"F4", "F5"}:
        correctness_assert_fn = _numpy_optional_correctness_assert

    return BenchmarkScenarioSpec(
        scenario_id=code,
        name=feature["name"],
        category=category,
        measurement_type=measurement_type,
        primary_unit=primary_unit,
        timing_boundary=timing_boundary,
        state_profile=state_profile,
        expected_model=expected_model,
        setup_fn=setup_fn,
        warmup_fn=warmup_fn,
        measure_fn=measure_fn,
        teardown_fn=teardown_fn,
        correctness_assert_fn=correctness_assert_fn,
        complexity_assert_fn=complexity_assert_fn,
    )


def build_scenario_registry() -> dict[str, BenchmarkScenarioSpec]:
    specs: dict[str, BenchmarkScenarioSpec] = {}
    for code, feature in td.FEATURES.items():
        specs[code] = _spec_from_code(code, feature)
    return specs
