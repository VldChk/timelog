#!/usr/bin/env python3
"""Schema/types for methodology benchmark runs."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any, Callable, Literal

MeasurementType = Literal["e2e", "engine_only", "api_overhead", "mixed_workload"]
PrimaryUnit = Literal[
    "records_in_per_sec",
    "records_out_per_sec",
    "queries_per_sec",
    "ops_per_sec",
    "ms_per_op",
    "timestamps_per_sec",
    "objects_per_sec",
    "bytes_per_sec",
]
TimingBoundary = Literal["full_stack", "python_api", "engine_core", "mixed"]
StateProfile = Literal["hot", "warm", "cold", "mixed", "na"]
GateOutcome = Literal["pass", "fail", "warn", "na"]


@dataclass
class BenchmarkScenarioSpec:
    scenario_id: str
    name: str
    category: str
    measurement_type: MeasurementType
    primary_unit: PrimaryUnit
    timing_boundary: TimingBoundary
    state_profile: StateProfile
    expected_model: str
    # setup_fn returns scenario-local state object; measure_fn consumes it.
    setup_fn: Callable[["BenchmarkCaseContext"], Any]
    warmup_fn: Callable[["BenchmarkCaseContext", Any], None]
    measure_fn: Callable[["BenchmarkCaseContext", Any], dict[str, Any]]
    teardown_fn: Callable[["BenchmarkCaseContext", Any], None]
    correctness_assert_fn: Callable[[dict[str, Any]], tuple[bool, str]] | None = None
    complexity_assert_fn: Callable[[dict[str, Any]], tuple[bool, str]] | None = None


@dataclass
class BenchmarkCaseContext:
    data_path: str
    quick: bool
    csv_mode: str
    preload_csv: bool
    ingest_mode: str
    reuse_obj: bool
    track_memory: bool
    track_gc: bool
    seed: int
    log_overrides: dict[str, Any] = field(default_factory=dict)
    feature_code: str | None = None


@dataclass
class PhaseTiming:
    setup_time_s: float = 0.0
    warmup_time_s: float = 0.0
    measure_time_s: float = 0.0
    teardown_time_s: float = 0.0

    @property
    def total_time_s(self) -> float:
        return self.setup_time_s + self.warmup_time_s + self.measure_time_s + self.teardown_time_s


@dataclass
class RunSample:
    run_index: int
    measure_time_s: float
    primary_count: float
    primary_rate: float
    primary_latency_ns: float
    result: dict[str, Any]


@dataclass
class ScenarioStats:
    samples: int
    median_rate: float
    p95_rate: float
    p99_rate: float
    mad_rate: float
    ci95_low_rate: float
    ci95_high_rate: float
    median_latency_ns: float
    p95_latency_ns: float
    p99_latency_ns: float


@dataclass
class ComplexityFitResult:
    gate: GateOutcome
    summary: str
    metrics: dict[str, Any] = field(default_factory=dict)


@dataclass
class GateStatus:
    correctness: GateOutcome
    complexity: GateOutcome
    throughput: GateOutcome
    details: dict[str, Any] = field(default_factory=dict)


@dataclass
class MethodologyResultV1:
    schema_version: str
    timestamp: str
    profile: str
    platform: str
    python_version: str
    system: dict[str, Any]
    config: dict[str, Any]
    scenarios: list[dict[str, Any]]
    summary: dict[str, Any]


@dataclass
class BaselineScenario:
    scenario_id: str
    apples_contract: dict[str, Any]
    median_rate: float


def to_dict(obj: Any) -> Any:
    """Convert dataclass/object tree to plain JSON-serializable structures."""
    if hasattr(obj, "__dataclass_fields__"):
        return asdict(obj)
    return obj
