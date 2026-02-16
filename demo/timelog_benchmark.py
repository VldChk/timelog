#!/usr/bin/env python3
"""Methodology-compliant benchmark harness for Timelog."""

from __future__ import annotations

import argparse
import json
import platform
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

import timelog_demo as td

from benchmark_baseline import SCHEMA_VERSION, build_baseline_from_results, default_baseline_path, save_baseline
from benchmark_profiles import BenchmarkProfile, default_profile, load_custom_profile, profile_to_dict
from benchmark_report import write_markdown_report
from benchmark_runner import run_benchmark_suite, summarize_gate_counts
from benchmark_scenarios import build_scenario_registry
from benchmark_schema import BenchmarkCaseContext

DEFAULT_SEED = 12345


def _resolve_profile(args: argparse.Namespace) -> BenchmarkProfile:
    if args.profile == "custom" and args.config is not None:
        return load_custom_profile(Path(args.config), args.data)
    return default_profile(args.profile, args.data)


def _resolve_scenarios(
    all_specs: dict[str, Any],
    profile: BenchmarkProfile,
    scenario_override: str | None,
) -> list[str]:
    if scenario_override:
        wanted = [x.strip().upper() for x in scenario_override.split(",") if x.strip()]
        return [code for code in wanted if code in all_specs]

    if profile.scenarios == "all":
        return sorted(all_specs.keys())

    wanted = [x.upper() for x in profile.scenarios]
    return [code for code in wanted if code in all_specs]


def _load_json(path: Path) -> dict[str, Any]:
    with path.open() as f:
        return json.load(f)


def _ensure_data_generated(args: argparse.Namespace) -> None:
    """Generate benchmark CSV data on-the-fly if --generate-data is set."""
    if not getattr(args, "generate_data", False):
        return

    def _rate_from_name(path: Path, default: float) -> float:
        name = path.name
        if "20pct" in name:
            return 0.20
        if "5pct" in name:
            return 0.05
        return default

    data_path = Path(args.data)
    from hft_synthetic import generate_csv

    ooo_rate = getattr(args, "ooo_rate", 0.05)
    generate_rows = getattr(args, "generate_rows", 581_400)

    def _ensure_one(path: Path, rate: float) -> None:
        if path.exists():
            return
        print(f"[benchmark] Generating test data: {path} "
              f"(rows={generate_rows}, ooo_rate={rate})")
        generate_csv(
            path,
            rows=generate_rows,
            ooo_rate=rate,
            seed=args.seed,
        )

    # Primary benchmark dataset.
    _ensure_one(data_path, _rate_from_name(data_path, ooo_rate))

    # Scenario A6 compares against an alternate ordering profile; when using
    # generated datasets, ensure the paired file exists as well.
    alt = td._alternate_dataset_path(str(data_path))
    if alt is not None:
        alt_path = Path(alt)
        _ensure_one(alt_path, _rate_from_name(alt_path, ooo_rate))


def run_methodology(args: argparse.Namespace) -> tuple[int, dict[str, Any]]:
    _ensure_data_generated(args)
    profile = _resolve_profile(args)

    registry = build_scenario_registry()
    selected_codes = _resolve_scenarios(registry, profile, args.scenarios)
    selected_specs = [registry[code] for code in selected_codes]

    baseline_path = Path(args.baseline) if args.baseline else default_baseline_path(platform.platform())
    scenarios: list[dict[str, Any]] = []
    data_paths = profile.data_paths if profile.data_paths else [args.data]
    for data_path in data_paths:
        base_ctx = BenchmarkCaseContext(
            data_path=data_path,
            quick=profile.quick,
            csv_mode="validated" if not args.trust_csv else "trusted",
            preload_csv=args.preload_csv,
            ingest_mode="all",
            reuse_obj=args.reuse_obj,
            track_memory=not args.no_tracemalloc,
            track_gc=not args.no_tracemalloc,
            seed=args.seed,
            log_overrides={},
        )
        scenarios.extend(
            run_benchmark_suite(
                selected_specs,
                base_ctx,
                warmup_runs=profile.warmup_runs,
                measured_runs=profile.measured_runs,
                baseline_path=baseline_path,
            )
        )

    system_info = td.get_system_info()
    summary = summarize_gate_counts(scenarios)

    payload = {
        "schema_version": SCHEMA_VERSION,
        "timestamp": datetime.now().isoformat(),
        "profile": profile.name,
        "platform": platform.platform(),
        "python_version": sys.version,
        "system": system_info,
        "config": {
            "data_path": args.data,
            "data_paths": data_paths,
            "baseline_path": str(baseline_path),
            "seed": args.seed,
            "quick": profile.quick,
            "preload_csv": args.preload_csv,
            "trust_csv": args.trust_csv,
            "reuse_obj": args.reuse_obj,
            "profile": profile_to_dict(profile),
        },
        "scenarios": scenarios,
        "summary": summary,
    }

    if args.export_json:
        out_json = Path(args.export_json)
        out_json.parent.mkdir(parents=True, exist_ok=True)
        with out_json.open("w") as f:
            json.dump(payload, f, indent=2)
        print(f"Methodology JSON exported: {out_json}")

    if args.export_md:
        out_md = Path(args.export_md)
        write_markdown_report(payload, out_md)
        print(f"Methodology Markdown exported: {out_md}")

    if args.update_baseline:
        baseline_payload = build_baseline_from_results(
            schema_version=SCHEMA_VERSION,
            platform_name=payload["platform"],
            timestamp=payload["timestamp"],
            scenarios=scenarios,
        )
        save_baseline(baseline_path, baseline_payload)
        print(f"Baseline updated: {baseline_path}")

    gate_counts = summary.get("gate_counts", {})
    correctness_fail = gate_counts.get("correctness", {}).get("fail", 0)
    complexity_fail = gate_counts.get("complexity", {}).get("fail", 0)
    throughput_warn = gate_counts.get("throughput", {}).get("warn", 0)

    print(
        "Methodology summary | "
        f"scenarios={summary.get('scenario_count', 0)} "
        f"correctness_fail={correctness_fail} "
        f"complexity_fail={complexity_fail} "
        f"throughput_warn={throughput_warn}"
    )

    if correctness_fail > 0:
        return 2, payload
    if complexity_fail > 0:
        return 3, payload
    return 0, payload


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Timelog methodology benchmark harness")
    parser.add_argument("--profile", choices=["pr", "full", "custom"], default="pr")
    parser.add_argument("--config", type=str, help="Path to custom profile JSON config")
    parser.add_argument("--scenarios", type=str, help="Comma-separated scenario ids override")
    parser.add_argument("--data", type=str, default="demo/generated_5pct.csv")
    parser.add_argument("--baseline", type=str, default=None)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--export-json", type=str, default="demo/benchmark_runs/methodology_v1.json")
    parser.add_argument("--export-md", type=str, default="demo/benchmark_runs/methodology_v1.md")
    parser.add_argument("--update-baseline", action="store_true")
    parser.add_argument("--generate-data", action="store_true",
                        help="Generate CSV test data before benchmark if file missing")
    parser.add_argument("--ooo-rate", type=float, default=0.05,
                        help="OOO rate for generated data (default: 0.05)")
    parser.add_argument("--generate-rows", type=int, default=581_400,
                        help="Row count when generating data (default: 581400)")

    parser.add_argument("--trust-csv", action="store_true")
    parser.add_argument("--preload-csv", action="store_true")
    parser.add_argument("--reuse-obj", action="store_true")
    parser.add_argument("--no-tracemalloc", action="store_true")

    return parser


def run_from_demo_namespace(ns: argparse.Namespace) -> int:
    """Entry point used by timelog_demo.py forwarding path."""
    parser = build_parser()
    args = parser.parse_args([])

    args.profile = ns.methodology_profile
    args.config = ns.methodology_config
    args.data = ns.data
    args.baseline = ns.methodology_baseline
    args.seed = ns.methodology_seed
    args.export_json = ns.methodology_export_json
    args.export_md = ns.methodology_export_md
    args.update_baseline = False

    args.trust_csv = ns.trust_csv
    args.preload_csv = ns.preload_csv
    args.reuse_obj = ns.reuse_obj
    args.no_tracemalloc = ns.no_tracemalloc

    code, _payload = run_methodology(args)
    return code


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    code, _payload = run_methodology(args)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
