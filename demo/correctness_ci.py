#!/usr/bin/env python3
"""CI orchestrator for correctness_checker.py profiles."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SEED = 12345
FAIL_STATUSES = "CONFIRMED_ENGINE_BUG,CHECKER_BUG"

CSV_7PCT = "demo/order_book_50MB_5pct_ooo_clean.csv"
CSV_21PCT = "demo/order_book_50MB_20pct_ooo_clean.csv"


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


@dataclass
class LegSpec:
    leg_id: str
    source_mode: str
    duration_seconds: int
    csv_paths: list[str]
    ci_profile: str


def _profile_legs(profile: str, duration_override_seconds: int | None) -> list[LegSpec]:
    if profile == "pr":
        duration = duration_override_seconds if duration_override_seconds is not None else 90
        return [
            LegSpec(
                leg_id="pr_csv_7pct",
                source_mode="csv",
                duration_seconds=duration,
                csv_paths=[CSV_7PCT],
                ci_profile="pr",
            )
        ]

    # nightly profile
    duration = duration_override_seconds if duration_override_seconds is not None else 200
    return [
        LegSpec(
            leg_id="nightly_csv_7pct",
            source_mode="csv",
            duration_seconds=duration,
            csv_paths=[CSV_7PCT],
            ci_profile="nightly",
        ),
        LegSpec(
            leg_id="nightly_csv_21pct",
            source_mode="csv",
            duration_seconds=duration,
            csv_paths=[CSV_21PCT],
            ci_profile="nightly",
        ),
        LegSpec(
            leg_id="nightly_mixed",
            source_mode="mixed",
            duration_seconds=duration,
            csv_paths=[CSV_7PCT, CSV_21PCT],
            ci_profile="nightly",
        ),
    ]


def _validate_legs(legs: list[LegSpec]) -> None:
    missing: list[str] = []
    for leg in legs:
        for csv in leg.csv_paths:
            if not (REPO_ROOT / csv).exists():
                missing.append(csv)
    if missing:
        uniq = sorted(set(missing))
        raise SystemExit(f"Missing CSV inputs for correctness CI: {', '.join(uniq)}")


def _load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as f:
        return json.load(f)


def _run_leg(
    *,
    leg: LegSpec,
    seed: int,
    python_exe: str,
    out_dir: Path,
    failure_bundle_dir: Path,
) -> dict[str, Any]:
    work_dir = out_dir / "work"
    work_dir.mkdir(parents=True, exist_ok=True)
    failure_bundle_dir.mkdir(parents=True, exist_ok=True)

    summary_json = out_dir / f"{leg.leg_id}.summary.json"
    summary_md = out_dir / f"{leg.leg_id}.summary.md"
    run_log = out_dir / f"{leg.leg_id}.log"
    bundle_out = failure_bundle_dir / f"{leg.leg_id}.failure_bundle.tar.gz"
    run_id = f"{leg.leg_id}_seed{seed}"

    cmd = [
        python_exe,
        "demo/correctness_checker.py",
        "--ci-profile",
        leg.ci_profile,
        "--artifact-mode",
        "fail-bundle",
        "--fail-statuses",
        FAIL_STATUSES,
        "--duration-seconds",
        str(leg.duration_seconds),
        "--seed",
        str(seed),
        "--source-mode",
        leg.source_mode,
        "--out-dir",
        str(work_dir),
        "--summary-json-out",
        str(summary_json),
        "--summary-md-out",
        str(summary_md),
        "--failure-bundle-out",
        str(bundle_out),
        "--run-id",
        run_id,
    ]
    for csv in leg.csv_paths:
        cmd.extend(["--csv", csv])

    try:
        proc = subprocess.run(
            cmd,
            cwd=str(REPO_ROOT),
            text=True,
            capture_output=True,
            check=False,
            timeout=leg.duration_seconds + 120,
        )
    except subprocess.TimeoutExpired as exc:
        timeout_msg = f"[correctness-ci] TIMEOUT: {leg.leg_id} exceeded {leg.duration_seconds + 120}s\n"
        log_payload = (exc.stdout or "") + "\n[stderr]\n" + (exc.stderr or "") + "\n" + timeout_msg
        run_log.write_text(log_payload, encoding="utf-8")
        print(timeout_msg, file=sys.stderr)
        return {
            "leg_id": leg.leg_id,
            "seed": seed,
            "source_mode": leg.source_mode,
            "duration_seconds": leg.duration_seconds,
            "csv_paths": leg.csv_paths,
            "return_code": -1,
            "result": "fail",
            "fail_status_counts": {"TIMEOUT": 1},
            "summary_path": str(summary_json),
            "artifacts": {"run_log": str(run_log)},
        }

    log_payload = proc.stdout
    if proc.stderr:
        log_payload += "\n[stderr]\n" + proc.stderr
    run_log.write_text(log_payload, encoding="utf-8")
    if proc.stdout:
        print(proc.stdout, end="")
    if proc.stderr:
        print(proc.stderr, end="", file=sys.stderr)

    summary: dict[str, Any] | None = None
    if summary_json.exists():
        summary = _load_json(summary_json)

    result = "fail" if proc.returncode != 0 else "pass"
    if summary is not None and summary.get("result") in {"pass", "fail"}:
        result = str(summary["result"])

    artifacts = {
        "summary_json": str(summary_json),
        "summary_md": str(summary_md),
        "run_log": str(run_log),
    }
    if bundle_out.exists():
        artifacts["failure_bundle"] = str(bundle_out)

    fail_counts: dict[str, int] = {}
    if summary is not None:
        fail_counts = dict(summary.get("gate", {}).get("fail_status_counts", {}))

    return {
        "leg_id": leg.leg_id,
        "seed": seed,
        "source_mode": leg.source_mode,
        "duration_seconds": leg.duration_seconds,
        "csv_paths": leg.csv_paths,
        "return_code": proc.returncode,
        "result": result,
        "fail_status_counts": fail_counts,
        "summary_path": str(summary_json),
        "artifacts": artifacts,
    }


def _build_markdown(payload: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Timelog Correctness CI Summary")
    lines.append("")
    lines.append(f"- Timestamp: `{payload.get('timestamp')}`")
    lines.append(f"- Profile: `{payload.get('profile')}`")
    lines.append(f"- Result: `{payload.get('result')}`")
    lines.append(f"- Exit code: `{payload.get('exit_code')}`")
    lines.append("")
    lines.append("## Legs")
    lines.append("")
    lines.append("| Leg | Source | Duration(s) | Result | Exit |")
    lines.append("|---|---|---:|---|---:|")
    for leg in payload.get("legs", []):
        lines.append(
            f"| {leg.get('leg_id')} | {leg.get('source_mode')} | {leg.get('duration_seconds')} | "
            f"{leg.get('result')} | {leg.get('return_code')} |"
        )
    lines.append("")
    lines.append("## Gate Counts")
    lines.append("")
    gate_counts = payload.get("gate_status_totals", {})
    for k, v in sorted(gate_counts.items()):
        lines.append(f"- `{k}`: `{v}`")
    return "\n".join(lines) + "\n"


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run correctness checker CI profiles")
    parser.add_argument("--profile", choices=["pr", "nightly"], default="pr")
    parser.add_argument("--out-dir", type=str, default="demo/correctness_ci_runs")
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--export-json", type=str, default=None)
    parser.add_argument("--export-md", type=str, default=None)
    parser.add_argument("--failure-bundle-dir", type=str, default=None)
    parser.add_argument("--python", type=str, default=sys.executable)
    parser.add_argument("--duration-override-seconds", type=int, default=None, help=argparse.SUPPRESS)
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    failure_bundle_dir = Path(args.failure_bundle_dir) if args.failure_bundle_dir else (out_dir / "failure_bundles")
    export_json = Path(args.export_json) if args.export_json else (out_dir / "correctness_ci_summary.json")
    export_md = Path(args.export_md) if args.export_md else (out_dir / "correctness_ci_summary.md")
    export_json.parent.mkdir(parents=True, exist_ok=True)
    export_md.parent.mkdir(parents=True, exist_ok=True)

    legs = _profile_legs(args.profile, args.duration_override_seconds)
    _validate_legs(legs)
    leg_results: list[dict[str, Any]] = []
    gate_totals: dict[str, int] = {}

    started = _utc_now_iso()
    for idx, leg in enumerate(legs):
        leg_seed = args.seed + idx
        print(f"[correctness-ci] running {leg.leg_id} (seed={leg_seed}, duration={leg.duration_seconds}s)")
        result = _run_leg(
            leg=leg,
            seed=leg_seed,
            python_exe=args.python,
            out_dir=out_dir,
            failure_bundle_dir=failure_bundle_dir,
        )
        leg_results.append(result)
        for status, count in result.get("fail_status_counts", {}).items():
            gate_totals[status] = gate_totals.get(status, 0) + int(count)

    failed_legs = [leg["leg_id"] for leg in leg_results if leg.get("result") == "fail"]
    overall_fail = bool(failed_legs)
    exit_code = 2 if overall_fail else 0

    payload = {
        "schema_version": "correctness_ci_v1",
        "timestamp": _utc_now_iso(),
        "started_utc": started,
        "profile": args.profile,
        "result": "fail" if overall_fail else "pass",
        "exit_code": exit_code,
        "seed_base": args.seed,
        "legs": leg_results,
        "failed_legs": failed_legs,
        "gate_status_totals": gate_totals,
    }

    export_json.write_text(json.dumps(payload, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    export_md.write_text(_build_markdown(payload), encoding="utf-8")
    print(f"[correctness-ci] JSON: {export_json}")
    print(f"[correctness-ci] MD: {export_md}")
    print(
        f"[correctness-ci] result={payload['result']} "
        f"legs={len(leg_results)} failed_legs={len(failed_legs)}"
    )
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
