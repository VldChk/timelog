#!/usr/bin/env python3
"""Run compatibility-baseline pytest legs and export summaries."""

from __future__ import annotations

import argparse
import json
import platform
from dataclasses import dataclass
from datetime import datetime, timezone
import os
from pathlib import Path
import subprocess
import sys
import time
from typing import Any


LEG_CONFIG = {
    "subinterpreters": {
        "paths": ["python/tests/test_subinterpreters.py"],
        "marker": "subinterpreters",
    },
    "freethreading": {
        "paths": ["python/tests/test_free_threading.py"],
        "marker": "freethreading",
    },
    "stress": {
        "paths": ["python/tests/test_compat_stress.py"],
        "marker": "stress",
    },
}

SUMMARY_SCHEMA: dict[str, Any] = {
    "collected": 0,
    "passed": 0,
    "failed": 0,
    "errors": 0,
    "skipped": 0,
    "xfailed": 0,
    "xpassed": 0,
    "failed_nodeids": [],
    "error_nodeids": [],
    "xpassed_nodeids": [],
    "exit_code": 0,
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run compatibility-baseline pytest legs and export JSON/Markdown summaries."
        )
    )
    parser.add_argument(
        "--legs",
        default="subinterpreters,freethreading,stress",
        help="Comma-separated leg list. Default runs all known compatibility legs.",
    )
    parser.add_argument(
        "--summary-json",
        required=True,
        help="Output path for machine-readable summary JSON.",
    )
    parser.add_argument(
        "--summary-md",
        required=True,
        help="Output path for human-readable summary Markdown.",
    )
    return parser.parse_args()


def _parse_legs(raw: str) -> list[str]:
    legs = [part.strip() for part in raw.split(",") if part.strip()]
    if not legs:
        raise ValueError("At least one compatibility leg is required.")

    unknown = [leg for leg in legs if leg not in LEG_CONFIG]
    if unknown:
        raise ValueError(f"Unknown compatibility legs: {', '.join(sorted(unknown))}")

    return legs


def _ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def _parse_report_line(line: str, prefix: str) -> list[str] | None:
    if not line.startswith(prefix):
        return None

    payload = line[len(prefix):].strip()
    if not payload:
        return []
    return [part.strip() for part in payload.split(",") if part.strip()]


def _summary_from_stdout(stdout: str, exit_code: int) -> dict[str, Any]:
    summary = dict(SUMMARY_SCHEMA)
    summary["exit_code"] = exit_code

    for line in stdout.splitlines():
        line = line.strip()
        if line.startswith("COMPAT_BASELINE_COUNTS "):
            summary.update(json.loads(line.split(" ", 1)[1]))
            continue

        failed = _parse_report_line(line, "COMPAT_BASELINE_FAILED ")
        if failed is not None:
            summary["failed_nodeids"] = failed
            continue

        errors = _parse_report_line(line, "COMPAT_BASELINE_ERRORS ")
        if errors is not None:
            summary["error_nodeids"] = errors
            continue

        xpassed = _parse_report_line(line, "COMPAT_BASELINE_XPASSED ")
        if xpassed is not None:
            summary["xpassed_nodeids"] = xpassed

    return summary


def _subprocess_pytest_script() -> str:
    return """
import json
import pytest
import sys

SUMMARY_SCHEMA = %s

class Capture:
    def __init__(self):
        self.summary = dict(SUMMARY_SCHEMA)

    def pytest_collection_finish(self, session):
        self.summary["collected"] = len(session.items)

    def pytest_terminal_summary(self, terminalreporter, exitstatus, config):
        stats = terminalreporter.stats

        def nodeids(key):
            return [
                report.nodeid
                for report in stats.get(key, [])
                if hasattr(report, "nodeid")
            ]

        self.summary.update(
            {
                "exit_code": int(exitstatus),
                "passed": len(stats.get("passed", [])),
                "failed": len(stats.get("failed", [])),
                "errors": len(stats.get("error", [])),
                "skipped": len(stats.get("skipped", [])),
                "xfailed": len(stats.get("xfailed", [])),
                "xpassed": len(stats.get("xpassed", [])),
                "failed_nodeids": nodeids("failed"),
                "error_nodeids": nodeids("error"),
                "xpassed_nodeids": nodeids("xpassed"),
            }
        )

capture = Capture()
exit_code = pytest.main(sys.argv[1:], plugins=[capture])
print("COMPAT_BASELINE_COUNTS " + json.dumps(capture.summary, sort_keys=True))
if capture.summary["failed_nodeids"]:
    print("COMPAT_BASELINE_FAILED " + ", ".join(capture.summary["failed_nodeids"]))
if capture.summary["error_nodeids"]:
    print("COMPAT_BASELINE_ERRORS " + ", ".join(capture.summary["error_nodeids"]))
if capture.summary["xpassed_nodeids"]:
    print("COMPAT_BASELINE_XPASSED " + ", ".join(capture.summary["xpassed_nodeids"]))
raise SystemExit(int(exit_code))
""" % json.dumps(SUMMARY_SCHEMA, sort_keys=True)


@dataclass(frozen=True)
class LegResult:
    name: str
    status: str
    duration_sec: float
    summary: dict[str, Any]


def _classify_leg(summary: dict[str, Any]) -> str:
    if summary["collected"] == 0:
        return "fail"
    if summary["failed"] > 0 or summary["errors"] > 0 or summary["xpassed"] > 0:
        return "fail"
    if summary["passed"] == 0 and summary["xfailed"] == 0:
        return "fail"
    if summary["xfailed"] > 0:
        return "xfail"
    if summary["passed"] > 0:
        return "pass"
    return "skip"


def _run_leg(name: str) -> LegResult:
    config = LEG_CONFIG[name]
    args = [
        *config["paths"],
        "-q",
        "-rA",
        "-m",
        config["marker"],
    ]

    started = time.perf_counter()
    completed = subprocess.run(
        [sys.executable, "-c", _subprocess_pytest_script(), *args],
        capture_output=True,
        text=True,
        env=os.environ.copy(),
    )
    duration = time.perf_counter() - started

    summary = _summary_from_stdout(completed.stdout, completed.returncode)
    return LegResult(
        name=name,
        status=_classify_leg(summary),
        duration_sec=duration,
        summary=summary,
    )


def _to_payload(
    legs: list[LegResult], started_at: datetime, finished_at: datetime
) -> dict[str, Any]:
    result = "pass"
    if any(leg.status == "fail" for leg in legs):
        result = "fail"

    return {
        "result": result,
        "runner_os": platform.system(),
        "python": sys.version,
        "started_at_utc": started_at.isoformat(),
        "finished_at_utc": finished_at.isoformat(),
        "legs": [
            {
                "name": leg.name,
                "status": leg.status,
                "duration_sec": round(leg.duration_sec, 6),
                "summary": leg.summary,
            }
            for leg in legs
        ],
    }


def _write_markdown(path: Path, payload: dict[str, Any]) -> None:
    lines = [
        "# Compatibility Baseline Summary",
        "",
        f"- result: `{payload['result']}`",
        f"- runner_os: `{payload['runner_os']}`",
        f"- python: `{payload['python'].splitlines()[0]}`",
        "",
        "| Leg | Status | Collected | Pass | Skip | XFail | XPass | Fail | Error |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]

    for leg in payload["legs"]:
        summary = leg["summary"]
        lines.append(
            "| "
            f"{leg['name']} | "
            f"{leg['status']} | "
            f"{summary['collected']} | "
            f"{summary['passed']} | "
            f"{summary['skipped']} | "
            f"{summary['xfailed']} | "
            f"{summary['xpassed']} | "
            f"{summary['failed']} | "
            f"{summary['errors']} |"
        )
        for label, key in (
            ("xpassed", "xpassed_nodeids"),
            ("failed", "failed_nodeids"),
            ("errors", "error_nodeids"),
        ):
            nodeids = summary.get(key) or []
            if nodeids:
                lines.append("")
                lines.append(f"- `{leg['name']}` {label}: `{', '.join(nodeids)}`")

    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = _parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    python_root = repo_root / "python"
    if str(python_root) not in sys.path:
        sys.path.insert(0, str(python_root))

    legs = _parse_legs(args.legs)
    started_at = datetime.now(timezone.utc)
    results = [_run_leg(leg) for leg in legs]
    finished_at = datetime.now(timezone.utc)

    payload = _to_payload(results, started_at, finished_at)

    summary_json = Path(args.summary_json)
    summary_md = Path(args.summary_md)
    _ensure_parent(summary_json)
    _ensure_parent(summary_md)
    summary_json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    _write_markdown(summary_md, payload)

    return 0 if payload["result"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
