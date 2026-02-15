#!/usr/bin/env python3
"""Run core C tests group-by-group via TL_TEST_GROUPS and export summaries."""

from __future__ import annotations

import argparse
import json
import platform
import subprocess
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable


DEFAULT_GROUPS = [
    "internal_sync",
    "internal_data",
    "storage",
    "delta",
    "compaction",
    "pagespan",
    "adaptive",
    "functional",
    "api_semantics",
    "snapshot_lifetime",
    "invariants",
    "concurrency",
    "stress",
]


@dataclass(frozen=True)
class GroupResult:
    name: str
    exit_code: int
    duration_sec: float
    status: str
    failure_excerpt: str | None = None


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run timelog core tests one TL_TEST_GROUPS group at a time and export"
            " JSON/Markdown summaries."
        )
    )
    parser.add_argument(
        "--build-dir",
        required=True,
        help="CMake build directory used by ctest.",
    )
    parser.add_argument(
        "--config",
        default="Release",
        help="CTest config for multi-config generators (default: Release).",
    )
    parser.add_argument(
        "--ctest-regex",
        default="^timelog_tests$",
        help="CTest -R regex selecting the core test entry (default: ^timelog_tests$).",
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
    parser.add_argument(
        "--groups",
        default=",".join(DEFAULT_GROUPS),
        help="Comma-separated group override. Default is the canonical 13 groups.",
    )
    parser.add_argument(
        "--failure-lines",
        type=int,
        default=60,
        help="How many trailing lines of failing output to retain in summaries.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Per-group timeout in seconds (default: 300).",
    )
    return parser.parse_args()


def _parse_groups(groups_arg: str) -> list[str]:
    groups = [part.strip() for part in groups_arg.split(",") if part.strip()]
    if not groups:
        raise ValueError("At least one group is required.")
    return groups


def _tail_lines(text: str, count: int) -> str:
    lines = [line for line in text.splitlines() if line.strip()]
    if len(lines) <= count:
        return "\n".join(lines)
    return "\n".join(lines[-count:])


def _run_group(
    *,
    build_dir: str,
    config: str,
    ctest_regex: str,
    group: str,
    failure_lines: int,
    timeout: int,
) -> GroupResult:
    cmd = [
        "cmake",
        "-E",
        "env",
        f"TL_TEST_GROUPS={group}",
        "ctest",
        "--test-dir",
        build_dir,
        "-C",
        config,
        "--output-on-failure",
        "-R",
        ctest_regex,
    ]
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            errors="replace",
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        duration = time.perf_counter() - started
        combined = (exc.stdout or "") + "\n" + (exc.stderr or "")
        excerpt = _tail_lines(combined, failure_lines)
        return GroupResult(
            name=group,
            exit_code=-1,
            duration_sec=duration,
            status="fail",
            failure_excerpt=f"TIMEOUT after {timeout}s\n{excerpt}",
        )
    duration = time.perf_counter() - started

    status = "pass" if completed.returncode == 0 else "fail"
    excerpt = None
    if completed.returncode != 0:
        combined = "\n".join(
            chunk for chunk in (completed.stdout, completed.stderr) if chunk
        )
        excerpt = _tail_lines(combined, failure_lines)

    return GroupResult(
        name=group,
        exit_code=completed.returncode,
        duration_sec=duration,
        status=status,
        failure_excerpt=excerpt,
    )


def _ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def _to_json_payload(
    *,
    results: Iterable[GroupResult],
    started_at: datetime,
    finished_at: datetime,
    build_dir: str,
    config: str,
    ctest_regex: str,
) -> dict:
    rows = list(results)
    groups_passed = sum(1 for row in rows if row.status == "pass")
    groups_failed = len(rows) - groups_passed
    payload_rows = []
    for row in rows:
        entry = {
            "name": row.name,
            "exit_code": row.exit_code,
            "duration_sec": round(row.duration_sec, 6),
            "status": row.status,
        }
        if row.failure_excerpt:
            entry["failure_excerpt"] = row.failure_excerpt
        payload_rows.append(entry)

    return {
        "result": "pass" if groups_failed == 0 else "fail",
        "groups_total": len(rows),
        "groups_passed": groups_passed,
        "groups_failed": groups_failed,
        "groups": payload_rows,
        "started_at_utc": started_at.isoformat(),
        "finished_at_utc": finished_at.isoformat(),
        "runner_os": platform.system(),
        "build_dir": build_dir,
        "config": config,
        "ctest_regex": ctest_regex,
    }


def _write_markdown(path: Path, payload: dict) -> None:
    lines = [
        "# Core C Test Groups Summary",
        "",
        f"- result: `{payload['result']}`",
        f"- groups_total: `{payload['groups_total']}`",
        f"- groups_passed: `{payload['groups_passed']}`",
        f"- groups_failed: `{payload['groups_failed']}`",
        f"- runner_os: `{payload['runner_os']}`",
        "",
        "| Group | Status | Exit Code | Duration (s) |",
        "| --- | --- | --- | --- |",
    ]
    for row in payload["groups"]:
        lines.append(
            f"| `{row['name']}` | `{row['status']}` | `{row['exit_code']}` | "
            f"`{row['duration_sec']:.6f}` |"
        )

    failed = [row for row in payload["groups"] if row["status"] == "fail"]
    if failed:
        lines.extend(["", "## Failure Excerpts"])
        for row in failed:
            lines.extend(
                [
                    "",
                    f"### `{row['name']}`",
                    "```text",
                    row.get("failure_excerpt", "(no output captured)"),
                    "```",
                ]
            )

    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = _parse_args()
    groups = _parse_groups(args.groups)

    started_at = datetime.now(timezone.utc)
    results: list[GroupResult] = []

    print(f"Running {len(groups)} core test groups via TL_TEST_GROUPS...")
    for index, group in enumerate(groups, start=1):
        print(f"[{index}/{len(groups)}] group={group}")
        result = _run_group(
            build_dir=args.build_dir,
            config=args.config,
            ctest_regex=args.ctest_regex,
            group=group,
            failure_lines=args.failure_lines,
            timeout=args.timeout,
        )
        results.append(result)
        print(
            f"  status={result.status} exit_code={result.exit_code} "
            f"duration={result.duration_sec:.3f}s"
        )

    finished_at = datetime.now(timezone.utc)
    payload = _to_json_payload(
        results=results,
        started_at=started_at,
        finished_at=finished_at,
        build_dir=args.build_dir,
        config=args.config,
        ctest_regex=args.ctest_regex,
    )

    summary_json = Path(args.summary_json)
    summary_md = Path(args.summary_md)
    _ensure_parent(summary_json)
    _ensure_parent(summary_md)
    summary_json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    _write_markdown(summary_md, payload)

    print(f"Wrote JSON summary: {summary_json}")
    print(f"Wrote Markdown summary: {summary_md}")

    return 0 if payload["result"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
