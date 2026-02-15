#!/usr/bin/env python3
"""Reporting helpers for methodology benchmark artifacts."""

from __future__ import annotations

from datetime import datetime
from pathlib import Path
from typing import Any


def _fmt_gate(g: str) -> str:
    return g.upper()


def build_markdown_report(payload: dict[str, Any]) -> str:
    ts = payload.get("timestamp", datetime.now().isoformat())
    profile = payload.get("profile", "unknown")
    system = payload.get("system", {})
    summary = payload.get("summary", {})
    scenarios = payload.get("scenarios", [])

    lines: list[str] = []
    lines.append("# Timelog Methodology Benchmark Report")
    lines.append("")
    lines.append(f"- Timestamp: `{ts}`")
    lines.append(f"- Profile: `{profile}`")
    lines.append(f"- Platform: `{payload.get('platform', 'unknown')}`")
    lines.append(f"- Python: `{payload.get('python_version', 'unknown')}`")
    lines.append(f"- CPU Count: `{system.get('cpu_count', 'unknown')}`")
    lines.append(f"- Data Path: `{payload.get('config', {}).get('data_path', 'unknown')}`")
    lines.append("")

    gate_counts = summary.get("gate_counts", {})
    lines.append("## Gate Summary")
    lines.append("")
    lines.append("| Gate | pass | fail | warn | na |")
    lines.append("|---|---:|---:|---:|---:|")
    for gate in ("correctness", "complexity", "throughput"):
        c = gate_counts.get(gate, {})
        lines.append(
            f"| {gate} | {c.get('pass', 0)} | {c.get('fail', 0)} | {c.get('warn', 0)} | {c.get('na', 0)} |"
        )

    lines.append("")
    lines.append("## Scenario Results")
    lines.append("")
    lines.append(
        "| Scenario | Name | Type | Unit | Median | p95 | p99 | Correctness | Complexity | Throughput |"
    )
    lines.append("|---|---|---|---|---:|---:|---:|---|---|---|")

    for s in scenarios:
        stats = s.get("stats", {})
        gates = s.get("gates", {})
        median = stats.get("median_rate", 0.0)
        p95 = stats.get("p95_rate", 0.0)
        p99 = stats.get("p99_rate", 0.0)
        lines.append(
            f"| {s.get('scenario_id')} | {s.get('name')} | {s.get('measurement_type')} | {s.get('primary_unit')} "
            f"| {median:,.3f} | {p95:,.3f} | {p99:,.3f} "
            f"| {_fmt_gate(gates.get('correctness', 'na'))} "
            f"| {_fmt_gate(gates.get('complexity', 'na'))} "
            f"| {_fmt_gate(gates.get('throughput', 'na'))} |"
        )

    lines.append("")
    lines.append("## Apples Contract")
    lines.append("")
    lines.append("Methodology comparison is performed only when scenario apples-contract metadata matches baseline.")
    lines.append("")
    return "\n".join(lines)


def write_markdown_report(payload: dict[str, Any], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(build_markdown_report(payload))
