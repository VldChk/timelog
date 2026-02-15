#!/usr/bin/env python3
"""
Timelog Correctness Checker.

Chaotic long-run validator with dual-oracle verification, issue triage,
and structured artifacts:
  - ops.jsonl
  - checks.jsonl
  - issues.jsonl
  - summary.json
  - summary.md
  - issues/<issue_id>/{report.md,evidence.json}
"""

from __future__ import annotations

import argparse
import bisect
import csv
import gc
import hashlib
import json
import math
import random
import shutil
import subprocess
import sys
import tarfile
import time
import traceback
import weakref
from collections import Counter, deque
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable


# ---------------------------------------------------------------------------
# Ensure timelog is importable
# ---------------------------------------------------------------------------

_REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_REPO / "python"))
for _candidate in [
    _REPO / "bindings" / "cpython" / "build-test" / "Release",
    _REPO / "bindings" / "cpython" / "build-test" / "Debug",
    _REPO / "bindings" / "cpython" / "build-py313" / "Release",
    _REPO / "bindings" / "cpython" / "build-py313" / "Debug",
]:
    if _candidate.is_dir():
        sys.path.insert(0, str(_candidate))

from timelog import Timelog, TimelogBusyError, TimelogError  # noqa: E402
from timelog._api import TL_TS_MAX, TL_TS_MIN, _coerce_ts  # noqa: E402


DEFAULT_CSVS = [
    str(Path("demo") / "order_book_less_ordered_clean.csv"),
    str(Path("demo") / "order_book_more_ordered_clean.csv"),
]

ISSUE_STATUS_CONFIRMED = "CONFIRMED_ENGINE_BUG"
ISSUE_STATUS_CHECKER = "CHECKER_BUG"
ISSUE_STATUS_TRANSIENT = "UNCONFIRMED_TRANSIENT"
DEFAULT_FAIL_STATUSES = ISSUE_STATUS_CONFIRMED


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _safe_git_commit() -> str | None:
    try:
        out = subprocess.check_output(
            ["git", "-C", str(_REPO), "rev-parse", "--short", "HEAD"],
            stderr=subprocess.DEVNULL,
            text=True,
        )
        return out.strip() or None
    except Exception:
        return None


def _canonicalize(value: Any) -> Any:
    if isinstance(value, dict):
        return (
            "dict",
            tuple(
                (_canonicalize(k), _canonicalize(value[k]))
                for k in sorted(value.keys(), key=lambda x: repr(x))
            ),
        )
    if isinstance(value, list):
        return ("list", tuple(_canonicalize(v) for v in value))
    if isinstance(value, tuple):
        return ("tuple", tuple(_canonicalize(v) for v in value))
    if isinstance(value, set):
        return ("set", tuple(sorted((_canonicalize(v) for v in value), key=repr)))
    if isinstance(value, frozenset):
        return ("frozenset", tuple(sorted((_canonicalize(v) for v in value), key=repr)))
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, float):
        if math.isnan(value):
            return ("float", "nan")
        if math.isinf(value):
            return ("float", "+inf" if value > 0 else "-inf")
        return ("float", format(value, ".17g"))
    return value


def _payload_digest(value: Any) -> str:
    return hashlib.sha256(repr(_canonicalize(value)).encode("utf-8")).hexdigest()


def _normalize_csv_row(row: dict[str, str]) -> dict[str, Any]:
    int_fields = {"timestamp", "amount", "order_id"}
    float_fields = {"ask_price", "bid_price", "commission"}
    out: dict[str, Any] = {}
    for k, raw in row.items():
        if raw is None:
            out[k] = None
            continue
        v = raw.strip()
        if k in int_fields:
            try:
                out[k] = int(v)
                continue
            except ValueError:
                pass
        if k in float_fields:
            try:
                out[k] = float(v)
                continue
            except ValueError:
                pass
        out[k] = v
    return out


def _extract_rid_digest(obj: Any) -> tuple[int | None, str]:
    if isinstance(obj, dict) and obj.get("__cc_schema") == 1 and isinstance(obj.get("rid"), int):
        rid = int(obj["rid"])
        digest = obj.get("payload_digest")
        if isinstance(digest, str) and digest:
            return rid, digest
        return rid, _payload_digest(obj.get("payload"))
    return None, _payload_digest(obj)


@dataclass
class RunConfig:
    duration_seconds: int
    seed: int
    source_mode: str
    csv_paths: list[str]
    out_dir: str
    min_batch: int
    max_batch: int
    maintenance: str
    busy_policy: str
    full_verify_interval_ops: int
    full_verify_interval_seconds: int
    checkpoint_interval_ops: int
    len_checks: bool
    len_slice_samples: int
    len_consume_samples: int
    continue_on_mismatch: bool
    max_issues: int
    verbose: bool
    log_alias_path: str | None = None
    ci_profile: str = "off"
    artifact_mode: str = "full"
    fail_statuses: set[str] = field(default_factory=lambda: {DEFAULT_FAIL_STATUSES})
    summary_json_out: str | None = None
    summary_md_out: str | None = None
    failure_bundle_out: str | None = None
    run_id_override: str | None = None


@dataclass
class RunOutcome:
    exit_code: int
    result: str
    fail_status_counts: dict[str, int]
    artifact_manifest: dict[str, Any] = field(default_factory=dict)


def _parse_fail_statuses(raw: str | None) -> set[str]:
    if raw is None:
        return {DEFAULT_FAIL_STATUSES}
    statuses = {token.strip() for token in raw.split(",") if token.strip()}
    if not statuses:
        return {DEFAULT_FAIL_STATUSES}
    return statuses


def _compute_exit_code(issue_status_counts: dict[str, int], fail_statuses: set[str]) -> RunOutcome:
    fail_counts = {status: int(issue_status_counts.get(status, 0)) for status in sorted(fail_statuses)}
    has_fail = any(count > 0 for count in fail_counts.values())
    return RunOutcome(
        exit_code=2 if has_fail else 0,
        result="fail" if has_fail else "pass",
        fail_status_counts=fail_counts,
    )


def _apply_artifact_policy(
    *,
    run_dir: Path,
    artifact_mode: str,
    result: str,
    detail_paths: list[Path],
    failure_bundle_out: Path | None,
) -> dict[str, Any]:
    removed_paths: list[str] = []
    bundled_paths: list[str] = []
    bundle_path: str | None = None

    def _remove_path(path: Path) -> None:
        if not path.exists():
            return
        if path.is_dir():
            shutil.rmtree(path, ignore_errors=True)
        else:
            try:
                path.unlink()
            except FileNotFoundError:
                return
        removed_paths.append(str(path))

    detail_existing: list[Path] = [p for p in detail_paths if p.exists()]

    if artifact_mode == "full":
        pass
    elif artifact_mode == "minimal":
        for path in detail_existing:
            _remove_path(path)
    elif artifact_mode == "fail-bundle":
        if result == "fail" and detail_existing:
            out = failure_bundle_out or (run_dir / "failure_bundle.tar.gz")
            out.parent.mkdir(parents=True, exist_ok=True)
            with tarfile.open(out, "w:gz") as tar:
                for path in detail_existing:
                    if not path.exists():
                        continue
                    try:
                        arcname = path.relative_to(run_dir)
                    except ValueError:
                        arcname = Path(path.name)
                    tar.add(path, arcname=str(arcname))
                    bundled_paths.append(str(path))
            bundle_path = str(out)
        for path in detail_existing:
            _remove_path(path)
    else:
        raise ValueError(f"unknown artifact mode: {artifact_mode}")

    retained: set[str] = set()
    if run_dir.exists():
        for path in run_dir.rglob("*"):
            if path.is_file():
                retained.add(str(path))
    if bundle_path:
        retained.add(bundle_path)

    return {
        "mode": artifact_mode,
        "result": result,
        "bundle_path": bundle_path,
        "bundled_paths": sorted(bundled_paths),
        "removed_paths": sorted(removed_paths),
        "retained_files": sorted(retained),
    }


@dataclass
class SourceRecord:
    ts: int
    payload: Any
    src: str
    cycle: int
    source_file: str


@dataclass
class StoredRow:
    rid: int
    ts: int
    obj: Any
    payload_digest: str
    src: str
    cycle: int
    source_file: str
    insert_op: int
    alive: bool = True
    delete_op: int | None = None


@dataclass
class CheckContext:
    query_kind: str
    params: dict[str, Any]
    description: str


@dataclass
class ComparisonResult:
    ok: bool
    reason: str
    expected_n: int
    got_n: int
    expected_keys: list[tuple[int, int | None, str]] = field(default_factory=list)
    got_keys: list[tuple[int, int | None, str]] = field(default_factory=list)
    missing: list[tuple[int, int | None, str]] = field(default_factory=list)
    extra: list[tuple[int, int | None, str]] = field(default_factory=list)


@dataclass
class IssueOutcome:
    status: str
    notes: list[str]
    triage_records: dict[str, Any]


class JsonlWriter:
    def __init__(self, path: Path):
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._fh = open(self.path, "w", encoding="utf-8")

    def write(self, record: dict[str, Any], flush: bool = False) -> None:
        self._fh.write(json.dumps(record, default=str, ensure_ascii=True) + "\n")
        if flush:
            self._fh.flush()

    def flush(self) -> None:
        self._fh.flush()

    def close(self) -> None:
        try:
            self._fh.flush()
        finally:
            self._fh.close()


class IssueRegistry:
    def __init__(self, run_dir: Path, issues_writer: JsonlWriter, repro_cmd: str):
        self.run_dir = run_dir
        self.issues_writer = issues_writer
        self.repro_cmd = repro_cmd
        self.issues_dir = run_dir / "issues"
        self.issues_dir.mkdir(parents=True, exist_ok=True)
        self.count = 0
        self.by_status: Counter[str] = Counter()
        self.by_kind: Counter[str] = Counter()

    def create_issue(
        self,
        *,
        kind: str,
        severity: str,
        status: str,
        op_index: int,
        check_index: int,
        title: str,
        context: dict[str, Any],
        evidence: dict[str, Any],
    ) -> str:
        self.count += 1
        issue_id = f"ISSUE_{self.count:04d}"
        now = _utc_now_iso()
        issue = {
            "issue_id": issue_id,
            "t_utc": now,
            "kind": kind,
            "severity": severity,
            "status": status,
            "op_index": op_index,
            "check_index": check_index,
            "title": title,
            "context": context,
        }
        self.issues_writer.write(issue, flush=True)
        self.by_status[status] += 1
        self.by_kind[kind] += 1

        issue_path = self.issues_dir / issue_id
        issue_path.mkdir(parents=True, exist_ok=True)

        payload = {"issue": issue, "evidence": evidence, "repro_cmd": self.repro_cmd}
        with open(issue_path / "evidence.json", "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, ensure_ascii=True, default=str)

        report_lines = [
            f"# {issue_id}: {title}",
            "",
            f"- Kind: `{kind}`",
            f"- Severity: `{severity}`",
            f"- Status: `{status}`",
            f"- Operation index: `{op_index}`",
            f"- Check index: `{check_index}`",
            "",
            "## Reproduction",
            "```powershell",
            self.repro_cmd,
            "```",
            "",
            "## Context",
            "```json",
            json.dumps(context, indent=2, ensure_ascii=True, default=str),
            "```",
            "",
            "## Evidence",
            "```json",
            json.dumps(evidence, indent=2, ensure_ascii=True, default=str),
            "```",
        ]
        with open(issue_path / "report.md", "w", encoding="utf-8") as fh:
            fh.write("\n".join(report_lines) + "\n")
        return issue_id


class SyntheticSource:
    def __init__(self, rng: random.Random, base_ts: int = 1_000_000):
        self.rng = rng
        self.cursor = base_ts
        self.floor = base_ts
        self.ooo_rate = 0.20
        self.max_lookback = 50_000
        self.total = 0
        self.cycle = 0

    def _tick_total(self) -> None:
        self.total += 1
        if self.total % 1_000_000 == 0:
            self.cycle += 1

    def _next_ts(self) -> int:
        if self.rng.random() < self.ooo_rate and self.cursor > self.floor + 10:
            max_lb = min(self.max_lookback, self.cursor - self.floor - 1)
            if max_lb > 0:
                ts = self.cursor - self.rng.randint(1, max_lb)
                if TL_TS_MIN <= ts <= TL_TS_MAX:
                    self._tick_total()
                    return ts
        nxt = self.cursor + self.rng.randint(1, 1000)
        if nxt > TL_TS_MAX:
            nxt = TL_TS_MAX - self.rng.randint(0, 100)
        self.cursor = nxt
        self._tick_total()
        return self.cursor

    def _next_payload(self) -> Any:
        kind = self.rng.randint(0, 8)
        if kind == 0:
            return {"kind": "quote", "px": self.rng.random(), "sz": self.rng.randint(1, 10000)}
        if kind == 1:
            return {"kind": "trade", "side": self.rng.choice(["B", "S"]), "qty": self.rng.randint(1, 5000)}
        if kind == 2:
            return ["evt", self.rng.randint(-10_000, 10_000), self.rng.random()]
        if kind == 3:
            return ("tuple", self.rng.randint(0, 1_000_000))
        if kind == 4:
            return self.rng.randint(-2**31, 2**31 - 1)
        if kind == 5:
            return self.rng.random()
        if kind == 6:
            return None
        if kind == 7:
            return {"nested": {"a": self.rng.randint(0, 99), "b": [1, 2, 3]}, "ok": True}
        return f"synthetic_{self.total}_{self.rng.randint(0, 1_000_000)}"

    def next_records(self, count: int) -> list[SourceRecord]:
        out: list[SourceRecord] = []
        for _ in range(count):
            out.append(
                SourceRecord(
                    ts=self._next_ts(),
                    payload=self._next_payload(),
                    src="syn",
                    cycle=self.cycle,
                    source_file="<synthetic>",
                )
            )
        return out


class CsvRollingSource:
    def __init__(self, paths: list[Path]):
        if not paths:
            raise ValueError("CsvRollingSource requires at least one CSV")
        self.paths = paths
        self.file_idx = 0
        self.file_handle = None
        self.reader = None
        self.global_cycle = 0
        self.global_offset = 0
        self.cycle_min_raw: int | None = None
        self.cycle_max_raw: int | None = None
        self.rows_in_cycle = 0
        self.rows_emitted_in_cycle = 0

    def close(self) -> None:
        if self.file_handle is not None:
            self.file_handle.close()
            self.file_handle = None
            self.reader = None

    def _open_current_file(self) -> None:
        self.close()
        path = self.paths[self.file_idx]
        self.file_handle = open(path, "r", encoding="utf-8", newline="")
        self.reader = csv.DictReader(self.file_handle)

    def _advance_file_or_cycle(self) -> None:
        self.close()
        self.file_idx += 1
        if self.file_idx >= len(self.paths):
            if self.rows_in_cycle == 0:
                raise RuntimeError("CSV source produced no timestamp rows in a full cycle")
            if self.rows_emitted_in_cycle == 0:
                raise RuntimeError(
                    "CSV source produced no in-range timestamps in a full cycle; "
                    "offset likely exceeded int64 range"
                )
            self.file_idx = 0
            span = 1
            if self.cycle_min_raw is not None and self.cycle_max_raw is not None:
                span = max(1, self.cycle_max_raw - self.cycle_min_raw + 1)
            self.global_offset += span
            self.global_cycle += 1
            self.cycle_min_raw = None
            self.cycle_max_raw = None
            self.rows_in_cycle = 0
            self.rows_emitted_in_cycle = 0
        self._open_current_file()

    def _next(self) -> SourceRecord:
        if self.reader is None:
            self._open_current_file()
        while True:
            assert self.reader is not None
            try:
                row = next(self.reader)
            except StopIteration:
                self._advance_file_or_cycle()
                continue
            raw_ts = row.get("timestamp")
            if raw_ts is None:
                continue
            try:
                ts_raw = int(raw_ts)
            except ValueError:
                continue
            if self.cycle_min_raw is None or ts_raw < self.cycle_min_raw:
                self.cycle_min_raw = ts_raw
            if self.cycle_max_raw is None or ts_raw > self.cycle_max_raw:
                self.cycle_max_raw = ts_raw
            self.rows_in_cycle += 1
            ts = ts_raw + self.global_offset
            if ts < TL_TS_MIN or ts > TL_TS_MAX:
                continue
            self.rows_emitted_in_cycle += 1
            return SourceRecord(
                ts=ts,
                payload=_normalize_csv_row(row),
                src="csv",
                cycle=self.global_cycle,
                source_file=self.paths[self.file_idx].name,
            )

    def next_records(self, count: int) -> list[SourceRecord]:
        return [self._next() for _ in range(count)]

    def stats(self) -> dict[str, Any]:
        return {
            "global_cycle": self.global_cycle,
            "global_offset": self.global_offset,
            "rows_in_cycle": self.rows_in_cycle,
            "current_file": self.paths[self.file_idx].name,
        }


class MixedSource:
    def __init__(
        self,
        rng: random.Random,
        synthetic: SyntheticSource,
        csv_source: CsvRollingSource | None,
        csv_weight: float = 0.7,
    ):
        self.rng = rng
        self.synthetic = synthetic
        self.csv_source = csv_source
        self.csv_weight = csv_weight

    def next_records(self, count: int) -> list[SourceRecord]:
        if self.csv_source is None:
            return self.synthetic.next_records(count)
        if self.rng.random() < self.csv_weight:
            return self.csv_source.next_records(count)
        return self.synthetic.next_records(count)


class ShadowFast:
    def __init__(self):
        self._index: list[tuple[int, int]] = []  # (ts, rid)
        self._live_rows: dict[int, StoredRow] = {}

    def insert_rows(self, rows: list[StoredRow]) -> None:
        for row in rows:
            bisect.insort(self._index, (row.ts, row.rid))
            self._live_rows[row.rid] = row

    def delete_range(self, t1: int, t2: int, op_index: int) -> list[StoredRow]:
        lo = bisect.bisect_left(self._index, (t1, -1))
        hi = bisect.bisect_left(self._index, (t2, -1))
        doomed = self._index[lo:hi]
        del self._index[lo:hi]
        removed: list[StoredRow] = []
        for _, rid in doomed:
            row = self._live_rows.pop(rid, None)
            if row is None:
                continue
            row.alive = False
            row.delete_op = op_index
            removed.append(row)
        return removed

    def query_range(self, t1: int, t2: int) -> list[StoredRow]:
        lo = bisect.bisect_left(self._index, (t1, -1))
        hi = bisect.bisect_left(self._index, (t2, -1))
        out: list[StoredRow] = []
        for _, rid in self._index[lo:hi]:
            row = self._live_rows.get(rid)
            if row is not None:
                out.append(row)
        return out

    def query_since(self, t1: int) -> list[StoredRow]:
        lo = bisect.bisect_left(self._index, (t1, -1))
        out: list[StoredRow] = []
        for _, rid in self._index[lo:]:
            row = self._live_rows.get(rid)
            if row is not None:
                out.append(row)
        return out

    def query_point(self, ts: int) -> list[StoredRow]:
        lo = bisect.bisect_left(self._index, (ts, -1))
        hi = bisect.bisect_right(self._index, (ts, 2**63))
        out: list[StoredRow] = []
        for _, rid in self._index[lo:hi]:
            row = self._live_rows.get(rid)
            if row is not None:
                out.append(row)
        return out

    def query_all(self) -> list[StoredRow]:
        return [self._live_rows[rid] for _, rid in self._index if rid in self._live_rows]

    def count_range(self, t1: int, t2: int) -> int:
        lo = bisect.bisect_left(self._index, (t1, -1))
        hi = bisect.bisect_left(self._index, (t2, -1))
        return max(0, hi - lo)

    def count_since(self, t1: int) -> int:
        lo = bisect.bisect_left(self._index, (t1, -1))
        return max(0, len(self._index) - lo)

    def count_point(self, ts: int) -> int:
        lo = bisect.bisect_left(self._index, (ts, -1))
        hi = bisect.bisect_right(self._index, (ts, 2**63))
        return max(0, hi - lo)

    def count_all(self) -> int:
        return len(self._index)

    def live_count(self) -> int:
        return len(self._index)

    def min_ts(self) -> int | None:
        return self._index[0][0] if self._index else None

    def max_ts(self) -> int | None:
        return self._index[-1][0] if self._index else None

    def random_live_ts(self, rng: random.Random) -> int | None:
        if not self._index:
            return None
        return rng.choice(self._index)[0]

    def next_ts(self, ts: int) -> int | None:
        idx = bisect.bisect_right(self._index, (ts, 2**63))
        if idx >= len(self._index):
            return None
        return self._index[idx][0]

    def prev_ts(self, ts: int) -> int | None:
        idx = bisect.bisect_left(self._index, (ts, -1)) - 1
        if idx < 0:
            return None
        return self._index[idx][0]


class ShadowTruth:
    def __init__(self):
        self.events: list[tuple[Any, ...]] = []

    def record_insert(self, row: StoredRow) -> None:
        self.events.append(("ins", row))

    def record_delete(self, t1: int, t2: int, op_index: int) -> None:
        self.events.append(("del", t1, t2, op_index))

    def replay_live(self) -> dict[int, StoredRow]:
        live: dict[int, StoredRow] = {}
        for ev in self.events:
            if ev[0] == "ins":
                row = ev[1]
                live[row.rid] = row
            else:
                _, t1, t2, _ = ev
                doomed = [rid for rid, row in live.items() if t1 <= row.ts < t2]
                for rid in doomed:
                    live.pop(rid, None)
        return live

    def query_range(self, t1: int, t2: int) -> list[StoredRow]:
        rows = [row for row in self.replay_live().values() if t1 <= row.ts < t2]
        rows.sort(key=lambda r: (r.ts, r.rid))
        return rows

    def query_since(self, t1: int) -> list[StoredRow]:
        rows = [row for row in self.replay_live().values() if row.ts >= t1]
        rows.sort(key=lambda r: (r.ts, r.rid))
        return rows

    def query_point(self, ts: int) -> list[StoredRow]:
        rows = [row for row in self.replay_live().values() if row.ts == ts]
        rows.sort(key=lambda r: (r.ts, r.rid))
        return rows

    def query_all(self) -> list[StoredRow]:
        rows = list(self.replay_live().values())
        rows.sort(key=lambda r: (r.ts, r.rid))
        return rows

    def count_range(self, t1: int, t2: int) -> int:
        return len(self.query_range(t1, t2))

    def count_since(self, t1: int) -> int:
        return len(self.query_since(t1))

    def count_point(self, ts: int) -> int:
        return len(self.query_point(ts))

    def count_all(self) -> int:
        return len(self.query_all())


def _rows_to_expected_keys(rows: list[StoredRow]) -> list[tuple[int, int | None, str]]:
    return [(r.ts, r.rid, r.payload_digest) for r in rows]


def _records_to_engine_keys(records: list[tuple[int, Any]]) -> list[tuple[int, int | None, str]]:
    out: list[tuple[int, int | None, str]] = []
    for ts, obj in records:
        rid, dg = _extract_rid_digest(obj)
        out.append((int(ts), rid, dg))
    return out


def _compare_rows(
    expected_rows: list[StoredRow],
    got_records: list[tuple[int, Any]],
) -> ComparisonResult:
    expected_keys = _rows_to_expected_keys(expected_rows)
    got_keys = _records_to_engine_keys(got_records)

    for i in range(1, len(got_keys)):
        if got_keys[i][0] < got_keys[i - 1][0]:
            return ComparisonResult(
                ok=False,
                reason="ORDER_VIOLATION",
                expected_n=len(expected_keys),
                got_n=len(got_keys),
                expected_keys=expected_keys,
                got_keys=got_keys,
            )

    exp_counter = Counter(expected_keys)
    got_counter = Counter(got_keys)
    if exp_counter == got_counter:
        return ComparisonResult(
            ok=True,
            reason="OK",
            expected_n=len(expected_keys),
            got_n=len(got_keys),
            expected_keys=expected_keys,
            got_keys=got_keys,
        )

    missing = list((exp_counter - got_counter).elements())[:20]
    extra = list((got_counter - exp_counter).elements())[:20]
    if missing and not extra:
        reason = "MISSING_ROW"
    elif extra and not missing:
        reason = "PHANTOM_ROW"
    else:
        reason = "PAYLOAD_MISMATCH"
    return ComparisonResult(
        ok=False,
        reason=reason,
        expected_n=len(expected_keys),
        got_n=len(got_keys),
        expected_keys=expected_keys,
        got_keys=got_keys,
        missing=missing,
        extra=extra,
    )


class MismatchTriager:
    def __init__(self, runner: "CorrectnessRunner"):
        self.runner = runner

    def _truth_expected(self, ctx: CheckContext) -> list[tuple[int, int | None, str]] | None:
        kind = ctx.query_kind
        p = ctx.params
        if kind == "point":
            ts = int(p["ts"])
            return _rows_to_expected_keys(self.runner.shadow_truth.query_point(ts))
        if kind in {"range", "slice_since", "slice_until", "slice_all", "full_scan", "all_sample"}:
            if kind == "slice_since":
                return _rows_to_expected_keys(self.runner.shadow_truth.query_since(int(p["t1"])))
            elif kind == "slice_until":
                t1, t2 = TL_TS_MIN, int(p["t2"])
            elif kind in {"slice_all", "full_scan", "all_sample"}:
                return _rows_to_expected_keys(self.runner.shadow_truth.query_all())
            else:
                t1, t2 = int(p["t1"]), int(p["t2"])
            return _rows_to_expected_keys(self.runner.shadow_truth.query_range(t1, t2))
        return None

    def triage(
        self,
        *,
        ctx: CheckContext,
        expected_rows: list[StoredRow],
        engine_fetch: Callable[[], list[tuple[int, Any]]],
        alt_fetch: Callable[[], list[tuple[int, Any]]] | None,
        initial_got: list[tuple[int, Any]] | None,
    ) -> IssueOutcome:
        notes: list[str] = []
        expected_fast = _rows_to_expected_keys(expected_rows)
        expected_truth = self._truth_expected(ctx)
        triage_records: dict[str, Any] = {
            "expected_fast_n": len(expected_fast),
            "expected_truth_n": None if expected_truth is None else len(expected_truth),
            "truth_agrees": None,
            "reruns": {},
        }
        if expected_truth is not None:
            triage_records["truth_agrees"] = Counter(expected_fast) == Counter(expected_truth)
            if not triage_records["truth_agrees"]:
                notes.append("ShadowFast and ShadowTruth disagree")
                return IssueOutcome(ISSUE_STATUS_CHECKER, notes, triage_records)

        if initial_got is not None:
            cmp_initial = _compare_rows(expected_rows, initial_got)
            triage_records["reruns"]["initial"] = {
                "reason": cmp_initial.reason,
                "expected_n": cmp_initial.expected_n,
                "got_n": cmp_initial.got_n,
            }

        try:
            rerun = engine_fetch()
            cmp_rerun = _compare_rows(expected_rows, rerun)
            triage_records["reruns"]["same_query"] = {
                "reason": cmp_rerun.reason,
                "expected_n": cmp_rerun.expected_n,
                "got_n": cmp_rerun.got_n,
            }
            if cmp_rerun.ok:
                notes.append("mismatch disappeared on identical rerun")
                return IssueOutcome(ISSUE_STATUS_TRANSIENT, notes, triage_records)
        except Exception as exc:
            triage_records["reruns"]["same_query"] = {"exception": repr(exc)}

        if alt_fetch is not None:
            try:
                rerun_alt = alt_fetch()
                cmp_alt = _compare_rows(expected_rows, rerun_alt)
                triage_records["reruns"]["alternate_query"] = {
                    "reason": cmp_alt.reason,
                    "expected_n": cmp_alt.expected_n,
                    "got_n": cmp_alt.got_n,
                }
                if cmp_alt.ok:
                    notes.append("mismatch disappeared on alternate query")
                    return IssueOutcome(ISSUE_STATUS_TRANSIENT, notes, triage_records)
            except Exception as exc:
                triage_records["reruns"]["alternate_query"] = {"exception": repr(exc)}

        self.runner._safe_maintenance_sweep("triage")
        try:
            rerun_after = engine_fetch()
            cmp_after = _compare_rows(expected_rows, rerun_after)
            triage_records["reruns"]["post_maintenance"] = {
                "reason": cmp_after.reason,
                "expected_n": cmp_after.expected_n,
                "got_n": cmp_after.got_n,
            }
            if cmp_after.ok:
                notes.append("mismatch disappeared after maintenance sweep")
                return IssueOutcome(ISSUE_STATUS_TRANSIENT, notes, triage_records)
        except Exception as exc:
            triage_records["reruns"]["post_maintenance"] = {"exception": repr(exc)}

        notes.append("mismatch persisted across reruns")
        return IssueOutcome(ISSUE_STATUS_CONFIRMED, notes, triage_records)


class CorrectnessRunner:
    WEIGHTS = [
        ("extend_batch", 30),
        ("append_single", 10),
        ("setitem_single", 5),
        ("query_point_hot", 8),
        ("query_point_random", 6),
        ("query_range_small", 8),
        ("query_range_wide", 5),
        ("query_slice", 4),
        ("query_all_sample", 2),
        ("query_views", 2),
        ("delete_point", 4),
        ("delete_range", 5),
        ("cutoff", 3),
        ("flush", 2),
        ("compact", 2),
        ("meta_probe", 4),
    ]

    class _ProbeBox:
        pass

    def __init__(self, cfg: RunConfig):
        self.cfg = cfg
        self.rng = random.Random(cfg.seed)
        self.git_commit = _safe_git_commit()
        self.run_id = cfg.run_id_override or f"cc_{datetime.now().strftime('%Y%m%d_%H%M%S')}_seed{cfg.seed}"
        self.run_dir = Path(cfg.out_dir) / self.run_id
        self.run_dir.mkdir(parents=True, exist_ok=True)

        ops_path = Path(cfg.log_alias_path) if cfg.log_alias_path else self.run_dir / "ops.jsonl"
        self.ops_writer = JsonlWriter(ops_path)
        self.checks_writer = JsonlWriter(self.run_dir / "checks.jsonl")
        self.issues_writer = JsonlWriter(self.run_dir / "issues.jsonl")

        self.repro_cmd = (
            "py -V:3.13 demo/correctness_checker.py "
            f"--duration-seconds={cfg.duration_seconds} "
            f"--seed={cfg.seed} "
            f"--source-mode={cfg.source_mode} "
            f"--len-checks={'on' if cfg.len_checks else 'off'} "
            f"--len-slice-samples={cfg.len_slice_samples} "
            f"--len-consume-samples={cfg.len_consume_samples}"
        )
        self.issue_registry = IssueRegistry(self.run_dir, self.issues_writer, self.repro_cmd)

        self.log = Timelog(
            maintenance=cfg.maintenance,
            busy_policy=cfg.busy_policy,
            time_unit="ns",
        )

        csv_paths = [Path(p) if Path(p).is_absolute() else (_REPO / p) for p in cfg.csv_paths]
        csv_paths = [p for p in csv_paths if p.exists()]
        self.csv_source = CsvRollingSource(csv_paths) if csv_paths else None
        self.synthetic_source = SyntheticSource(self.rng)
        self.mixed_source = MixedSource(self.rng, self.synthetic_source, self.csv_source)

        self.shadow_fast = ShadowFast()
        self.shadow_truth = ShadowTruth()
        self.triager = MismatchTriager(self)

        self.rows_by_rid: dict[int, StoredRow] = {}
        self.next_rid = 1
        self.recent_insert_ts: deque[int] = deque(maxlen=50_000)
        self.recent_delete_points: deque[int] = deque(maxlen=20_000)
        self.recent_delete_ranges: deque[tuple[int, int]] = deque(maxlen=20_000)
        self.boundary_max_seeded = False

        self.op_index = 0
        self.check_index = 0
        self.inserts = 0
        self.deletes = 0
        self.mismatches = 0
        self.full_verifies = 0
        self.len_checks_total = 0
        self.len_checks_failed = 0
        self.len_mismatches_by_kind: Counter[str] = Counter()
        self.stop_reason: str | None = None
        self.started_utc = _utc_now_iso()

        self._choices = [name for name, _ in self.WEIGHTS]
        self._weights = [w for _, w in self.WEIGHTS]

        self.last_full_verify_mono = time.monotonic()
        self.last_side_probe_mono = time.monotonic()

        self._write_run_header()

    def _write_run_header(self) -> None:
        cfg_dict = asdict(self.cfg)
        cfg_dict["fail_statuses"] = sorted(self.cfg.fail_statuses)
        self.ops_writer.write(
            {
                "op": "run_start",
                "t_utc": self.started_utc,
                "run_id": self.run_id,
                "git_commit": self.git_commit,
                "config": cfg_dict,
                "csv_source": None if self.csv_source is None else [str(p) for p in self.csv_source.paths],
            },
            flush=True,
        )

    def _close_all(self) -> None:
        try:
            if self.csv_source is not None:
                self.csv_source.close()
        except Exception:
            pass
        try:
            self.log.flush()
        except Exception:
            pass
        try:
            self.log.close()
        except Exception:
            pass
        self.ops_writer.close()
        self.checks_writer.close()
        self.issues_writer.close()

    def run(self) -> int:
        print(
            "Timelog Correctness Checker | "
            f"seed={self.cfg.seed} | duration={self.cfg.duration_seconds}s | run_id={self.run_id}"
        )
        print("=" * 96)

        started = time.monotonic()
        last_progress = started
        summary: dict[str, Any] | None = None
        outcome: RunOutcome | None = None
        try:
            while True:
                elapsed = time.monotonic() - started
                if elapsed >= self.cfg.duration_seconds or self.stop_reason is not None:
                    break

                self.op_index += 1
                if self.op_index % 500 == 0:
                    self._boundary_probe()

                op_name = self._pick_operation()
                t0 = time.perf_counter_ns()
                try:
                    getattr(self, f"_op_{op_name}")()
                    ok = True
                    err = None
                except Exception as exc:
                    ok = False
                    err = "".join(traceback.format_exception_only(type(exc), exc)).strip()
                    self._register_runtime_issue(
                        kind="CHECKER_INCONSISTENCY",
                        title=f"operation crashed: {op_name}",
                        evidence={
                            "operation": op_name,
                            "exception": err,
                            "traceback": traceback.format_exc(),
                        },
                        severity="HIGH",
                        status=ISSUE_STATUS_CHECKER,
                    )
                self.ops_writer.write(
                    {
                        "op": "operation",
                        "op_index": self.op_index,
                        "name": op_name,
                        "ok": ok,
                        "error": err,
                        "latency_ns": time.perf_counter_ns() - t0,
                        "live_rows": self.shadow_fast.live_count(),
                        "inserts": self.inserts,
                        "deletes": self.deletes,
                        "issues": self.issue_registry.count,
                    }
                )

                now = time.monotonic()
                if (
                    self.op_index % self.cfg.full_verify_interval_ops == 0
                    or now - self.last_full_verify_mono >= self.cfg.full_verify_interval_seconds
                ):
                    self._full_verify()
                    self.last_full_verify_mono = now

                if self.op_index % self.cfg.checkpoint_interval_ops == 0:
                    self._checkpoint()

                if now - self.last_side_probe_mono >= 600:
                    self._side_probes()
                    self.last_side_probe_mono = now

                if now - last_progress >= 30:
                    print(
                        f"[{int(now-started):5d}s] "
                        f"ops={self.op_index} live={self.shadow_fast.live_count()} "
                        f"inserts={self.inserts} deletes={self.deletes} "
                        f"issues={self.issue_registry.count}"
                    )
                    last_progress = now

                if self.issue_registry.count >= self.cfg.max_issues:
                    self.stop_reason = "max_issues_reached"

            outcome = _compute_exit_code(dict(self.issue_registry.by_status), self.cfg.fail_statuses)
            summary = self._finalize_summary(started, outcome)
        finally:
            self._close_all()

        if outcome is None:
            outcome = _compute_exit_code(dict(self.issue_registry.by_status), self.cfg.fail_statuses)
        if summary is None:
            summary = self._build_summary(started, outcome)

        self._finalize_artifacts(summary, outcome)
        self._write_summary_files(summary)
        self._print_summary(summary)
        return outcome.exit_code

    def _pick_operation(self) -> str:
        if self.shadow_fast.live_count() == 0:
            return self.rng.choice(["extend_batch", "append_single", "setitem_single", "flush", "meta_probe"])
        return self.rng.choices(self._choices, self._weights, k=1)[0]

    def _checkpoint(self) -> None:
        self._handle_drop_health_probe()
        self.ops_writer.flush()
        self.checks_writer.flush()
        self.issues_writer.flush()
        self.ops_writer.write(
            {
                "op": "checkpoint",
                "op_index": self.op_index,
                "live_rows": self.shadow_fast.live_count(),
                "issues": self.issue_registry.count,
                "csv_stats": None if self.csv_source is None else self.csv_source.stats(),
            },
            flush=True,
        )

    def _source_next_records(self, count: int) -> list[SourceRecord]:
        if self.cfg.source_mode == "synthetic":
            return self.synthetic_source.next_records(count)
        if self.cfg.source_mode == "csv":
            if self.csv_source is None:
                return self.synthetic_source.next_records(count)
            return self.csv_source.next_records(count)
        return self.mixed_source.next_records(count)

    def _choose_reinsert_ts(self) -> int | None:
        p = self.rng.random()
        if p < 0.10 and self.recent_delete_points:
            return self.rng.choice(self.recent_delete_points)
        if p < 0.30 and self.recent_delete_ranges:
            t1, t2 = self.rng.choice(self.recent_delete_ranges)
            if t1 < t2:
                return self.rng.randint(t1, t2 - 1)
        return None

    def _bounded_ts(self, ts: int) -> int:
        if ts < TL_TS_MIN:
            return TL_TS_MIN
        if ts > TL_TS_MAX:
            return TL_TS_MAX
        return ts

    def _make_stored_rows(self, src_records: list[SourceRecord]) -> list[StoredRow]:
        out: list[StoredRow] = []
        for src in src_records:
            ts = _coerce_ts(self._bounded_ts(src.ts))
            forced_ts = self._choose_reinsert_ts()
            if forced_ts is not None:
                ts = _coerce_ts(self._bounded_ts(forced_ts))
            rid = self.next_rid
            self.next_rid += 1
            digest = _payload_digest(src.payload)
            obj = {
                "__cc_schema": 1,
                "rid": rid,
                "src": src.src,
                "cycle": src.cycle,
                "payload_digest": digest,
                "payload": src.payload,
            }
            row = StoredRow(
                rid=rid,
                ts=ts,
                obj=obj,
                payload_digest=digest,
                src=src.src,
                cycle=src.cycle,
                source_file=src.source_file,
                insert_op=self.op_index,
            )
            out.append(row)
            self.rows_by_rid[rid] = row
        return out

    def _oracle_insert(self, rows: list[StoredRow]) -> None:
        self.shadow_fast.insert_rows(rows)
        for row in rows:
            self.shadow_truth.record_insert(row)
            self.recent_insert_ts.append(row.ts)

    def _oracle_delete_range(self, t1: int, t2: int) -> list[StoredRow]:
        removed = self.shadow_fast.delete_range(t1, t2, self.op_index)
        self.shadow_truth.record_delete(t1, t2, self.op_index)
        self.recent_delete_ranges.append((t1, t2))
        return removed

    # ------------------------------------------------------------------
    # Write operations
    # ------------------------------------------------------------------

    def _op_extend_batch(self) -> None:
        count = self.rng.randint(self.cfg.min_batch, self.cfg.max_batch)
        rows = self._make_stored_rows(self._source_next_records(count))
        pairs = [(r.ts, r.obj) for r in rows]
        pattern = self.rng.choice(["pairs", "dual", "iter"])
        busy = False
        try:
            if pattern == "pairs":
                self.log.extend(pairs)
            elif pattern == "dual":
                self.log.extend([r.ts for r in rows], [r.obj for r in rows])
            else:
                self.log.extend(iter(pairs))
        except TimelogBusyError:
            busy = True
        self._oracle_insert(rows)
        self.inserts += len(rows)
        self.ops_writer.write(
            {
                "op": "extend_batch",
                "op_index": self.op_index,
                "count": len(rows),
                "pattern": pattern,
                "busy": busy,
            }
        )
        self._post_insert_probe(rows)

    def _op_append_single(self) -> None:
        row = self._make_stored_rows(self._source_next_records(1))[0]
        pattern = self.rng.choice(["kwarg", "positional"])
        busy = False
        try:
            if pattern == "kwarg":
                self.log.append(row.obj, ts=row.ts)
            else:
                self.log.append(row.ts, row.obj)
        except TimelogBusyError:
            busy = True
        self._oracle_insert([row])
        self.inserts += 1
        self.ops_writer.write(
            {"op": "append_single", "op_index": self.op_index, "ts": row.ts, "rid": row.rid, "busy": busy}
        )
        self._post_insert_probe([row])

    def _op_setitem_single(self) -> None:
        row = self._make_stored_rows(self._source_next_records(1))[0]
        busy = False
        try:
            self.log[row.ts] = row.obj
        except TimelogBusyError:
            busy = True
        self._oracle_insert([row])
        self.inserts += 1
        self.ops_writer.write(
            {"op": "setitem_single", "op_index": self.op_index, "ts": row.ts, "rid": row.rid, "busy": busy}
        )
        self._post_insert_probe([row])

    # ------------------------------------------------------------------
    # Delete operations
    # ------------------------------------------------------------------

    def _pick_delete_point_ts(self) -> int | None:
        if self.shadow_fast.live_count() == 0:
            return None
        candidates = [ts for ts in self.recent_insert_ts if ts < TL_TS_MAX]
        if candidates and self.rng.random() < 0.5:
            return self.rng.choice(candidates)
        for _ in range(16):
            ts = self.shadow_fast.random_live_ts(self.rng)
            if ts is None:
                return None
            if ts < TL_TS_MAX:
                return ts
        return None

    def _op_delete_point(self) -> None:
        ts = self._pick_delete_point_ts()
        if ts is None:
            return
        pattern = self.rng.choice(["delete", "delitem"])
        busy = False
        try:
            if pattern == "delete":
                self.log.delete(ts)
            else:
                del self.log[ts]
        except TimelogBusyError:
            busy = True
        removed = self._oracle_delete_range(ts, ts + 1 if ts < TL_TS_MAX else TL_TS_MAX)
        self.recent_delete_points.append(ts)
        self.deletes += len(removed)
        self.ops_writer.write(
            {
                "op": "delete_point",
                "op_index": self.op_index,
                "ts": ts,
                "removed": len(removed),
                "pattern": pattern,
                "busy": busy,
            }
        )
        self._post_delete_probe(removed)

    def _op_delete_range(self) -> None:
        mn, mx = self.shadow_fast.min_ts(), self.shadow_fast.max_ts()
        if mn is None or mx is None:
            return
        t1 = mn if mn == mx else self.rng.randint(mn, mx)
        span = max(1, mx - mn)
        width = self.rng.randint(1, max(1, span // 20))
        t2 = self._bounded_ts(t1 + width)
        if t2 <= t1:
            t2 = t1 + 1 if t1 < TL_TS_MAX else TL_TS_MAX
        pattern = self.rng.choice(["delete", "delitem"])
        busy = False
        try:
            if pattern == "delete":
                self.log.delete(t1, t2)
            else:
                del self.log[t1:t2]
        except TimelogBusyError:
            busy = True
        removed = self._oracle_delete_range(t1, t2)
        self.deletes += len(removed)
        self.ops_writer.write(
            {
                "op": "delete_range",
                "op_index": self.op_index,
                "t1": t1,
                "t2": t2,
                "removed": len(removed),
                "pattern": pattern,
                "busy": busy,
            }
        )
        self._post_delete_probe(removed)

    def _op_cutoff(self) -> None:
        mn, mx = self.shadow_fast.min_ts(), self.shadow_fast.max_ts()
        if mn is None or mx is None:
            return
        cutoff = mn if mn == mx else self.rng.randint(mn, mn + max(1, (mx - mn) * 3 // 10))
        busy = False
        try:
            self.log.cutoff(cutoff)
        except TimelogBusyError:
            busy = True
        removed = self._oracle_delete_range(TL_TS_MIN, cutoff)
        self.deletes += len(removed)
        self.ops_writer.write(
            {"op": "cutoff", "op_index": self.op_index, "cutoff": cutoff, "removed": len(removed), "busy": busy}
        )
        self._post_delete_probe(removed)

    # ------------------------------------------------------------------
    # Query operations
    # ------------------------------------------------------------------

    def _op_query_point_hot(self) -> None:
        if not self.recent_insert_ts:
            return
        self._verify_point(self.rng.choice(self.recent_insert_ts), "query_point_hot")

    def _op_query_point_random(self) -> None:
        ts = self.shadow_fast.random_live_ts(self.rng)
        if ts is None:
            return
        self._verify_point(ts, "query_point_random")

    def _op_query_range_small(self) -> None:
        mn, mx = self.shadow_fast.min_ts(), self.shadow_fast.max_ts()
        if mn is None or mx is None:
            return
        t1 = self.rng.randint(mn, mx)
        width = self.rng.randint(1, max(1, max(1, mx - mn) // 100))
        t2 = self._bounded_ts(t1 + width)
        if t2 <= t1:
            t2 = t1 + 1 if t1 < TL_TS_MAX else TL_TS_MAX
        self._verify_range(t1, t2, "query_range_small")

    def _op_query_range_wide(self) -> None:
        mn, mx = self.shadow_fast.min_ts(), self.shadow_fast.max_ts()
        if mn is None or mx is None:
            return
        t1 = self.rng.randint(mn, mx)
        span = max(1, mx - mn)
        width = self.rng.randint(max(1, span // 20), max(1, span // 2))
        t2 = self._bounded_ts(t1 + width)
        if t2 <= t1:
            t2 = t1 + 1 if t1 < TL_TS_MAX else TL_TS_MAX
        self._verify_range(t1, t2, "query_range_wide")

    def _op_query_slice(self) -> None:
        mn, mx = self.shadow_fast.min_ts(), self.shadow_fast.max_ts()
        if mn is None or mx is None:
            return
        variant = self.rng.choice(["since", "until", "all"])
        if variant == "since":
            t1 = self.rng.randint(mn, mx)
            self._run_row_check(
                ctx=CheckContext("slice_since", {"t1": t1}, f"slice[{t1}:]"),
                expected_rows=self.shadow_fast.query_since(t1),
                engine_fetch=lambda: list(self.log[t1:]),
                alt_fetch=lambda: list(self.log.since(t1)),
            )
            return
        if variant == "until":
            t2 = self.rng.randint(mn, mx)
            self._run_row_check(
                ctx=CheckContext("slice_until", {"t2": t2}, f"slice[:{t2}]"),
                expected_rows=self.shadow_fast.query_range(TL_TS_MIN, t2),
                engine_fetch=lambda: list(self.log[:t2]),
                alt_fetch=lambda: list(self.log.until(t2)),
            )
            return
        self._run_row_check(
            ctx=CheckContext("slice_all", {}, "slice[:]"),
            expected_rows=self.shadow_fast.query_all(),
            engine_fetch=lambda: list(self.log[:]),
            alt_fetch=lambda: list(self.log.all()),
        )

    def _op_query_all_sample(self) -> None:
        self._run_row_check(
            ctx=CheckContext("all_sample", {}, "iter_all"),
            expected_rows=self.shadow_fast.query_all(),
            engine_fetch=lambda: list(self.log),
            alt_fetch=lambda: list(self.log[:]),
        )

    def _op_query_views(self) -> None:
        mn, mx = self.shadow_fast.min_ts(), self.shadow_fast.max_ts()
        if mn is None or mx is None:
            return
        self._safe_flush("views_pre_flush")
        t1 = self.rng.randint(mn, mx)
        width = self.rng.randint(1, max(1, max(1, mx - mn) // 10))
        t2 = self._bounded_ts(t1 + width)
        if t2 <= t1:
            t2 = t1 + 1 if t1 < TL_TS_MAX else TL_TS_MAX

        self._verify_range(t1, t2, "query_views_logical_range")
        logical_counter = Counter(_rows_to_expected_keys(self.shadow_fast.query_range(t1, t2)))
        ctx = CheckContext("range", {"t1": t1, "t2": t2}, f"views subset [{t1},{t2})")

        try:
            view_rows = self._collect_views_records(t1, t2)
        except Exception as exc:
            self._register_runtime_issue(
                kind="VIEWS_CONTRACT",
                title="views() raised unexpected exception",
                evidence={"exception": repr(exc), "traceback": traceback.format_exc(), "context": asdict(ctx)},
                severity="MEDIUM",
                status=ISSUE_STATUS_CONFIRMED,
            )
            return

        view_counter = Counter(_records_to_engine_keys(view_rows))
        missing = list((logical_counter - view_counter).elements())[:20]
        self.check_index += 1
        if missing:
            self.checks_writer.write(
                {
                    "check_index": self.check_index,
                    "op_index": self.op_index,
                    "kind": "views_subset",
                    "ok": False,
                    "missing_sample": missing,
                    "context": asdict(ctx),
                },
                flush=True,
            )
            self._register_runtime_issue(
                kind="VIEWS_CONTRACT",
                title="views missing logical rows",
                evidence={"context": asdict(ctx), "missing_sample": missing},
                severity="HIGH",
                status=ISSUE_STATUS_CONFIRMED,
            )
            return
        self.checks_writer.write(
            {
                "check_index": self.check_index,
                "op_index": self.op_index,
                "kind": "views_subset",
                "ok": True,
                "context": asdict(ctx),
            }
        )

    # ------------------------------------------------------------------
    # Maintenance / meta operations
    # ------------------------------------------------------------------

    def _op_flush(self) -> None:
        self._safe_flush("op_flush")

    def _op_compact(self) -> None:
        self._safe_compact("op_compact")

    def _op_meta_probe(self) -> None:
        self.check_index += 1
        ok = True
        errs: list[str] = []
        exp_min, exp_max = self.shadow_fast.min_ts(), self.shadow_fast.max_ts()
        got_min, got_max = self.log.min_ts(), self.log.max_ts()
        if got_min != exp_min:
            ok = False
            errs.append(f"min_ts mismatch: expected={exp_min} got={got_min}")
        if got_max != exp_max:
            ok = False
            errs.append(f"max_ts mismatch: expected={exp_max} got={got_max}")

        ts = self.shadow_fast.random_live_ts(self.rng)
        if ts is not None:
            exp_next, exp_prev = self.shadow_fast.next_ts(ts), self.shadow_fast.prev_ts(ts)
            got_next, got_prev = self.log.next_ts(ts), self.log.prev_ts(ts)
            if got_next != exp_next:
                ok = False
                errs.append(f"next_ts mismatch at {ts}: expected={exp_next} got={got_next}")
            if got_prev != exp_prev:
                ok = False
                errs.append(f"prev_ts mismatch at {ts}: expected={exp_prev} got={got_prev}")

        try:
            self.log.validate()
        except Exception as exc:
            ok = False
            errs.append(f"validate() failed: {exc!r}")

        self.checks_writer.write(
            {
                "check_index": self.check_index,
                "op_index": self.op_index,
                "kind": "meta_probe",
                "ok": ok,
                "errors": errs,
                "expected_min": exp_min,
                "expected_max": exp_max,
                "got_min": got_min,
                "got_max": got_max,
            },
            flush=not ok,
        )
        if not ok:
            self._register_runtime_issue(
                kind="VALIDATE_FAILURE",
                title="meta probe failed",
                evidence={"errors": errs},
                severity="HIGH",
                status=ISSUE_STATUS_CONFIRMED,
            )

        # Higher-frequency one-shot len() contract check.
        if self.cfg.len_checks:
            self._verify_len_full_contract()

    # ------------------------------------------------------------------
    # Verification core
    # ------------------------------------------------------------------

    def _make_slice_iter(self, variant: str, t1: int, t2: int):
        if variant == "range":
            return self.log[t1:t2]
        if variant == "since":
            return self.log[t1:]
        if variant == "until":
            return self.log[:t2]
        return self.log[:]

    def _expected_len_count(self, shadow: ShadowFast | ShadowTruth, variant: str, t1: int, t2: int) -> int:
        if variant == "range":
            return shadow.count_range(t1, t2)
        if variant == "since":
            return shadow.count_since(t1)
        if variant == "until":
            return shadow.count_range(TL_TS_MIN, t2)
        if variant == "point":
            return shadow.count_point(t1)
        return shadow.count_all()

    def _len_slice_once(self, variant: str, t1: int, t2: int) -> int:
        it = self._make_slice_iter(variant, t1, t2)
        try:
            return len(it)
        finally:
            try:
                it.close()
            except Exception:
                pass

    def _sum_slice_once(self, variant: str, t1: int, t2: int) -> int:
        with self._make_slice_iter(variant, t1, t2) as it:
            return sum(1 for _ in it)

    def _len_point_once(self, ts: int, use_equal: bool = False) -> int:
        with (self.log.equal(ts) if use_equal else self.log.point(ts)) as it:
            return len(it)

    def _pick_len_window(self) -> tuple[int, int]:
        mn, mx = self.shadow_fast.min_ts(), self.shadow_fast.max_ts()
        if mn is None or mx is None:
            return TL_TS_MIN, TL_TS_MIN + 1
        t1 = mn if mn == mx else self.rng.randint(mn, mx)
        if t1 >= TL_TS_MAX:
            return TL_TS_MAX, TL_TS_MAX
        span = max(1, mx - mn)
        width = self.rng.randint(1, max(1, span // 20))
        t2 = self._bounded_ts(t1 + width)
        if t2 <= t1:
            t2 = t1 + 1
        return t1, t2

    def _triage_len_mismatch(
        self,
        *,
        kind: str,
        expected_fast: int,
        expected_truth: int,
        engine_fetch: Callable[[], int],
        alt_fetch: Callable[[], int] | None,
    ) -> IssueOutcome:
        notes: list[str] = []
        triage_records: dict[str, Any] = {
            "kind": kind,
            "expected_fast": expected_fast,
            "expected_truth": expected_truth,
            "truth_agrees": expected_fast == expected_truth,
            "reruns": {},
        }

        if expected_fast != expected_truth:
            notes.append("ShadowFast and ShadowTruth disagree")
            return IssueOutcome(ISSUE_STATUS_CHECKER, notes, triage_records)

        try:
            got_same = engine_fetch()
            triage_records["reruns"]["same_query"] = {"got": got_same}
            if got_same == expected_fast:
                notes.append("len mismatch disappeared on identical rerun")
                return IssueOutcome(ISSUE_STATUS_TRANSIENT, notes, triage_records)
        except Exception as exc:
            triage_records["reruns"]["same_query"] = {"exception": repr(exc)}

        if alt_fetch is not None:
            try:
                got_alt = alt_fetch()
                triage_records["reruns"]["alternate_query"] = {"got": got_alt}
                if got_alt == expected_fast:
                    notes.append("len mismatch disappeared on alternate query")
                    return IssueOutcome(ISSUE_STATUS_TRANSIENT, notes, triage_records)
            except Exception as exc:
                triage_records["reruns"]["alternate_query"] = {"exception": repr(exc)}

        self._safe_maintenance_sweep("len-triage")
        try:
            got_post = engine_fetch()
            triage_records["reruns"]["post_maintenance"] = {"got": got_post}
            if got_post == expected_fast:
                notes.append("len mismatch disappeared after maintenance sweep")
                return IssueOutcome(ISSUE_STATUS_TRANSIENT, notes, triage_records)
        except Exception as exc:
            triage_records["reruns"]["post_maintenance"] = {"exception": repr(exc)}

        notes.append("len mismatch persisted across reruns")
        return IssueOutcome(ISSUE_STATUS_CONFIRMED, notes, triage_records)

    def _triage_len_remaining_mismatch(
        self,
        *,
        kind: str,
        probe_fetch: Callable[[], dict[str, Any]],
    ) -> IssueOutcome:
        notes: list[str] = []
        triage_records: dict[str, Any] = {"kind": kind, "reruns": {}}

        try:
            same = probe_fetch()
            triage_records["reruns"]["same_query"] = same
            if same.get("ok"):
                notes.append("remaining-len mismatch disappeared on identical rerun")
                return IssueOutcome(ISSUE_STATUS_TRANSIENT, notes, triage_records)
        except Exception as exc:
            triage_records["reruns"]["same_query"] = {"exception": repr(exc)}

        self._safe_maintenance_sweep("len-remaining-triage")
        try:
            post = probe_fetch()
            triage_records["reruns"]["post_maintenance"] = post
            if post.get("ok"):
                notes.append("remaining-len mismatch disappeared after maintenance sweep")
                return IssueOutcome(ISSUE_STATUS_TRANSIENT, notes, triage_records)
        except Exception as exc:
            triage_records["reruns"]["post_maintenance"] = {"exception": repr(exc)}

        notes.append("remaining-len mismatch persisted across reruns")
        return IssueOutcome(ISSUE_STATUS_CONFIRMED, notes, triage_records)

    def _handle_len_mismatch(
        self,
        *,
        check_kind: str,
        title: str,
        expected_fast: int,
        expected_truth: int,
        got: int,
        engine_fetch: Callable[[], int],
        alt_fetch: Callable[[], int] | None,
        context: dict[str, Any],
    ) -> None:
        self.mismatches += 1
        self.len_checks_failed += 1
        self.len_mismatches_by_kind[check_kind] += 1
        outcome = self._triage_len_mismatch(
            kind=check_kind,
            expected_fast=expected_fast,
            expected_truth=expected_truth,
            engine_fetch=engine_fetch,
            alt_fetch=alt_fetch,
        )
        severity = "CRITICAL" if outcome.status == ISSUE_STATUS_CONFIRMED else "HIGH"
        issue_id = self.issue_registry.create_issue(
            kind="LEN_CONTRACT",
            severity=severity,
            status=outcome.status,
            op_index=self.op_index,
            check_index=self.check_index,
            title=title,
            context=context,
            evidence={
                "expected_fast": expected_fast,
                "expected_truth": expected_truth,
                "got": got,
                "triage": {"notes": outcome.notes, "records": outcome.triage_records},
            },
        )
        self.checks_writer.write(
            {
                "check_index": self.check_index,
                "op_index": self.op_index,
                "kind": check_kind,
                "ok": False,
                "issue_id": issue_id,
                "status": outcome.status,
                "expected_fast": expected_fast,
                "expected_truth": expected_truth,
                "got": got,
                "context": context,
            },
            flush=True,
        )
        if outcome.status in {ISSUE_STATUS_CONFIRMED, ISSUE_STATUS_CHECKER} and not self.cfg.continue_on_mismatch:
            self.stop_reason = f"{outcome.status}:{issue_id}"

    def _verify_len_count_case(
        self,
        *,
        check_kind: str,
        title: str,
        expected_fast: int,
        expected_truth: int,
        engine_fetch: Callable[[], int],
        alt_fetch: Callable[[], int] | None,
        context: dict[str, Any],
    ) -> None:
        self.check_index += 1
        self.len_checks_total += 1
        try:
            got = engine_fetch()
        except Exception as exc:
            self._register_runtime_issue(
                kind="CHECKER_INCONSISTENCY",
                title=f"len check crashed: {title}",
                evidence={"exception": repr(exc), "traceback": traceback.format_exc(), "context": context},
                severity="HIGH",
                status=ISSUE_STATUS_CHECKER,
            )
            return

        if got == expected_fast and expected_fast == expected_truth:
            self.checks_writer.write(
                {
                    "check_index": self.check_index,
                    "op_index": self.op_index,
                    "kind": check_kind,
                    "ok": True,
                    "expected_fast": expected_fast,
                    "expected_truth": expected_truth,
                    "got": got,
                    "context": context,
                }
            )
            return

        self._handle_len_mismatch(
            check_kind=check_kind,
            title=title,
            expected_fast=expected_fast,
            expected_truth=expected_truth,
            got=got,
            engine_fetch=engine_fetch,
            alt_fetch=alt_fetch,
            context=context,
        )

    def _remaining_len_probe(self, variant: str, t1: int, t2: int) -> dict[str, Any]:
        it = self._make_slice_iter(variant, t1, t2)
        before = 0
        consumed = 0
        after = 0
        closed_len = -1
        try:
            before = len(it)
            consume_target = min(self.cfg.len_consume_samples, before)
            for _ in range(consume_target):
                try:
                    next(it)
                    consumed += 1
                except StopIteration:
                    break
            after = len(it)
        finally:
            try:
                it.close()
            except Exception:
                pass
            try:
                closed_len = len(it)
            except Exception:
                closed_len = -1
        expected_after = before - consumed
        ok = (after == expected_after) and (closed_len == 0)
        return {
            "variant": variant,
            "before": before,
            "consumed": consumed,
            "after": after,
            "expected_after": expected_after,
            "closed_len": closed_len,
            "ok": ok,
        }

    def _verify_len_full_contract(self) -> None:
        if not self.cfg.len_checks:
            return
        expected_fast = self.shadow_fast.count_all()
        expected_truth = self.shadow_truth.count_all()
        self._verify_len_count_case(
            check_kind="len_full",
            title="len(log) contract mismatch",
            expected_fast=expected_fast,
            expected_truth=expected_truth,
            engine_fetch=lambda: len(self.log),
            alt_fetch=lambda: sum(1 for _ in self.log[:]),
            context={"query": "len(log)"},
        )

    def _verify_len_slice_contracts(self) -> None:
        if not self.cfg.len_checks:
            return
        if self.shadow_fast.live_count() == 0:
            return

        for i in range(self.cfg.len_slice_samples):
            variant = ("range", "since", "until", "all")[i % 4]
            t1, t2 = self._pick_len_window()
            expected_fast = self._expected_len_count(self.shadow_fast, variant, t1, t2)
            expected_truth = self._expected_len_count(self.shadow_truth, variant, t1, t2)
            desc = f"len(slice:{variant})"
            self._verify_len_count_case(
                check_kind="len_slice",
                title=f"{desc} contract mismatch",
                expected_fast=expected_fast,
                expected_truth=expected_truth,
                engine_fetch=lambda v=variant, a=t1, b=t2: self._len_slice_once(v, a, b),
                alt_fetch=lambda v=variant, a=t1, b=t2: self._sum_slice_once(v, a, b),
                context={"variant": variant, "t1": t1, "t2": t2},
            )

        # Remaining-length contract checks (decrement + close).
        for variant in ("range", "since", "until", "all"):
            t1, t2 = self._pick_len_window()
            self.check_index += 1
            self.len_checks_total += 1
            try:
                probe = self._remaining_len_probe(variant, t1, t2)
            except Exception as exc:
                self._register_runtime_issue(
                    kind="CHECKER_INCONSISTENCY",
                    title=f"remaining len probe crashed: {variant}",
                    evidence={"exception": repr(exc), "traceback": traceback.format_exc()},
                    severity="HIGH",
                    status=ISSUE_STATUS_CHECKER,
                )
                continue

            if probe["ok"]:
                self.checks_writer.write(
                    {
                        "check_index": self.check_index,
                        "op_index": self.op_index,
                        "kind": "len_slice_remaining",
                        "ok": True,
                        "context": probe,
                    }
                )
                continue

            self.mismatches += 1
            self.len_checks_failed += 1
            self.len_mismatches_by_kind["len_slice_remaining"] += 1
            outcome = self._triage_len_remaining_mismatch(
                kind="len_slice_remaining",
                probe_fetch=lambda v=variant, a=t1, b=t2: self._remaining_len_probe(v, a, b),
            )
            severity = "CRITICAL" if outcome.status == ISSUE_STATUS_CONFIRMED else "HIGH"
            issue_id = self.issue_registry.create_issue(
                kind="LEN_CONTRACT",
                severity=severity,
                status=outcome.status,
                op_index=self.op_index,
                check_index=self.check_index,
                title=f"remaining len contract mismatch ({variant})",
                context={"variant": variant, "t1": t1, "t2": t2},
                evidence={"probe": probe, "triage": {"notes": outcome.notes, "records": outcome.triage_records}},
            )
            self.checks_writer.write(
                {
                    "check_index": self.check_index,
                    "op_index": self.op_index,
                    "kind": "len_slice_remaining",
                    "ok": False,
                    "issue_id": issue_id,
                    "status": outcome.status,
                    "context": probe,
                },
                flush=True,
            )
            if outcome.status in {ISSUE_STATUS_CONFIRMED, ISSUE_STATUS_CHECKER} and not self.cfg.continue_on_mismatch:
                self.stop_reason = f"{outcome.status}:{issue_id}"

    def _verify_len_point_contract(self) -> None:
        if not self.cfg.len_checks:
            return
        ts_candidates: list[int] = []
        rnd = self.shadow_fast.random_live_ts(self.rng)
        if rnd is not None:
            ts_candidates.append(rnd)
        if self.shadow_fast.count_point(TL_TS_MAX) > 0:
            ts_candidates.append(TL_TS_MAX)
        if not ts_candidates:
            return

        for ts in ts_candidates:
            expected_fast = self.shadow_fast.count_point(ts)
            expected_truth = self.shadow_truth.count_point(ts)
            self._verify_len_count_case(
                check_kind="len_point",
                title=f"len(point:{ts}) contract mismatch",
                expected_fast=expected_fast,
                expected_truth=expected_truth,
                engine_fetch=lambda q=ts: self._len_point_once(q, use_equal=False),
                alt_fetch=lambda q=ts: self._len_point_once(q, use_equal=True),
                context={"ts": ts},
            )

    def _verify_point(self, ts: int, tag: str) -> None:
        self._run_row_check(
            ctx=CheckContext("point", {"ts": ts}, f"{tag} ts={ts}"),
            expected_rows=self.shadow_fast.query_point(ts),
            engine_fetch=lambda: [(ts, obj) for obj in self.log[ts]],
            alt_fetch=lambda: list(self.log.point(ts)),
        )

    def _verify_range(self, t1: int, t2: int, tag: str) -> None:
        self._run_row_check(
            ctx=CheckContext("range", {"t1": t1, "t2": t2}, f"{tag} [{t1},{t2})"),
            expected_rows=self.shadow_fast.query_range(t1, t2),
            engine_fetch=lambda: list(self.log[t1:t2]),
            alt_fetch=lambda: list(self.log.range(t1, t2)),
        )

    def _run_row_check(
        self,
        *,
        ctx: CheckContext,
        expected_rows: list[StoredRow],
        engine_fetch: Callable[[], list[tuple[int, Any]]],
        alt_fetch: Callable[[], list[tuple[int, Any]]] | None,
    ) -> None:
        self.check_index += 1
        initial_got = None
        try:
            initial_got = engine_fetch()
            cmp = _compare_rows(expected_rows, initial_got)
        except Exception as exc:
            self._register_runtime_issue(
                kind="CHECKER_INCONSISTENCY",
                title=f"engine fetch crashed during check: {ctx.description}",
                evidence={"exception": repr(exc), "traceback": traceback.format_exc(), "context": asdict(ctx)},
                severity="HIGH",
                status=ISSUE_STATUS_CHECKER,
            )
            return

        if cmp.ok:
            self.checks_writer.write(
                {
                    "check_index": self.check_index,
                    "op_index": self.op_index,
                    "kind": ctx.query_kind,
                    "ok": True,
                    "reason": cmp.reason,
                    "expected_n": cmp.expected_n,
                    "got_n": cmp.got_n,
                    "context": asdict(ctx),
                }
            )
            return

        self.mismatches += 1
        outcome = self.triager.triage(
            ctx=ctx,
            expected_rows=expected_rows,
            engine_fetch=engine_fetch,
            alt_fetch=alt_fetch,
            initial_got=initial_got,
        )
        severity = "CRITICAL" if outcome.status == ISSUE_STATUS_CONFIRMED else "HIGH"
        issue_id = self.issue_registry.create_issue(
            kind=cmp.reason,
            severity=severity,
            status=outcome.status,
            op_index=self.op_index,
            check_index=self.check_index,
            title=f"{cmp.reason} in {ctx.description}",
            context=asdict(ctx),
            evidence={
                "comparison": {
                    "reason": cmp.reason,
                    "expected_n": cmp.expected_n,
                    "got_n": cmp.got_n,
                    "missing_sample": cmp.missing,
                    "extra_sample": cmp.extra,
                },
                "triage": {"notes": outcome.notes, "records": outcome.triage_records},
            },
        )
        self.checks_writer.write(
            {
                "check_index": self.check_index,
                "op_index": self.op_index,
                "kind": ctx.query_kind,
                "ok": False,
                "issue_id": issue_id,
                "status": outcome.status,
                "reason": cmp.reason,
                "context": asdict(ctx),
            },
            flush=True,
        )
        if outcome.status in {ISSUE_STATUS_CONFIRMED, ISSUE_STATUS_CHECKER} and not self.cfg.continue_on_mismatch:
            self.stop_reason = f"{outcome.status}:{issue_id}"

    def _full_verify(self) -> None:
        self.full_verifies += 1
        self._run_row_check(
            ctx=CheckContext("full_scan", {}, "periodic full scan"),
            expected_rows=self.shadow_fast.query_all(),
            engine_fetch=lambda: list(self.log),
            alt_fetch=lambda: list(self.log[:]),
        )
        if self.cfg.len_checks:
            self._verify_len_slice_contracts()
            self._verify_len_point_contract()
        self._op_meta_probe()

    # ------------------------------------------------------------------
    # Post-op probes
    # ------------------------------------------------------------------

    def _post_insert_probe(self, rows: list[StoredRow]) -> None:
        for row in rows[: min(3, len(rows))]:
            self._verify_point(row.ts, "post_insert_hot")

    def _post_delete_probe(self, removed: list[StoredRow]) -> None:
        for row in removed[: min(3, len(removed))]:
            self._run_row_check(
                ctx=CheckContext("point", {"ts": row.ts}, f"post_delete_absence ts={row.ts} rid={row.rid}"),
                expected_rows=self.shadow_fast.query_point(row.ts),
                engine_fetch=lambda ts=row.ts: [(ts, obj) for obj in self.log[ts]],
                alt_fetch=lambda ts=row.ts: list(self.log.point(ts)),
            )

    # ------------------------------------------------------------------
    # Views and side probes
    # ------------------------------------------------------------------

    def _collect_views_records(self, t1: int, t2: int) -> list[tuple[int, Any]]:
        out: list[tuple[int, Any]] = []
        with self.log.views(t1, t2) as spans:
            for span in spans:
                try:
                    ts_view = span.timestamps
                    objs = span.objects()
                    prev_ts = None
                    for i in range(len(ts_view)):
                        ts = int(ts_view[i])
                        if ts < t1 or ts >= t2:
                            raise AssertionError(f"views timestamp out of range: ts={ts}")
                        if prev_ts is not None and ts < prev_ts:
                            raise AssertionError("views span timestamp order violation")
                        prev_ts = ts
                        out.append((ts, objs[i]))
                finally:
                    try:
                        span.close()
                    except Exception:
                        pass
        return out

    def _views_exact_side_probe(self) -> None:
        tl = Timelog(maintenance="disabled", busy_policy="flush", time_unit="ns")
        try:
            base = self.rng.randint(1_000_000, 9_000_000)
            pairs = []
            for i in range(300):
                ts = base + i * self.rng.randint(1, 10)
                pairs.append((ts, {"probe": "views_exact", "i": i, "rnd": self.rng.randint(0, 999)}))
            tl.extend(pairs)
            tl.flush()
            t1 = base + 20
            t2 = base + 1500

            # Explicit iterator lifecycle to avoid lingering snapshots.
            with tl.range(t1, t2) as it:
                logical = list(it)

            views: list[tuple[int, Any]] = []
            with tl.views(t1, t2) as spans:
                for span in spans:
                    ts_copy = None
                    objs = None
                    try:
                        # Use copied timestamps (not memoryview) so no exported buffer
                        # can block span close.
                        ts_copy = span.copy_timestamps()
                        objs = span.objects()
                        for i, ts in enumerate(ts_copy):
                            views.append((int(ts), objs[i]))
                    finally:
                        ts_copy = None
                        objs = None
                        try:
                            span.close()
                        except Exception:
                            pass

            lc = Counter((ts, _payload_digest(obj)) for ts, obj in logical)
            vc = Counter((ts, _payload_digest(obj)) for ts, obj in views)
            if lc != vc:
                self._register_runtime_issue(
                    kind="VIEWS_CONTRACT",
                    title="views exact side probe mismatch (no-delete)",
                    evidence={
                        "logical_n": len(logical),
                        "views_n": len(views),
                        "missing_sample": list((lc - vc).elements())[:20],
                        "extra_sample": list((vc - lc).elements())[:20],
                    },
                    severity="HIGH",
                    status=ISSUE_STATUS_CONFIRMED,
                )
        finally:
            gc.collect()
            tl.close()

    def _lifecycle_side_probe(self) -> None:
        box = self._ProbeBox()
        ref = weakref.ref(box)
        tl = Timelog(maintenance="disabled", busy_policy="flush", time_unit="ns")
        tl.append(123, box)
        del box
        tl.close()

        errs: list[str] = []
        for name, fn in [
            ("append", lambda: tl.append(124, {"x": 1})),
            ("flush", lambda: tl.flush()),
            ("compact", lambda: tl.compact()),
            ("range", lambda: list(tl[0:10])),
        ]:
            try:
                fn()
                errs.append(f"{name} did not raise on closed")
            except TimelogError:
                pass
            except Exception as exc:
                errs.append(f"{name} raised wrong exception: {exc!r}")

        for _ in range(3):
            gc.collect()
        if ref() is not None:
            errs.append("object retained after close + gc")

        if errs:
            self._register_runtime_issue(
                kind="LIFECYCLE_CONTRACT",
                title="lifecycle side probe failures",
                evidence={"errors": errs},
                severity="HIGH",
                status=ISSUE_STATUS_CONFIRMED,
            )

        tl2 = Timelog(maintenance="disabled", busy_policy="flush", time_unit="ns")
        tl2.append(1, {"probe": "close_after_flush"})
        tl2.flush()
        tl2.close()

    def _gc_cycle_side_probe(self) -> None:
        wr = None
        try:
            tl = Timelog(maintenance="disabled", busy_policy="flush", time_unit="ns")
            wr = weakref.ref(tl)
            holder = []
            holder.append(tl)
            tl.append(1, holder)
            del holder
            del tl
        except Exception as exc:
            self._register_runtime_issue(
                kind="LIFECYCLE_CONTRACT",
                title="gc side probe setup failed",
                evidence={"exception": repr(exc), "traceback": traceback.format_exc()},
                severity="MEDIUM",
                status=ISSUE_STATUS_TRANSIENT,
            )
            return
        for _ in range(5):
            gc.collect()
        if wr is not None and wr() is not None:
            self._register_runtime_issue(
                kind="LIFECYCLE_CONTRACT",
                title="gc cycle side probe did not collect timelog cycle",
                evidence={},
                severity="MEDIUM",
                status=ISSUE_STATUS_TRANSIENT,
            )

    def _handle_drop_health_probe(self) -> None:
        try:
            retired_q = int(getattr(self.log, "retired_queue_len", 0))
            alloc_failures = int(getattr(self.log, "alloc_failures", 0))
        except Exception:
            return
        self.ops_writer.write(
            {
                "op": "drop_health",
                "op_index": self.op_index,
                "retired_queue_len": retired_q,
                "alloc_failures": alloc_failures,
            }
        )
        if alloc_failures > 0:
            self._register_runtime_issue(
                kind="LIFECYCLE_CONTRACT",
                title="alloc_failures > 0",
                evidence={"alloc_failures": alloc_failures, "retired_queue_len": retired_q},
                severity="HIGH",
                status=ISSUE_STATUS_CONFIRMED,
            )

    def _side_probes(self) -> None:
        self.ops_writer.write({"op": "side_probes_start", "op_index": self.op_index}, flush=True)
        try:
            self._views_exact_side_probe()
        except Exception:
            self._register_runtime_issue(
                kind="VIEWS_CONTRACT",
                title="views exact side probe crashed",
                evidence={"traceback": traceback.format_exc()},
                severity="MEDIUM",
                status=ISSUE_STATUS_CHECKER,
            )
        try:
            self._lifecycle_side_probe()
        except Exception:
            self._register_runtime_issue(
                kind="LIFECYCLE_CONTRACT",
                title="lifecycle side probe crashed",
                evidence={"traceback": traceback.format_exc()},
                severity="MEDIUM",
                status=ISSUE_STATUS_CHECKER,
            )
        try:
            self._gc_cycle_side_probe()
        except Exception:
            self._register_runtime_issue(
                kind="LIFECYCLE_CONTRACT",
                title="gc side probe crashed",
                evidence={"traceback": traceback.format_exc()},
                severity="MEDIUM",
                status=ISSUE_STATUS_CHECKER,
            )

    # ------------------------------------------------------------------
    # Boundary and safe maintenance
    # ------------------------------------------------------------------

    def _boundary_probe(self) -> None:
        self.ops_writer.write({"op": "boundary_probe_start", "op_index": self.op_index}, flush=True)
        # TL_TS_MIN
        rid_min = self.next_rid
        self.next_rid += 1
        row_min = StoredRow(
            rid=rid_min,
            ts=TL_TS_MIN,
            obj={"__cc_schema": 1, "rid": rid_min, "src": "boundary", "cycle": 0,
                 "payload_digest": _payload_digest("tl_ts_min"), "payload": "tl_ts_min"},
            payload_digest=_payload_digest("tl_ts_min"),
            src="boundary",
            cycle=0,
            source_file="<boundary>",
            insert_op=self.op_index,
        )
        try:
            self.log.append(row_min.ts, row_min.obj)
        except TimelogBusyError:
            pass
        self._oracle_insert([row_min])
        self.inserts += 1
        self._verify_point(TL_TS_MIN, "boundary_tl_ts_min")

        # TL_TS_MAX (seed once; point-delete at TL_TS_MAX is intentionally unsupported)
        if not self.boundary_max_seeded:
            rid_max = self.next_rid
            self.next_rid += 1
            row_max = StoredRow(
                rid=rid_max,
                ts=TL_TS_MAX,
                obj={"__cc_schema": 1, "rid": rid_max, "src": "boundary", "cycle": 0,
                     "payload_digest": _payload_digest("tl_ts_max"), "payload": "tl_ts_max"},
                payload_digest=_payload_digest("tl_ts_max"),
                src="boundary",
                cycle=0,
                source_file="<boundary>",
                insert_op=self.op_index,
            )
            try:
                self.log.append(row_max.ts, row_max.obj)
            except TimelogBusyError:
                pass
            self._oracle_insert([row_max])
            self.inserts += 1
            self.boundary_max_seeded = True
        self._verify_point(TL_TS_MAX, "boundary_tl_ts_max")

        raised = False
        try:
            self.log.delete(TL_TS_MAX)
        except ValueError:
            raised = True
        except Exception as exc:
            raised = True
            self._register_runtime_issue(
                kind="BOUNDARY_CONTRACT",
                title="unexpected exception on delete(TL_TS_MAX)",
                evidence={"exception": repr(exc)},
                severity="MEDIUM",
                status=ISSUE_STATUS_CONFIRMED,
            )
        if not raised:
            self._register_runtime_issue(
                kind="BOUNDARY_CONTRACT",
                title="delete(TL_TS_MAX) did not raise ValueError",
                evidence={},
                severity="HIGH",
                status=ISSUE_STATUS_CONFIRMED,
            )

    def _safe_flush(self, tag: str) -> None:
        try:
            self.log.flush()
            self.ops_writer.write({"op": "flush", "op_index": self.op_index, "tag": tag, "ok": True})
        except TimelogError as exc:
            self.ops_writer.write({"op": "flush", "op_index": self.op_index, "tag": tag, "ok": False, "error": repr(exc)})

    def _safe_compact(self, tag: str) -> None:
        try:
            self.log.compact()
            self.ops_writer.write({"op": "compact", "op_index": self.op_index, "tag": tag, "ok": True})
        except TimelogError as exc:
            self.ops_writer.write({"op": "compact", "op_index": self.op_index, "tag": tag, "ok": False, "error": repr(exc)})

    def _safe_maintenance_sweep(self, tag: str) -> None:
        self._safe_flush(f"{tag}:flush")
        self._safe_compact(f"{tag}:compact")
        try:
            self.log.validate()
            self.ops_writer.write({"op": "validate", "op_index": self.op_index, "tag": tag, "ok": True})
        except TimelogError as exc:
            self.ops_writer.write({"op": "validate", "op_index": self.op_index, "tag": tag, "ok": False, "error": repr(exc)})

    # ------------------------------------------------------------------
    # Issue and summary
    # ------------------------------------------------------------------

    def _register_runtime_issue(
        self,
        *,
        kind: str,
        title: str,
        evidence: dict[str, Any],
        severity: str,
        status: str,
    ) -> None:
        issue_id = self.issue_registry.create_issue(
            kind=kind,
            severity=severity,
            status=status,
            op_index=self.op_index,
            check_index=self.check_index,
            title=title,
            context={"op_index": self.op_index, "check_index": self.check_index},
            evidence=evidence,
        )
        if status in {ISSUE_STATUS_CONFIRMED, ISSUE_STATUS_CHECKER} and not self.cfg.continue_on_mismatch:
            self.stop_reason = f"{status}:{issue_id}"

    def _build_summary(self, started: float, outcome: RunOutcome) -> dict[str, Any]:
        ended_utc = _utc_now_iso()
        elapsed_s = int(time.monotonic() - started)
        triggered_statuses = sorted([k for k, v in outcome.fail_status_counts.items() if v > 0])
        cfg_dict = asdict(self.cfg)
        cfg_dict["fail_statuses"] = sorted(self.cfg.fail_statuses)
        return {
            "run_id": self.run_id,
            "started_utc": self.started_utc,
            "ended_utc": ended_utc,
            "elapsed_seconds": elapsed_s,
            "git_commit": self.git_commit,
            "config": cfg_dict,
            "result": outcome.result,
            "exit_code": outcome.exit_code,
            "artifact_mode": self.cfg.artifact_mode,
            "gate": {
                "fail_statuses": sorted(self.cfg.fail_statuses),
                "fail_status_counts": dict(outcome.fail_status_counts),
                "triggered_statuses": triggered_statuses,
            },
            "stats": {
                "ops": self.op_index,
                "checks": self.check_index,
                "inserts": self.inserts,
                "deletes": self.deletes,
                "live_rows": self.shadow_fast.live_count(),
                "full_verifies": self.full_verifies,
                "mismatches": self.mismatches,
                "len_checks_total": self.len_checks_total,
                "len_checks_failed": self.len_checks_failed,
                "len_mismatches_by_kind": dict(self.len_mismatches_by_kind),
                "issues_total": self.issue_registry.count,
                "issues_by_status": dict(self.issue_registry.by_status),
                "issues_by_kind": dict(self.issue_registry.by_kind),
                "stop_reason": self.stop_reason,
            },
            "artifact_paths": {
                "run_dir": str(self.run_dir),
                "ops_jsonl": str(self.ops_writer.path),
                "checks_jsonl": str(self.checks_writer.path),
                "issues_jsonl": str(self.issues_writer.path),
                "issues_dir": str(self.issue_registry.issues_dir),
            },
            "artifact_manifest": [],
            "csv_source": None if self.csv_source is None else self.csv_source.stats(),
        }

    def _render_summary_md(self, summary: dict[str, Any]) -> str:
        md = [
            "# Timelog Correctness Checker Summary",
            "",
            f"- Run ID: `{summary.get('run_id')}`",
            f"- Started (UTC): `{summary.get('started_utc')}`",
            f"- Ended (UTC): `{summary.get('ended_utc')}`",
            f"- Elapsed: `{summary.get('elapsed_seconds')}s`",
            f"- Git commit: `{summary.get('git_commit')}`",
            f"- Result: `{summary.get('result')}`",
            f"- Exit code: `{summary.get('exit_code')}`",
            f"- Artifact mode: `{summary.get('artifact_mode')}`",
            "",
            "## Totals",
            "",
            f"- Operations: `{summary['stats']['ops']}`",
            f"- Checks: `{summary['stats']['checks']}`",
            f"- Inserts: `{summary['stats']['inserts']}`",
            f"- Deletes: `{summary['stats']['deletes']}`",
            f"- Live rows: `{summary['stats']['live_rows']}`",
            f"- Full verifies: `{summary['stats']['full_verifies']}`",
            f"- Mismatches: `{summary['stats']['mismatches']}`",
            f"- Len checks total: `{summary['stats']['len_checks_total']}`",
            f"- Len checks failed: `{summary['stats']['len_checks_failed']}`",
            f"- Issues: `{summary['stats']['issues_total']}`",
            f"- Stop reason: `{summary['stats']['stop_reason']}`",
            "",
            "## Gate",
            "",
            f"- Fail statuses: `{', '.join(summary['gate']['fail_statuses'])}`",
            f"- Triggered: `{', '.join(summary['gate']['triggered_statuses']) or 'none'}`",
            "",
            "## Issues by Status",
            "",
        ]
        for k, v in sorted(summary["stats"]["issues_by_status"].items()):
            md.append(f"- `{k}`: `{v}`")
        md += ["", "## Issues by Kind", ""]
        for k, v in sorted(summary["stats"]["issues_by_kind"].items()):
            md.append(f"- `{k}`: `{v}`")
        md += ["", "## Len Mismatches by Kind", ""]
        if summary["stats"]["len_mismatches_by_kind"]:
            for k, v in sorted(summary["stats"]["len_mismatches_by_kind"].items()):
                md.append(f"- `{k}`: `{v}`")
        else:
            md.append("- none")
        md += ["", "## Retained Artifacts", ""]
        manifest = summary.get("artifact_manifest", [])
        if manifest:
            for item in manifest:
                md.append(f"- `{item}`")
        else:
            md.append("- pending")
        md += ["", "## Reproduction Command", "", "```powershell", self.repro_cmd, "```", ""]
        return "\n".join(md) + "\n"

    def _finalize_summary(self, started: float, outcome: RunOutcome) -> dict[str, Any]:
        summary = self._build_summary(started, outcome)
        self.ops_writer.write({"op": "run_end", "t_utc": summary["ended_utc"], "summary": summary["stats"]}, flush=True)
        return summary

    def _write_summary_files(self, summary: dict[str, Any]) -> None:
        summary_json_path = self.run_dir / "summary.json"
        summary_md_path = self.run_dir / "summary.md"

        summary_json_path.write_text(json.dumps(summary, indent=2, ensure_ascii=True, default=str) + "\n", encoding="utf-8")
        summary_md_path.write_text(self._render_summary_md(summary), encoding="utf-8")

        extra_outputs: list[Path] = []
        if self.cfg.summary_json_out:
            extra_outputs.append(Path(self.cfg.summary_json_out))
        if self.cfg.summary_md_out:
            extra_outputs.append(Path(self.cfg.summary_md_out))

        for out in extra_outputs:
            out.parent.mkdir(parents=True, exist_ok=True)

        if self.cfg.summary_json_out:
            Path(self.cfg.summary_json_out).write_text(
                json.dumps(summary, indent=2, ensure_ascii=True, default=str) + "\n",
                encoding="utf-8",
            )
        if self.cfg.summary_md_out:
            Path(self.cfg.summary_md_out).write_text(self._render_summary_md(summary), encoding="utf-8")

        retained: set[str] = set(summary.get("artifact_manifest", []))
        retained.add(str(summary_json_path))
        retained.add(str(summary_md_path))
        if self.cfg.summary_json_out:
            retained.add(str(Path(self.cfg.summary_json_out)))
        if self.cfg.summary_md_out:
            retained.add(str(Path(self.cfg.summary_md_out)))
        summary["artifact_manifest"] = sorted(retained)
        if "artifact_policy" in summary:
            summary["artifact_policy"]["retained_files"] = list(summary["artifact_manifest"])

        summary_json_path.write_text(json.dumps(summary, indent=2, ensure_ascii=True, default=str) + "\n", encoding="utf-8")
        summary_md_path.write_text(self._render_summary_md(summary), encoding="utf-8")
        if self.cfg.summary_json_out:
            Path(self.cfg.summary_json_out).write_text(
                json.dumps(summary, indent=2, ensure_ascii=True, default=str) + "\n",
                encoding="utf-8",
            )
        if self.cfg.summary_md_out:
            Path(self.cfg.summary_md_out).write_text(self._render_summary_md(summary), encoding="utf-8")

    def _finalize_artifacts(self, summary: dict[str, Any], outcome: RunOutcome) -> None:
        detail_paths = [
            Path(summary["artifact_paths"]["ops_jsonl"]),
            Path(summary["artifact_paths"]["checks_jsonl"]),
            Path(summary["artifact_paths"]["issues_jsonl"]),
            Path(summary["artifact_paths"]["issues_dir"]),
        ]
        bundle_out = Path(self.cfg.failure_bundle_out) if self.cfg.failure_bundle_out else None
        manifest = _apply_artifact_policy(
            run_dir=self.run_dir,
            artifact_mode=self.cfg.artifact_mode,
            result=outcome.result,
            detail_paths=detail_paths,
            failure_bundle_out=bundle_out,
        )
        outcome.artifact_manifest = manifest
        if manifest.get("bundle_path"):
            summary["artifact_paths"]["failure_bundle"] = manifest["bundle_path"]
        summary["artifact_manifest"] = list(manifest.get("retained_files", []))
        summary["artifact_policy"] = manifest

    def _print_summary(self, summary: dict[str, Any]) -> None:
        print("=" * 96)
        print(
            "SUMMARY: "
            f"ops={summary['stats']['ops']} checks={summary['stats']['checks']} "
            f"inserts={summary['stats']['inserts']} deletes={summary['stats']['deletes']} "
            f"issues={summary['stats']['issues_total']} "
            f"confirmed={summary['stats']['issues_by_status'].get(ISSUE_STATUS_CONFIRMED, 0)} "
            f"checker={summary['stats']['issues_by_status'].get(ISSUE_STATUS_CHECKER, 0)} "
            f"result={summary.get('result')}"
        )
        print(f"Artifacts: {self.run_dir}")
        print("=" * 96)


def _parse_args() -> RunConfig:
    parser = argparse.ArgumentParser(
        description="Timelog Correctness Checker (chaotic, oracle-backed validator)"
    )
    parser.add_argument("--duration-seconds", type=int, default=3600)
    parser.add_argument("--duration", type=int, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--seed", type=int, default=None)
    parser.add_argument("--source-mode", choices=["synthetic", "csv", "mixed"], default="mixed")
    parser.add_argument("--csv", action="append", default=None,
                        help="CSV file path (repeatable). Default: two demo files.")
    parser.add_argument("--out-dir", type=str, default="demo/correctness_runs")
    parser.add_argument("--min-batch", type=int, default=1)
    parser.add_argument("--max-batch", type=int, default=10_000)
    parser.add_argument("--maintenance", choices=["background", "disabled"], default="background")
    parser.add_argument("--busy-policy", choices=["raise", "silent", "flush"], default="flush")
    parser.add_argument("--full-verify-interval-ops", type=int, default=200)
    parser.add_argument("--full-verify-interval-seconds", type=int, default=30)
    parser.add_argument("--checkpoint-interval-ops", type=int, default=1000)
    parser.add_argument("--len-checks", choices=["on", "off"], default="on")
    parser.add_argument("--len-slice-samples", type=int, default=6)
    parser.add_argument("--len-consume-samples", type=int, default=3)
    parser.add_argument("--continue-on-mismatch", action="store_true")
    parser.add_argument("--max-issues", type=int, default=100)
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--log", type=str, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--ci-profile", choices=["off", "pr", "nightly"], default="off")
    parser.add_argument("--artifact-mode", choices=["full", "minimal", "fail-bundle"], default="full")
    parser.add_argument(
        "--fail-statuses",
        type=str,
        default=DEFAULT_FAIL_STATUSES,
        help="Comma-separated statuses that should fail the run.",
    )
    parser.add_argument("--summary-json-out", type=str, default=None)
    parser.add_argument("--summary-md-out", type=str, default=None)
    parser.add_argument("--failure-bundle-out", type=str, default=None)
    parser.add_argument("--run-id", type=str, default=None)
    args = parser.parse_args()

    duration = args.duration if args.duration is not None else args.duration_seconds
    if duration <= 0:
        raise SystemExit("--duration-seconds must be positive")
    seed = args.seed if args.seed is not None else random.randint(0, 2**32 - 1)
    min_batch = max(1, args.min_batch)
    max_batch = max(min_batch, args.max_batch)
    csv_paths = args.csv if args.csv is not None else DEFAULT_CSVS
    fail_statuses = _parse_fail_statuses(args.fail_statuses)

    return RunConfig(
        duration_seconds=duration,
        seed=seed,
        source_mode=args.source_mode,
        csv_paths=csv_paths,
        out_dir=args.out_dir,
        min_batch=min_batch,
        max_batch=max_batch,
        maintenance=args.maintenance,
        busy_policy=args.busy_policy,
        full_verify_interval_ops=max(1, args.full_verify_interval_ops),
        full_verify_interval_seconds=max(1, args.full_verify_interval_seconds),
        checkpoint_interval_ops=max(1, args.checkpoint_interval_ops),
        len_checks=(args.len_checks == "on"),
        len_slice_samples=max(1, args.len_slice_samples),
        len_consume_samples=max(0, args.len_consume_samples),
        continue_on_mismatch=args.continue_on_mismatch,
        max_issues=max(1, args.max_issues),
        verbose=args.verbose,
        log_alias_path=args.log,
        ci_profile=args.ci_profile,
        artifact_mode=args.artifact_mode,
        fail_statuses=fail_statuses,
        summary_json_out=args.summary_json_out,
        summary_md_out=args.summary_md_out,
        failure_bundle_out=args.failure_bundle_out,
        run_id_override=args.run_id,
    )


def main() -> int:
    cfg = _parse_args()
    runner = CorrectnessRunner(cfg)
    return runner.run()


if __name__ == "__main__":
    raise SystemExit(main())
