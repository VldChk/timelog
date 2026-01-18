#!/usr/bin/env python3
"""
Rolling retention stress test for Timelog.

This script simulates a long-running server workload:
  - Load an initial chunk (default: 1/5 of file)
  - Delete the earliest 20% of that chunk
  - Then roll: append 1/25 of file, delete earliest 1/25
  - When EOF is reached, loop the file and add a timestamp offset

It focuses on long-run behavior under continuous delete/append:
  - Maintenance/compaction behavior
  - Backpressure and busy errors
  - Memory growth and stability
  - Out-of-order ingestion effects

All monitoring is written to a JSONL file for offline analysis.

Delete modes:
  - ttl: uses delete_before(cutoff) where cutoff = latest_ts - retain_span
    retain_span is a fraction of the full file time span.
  - range: uses delete_range(old_min, old_max) for queued batch ranges.
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import os
import sys
import time
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator, Optional

# Add parent directory to path for timelog import
sys.path.insert(0, str(Path(__file__).parent.parent / "python"))

from timelog import Timelog, TimelogBusyError

try:
    import psutil
except ImportError:  # pragma: no cover - optional dependency
    psutil = None

CSV_COLUMNS = [
    "timestamp",
    "ticker",
    "isin",
    "direction",
    "status",
    "amount",
    "ask_price",
    "bid_price",
    "order_id",
    "commission",
]


@dataclass
class ScanResult:
    rows_total: int
    ts_min: int
    ts_max: int
    skipped: int

    @property
    def span(self) -> int:
        return self.ts_max - self.ts_min + 1


class CSVSource:
    """Reusable CSV source with optional preload and trusted parsing."""

    def __init__(self, path: str, trusted: bool, preload: bool) -> None:
        self.path = path
        self.trusted = trusted
        self.preload = preload
        self._cache: Optional[str] = None
        self._index_map: Optional[dict[str, int]] = None
        if preload:
            with open(path, "r", newline="") as f:
                self._cache = f.read()

    def _open(self):
        if self._cache is not None:
            return io.StringIO(self._cache)
        return open(self.path, "r", newline="")

    def iter_timestamps(self) -> Iterator[int]:
        with self._open() as f:
            if self.trusted:
                reader = csv.reader(f)
                header = next(reader, None)
                if header is None:
                    return
                if self._index_map is None:
                    self._index_map = {}
                    for name in CSV_COLUMNS:
                        if name not in header:
                            raise ValueError(f"missing column in trusted CSV: {name}")
                        self._index_map[name] = header.index(name)
                idx = self._index_map
                assert idx is not None
                for row in reader:
                    yield int(row[idx["timestamp"]])
            else:
                reader = csv.DictReader(f)
                for row in reader:
                    ts_raw = row.get("timestamp")
                    if ts_raw is None:
                        continue
                    try:
                        yield int(ts_raw)
                    except ValueError:
                        continue


class RollingReader:
    """Cycles through a CSV file, applying a monotonic timestamp offset."""

    def __init__(self, source: CSVSource, span: int) -> None:
        self.source = source
        self.span = span
        self.offset = 0
        self._iter: Optional[Iterator[int]] = None

    def _reset_iter(self) -> None:
        self._iter = self.source.iter_timestamps()

    def next_batch(self, batch_size: int) -> list[int]:
        if self._iter is None:
            self._reset_iter()
        assert self._iter is not None
        out: list[int] = []
        while len(out) < batch_size:
            try:
                ts = next(self._iter)
            except StopIteration:
                self.offset += self.span
                self._reset_iter()
                continue
            out.append(ts + self.offset)
        return out


class LatencyTracker:
    """Keep a bounded sample for latency percentiles."""

    def __init__(self, max_samples: int = 10000) -> None:
        self.max_samples = max_samples
        self.samples: list[int] = []
        self.count = 0
        self.total_ns = 0
        self.min_ns: Optional[int] = None
        self.max_ns: Optional[int] = None

    def add(self, ns: int) -> None:
        self.count += 1
        self.total_ns += ns
        self.min_ns = ns if self.min_ns is None else min(self.min_ns, ns)
        self.max_ns = ns if self.max_ns is None else max(self.max_ns, ns)
        if len(self.samples) < self.max_samples:
            self.samples.append(ns)

    def snapshot(self) -> dict:
        if self.count == 0:
            return {"count": 0}
        if not self.samples:
            return {"count": self.count}
        s = sorted(self.samples)
        n = len(s)

        def pct(p: float) -> int:
            idx = int((p / 100.0) * (n - 1))
            return s[idx]

        return {
            "count": self.count,
            "min_ns": self.min_ns,
            "p50_ns": pct(50),
            "p95_ns": pct(95),
            "p99_ns": pct(99),
            "max_ns": self.max_ns,
            "avg_ns": int(self.total_ns / self.count),
        }


def scan_csv(source: CSVSource, progress_every: int = 1_000_000) -> ScanResult:
    ts_min: Optional[int] = None
    ts_max: Optional[int] = None
    total = 0
    skipped = 0
    for ts in source.iter_timestamps():
        if ts_min is None or ts < ts_min:
            ts_min = ts
        if ts_max is None or ts > ts_max:
            ts_max = ts
        total += 1
        if progress_every and total % progress_every == 0:
            print(f"  Scanned {total:,} rows...")
    if ts_min is None or ts_max is None:
        raise RuntimeError("CSV scan produced no timestamps")
    return ScanResult(rows_total=total, ts_min=ts_min, ts_max=ts_max, skipped=skipped)


def process_rss_mb() -> float:
    if psutil is None:
        return 0.0
    return psutil.Process(os.getpid()).memory_info().rss / (1024 * 1024)


def build_timelog(args: argparse.Namespace) -> Timelog:
    if args.use_defaults:
        return Timelog()
    kwargs = {}
    if args.time_unit is not None:
        kwargs["time_unit"] = args.time_unit
    if args.maintenance is not None:
        kwargs["maintenance"] = args.maintenance
    if args.memtable_max_bytes is not None:
        kwargs["memtable_max_bytes"] = args.memtable_max_bytes
    if args.target_page_bytes is not None:
        kwargs["target_page_bytes"] = args.target_page_bytes
    if args.sealed_max_runs is not None:
        kwargs["sealed_max_runs"] = args.sealed_max_runs
    if args.drain_batch_limit is not None:
        kwargs["drain_batch_limit"] = args.drain_batch_limit
    if args.busy_policy is not None:
        kwargs["busy_policy"] = args.busy_policy
    return Timelog(**kwargs)


def write_jsonl(path: str, record: dict) -> None:
    with open(path, "a", newline="") as f:
        f.write(json.dumps(record, sort_keys=True))
        f.write("\n")


def main() -> int:
    parser = argparse.ArgumentParser(description="Timelog rolling retention stress test")
    parser.add_argument("--data", required=True, help="Path to CSV file")
    parser.add_argument("--duration-seconds", type=int, default=3600)
    parser.add_argument("--report-interval-seconds", type=int, default=10)
    parser.add_argument("--batch-size", type=int, default=10_000)
    parser.add_argument("--initial-fraction", type=float, default=0.2)
    parser.add_argument("--initial-delete-fraction", type=float, default=0.2)
    parser.add_argument("--step-fraction", type=float, default=0.04)
    parser.add_argument("--retain-fraction", type=float, default=None)
    parser.add_argument("--delete-mode", choices=["ttl", "range"], default="ttl")
    parser.add_argument("--delete-interval-batches", type=int, default=1)
    parser.add_argument("--trust-csv", action="store_true")
    parser.add_argument("--preload-csv", action="store_true")
    parser.add_argument("--reuse-obj", action="store_true", default=True)
    parser.add_argument("--unique-obj", dest="reuse_obj", action="store_false")
    parser.add_argument("--time-unit", choices=["s", "ms", "us", "ns"], default="ns")
    parser.add_argument("--maintenance", choices=["disabled", "background"], default="background")
    parser.add_argument("--busy-policy", choices=["raise", "silent", "flush"], default="flush")
    parser.add_argument("--busy-action", choices=["none", "flush", "compact"], default="none",
                        help="Action on TimelogBusyError (no retry)")
    parser.add_argument("--memtable-max-bytes", type=int, default=None)
    parser.add_argument("--target-page-bytes", type=int, default=None)
    parser.add_argument("--sealed-max-runs", type=int, default=None)
    parser.add_argument("--drain-batch-limit", type=int, default=None)
    parser.add_argument("--use-defaults", action="store_true",
                        help="Use Timelog() defaults (ignore explicit config)")
    parser.add_argument("--metrics-out", default="demo/rolling_retention_metrics.jsonl")
    parser.add_argument("--summary-out", default="demo/rolling_retention_summary.json")
    parser.add_argument("--flush-interval-seconds", type=int, default=0,
                        help="Optional: call flush() every N seconds")
    parser.add_argument("--compact-interval-seconds", type=int, default=0,
                        help="Optional: call compact() every N seconds")
    args = parser.parse_args()

    if args.batch_size <= 0:
        raise SystemExit("batch-size must be positive")
    if not (0.0 < args.initial_fraction <= 1.0):
        raise SystemExit("initial-fraction must be in (0, 1]")
    if not (0.0 < args.step_fraction <= 1.0):
        raise SystemExit("step-fraction must be in (0, 1]")
    if not (0.0 <= args.initial_delete_fraction <= 1.0):
        raise SystemExit("initial-delete-fraction must be in [0, 1]")
    if args.retain_fraction is not None and not (0.0 < args.retain_fraction <= 1.0):
        raise SystemExit("retain-fraction must be in (0, 1]")

    data_path = args.data
    source = CSVSource(data_path, trusted=args.trust_csv, preload=args.preload_csv)

    print("Scanning CSV for row count and timestamp span...")
    scan = scan_csv(source)
    span = scan.span
    rows_total = scan.rows_total

    initial_fraction = args.initial_fraction
    initial_delete_fraction = args.initial_delete_fraction
    step_fraction = args.step_fraction
    if args.retain_fraction is None:
        retain_fraction = initial_fraction * (1.0 - initial_delete_fraction)
    else:
        retain_fraction = args.retain_fraction

    initial_rows = max(1, int(rows_total * initial_fraction))
    step_rows = max(1, int(rows_total * step_fraction))
    retain_rows_target = max(1, int(rows_total * retain_fraction))

    time_unit_label = "default" if args.use_defaults else args.time_unit
    maintenance_label = "default" if args.use_defaults else args.maintenance
    busy_policy_label = "default" if args.use_defaults else args.busy_policy
    maintenance_effective = "disabled" if args.use_defaults else args.maintenance
    compact_requests_only = maintenance_effective != "background"

    print(f"Rows total: {rows_total:,}")
    print(f"Timestamp span: {span:,}")
    print(f"Initial rows: {initial_rows:,}")
    print(f"Step rows: {step_rows:,}")
    print(f"Retain rows target: {retain_rows_target:,}")
    print(f"Timelog config: time_unit={time_unit_label}, maintenance={maintenance_label}, "
          f"busy_policy={busy_policy_label}, use_defaults={args.use_defaults}")
    print("Compaction note: delete_debt_threshold defaults to 0.0 and is not configurable "
          "from Python; compaction triggers on L0 count or explicit compact().")
    if args.compact_interval_seconds > 0 and compact_requests_only:
        print("Warning: maintenance is disabled; compact() only requests work and "
              "no compaction will run without background maintenance.")

    reader = RollingReader(source, span=span)

    start_wall = time.perf_counter()
    last_report = start_wall
    last_flush = start_wall
    last_compact = start_wall

    append_latency = LatencyTracker()
    delete_latency = LatencyTracker()
    flush_latency = LatencyTracker()
    compact_latency = LatencyTracker()

    appended_total = 0
    deleted_requests = 0
    deleted_rows_est: Optional[int] = 0 if args.delete_mode == "range" else None
    busy_errors = 0
    flush_calls = 0
    compact_calls = 0

    adjacent_ooo = 0
    global_ooo = 0
    global_max_ts: Optional[int] = None
    last_ts: Optional[int] = None

    retained_rows_est = 0
    ranges = deque()  # (min_ts, max_ts_exclusive, count)
    latest_ts: Optional[int] = None
    last_delete_cutoff: Optional[int] = None
    late_records = 0

    last_appended_total = 0
    last_deleted_requests = 0
    last_busy_errors = 0

    write_jsonl(args.metrics_out, {
        "event": "start",
        "timestamp": time.time(),
        "data_path": data_path,
        "rows_total": rows_total,
        "ts_min": scan.ts_min,
        "ts_max": scan.ts_max,
        "span": span,
        "initial_rows": initial_rows,
        "step_rows": step_rows,
        "retain_rows_target": retain_rows_target,
        "delete_mode": args.delete_mode,
        "time_unit": time_unit_label,
        "maintenance": maintenance_label,
        "busy_policy": busy_policy_label,
        "trusted_csv": args.trust_csv,
        "preload_csv": args.preload_csv,
        "reuse_obj": args.reuse_obj,
        "memtable_max_bytes": args.memtable_max_bytes,
        "target_page_bytes": args.target_page_bytes,
        "sealed_max_runs": args.sealed_max_runs,
        "drain_batch_limit": args.drain_batch_limit,
        "use_defaults": args.use_defaults,
        "busy_action": args.busy_action,
        "maintenance_effective": maintenance_effective,
        "compact_requests_only": compact_requests_only,
        "compaction_note": "delete_debt_threshold default=0 (not configurable in Python)",
    })

    shared_obj = {"payload": 1}

    def make_obj(idx: int):
        if args.reuse_obj:
            return shared_obj
        return {"payload": idx}

    def handle_busy() -> None:
        nonlocal busy_errors, flush_calls, compact_calls
        busy_errors += 1
        if args.busy_action == "flush":
            t0 = time.perf_counter_ns()
            log.flush()
            t1 = time.perf_counter_ns()
            flush_latency.add(t1 - t0)
            flush_calls += 1
        elif args.busy_action == "compact":
            t0 = time.perf_counter_ns()
            log.compact()
            t1 = time.perf_counter_ns()
            compact_latency.add(t1 - t0)
            compact_calls += 1

    def ingest_batch(batch_ts: list[int]) -> tuple[int, int]:
        nonlocal appended_total, busy_errors, last_ts, global_max_ts
        nonlocal adjacent_ooo, global_ooo

        if not batch_ts:
            return 0, 0
        batch_min = min(batch_ts)
        batch_max = max(batch_ts)

        for ts in batch_ts:
            if last_ts is not None and ts < last_ts:
                adjacent_ooo += 1
            if global_max_ts is not None and ts < global_max_ts:
                global_ooo += 1
            if global_max_ts is None or ts > global_max_ts:
                global_max_ts = ts
            last_ts = ts

        records = [(ts, make_obj(appended_total + i)) for i, ts in enumerate(batch_ts)]
        t0 = time.perf_counter_ns()
        try:
            log.extend(records)
        except TimelogBusyError:
            handle_busy()
        finally:
            t1 = time.perf_counter_ns()
            append_latency.add(t1 - t0)

        appended_total += len(records)
        return batch_min, batch_max

    def ingest_step(step_count: int, collect_ts: bool) -> tuple[int, int, list[int]]:
        step_min: Optional[int] = None
        step_max: Optional[int] = None
        collected: list[int] = [] if collect_ts else []
        remaining = step_count
        while remaining > 0:
            batch_size = min(args.batch_size, remaining)
            batch = reader.next_batch(batch_size)
            batch_min, batch_max = ingest_batch(batch)
            if step_min is None or batch_min < step_min:
                step_min = batch_min
            if step_max is None or batch_max > step_max:
                step_max = batch_max
            if collect_ts:
                collected.extend(batch)
            remaining -= len(batch)
        assert step_min is not None and step_max is not None
        return step_min, step_max, collected

    with build_timelog(args) as log:
        # Initial load
        print("Initial load...")
        init_min = None
        init_max = None
        rows_loaded = 0
        while rows_loaded < initial_rows:
            batch_size = min(args.batch_size, initial_rows - rows_loaded)
            batch_ts = reader.next_batch(batch_size)
            batch_min, batch_max = ingest_batch(batch_ts)
            if init_min is None or batch_min < init_min:
                init_min = batch_min
            if init_max is None or batch_max > init_max:
                init_max = batch_max
            rows_loaded += len(batch_ts)
            if args.delete_mode == "range":
                ranges.append((batch_min, batch_max + 1, len(batch_ts)))
                retained_rows_est += len(batch_ts)

        # Initial delete: earliest 20% of initial chunk
        if init_min is not None and init_max is not None:
            cutoff = init_min + int((init_max - init_min + 1) * initial_delete_fraction)
            if args.delete_mode == "ttl":
                t0 = time.perf_counter_ns()
                try:
                    log.delete_before(cutoff)
                except TimelogBusyError:
                    handle_busy()
                t1 = time.perf_counter_ns()
                delete_latency.add(t1 - t0)
                last_delete_cutoff = cutoff
                deleted_requests += 1
            else:
                while retained_rows_est > retain_rows_target and ranges:
                    t0 = time.perf_counter_ns()
                    r_min, r_max, r_count = ranges.popleft()
                    try:
                        log.delete_range(r_min, r_max)
                    except TimelogBusyError:
                        handle_busy()
                    t1 = time.perf_counter_ns()
                    delete_latency.add(t1 - t0)
                    retained_rows_est -= r_count
                    if deleted_rows_est is not None:
                        deleted_rows_est += r_count
                    deleted_requests += 1

        print("Entering rolling retention loop...")
        last_appended_total = appended_total
        last_deleted_requests = deleted_requests
        last_busy_errors = busy_errors
        while True:
            now = time.perf_counter()
            elapsed = now - start_wall
            if elapsed >= args.duration_seconds:
                break

            step_min, step_max, step_ts = ingest_step(
                step_rows, collect_ts=(args.delete_mode == "ttl")
            )

            if latest_ts is None or step_max > latest_ts:
                latest_ts = step_max

            if args.delete_mode == "ttl" and latest_ts is not None:
                retain_span = max(1, int(span * retain_fraction))
                cutoff = latest_ts - retain_span
                if step_ts:
                    late_records += sum(1 for ts in step_ts if ts < cutoff)
                if last_delete_cutoff is None or cutoff > last_delete_cutoff:
                    if (appended_total // step_rows) % args.delete_interval_batches == 0:
                        t0 = time.perf_counter_ns()
                        try:
                            log.delete_before(cutoff)
                        except TimelogBusyError:
                            handle_busy()
                        t1 = time.perf_counter_ns()
                        delete_latency.add(t1 - t0)
                        deleted_requests += 1
                        last_delete_cutoff = cutoff
            else:
                ranges.append((step_min, step_max + 1, step_rows))
                retained_rows_est += step_rows
                while retained_rows_est > retain_rows_target and ranges:
                    t0 = time.perf_counter_ns()
                    r_min, r_max, r_count = ranges.popleft()
                    try:
                        log.delete_range(r_min, r_max)
                    except TimelogBusyError:
                        handle_busy()
                    t1 = time.perf_counter_ns()
                    delete_latency.add(t1 - t0)
                    retained_rows_est -= r_count
                    if deleted_rows_est is not None:
                        deleted_rows_est += r_count
                    deleted_requests += 1

            if args.flush_interval_seconds > 0 and now - last_flush >= args.flush_interval_seconds:
                t0 = time.perf_counter_ns()
                log.flush()
                t1 = time.perf_counter_ns()
                flush_latency.add(t1 - t0)
                flush_calls += 1
                last_flush = now

            if args.compact_interval_seconds > 0 and now - last_compact >= args.compact_interval_seconds:
                t0 = time.perf_counter_ns()
                log.compact()
                t1 = time.perf_counter_ns()
                compact_latency.add(t1 - t0)
                compact_calls += 1
                last_compact = now

            if now - last_report >= args.report_interval_seconds:
                dt = now - last_report
                appended_delta = appended_total - last_appended_total
                deleted_delta = deleted_requests - last_deleted_requests
                busy_delta = busy_errors - last_busy_errors
                write_jsonl(args.metrics_out, {
                    "event": "sample",
                    "timestamp": time.time(),
                    "elapsed_s": elapsed,
                    "appended_total": appended_total,
                    "deleted_requests": deleted_requests,
                    "append_rate_rps": appended_delta / dt if dt > 0 else 0,
                    "delete_rate_rps": deleted_delta / dt if dt > 0 else 0,
                    "busy_errors_delta": busy_delta,
                    "busy_errors": busy_errors,
                    "flush_calls": flush_calls,
                    "compact_calls": compact_calls,
                    "adjacent_ooo": adjacent_ooo,
                    "global_ooo": global_ooo,
                    "adjacent_ooo_ratio": adjacent_ooo / appended_total if appended_total else 0,
                    "global_ooo_ratio": global_ooo / appended_total if appended_total else 0,
                    "latest_ts": latest_ts,
                    "last_delete_cutoff": last_delete_cutoff,
                    "retained_rows_est": retained_rows_est if args.delete_mode == "range" else None,
                    "retained_rows_target": retain_rows_target if args.delete_mode == "range" else None,
                    "deleted_rows_est": deleted_rows_est if args.delete_mode == "range" else None,
                    "ranges_queue_len": len(ranges) if args.delete_mode == "range" else None,
                    "late_records": late_records if args.delete_mode == "ttl" else None,
                    "retired_queue_len": getattr(log, "retired_queue_len", None),
                    "alloc_failures": getattr(log, "alloc_failures", None),
                    "rss_mb": process_rss_mb(),
                    "append_latency": append_latency.snapshot(),
                    "delete_latency": delete_latency.snapshot(),
                    "flush_latency": flush_latency.snapshot(),
                    "compact_latency": compact_latency.snapshot(),
                })
                last_appended_total = appended_total
                last_deleted_requests = deleted_requests
                last_busy_errors = busy_errors
                last_report = now

    total_time = time.perf_counter() - start_wall
    summary = {
        "elapsed_s": total_time,
        "appended_total": appended_total,
        "deleted_requests": deleted_requests,
        "deleted_rows_est": deleted_rows_est if args.delete_mode == "range" else None,
        "ranges_queue_len": len(ranges) if args.delete_mode == "range" else None,
        "late_records": late_records if args.delete_mode == "ttl" else None,
        "busy_errors": busy_errors,
        "flush_calls": flush_calls,
        "compact_calls": compact_calls,
        "maintenance_effective": maintenance_effective,
        "compact_requests_only": compact_requests_only,
        "adjacent_ooo": adjacent_ooo,
        "global_ooo": global_ooo,
        "adjacent_ooo_ratio": adjacent_ooo / appended_total if appended_total else 0,
        "global_ooo_ratio": global_ooo / appended_total if appended_total else 0,
        "append_latency": append_latency.snapshot(),
        "delete_latency": delete_latency.snapshot(),
        "flush_latency": flush_latency.snapshot(),
        "compact_latency": compact_latency.snapshot(),
        "rss_mb": process_rss_mb(),
    }
    with open(args.summary_out, "w", newline="") as f:
        json.dump(summary, f, indent=2, sort_keys=True)

    write_jsonl(args.metrics_out, {
        "event": "summary",
        "timestamp": time.time(),
        "summary": summary,
    })

    print(f"Done. Summary written to {args.summary_out}")
    print(f"Metrics written to {args.metrics_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
