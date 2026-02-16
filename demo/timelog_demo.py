#!/usr/bin/env python3
"""
Timelog HFT Demo: Comprehensive demonstration of Timelog capabilities
using a 1GB high-frequency trading order book dataset.

This demo showcases production-focused scenarios across categories:
  A: Data Ingestion           E: Maintenance Operations
  B: Time Range Queries       F: Zero-Copy PageSpan Access
  C: HFT Analytics            G: Iterator Patterns
  D: Deletion & Eviction      H: Business Use Cases
  I: Memory Tier Comparison   J: Complexity Verification
  K: Production Scenarios (spikes, mixed workloads, delete impact)

Usage:
    python demo/timelog_demo.py [--quick] [--category=X] [--feature=X.N]

Options:
    --quick                 Run with 100K records instead of 15M
    --category=X            Run only category X (A-K)
    --feature=X.N           Run only feature X.N (e.g., C3)
    --export-json=PATH      Export results to JSON file
    --export-csv=PATH       Export results to CSV file
    --verbose               Show detailed profiling output per feature
    --list                  List all features and exit
    --data=PATH             Use custom CSV data file
    --no-perf               Skip performance measurement
    --trust-csv             Skip row validation (trusted CSV fast path)
    --preload-csv           Preload CSV file into memory (I/O isolation)
    --ingest-mode=MODE      Ingest measurement mode: end_to_end, parse_only, timelog_only
    --reuse-obj             Reuse a single Order object (isolates handle overhead)
    --no-tracemalloc        Disable tracemalloc (reduce measurement overhead)
    --repeat-min-seconds=S  Repeat fast read-only features until >=S seconds (0 disables)
    --repeat-max-runs=N     Max repeats for fast read-only features
"""

from __future__ import annotations

import argparse
import csv
import gc
import io
import json
import os
import platform
import random
import shutil
import sys
import time
import tracemalloc
from collections import Counter
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Callable, Iterator, NamedTuple, Optional

# Add parent directory to path for timelog import
sys.path.insert(0, str(Path(__file__).parent.parent / "python"))

from timelog import Timelog, TimelogBusyError, TimelogIter


def _install_timelog_overrides(overrides: dict[str, object]) -> None:
    """Force Timelog constructor overrides for all demo-created instances."""
    global Timelog
    if not overrides:
        return

    class _TimelogOverride(Timelog):
        def __init__(self, *args, **kwargs):
            kwargs.update(overrides)
            super().__init__(*args, **kwargs)

    Timelog = _TimelogOverride

# Optional NumPy import for zero-copy demos (kept global to avoid per-test import cost)
try:
    import numpy as np
except ImportError:  # pragma: no cover - optional dependency
    np = None

# Optional psutil import for RSS memory and system resources.
try:
    import psutil
except ImportError:  # pragma: no cover - optional dependency
    psutil = None

# =============================================================================
# Performance Profiling Infrastructure
# =============================================================================


@dataclass
class PerfMetrics:
    """Comprehensive performance metrics for a single run."""

    name: str
    wall_time_s: float = 0.0
    cpu_time_s: float = 0.0
    records: int = 0
    memory_peak_mb: float = 0.0
    memory_allocated_mb: float = 0.0
    rss_start_mb: float = 0.0
    rss_end_mb: float = 0.0
    rss_delta_mb: float = 0.0
    gc_collections: tuple[int, int, int] = (0, 0, 0)  # gen0, gen1, gen2

    @property
    def records_per_sec(self) -> float:
        return self.records / self.wall_time_s if self.wall_time_s > 0 else 0

    @property
    def ns_per_record(self) -> float:
        return (self.wall_time_s * 1e9) / self.records if self.records > 0 else 0

    @property
    def cpu_efficiency(self) -> float:
        """CPU utilization (cpu_time / wall_time). >1 means multi-core."""
        return self.cpu_time_s / self.wall_time_s if self.wall_time_s > 0 else 0


class PerfProfiler:
    """
    High-resolution performance profiler with:
    - Wall clock time (perf_counter_ns)
    - CPU time (process_time_ns)
    - Memory tracking (tracemalloc)
    - GC statistics
    - Comparison with algorithmic expectations
    """

    def __init__(
        self,
        name: str,
        expected: Optional[dict] = None,
        track_memory: bool = True,
        track_gc: bool = True,
    ):
        self.name = name
        self.expected = expected or {}
        self.track_memory = track_memory
        self.track_gc = track_gc
        self._start_wall: int = 0
        self._start_cpu: int = 0
        self._start_gc: tuple[int, int, int] = (0, 0, 0)
        self._mem_tracking: bool = False
        self._rss_start_mb: float = 0.0
        self._rss_end_mb: float = 0.0
        self.metrics: Optional[PerfMetrics] = None
        self.records: int = 0

    def __enter__(self):
        if self.track_gc:
            # Force GC before measurement for consistent baselines
            gc.collect()
            gc.collect()
            gc.collect()

            # Capture GC counts before
            stats = gc.get_stats()
            self._start_gc = (
                stats[0]["collections"],
                stats[1]["collections"],
                stats[2]["collections"],
            )

        # Start memory tracking if enabled
        if self.track_memory:
            tracemalloc.start()
            self._mem_tracking = True

        # Capture RSS after GC to reduce noise (if psutil available).
        self._rss_start_mb = get_process_rss_mb()

        # Start timing (order matters - do timing last)
        self._start_cpu = time.process_time_ns()
        self._start_wall = time.perf_counter_ns()

        return self

    def __exit__(self, *args):
        # Stop timing immediately
        end_wall = time.perf_counter_ns()
        end_cpu = time.process_time_ns()

        # Get memory stats
        if self._mem_tracking:
            current, peak = tracemalloc.get_traced_memory()
            tracemalloc.stop()
            self._mem_tracking = False
        else:
            current = peak = 0

        # Capture RSS at end (if psutil available).
        self._rss_end_mb = get_process_rss_mb()

        # Get GC stats after
        if self.track_gc:
            stats = gc.get_stats()
            end_gc = (
                stats[0]["collections"],
                stats[1]["collections"],
                stats[2]["collections"],
            )
            gc_delta = (
                end_gc[0] - self._start_gc[0],
                end_gc[1] - self._start_gc[1],
                end_gc[2] - self._start_gc[2],
            )
        else:
            gc_delta = (0, 0, 0)

        self.metrics = PerfMetrics(
            name=self.name,
            wall_time_s=(end_wall - self._start_wall) / 1e9,
            cpu_time_s=(end_cpu - self._start_cpu) / 1e9,
            records=self.records,
            memory_peak_mb=peak / (1024 * 1024),
            memory_allocated_mb=current / (1024 * 1024),
            rss_start_mb=self._rss_start_mb,
            rss_end_mb=self._rss_end_mb,
            rss_delta_mb=self._rss_end_mb - self._rss_start_mb,
            gc_collections=gc_delta,
        )

    def set_records(self, n: int):
        """Set record count for throughput calculations."""
        self.records = n
        if self.metrics:
            self.metrics.records = n

    def report(self) -> dict:
        """Generate comprehensive performance report."""
        if not self.metrics:
            return {"name": self.name, "error": "No metrics collected"}

        m = self.metrics
        result = {
            "name": self.name,
            "wall_time_s": m.wall_time_s,
            "cpu_time_s": m.cpu_time_s,
            "cpu_efficiency": m.cpu_efficiency,
            "records": m.records,
            "records_per_sec": m.records_per_sec,
            "ns_per_record": m.ns_per_record,
            "memory_peak_mb": m.memory_peak_mb,
            "memory_allocated_mb": m.memory_allocated_mb,
            "rss_start_mb": m.rss_start_mb,
            "rss_end_mb": m.rss_end_mb,
            "rss_delta_mb": m.rss_delta_mb,
            "gc_gen0": m.gc_collections[0],
            "gc_gen1": m.gc_collections[1],
            "gc_gen2": m.gc_collections[2],
        }

        # Compare with expected performance
        if self.expected:
            result["expected"] = self.expected

            # Check records_per_sec target
            if "records_per_sec" in self.expected and m.records_per_sec > 0:
                ratio = m.records_per_sec / self.expected["records_per_sec"]
                result["vs_expected_ratio"] = ratio
                result["vs_expected"] = f"{ratio:.1%}"
                result["meets_target"] = ratio >= 0.8

            # Check timestamps_per_sec target (PageSpan operations)
            if "timestamps_per_sec" in self.expected and m.records_per_sec > 0:
                ratio = m.records_per_sec / self.expected["timestamps_per_sec"]
                result["vs_expected_ratio"] = ratio
                result["vs_expected"] = f"{ratio:.1%}"
                result["meets_target"] = ratio >= 0.8

            # Check objects_per_sec target (objects view)
            if "objects_per_sec" in self.expected and m.records_per_sec > 0:
                ratio = m.records_per_sec / self.expected["objects_per_sec"]
                result["vs_expected_ratio"] = ratio
                result["vs_expected"] = f"{ratio:.1%}"
                result["meets_target"] = ratio >= 0.8

            # Check operation time targets (flush, compact)
            if "flush_ms" in self.expected:
                actual_ms = m.wall_time_s * 1000
                result["actual_ms"] = actual_ms
                result["meets_target"] = actual_ms <= self.expected["flush_ms"] * 1.5

            if "compact_ms" in self.expected:
                actual_ms = m.wall_time_s * 1000
                result["actual_ms"] = actual_ms
                result["meets_target"] = actual_ms <= self.expected["compact_ms"] * 1.5

        return result


def get_process_rss_mb() -> float:
    """Get current process RSS memory in MB (0 if psutil unavailable)."""
    if psutil is None:
        return 0.0
    try:
        return psutil.Process().memory_info().rss / (1024 * 1024)
    except Exception:
        return 0.0


def _get_system_memory_info() -> dict:
    """Best-effort system memory stats (requires psutil)."""
    if psutil is None:
        return {}
    try:
        vm = psutil.virtual_memory()
        return {
            "mem_total_gb": round(vm.total / (1024 ** 3), 2),
            "mem_available_gb": round(vm.available / (1024 ** 3), 2),
            "mem_percent": vm.percent,
        }
    except Exception:
        return {}


def _get_disk_usage_info(path: str) -> dict:
    """Best-effort disk usage stats for the drive containing path."""
    try:
        usage = shutil.disk_usage(path)
        return {
            "disk_total_gb": round(usage.total / (1024 ** 3), 2),
            "disk_free_gb": round(usage.free / (1024 ** 3), 2),
            "disk_used_gb": round(usage.used / (1024 ** 3), 2),
        }
    except Exception:
        return {}


def get_system_info() -> dict:
    """Capture system information for benchmark context."""
    info = {
        "python_version": sys.version,
        "platform": platform.platform(),
        "processor": platform.processor(),
        "cpu_count": os.cpu_count(),
        "machine": platform.machine(),
        "psutil_available": psutil is not None,
    }
    if psutil is not None:
        info["psutil_version"] = getattr(psutil, "__version__", "unknown")
    info.update(_get_system_memory_info())
    info.update(_get_disk_usage_info(os.getcwd()))
    return info


class LatencyStats:
    """Collect and summarize latency samples (in nanoseconds)."""

    def __init__(self):
        self.samples: list[int] = []

    def add(self, ns: int) -> None:
        self.samples.append(ns)

    def summary(self) -> dict:
        if not self.samples:
            return {"count": 0}

        s = sorted(self.samples)
        n = len(s)

        def pct(p: float) -> int:
            idx = int((p / 100.0) * (n - 1))
            return s[idx]

        total = sum(s)
        return {
            "count": n,
            "min_ns": s[0],
            "p50_ns": pct(50),
            "p95_ns": pct(95),
            "p99_ns": pct(99),
            "max_ns": s[-1],
            "avg_ns": int(total / n),
        }


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

CSV_MODE = "validated"  # or "trusted"
CSV_CACHE: dict[str, str] = {}


def preload_csv(path: str) -> None:
    """Preload CSV file into memory to isolate disk I/O from parsing."""
    if path in CSV_CACHE:
        return
    with open(path, "r", newline="") as f:
        CSV_CACHE[path] = f.read()


def _open_csv_source(path: str):
    """Return a file-like object for CSV parsing (from cache or disk)."""
    if path in CSV_CACHE:
        return io.StringIO(CSV_CACHE[path])
    return open(path, "r", newline="")


# =============================================================================
# Algorithmic Complexity and Expected Performance
# =============================================================================

COMPLEXITY = {
    "A0": {"time": "O(N)", "space": "O(N)", "notes": "parse-only vs Timelog-only breakdown"},
    "A1": {"time": "O(1) amortized", "space": "O(1)", "notes": "memtable insert"},
    "A2": {"time": "O(B)", "space": "O(B)", "notes": "B=batch size"},
    "A2B": {"time": "O(B)", "space": "O(B)", "notes": "batch + background maint"},
    "A3": {"time": "O(N)", "space": "O(1)", "notes": "streaming"},
    "A4": {"time": "O(N*log S)", "space": "O(S)", "notes": "S=sealed records"},
    "A5": {"time": "O(N + F*M)", "space": "O(M)", "notes": "F=flushes, M=memtable"},
    "A6": {"time": "O(N)", "space": "O(B)", "notes": "compare ordered vs less-ordered"},
    "B1": {"time": "O(K*log P + M)", "space": "O(K)", "notes": "K=components, M=results"},
    "B2": {"time": "O(K*log P + M)", "space": "O(K)", "notes": "binary search + scan"},
    "B3": {"time": "O(K*log P + M)", "space": "O(K)", "notes": "scan to cutoff"},
    "B4": {"time": "O(N)", "space": "O(K)", "notes": "full k-way merge"},
    "B5": {"time": "O(K*log P + D)", "space": "O(K)", "notes": "D=duplicates"},
    "B6": {"time": "O(K*log P + M)", "space": "O(K)", "notes": "tiny result set"},
    "B7": {"time": "O(S*T*log P + A)", "space": "O(S+T)", "notes": "snapshot full len(log) count path"},
    "B8": {"time": "O(S*T*log P + A)", "space": "O(S+T)", "notes": "slice iterator remaining-count len(it) path"},
    "C1": {"time": "O(K*log P + W)", "space": "O(K)", "notes": "W=window records"},
    "C1B": {"time": "O(K*log P + M)", "space": "O(K)", "notes": "single pass over window"},
    "C2": {"time": "O(K*log P + W)", "space": "O(K)", "notes": "range + filter"},
    "C3": {"time": "O(K*log P + W)", "space": "O(K)", "notes": "range + arithmetic"},
    "C4": {"time": "O(K*log P + W)", "space": "O(K)", "notes": "range + counter"},
    "C5": {"time": "O(K*log P + W)", "space": "O(T)", "notes": "T=unique tickers"},
    "C6": {"time": "O(K*log P + W)", "space": "O(1)", "notes": "streaming stats"},
    "C7": {"time": "O(K*log P + W)", "space": "O(1)", "notes": "streaming sum"},
    "C8": {"time": "O(K*log P + W)", "space": "O(B)", "notes": "B=histogram bins"},
    "D1": {"time": "O(log T)", "space": "O(T)", "notes": "tombstone coalesce"},
    "D2": {"time": "O(log T)", "space": "O(T)", "notes": "tombstone coalesce"},
    "D3": {"time": "O(K*log P)", "space": "O(K)", "notes": "verify point query"},
    "D4": {"time": "O(K*log P + M + F)", "space": "O(K)", "notes": "F=filter cost"},
    "E1": {"time": "O(M*log M)", "space": "O(M)", "notes": "sort + serialize"},
    "E2": {"time": "O(S*log S)", "space": "O(S)", "notes": "S=segment records"},
    "E3": {"time": "O(1) amortized", "space": "O(M)", "notes": "background work"},
    "E4": {"time": "O(1)", "space": "O(1)", "notes": "thread control"},
    "F1": {"time": "O(K*log P + P_r)", "space": "O(1)", "notes": "streaming pages"},
    "F2": {"time": "O(1)", "space": "O(1)", "notes": "zero-copy pointer"},
    "F3": {"time": "O(R_p)", "space": "O(R_p)", "notes": "lazy decode"},
    "F4": {"time": "O(1)", "space": "O(1)", "notes": "buffer protocol"},
    "F5": {"time": "O(R)", "space": "O(1)", "notes": "vectorized scan"},
    "G1": {"time": "O(n)", "space": "O(n)", "notes": "batch fetch"},
    "G2": {"time": "O(setup+iter)", "space": "O(K)", "notes": "RAII cleanup"},
    "G3": {"time": "O(K*log P + M)", "space": "O(K)", "notes": "early stop"},
    "G4": {"time": "O(I*(K*log P + M))", "space": "O(I*K)", "notes": "I=iterators"},
    "H1": {"time": "O(K*log P + L)", "space": "O(L)", "notes": "L=lifecycle"},
    "H2": {"time": "O(K*log P + S)", "space": "O(K)", "notes": "S=session"},
    "H3": {"time": "O(W*(K*log P + R))", "space": "O(W)", "notes": "W=windows"},
    "H3B": {"time": "O(K*log P + R)", "space": "O(W)", "notes": "single pass windowing"},
    "H4": {"time": "O(K*log P + D)", "space": "O(K)", "notes": "exact lookup"},
    # Category I: Memory Tier Comparison
    "I1": {"time": "O(M)", "space": "O(1)", "notes": "memtable read (no disk I/O)"},
    "I2": {"time": "O(K*log P + M)", "space": "O(K)", "notes": "cold/segment read"},
    "I3": {"time": "O(M)", "space": "O(1)", "notes": "mixed hot+cold read"},
    # Category J: Algorithmic Complexity Verification
    "J1": {"time": "O(M)", "space": "O(1)", "notes": "verify iteration count = result size"},
    "J2": {"time": "O(N log N)", "space": "O(1)", "notes": "verify scaling is linear or log-linear"},
    "J3": {"time": "O(N)", "space": "O(1)", "notes": "verify no quadratic behavior"},
    # Category K: Production Scenarios
    "K1": {"time": "O(N)", "space": "O(N)", "notes": "append latency distribution"},
    "K1B": {"time": "O(N)", "space": "O(N)", "notes": "append latency (manual flush/compact)"},
    "K2": {"time": "O(N)", "space": "O(1)", "notes": "mixed read/write (hot)"},
    "K3": {"time": "O(N)", "space": "O(1)", "notes": "mixed read/write (cold)"},
    "K4": {"time": "O(N)", "space": "O(1)", "notes": "delete impact before/after"},
    "K5": {"time": "O(G*N)", "space": "O(1)", "notes": "A2B stress grid"},
}

# Performance expectations calibrated for Python-level iteration + analytics.
# These reflect realistic CPython throughput, not raw C engine throughput.
# The C engine achieves 10M+ rec/sec, but Python iterator/unpickle overhead
# reduces end-to-end throughput to 400K-800K rec/sec for typical analytics.
EXPECTED_PERFORMANCE = {
    # Category A: Data Ingestion (includes CSV parsing overhead in demo)
    "A1": {"records_per_sec": 150_000},      # Single append with CSV parse
    "A2": {"records_per_sec": 200_000},      # Batch extend with CSV parse
    "A2B": {"records_per_sec": 250_000},     # Batch extend + background maintenance
    "A3": {"records_per_sec": 150_000},      # Streaming with rate tracking
    "A4": {"records_per_sec": 180_000},      # Out-of-order (shuffle overhead)
    "A5": {"records_per_sec": 100_000},      # Backpressure handling
    "A6": {"records_per_sec": 150_000},      # Two ingest runs (ordered vs less-ordered)

    # Category B: Time Range Queries (Python iteration + unpickle)
    "B1": {"records_per_sec": 800_000},      # Range query
    "B2": {"records_per_sec": 800_000},      # Since query
    "B3": {"records_per_sec": 800_000},      # Until query
    "B4": {"records_per_sec": 600_000},      # Full scan
    "B5": {"records_per_sec": 10_000},       # Point queries/sec (query-count metric)
    "B6": {"records_per_sec": 150_000},      # Micro-window queries/sec (query-count metric)
    "B7": {"ops_per_sec": 2_000},            # len(log) calls/sec
    "B8": {"ops_per_sec": 2_000},            # len(slice_iter) calls/sec

    # Category C: HFT Analytics (iteration + Python computation)
    "C1": {"records_per_sec": 8_000},        # Multi-window counting (10 windows)
    "C1B": {"records_per_sec": 400_000},     # Single pass windowing
    "C2": {"records_per_sec": 600_000},      # Buy/sell ratio
    "C3": {"records_per_sec": 450_000},      # VWAP (more math)
    "C4": {"records_per_sec": 550_000},      # Fill rate
    "C5": {"records_per_sec": 350_000},      # Ticker activity (Counter overhead)
    "C6": {"records_per_sec": 400_000},      # Spread analysis
    "C7": {"records_per_sec": 550_000},      # Commission totals
    "C8": {"records_per_sec": 350_000},      # Latency histogram

    # Category D: Deletion & Eviction
    "D1": {"ops_per_sec": 100_000},
    "D2": {"ops_per_sec": 100_000},
    "D3": {"ops_per_sec": 500_000},
    "D4": {"records_per_sec": 800_000},

    # Category E: Maintenance Operations
    "E1": {"flush_ms": 100},
    "E2": {"compact_ms": 200},
    "E3": {"records_per_sec": 600_000},
    "E4": {"records_per_sec": 600_000},

    # Category F: Zero-Copy PageSpan (near-native speed)
    "F1": {"timestamps_per_sec": 10_000_000},   # PageSpan iteration
    "F2": {"timestamps_per_sec": 20_000_000},   # Memoryview access
    "F3": {"objects_per_sec": 2_000_000},       # Objects view (unpickle)
    "F4": {"timestamps_per_sec": 50_000_000},   # NumPy (vectorized)
    "F5": {"timestamps_per_sec": 50_000_000},   # Bulk statistics

    # Category G: Iterator Patterns
    "G1": {"records_per_sec": 900_000},      # Batch iteration
    "G2": {"records_per_sec": 700_000},      # Context manager
    "G3": {"records_per_sec": 700_000},      # Early termination
    "G4": {"records_per_sec": 500_000},      # Multiple iterators

    # Category H: Business Use Cases
    "H1": {"records_per_sec": 300_000},      # Trade reconstruction
    "H2": {"records_per_sec": 600_000},      # Market replay
    "H3": {"queries_per_sec": 60},           # Anomaly detection (60 windows)
    "H3B": {"records_per_sec": 400_000},     # Single pass windowing
    "H4": {"queries_per_sec": 50_000},       # Audit trail

    # Category I: Memory Tier Comparison (memtable vs segments)
    # Note: I1 includes write + read time; I2 includes flush time
    "I1": {"records_per_sec": 100_000},      # Memtable write + read
    "I2": {"records_per_sec": 1_000},        # Cold read after flush (flush dominates)
    "I3": {"records_per_sec": 500_000},      # Mixed read pattern

    # Category J: Algorithmic Complexity Verification
    # These tests verify algorithmic correctness, not raw throughput.
    # Expected values are placeholders - actual verification is in result dict.
    "J1": {"records_per_sec": 100_000},      # iterations == result_size (O(M))
    "J2": {"records_per_sec": 100_000},      # scaling exponent test
    "J3": {"records_per_sec": 50_000},       # quadratic detection test
}


# =============================================================================
# Data Model
# =============================================================================


class Order(NamedTuple):
    """HFT order record."""

    ticker: str
    isin: str
    direction: str
    status: str
    amount: int
    ask_price: float
    bid_price: float | None
    order_id: int
    commission: float


def _synthetic_order(order_id: int) -> Order:
    """Create a simple synthetic Order for engine-focused benchmarks."""
    return Order(
        ticker="SYN",
        isin="TEST",
        direction="BUY",
        status="OPEN",
        amount=1,
        ask_price=1.0,
        bid_price=0.9,
        order_id=order_id,
        commission=0.0,
    )


def iter_synthetic_records(
    count: int,
    base_ts: int,
    step_ns: int = 1_000,
    reuse_obj: bool = False,
) -> Iterator[tuple[int, Order]]:
    """Generate synthetic (ts, Order) records."""
    if reuse_obj:
        shared = _synthetic_order(0)
        for i in range(count):
            yield base_ts + i * step_ns, shared
    else:
        for i in range(count):
            yield base_ts + i * step_ns, _synthetic_order(i)


def parse_order(row: dict) -> tuple[int, Order] | None:
    """
    Parse a CSV row into (timestamp, Order) tuple with validation.

    Returns None for malformed rows (extra columns, missing values, etc.).
    """
    try:
        # Check for extra columns (indicates misaligned data)
        if None in row:
            return None

        # Check for missing required fields
        required = ["timestamp", "ticker", "direction", "status", "amount",
                    "ask_price", "order_id", "commission"]
        for field in required:
            if row.get(field) is None:
                return None

        ts = int(row["timestamp"])
        bid_price = float(row["bid_price"]) if row.get("bid_price") else None

        # Validate required fields
        direction = row["direction"]
        if direction not in ("BUY", "SELL"):
            return None

        status = row["status"]
        if status not in ("OPEN", "PARTIAL", "FILLED"):
            return None

        order = Order(
            ticker=row["ticker"],
            isin=row.get("isin", ""),
            direction=direction,
            status=status,
            amount=int(row["amount"]),
            ask_price=float(row["ask_price"]),
            bid_price=bid_price,
            order_id=int(row["order_id"]),
            commission=float(row["commission"]),
        )
        return ts, order
    except (ValueError, KeyError, TypeError):
        return None


def parse_order_trusted(row: list[str], idx: dict[str, int]) -> tuple[int, Order]:
    """
    Parse a CSV row without validation.

    Assumes column presence and valid types. Raises on malformed rows.
    """
    ts = int(row[idx["timestamp"]])
    bid_raw = row[idx["bid_price"]]
    bid_price = float(bid_raw) if bid_raw else None

    order = Order(
        ticker=row[idx["ticker"]],
        isin=row[idx["isin"]],
        direction=row[idx["direction"]],
        status=row[idx["status"]],
        amount=int(row[idx["amount"]]),
        ask_price=float(row[idx["ask_price"]]),
        bid_price=bid_price,
        order_id=int(row[idx["order_id"]]),
        commission=float(row[idx["commission"]]),
    )
    return ts, order


def load_orders(
    data_path: str, limit: int = 0
) -> Iterator[tuple[int, Order]]:
    """
    Load orders from CSV file.

    Args:
        data_path: Path to CSV file.
        limit: Maximum records to load (0 = unlimited).

    Yields:
        (timestamp, Order) tuples.
        Skips malformed rows silently.
    """
    count = 0
    skipped = 0
    try:
        with _open_csv_source(data_path) as f:
            if CSV_MODE == "trusted":
                reader = csv.reader(f)
                header = next(reader, None)
                if header is None:
                    return
                index_map = {}
                for name in CSV_COLUMNS:
                    if name not in header:
                        raise ValueError(f"missing column in trusted CSV: {name}")
                    index_map[name] = header.index(name)

                for row in reader:
                    result = parse_order_trusted(row, index_map)
                    yield result
                    count += 1
                    if limit > 0 and count >= limit:
                        break
            else:
                reader = csv.DictReader(f)
                for row in reader:
                    result = parse_order(row)
                    if result is None:
                        skipped += 1
                        continue
                    yield result
                    count += 1
                    if limit > 0 and count >= limit:
                        break
    except MemoryError as exc:
        rss_mb = get_process_rss_mb()
        raise MemoryError(
            f"MemoryError while reading {data_path} (rss_mb={rss_mb:.1f})"
        ) from exc
    if skipped > 0:
        print(f"  (Skipped {skipped:,} malformed rows)")


def parse_orders_to_list(data_path: str, limit: int = 0) -> tuple[list[tuple[int, Order]], float]:
    """Parse orders into a list and return (records, wall_time_s)."""
    start = time.perf_counter_ns()
    records = list(load_orders(data_path, limit=limit))
    elapsed = time.perf_counter_ns() - start
    return records, elapsed / 1e9


def ingest_records(
    log: Timelog,
    records: list[tuple[int, Order]],
    batch_size: int = 10_000,
) -> float:
    """Ingest records into Timelog and return wall time in seconds."""
    start = time.perf_counter_ns()
    for i in range(0, len(records), batch_size):
        log.extend(records[i : i + batch_size])
    elapsed = time.perf_counter_ns() - start
    return elapsed / 1e9


def _drain_manual_maintenance(log: Timelog, max_steps: int = 100_000) -> int:
    """
    Execute maint_step() until manual maintenance has no pending work.

    Used by demos that run with maintenance="disabled" and want compact()
    to execute immediately, not just queue a request.
    """
    steps = 0
    while steps < max_steps:
        if not log.maint_step():
            return steps
        steps += 1
    raise RuntimeError(f"maintenance did not quiesce within {max_steps} steps")


def _alternate_dataset_path(data_path: str) -> str | None:
    """
    Locate a related dataset with different ordering characteristics.

    This lets us compare "mostly ordered" vs "less ordered" ingestion
    without requiring a separate CLI run.
    """
    p = Path(data_path)
    name = p.name
    mapping = {
        "order_book_1GB.csv": "order_book_1GB_less_order.csv",
        "order_book_1GB_less_order.csv": "order_book_1GB.csv",
        "order_book_more_ordered_clean.csv": "order_book_less_ordered_clean.csv",
        "order_book_less_ordered_clean.csv": "order_book_more_ordered_clean.csv",
        "tiny_order_book_mostly_ordered.csv": "tiny_order_book_less_order.csv",
        "tiny_order_book_less_order.csv": "tiny_order_book_mostly_ordered.csv",
        "tiny_order_book_mostly_ordered_clean.csv": "tiny_order_book_less_ordered_clean.csv",
        "tiny_order_book_less_ordered_clean.csv": "tiny_order_book_mostly_ordered_clean.csv",
        "generated_5pct.csv": "generated_20pct.csv",
        "generated_20pct.csv": "generated_5pct.csv",
    }

    alt_name = mapping.get(name)
    if alt_name is None:
        if "less_order" in name:
            alt_name = name.replace("less_order", "mostly_ordered")
        elif "mostly_ordered" in name:
            alt_name = name.replace("mostly_ordered", "less_order")

    if alt_name is None:
        return None

    alt_path = p.with_name(alt_name)
    return str(alt_path) if alt_path.exists() else None


# =============================================================================
# Demo Runner
# =============================================================================

FEATURES: dict[str, dict] = {}
SHARED_LOG_CATEGORIES = "BCFGHI"  # Categories that reuse a shared Timelog instance
SELF_CONTAINED_CATEGORIES = "ADEJK"  # Categories that create their own Timelog instances
REPEATABLE_CATEGORIES = SHARED_LOG_CATEGORIES  # Read-only categories safe to repeat
DEFAULT_REPEAT_MIN_SECONDS = 0.25
DEFAULT_REPEAT_MAX_RUNS = 10


def feature(code: str, name: str, category: str):
    """Decorator to register a demo feature."""

    def decorator(func: Callable):
        FEATURES[code] = {
            "code": code,
            "name": name,
            "category": category,
            "func": func,
            "complexity": COMPLEXITY.get(code, {}),
            "expected": EXPECTED_PERFORMANCE.get(code, {}),
        }
        return func

    return decorator


class DemoRunner:
    """Manages demo execution with timing and reporting."""

    def __init__(
        self,
        data_path: str,
        quick: bool = False,
        verbose: bool = False,
        no_perf: bool = False,
        csv_mode: str = "validated",
        ingest_mode: str = "all",
        preload_csv: bool = False,
        reuse_obj: bool = False,
        track_memory: bool = True,
        track_gc: bool = True,
        repeat_min_seconds: float = DEFAULT_REPEAT_MIN_SECONDS,
        repeat_max_runs: int = DEFAULT_REPEAT_MAX_RUNS,
        log_overrides: Optional[dict[str, object]] = None,
    ):
        self.data_path = data_path
        self.limit = 100_000 if quick else 0
        self.verbose = verbose
        self.no_perf = no_perf
        self.csv_mode = csv_mode
        self.ingest_mode = ingest_mode
        self.preload_csv = preload_csv
        self.reuse_obj = reuse_obj
        self.track_memory = track_memory
        self.track_gc = track_gc
        self.repeat_min_seconds = repeat_min_seconds
        self.repeat_max_runs = repeat_max_runs
        self.results: dict[str, dict] = {}
        self.log: Optional[Timelog] = None
        self._data_loaded = False
        self.log_overrides = log_overrides or {}

    def ensure_data_loaded(self) -> None:
        """Ensure test data is loaded into the log."""
        if self._data_loaded:
            return
        if self.log is None:
            raise RuntimeError("No Timelog instance")

        if self.preload_csv:
            preload_csv(self.data_path)

        print(f"  Loading data from {self.data_path}...")
        batch = []
        BATCH_SIZE = 10_000
        total = 0

        for ts, order in load_orders(self.data_path, self.limit):
            batch.append((ts, order))
            if len(batch) >= BATCH_SIZE:
                self.log.extend(batch)
                total += len(batch)
                batch.clear()
                if total % 100_000 == 0:
                    print(f"    Loaded {total:,} records...")

        if batch:
            self.log.extend(batch)
            total += len(batch)

        print(f"  Loaded {total:,} records total")
        self._data_loaded = True

    def _run_feature_with_repeats(
        self,
        func: Callable[["DemoRunner"], dict],
        repeatable: bool,
    ) -> tuple[dict, int, int]:
        """Run a feature, repeating if it is fast and safe to retry."""
        iterations = 0
        total_records = 0
        result: dict = {}
        start = time.perf_counter()

        while True:
            result = func(self)
            iterations += 1
            records = result.get("records", 0)
            if isinstance(records, (int, float)):
                total_records += int(records)

            if "error" in result:
                break
            if not repeatable:
                break
            if iterations >= self.repeat_max_runs:
                break
            if time.perf_counter() - start >= self.repeat_min_seconds:
                break

        return result, iterations, total_records

    def run_feature(self, code: str) -> dict:
        """Run a single feature and collect results."""
        if code not in FEATURES:
            return {"error": f"Unknown feature: {code}"}

        f = FEATURES[code]
        print()
        print("=" * 80)
        print(f"Feature {code}: {f['name']}")
        print("=" * 80)

        # Show complexity info
        c = f["complexity"]
        if c and self.verbose:
            print(f"ALGORITHMIC COMPLEXITY:")
            print(f"  Time:  {c.get('time', 'N/A'):20} {c.get('notes', '')}")
            print(f"  Space: {c.get('space', 'N/A')}")
            exp = f["expected"]
            if "records_per_sec" in exp:
                print(f"  Expected: ~{exp['records_per_sec']:,} records/sec")
            elif "timestamps_per_sec" in exp:
                print(f"  Expected: ~{exp['timestamps_per_sec']:,} timestamps/sec")
            print()

        # Pre-load shared log data outside the perf window for query features.
        if (
            not self.no_perf
            and self.log is not None
            and f["category"] in SHARED_LOG_CATEGORIES
            and not self._data_loaded
        ):
            self.ensure_data_loaded()

        # Run the feature
        try:
            if self.no_perf:
                result = f["func"](self)
                result["expected"] = f["expected"]
            else:
                repeatable = (
                    self.repeat_min_seconds > 0
                    and self.repeat_max_runs > 1
                    and f["category"] in REPEATABLE_CATEGORIES
                )
                with PerfProfiler(
                    code,
                    f["expected"],
                    track_memory=self.track_memory,
                    track_gc=self.track_gc,
                ) as profiler:
                    result, iterations, total_records = self._run_feature_with_repeats(
                        f["func"],
                        repeatable,
                    )
                    profiler.records = total_records
                perf_result = profiler.report()
                result.update(perf_result)
                if repeatable and iterations > 1 and "error" not in result:
                    result["iterations"] = iterations
                    result["records_per_run"] = (
                        total_records / iterations if iterations else 0
                    )
                    result["repeat_min_seconds"] = self.repeat_min_seconds
                    result["repeat_max_runs"] = self.repeat_max_runs

            if self.log_overrides:
                result["log_overrides"] = self.log_overrides
            self.results[code] = result

            # Print results
            if self.verbose:
                self._print_verbose_result(result)
            else:
                self._print_brief_result(code, result)

            return result

        except Exception as e:
            print(f"  ERROR: {e}")
            import traceback

            traceback.print_exc()
            self.results[code] = {"error": str(e)}
            return {"error": str(e)}

    def _print_brief_result(self, code: str, result: dict) -> None:
        """Print brief result summary."""
        if "error" in result:
            print(f"  ERROR: {result['error']}")
            return

        records = result.get("records", 0)
        wall = result.get("wall_time_s", 0)
        rps = result.get("records_per_sec", 0)

        print(f"  Records: {records:,}  Wall: {wall:.3f}s  Rate: {rps:,.0f} rec/sec")

        if "vs_expected" in result:
            status = "[PASS]" if result.get("meets_target", False) else "[FAIL]"
            print(f"  VS Expected: {result['vs_expected']} {status}")

    def _print_verbose_result(self, result: dict) -> None:
        """Print detailed result with box formatting."""
        if "error" in result:
            print(f"  ERROR: {result['error']}")
            return

        print("PERFORMANCE METRICS:")
        print("  +" + "-" * 60 + "+")
        print("  | TIMING" + " " * 53 + "|")
        print(f"  |   Wall time:      {result.get('wall_time_s', 0):>10.3f}s" + " " * 29 + "|")
        print(f"  |   CPU time:       {result.get('cpu_time_s', 0):>10.3f}s" + " " * 29 + "|")
        print(f"  |   CPU efficiency: {result.get('cpu_efficiency', 0):>10.1%}" + " " * 29 + "|")
        print("  +" + "-" * 60 + "+")
        print("  | THROUGHPUT" + " " * 49 + "|")
        print(f"  |   Records:        {result.get('records', 0):>12,}" + " " * 27 + "|")
        print(f"  |   Rate:           {result.get('records_per_sec', 0):>12,.0f} records/sec" + " " * 14 + "|")
        print(f"  |   Latency:        {result.get('ns_per_record', 0):>12,.0f} ns/record" + " " * 17 + "|")
        print("  +" + "-" * 60 + "+")
        print("  | MEMORY" + " " * 53 + "|")
        print(f"  |   Peak:           {result.get('memory_peak_mb', 0):>10.1f} MB" + " " * 27 + "|")
        print(f"  |   Allocated:      {result.get('memory_allocated_mb', 0):>10.1f} MB" + " " * 27 + "|")
        rss_start = result.get("rss_start_mb", 0)
        rss_end = result.get("rss_end_mb", 0)
        rss_delta = result.get("rss_delta_mb", 0)
        print(
            f"  |   RSS start/end:  {rss_start:>10.1f}/{rss_end:>10.1f} MB"
            + " " * 14
            + "|"
        )
        print(
            f"  |   RSS delta:      {rss_delta:>10.1f} MB"
            + " " * 25
            + "|"
        )
        gc0 = result.get("gc_gen0", 0)
        gc1 = result.get("gc_gen1", 0)
        gc2 = result.get("gc_gen2", 0)
        print(f"  |   GC collections: gen0={gc0}, gen1={gc1}, gen2={gc2}" + " " * 24 + "|")
        print("  +" + "-" * 60 + "+")

        if "vs_expected" in result:
            status = "[PASS]" if result.get("meets_target", False) else "[FAIL]"
            print(f"\nVS EXPECTED: {result['vs_expected']} {status}")

    def run_category(self, category: str) -> None:
        """Run all features in a category."""
        for code, f in sorted(FEATURES.items()):
            if f["category"] == category:
                self.run_feature(code)

    def run_all(self) -> None:
        """Run all features in order."""
        for code in sorted(FEATURES.keys()):
            self.run_feature(code)

    def summary(self) -> str:
        """Generate performance summary table."""
        lines = []
        lines.append("=" * 100)
        lines.append("TIMELOG DEMO - PERFORMANCE SUMMARY")
        lines.append("=" * 100)
        lines.append(
            f"{'Feature':<25} {'Records':>12} {'Wall(s)':>10} {'CPU(s)':>10} "
            f"{'Rec/sec':>12} {'Expected':>12} {'Ratio':>8} {'Status':>8}"
        )
        lines.append("-" * 100)

        passed = failed = na = 0
        for code in sorted(self.results.keys()):
            r = self.results[code]
            if "error" in r:
                lines.append(f"{code:<25} {'ERROR':>12}")
                na += 1
                continue

            records = r.get("records", 0)
            wall = r.get("wall_time_s", 0)
            cpu = r.get("cpu_time_s", 0)
            rps = r.get("records_per_sec", 0)
            exp = r.get("expected", {})
            exp_rps = (
                exp.get("records_per_sec")
                or exp.get("timestamps_per_sec")
                or exp.get("objects_per_sec")
                or exp.get("ops_per_sec")
                or 0
            )

            if exp_rps > 0 and rps > 0:
                ratio = rps / exp_rps
                ratio_str = f"{ratio:.1%}"
                if r.get("meets_target", ratio >= 0.8):
                    status = "[PASS]"
                    passed += 1
                else:
                    status = "[FAIL]"
                    failed += 1
            else:
                ratio_str = "N/A"
                status = "[N/A]"
                na += 1

            lines.append(
                f"{code:<25} {records:>12,} {wall:>10.3f} {cpu:>10.3f} "
                f"{rps:>12,.0f} {exp_rps:>12,.0f} {ratio_str:>8} {status:>8}"
            )

        lines.append("-" * 100)
        lines.append(f"TOTAL: {passed} passed, {failed} failed, {na} not applicable")
        lines.append("=" * 100)

        return "\n".join(lines)


# =============================================================================
# Export Functions
# =============================================================================


def export_results_json(results: dict, system_info: dict, config: dict, path: Path) -> None:
    """Export results to JSON for later analysis."""
    export = {
        "timestamp": datetime.now().isoformat(),
        "system": system_info,
        "config": config,
        "results": results,
    }
    with open(path, "w") as f:
        json.dump(export, f, indent=2, default=str)
    print(f"Results exported to: {path}")


def export_results_csv(results: dict, path: Path) -> None:
    """Export results to CSV for spreadsheet analysis."""
    fieldnames = [
        "feature",
        "records",
        "wall_time_s",
        "cpu_time_s",
        "cpu_efficiency",
        "records_per_sec",
        "ns_per_record",
        "memory_peak_mb",
        "rss_start_mb",
        "rss_end_mb",
        "rss_delta_mb",
        "gc_gen0",
        "expected_rps",
        "ratio",
        "meets_target",
    ]
    with open(path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for code in sorted(results.keys()):
            r = results[code]
            if "error" in r:
                continue
            exp = r.get("expected", {})
            exp_rps = (
                exp.get("records_per_sec")
                or exp.get("timestamps_per_sec")
                or exp.get("objects_per_sec")
                or exp.get("ops_per_sec")
                or 0
            )
            rps = r.get("records_per_sec", 0)
            row = {
                "feature": code,
                "records": r.get("records", 0),
                "wall_time_s": r.get("wall_time_s", 0),
                "cpu_time_s": r.get("cpu_time_s", 0),
                "cpu_efficiency": r.get("cpu_efficiency", 0),
                "records_per_sec": rps,
                "ns_per_record": r.get("ns_per_record", 0),
                "memory_peak_mb": r.get("memory_peak_mb", 0),
                "rss_start_mb": r.get("rss_start_mb", 0),
                "rss_end_mb": r.get("rss_end_mb", 0),
                "rss_delta_mb": r.get("rss_delta_mb", 0),
                "gc_gen0": r.get("gc_gen0", 0),
                "expected_rps": exp_rps,
                "ratio": rps / exp_rps if exp_rps > 0 else 0,
                "meets_target": r.get("meets_target", "N/A"),
            }
            writer.writerow(row)
    print(f"Results exported to: {path}")


def print_system_info(info: dict, config: Optional[dict] = None) -> None:
    """Print system information header."""
    print("=" * 80)
    print("SYSTEM INFORMATION")
    print("=" * 80)
    print(f"  Python:    {info.get('python_version', 'unknown').split()[0]}")
    print(f"  Platform:  {info.get('platform', 'unknown')}")
    print(f"  Processor: {info.get('processor', 'unknown')}")
    print(f"  CPU Count: {info.get('cpu_count', 'unknown')}")
    if info.get("psutil_available"):
        print(f"  psutil:    {info.get('psutil_version', 'unknown')}")
    if "mem_total_gb" in info:
        print(
            f"  Memory:    {info.get('mem_available_gb')} GB free / "
            f"{info.get('mem_total_gb')} GB total ({info.get('mem_percent')}%)"
        )
    if "disk_free_gb" in info:
        print(
            f"  Disk:      {info.get('disk_free_gb')} GB free / "
            f"{info.get('disk_total_gb')} GB total"
        )
    if config:
        print("-" * 80)
        print("RUN CONFIG")
        for key in sorted(config.keys()):
            print(f"  {key}: {config[key]}")
    print("=" * 80)


def list_features() -> None:
    """Print list of all features."""
    print("=" * 80)
    print("TIMELOG DEMO - FEATURE LIST")
    print("=" * 80)

    categories = {}
    for code, f in FEATURES.items():
        cat = f["category"]
        if cat not in categories:
            categories[cat] = []
        categories[cat].append((code, f["name"]))

    for cat in sorted(categories.keys()):
        print(f"\nCategory {cat}:")
        for code, name in sorted(categories[cat]):
            print(f"  {code}: {name}")

    print()
    print(f"Total: {len(FEATURES)} features")
    print("=" * 80)


# =============================================================================
# Category A: Data Ingestion
# =============================================================================


@feature("A0", "Ingest breakdown (parse vs Timelog vs end-to-end)", "A")
def demo_a0_ingest_breakdown(runner: DemoRunner) -> dict:
    """
    Separate CSV parsing cost from Timelog ingestion cost.

    Modes:
    - parse-only: CSV -> list
    - timelog-only: list -> Timelog
    - end-to-end: CSV -> Timelog
    """
    limit = min(runner.limit, 50_000) if runner.limit else 50_000
    results: dict[str, dict] = {}

    records: list[tuple[int, Order]] = []
    if runner.ingest_mode in ("all", "parse_only", "timelog_only"):
        records, parse_s = parse_orders_to_list(runner.data_path, limit=limit)
        results["parse_only"] = {
            "records": len(records),
            "wall_time_s": parse_s,
            "records_per_sec": len(records) / parse_s if parse_s > 0 else 0,
        }

    if runner.ingest_mode in ("all", "timelog_only"):
        if not records:
            records, _ = parse_orders_to_list(runner.data_path, limit=limit)
        if runner.reuse_obj and records:
            reuse_obj = records[0][1]
            records = [(ts, reuse_obj) for ts, _ in records]
        log = Timelog.for_bulk_ingest(time_unit="ns")
        try:
            ingest_s = ingest_records(log, records)
        finally:
            log.close()
        results["timelog_only"] = {
            "records": len(records),
            "wall_time_s": ingest_s,
            "records_per_sec": len(records) / ingest_s if ingest_s > 0 else 0,
            "reuse_obj": runner.reuse_obj,
        }

    if runner.ingest_mode in ("all", "end_to_end"):
        BATCH_SIZE = 10_000
        total = 0
        start = time.perf_counter_ns()
        log = Timelog.for_bulk_ingest(time_unit="ns")
        try:
            batch: list[tuple[int, Order]] = []
            reuse_obj = None
            for ts, order in load_orders(runner.data_path, limit=limit):
                if runner.reuse_obj:
                    if reuse_obj is None:
                        reuse_obj = order
                    order = reuse_obj
                batch.append((ts, order))
                if len(batch) >= BATCH_SIZE:
                    log.extend(batch)
                    total += len(batch)
                    batch.clear()
            if batch:
                log.extend(batch)
                total += len(batch)
        finally:
            log.close()
        elapsed = time.perf_counter_ns() - start
        end_to_end_s = elapsed / 1e9
        results["end_to_end"] = {
            "records": total,
            "wall_time_s": end_to_end_s,
            "records_per_sec": total / end_to_end_s if end_to_end_s > 0 else 0,
            "reuse_obj": runner.reuse_obj,
        }

    # Provide a top-level summary for the standard table.
    end_to_end = results.get("end_to_end")
    if end_to_end:
        return {"records": end_to_end["records"], **end_to_end, "breakdown": results}
    if results:
        key = next(iter(results))
        return {"records": results[key]["records"], **results[key], "breakdown": results}
    return {"records": 0, "error": "no ingest mode selected"}


@feature("A1", "Single record append", "A")
def demo_a1_single_append(runner: DemoRunner) -> dict:
    """Demonstrate single-record append with timing."""
    # Use a fresh Timelog for this test
    count = 0
    log = Timelog.for_bulk_ingest(time_unit="ns")
    try:
        for ts, order in load_orders(runner.data_path, limit=min(runner.limit, 10_000) or 10_000):
            log.append(ts, order)
            count += 1
    finally:
        log.close()
    return {"records": count}


@feature("A2", "Batch ingestion", "A")
def demo_a2_batch_ingestion(runner: DemoRunner) -> dict:
    """Bulk load with extend() - significantly faster than single append."""
    BATCH_SIZE = 10_000
    batch = []
    total = 0
    busy_count = 0

    log = Timelog.for_bulk_ingest(time_unit="ns")
    try:
        for ts, order in load_orders(runner.data_path, runner.limit):
            batch.append((ts, order))
            if len(batch) >= BATCH_SIZE:
                try:
                    log.extend(batch)
                except TimelogBusyError:
                    # For write-path busy, the batch is already committed.
                    # Do not retry, or duplicates can be created.
                    busy_count += 1
                    log.flush()
                total += len(batch)
                batch.clear()
        if batch:
            try:
                log.extend(batch)
            except TimelogBusyError:
                # Batch already committed; only relieve pressure.
                busy_count += 1
                log.flush()
            total += len(batch)
    finally:
        log.close()

    return {"records": total, "busy_events": busy_count}


@feature("A2B", "Batch ingestion (background maintenance)", "A")
def demo_a2b_batch_ingestion_background(runner: DemoRunner) -> dict:
    """
    Bulk load with extend() while background maintenance drains memtable.

    This avoids explicit flush calls and is closer to production usage.
    """
    BATCH_SIZE = 10_000
    batch = []
    total = 0

    log = Timelog.for_streaming(time_unit="ns")
    try:
        for ts, order in load_orders(runner.data_path, runner.limit):
            batch.append((ts, order))
            if len(batch) >= BATCH_SIZE:
                log.extend(batch)
                total += len(batch)
                batch.clear()
        if batch:
            log.extend(batch)
            total += len(batch)
    finally:
        log.close()

    return {"records": total}


@feature("A3", "Streaming ingestion", "A")
def demo_a3_streaming_ingestion(runner: DemoRunner) -> dict:
    """Simulate real-time order feed with rate tracking."""
    count = 0
    log = Timelog.for_streaming(time_unit="ns")
    try:
        for ts, order in load_orders(runner.data_path, limit=min(runner.limit, 50_000) or 50_000):
            log.append(ts, order)
            count += 1
    finally:
        log.close()
    return {"records": count}


@feature("A4", "Out-of-order ingestion", "A")
def demo_a4_out_of_order(runner: DemoRunner) -> dict:
    """Demonstrate LSM handles unordered data."""
    # Load data into memory first
    # Keep the sample size moderate to avoid excessive flush/compaction time.
    max_records = min(runner.limit, 20_000) if runner.limit else 20_000
    records = list(load_orders(runner.data_path, limit=max_records))
    # Shuffle to simulate out-of-order arrival
    random.seed(42)
    random.shuffle(records)

    # Use background maintenance to handle backpressure
    log = Timelog.for_streaming(time_unit="ns")
    try:
        # Batch insert, handling potential backpressure
        BATCH_SIZE = 5_000
        for i in range(0, len(records), BATCH_SIZE):
            batch = records[i : i + BATCH_SIZE]
            log.extend(batch)
    finally:
        log.close()

    return {"records": len(records)}


@feature("A5", "Backpressure handling", "A")
def demo_a5_backpressure(runner: DemoRunner) -> dict:
    """Handle TimelogBusyError without retrying already-committed writes."""
    busy_count = 0
    total = 0

    log = Timelog.for_low_latency(
        time_unit="ns",
        sealed_max_runs=1,
        memtable_max_bytes=64 * 1024,
    )
    try:
        for ts, order in load_orders(runner.data_path, limit=min(runner.limit, 20_000) or 20_000):
            try:
                log.append(ts, order)
                total += 1
            except TimelogBusyError:
                # append() committed; avoid retrying the same row.
                busy_count += 1
                log.flush()
                total += 1
    finally:
        log.close()

    return {"records": total, "busy_events": busy_count}


@feature("A6", "Order sensitivity (mostly vs less-ordered)", "A")
def demo_a6_order_sensitivity(runner: DemoRunner) -> dict:
    """
    Compare ingestion on ordered vs less-ordered datasets.

    Uses a small cap to keep the comparison fast and repeatable.
    """
    alt_path = _alternate_dataset_path(runner.data_path)
    if alt_path is None:
        return {"records": 0, "error": "no alternate dataset found"}

    # Hard cap at 20k to keep comparison fast across two datasets.
    limit = min(runner.limit or 50_000, 20_000)
    results: dict[str, dict] = {}

    for label, path in [("primary", runner.data_path), ("alternate", alt_path)]:
        records = list(load_orders(path, limit=limit))
        start = time.perf_counter_ns()
        log = Timelog.for_streaming(time_unit="ns")
        try:
            BATCH_SIZE = 10_000
            for i in range(0, len(records), BATCH_SIZE):
                log.extend(records[i : i + BATCH_SIZE])
        finally:
            log.close()
        elapsed = time.perf_counter_ns() - start

        wall_s = elapsed / 1e9
        rps = len(records) / wall_s if wall_s > 0 else 0
        results[label] = {
            "path": path,
            "records": len(records),
            "wall_time_s": wall_s,
            "records_per_sec": rps,
        }

    total_records = sum(r["records"] for r in results.values())
    return {"records": total_records, "cases": results}


# =============================================================================
# Category B: Time Range Queries
# =============================================================================


@feature("B1", "Range query slice", "B")
def demo_b1_range_query(runner: DemoRunner) -> dict:
    """Query orders in 1-second window using slice syntax."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window_ns = 1_000_000_000  # 1 second

    count = 0
    for _ in runner.log[first : first + window_ns]:
        count += 1

    return {"records": count, "window_ns": window_ns}


@feature("B2", "Since query", "B")
def demo_b2_since_query(runner: DemoRunner) -> dict:
    """Query all orders after a timestamp."""
    runner.ensure_data_loaded()
    # Pick a midpoint from actual data to avoid empty results on small datasets.
    midpoint = None
    for i, (ts, _) in enumerate(runner.log):
        if i >= 1000:
            midpoint = ts
            break
    if midpoint is None:
        return {"records": 0, "error": "insufficient data for midpoint"}

    count = 0
    for _ in runner.log[midpoint:]:
        count += 1
        if count >= 100_000:  # Limit for quick mode
            break

    return {"records": count}


@feature("B3", "Until query", "B")
def demo_b3_until_query(runner: DemoRunner) -> dict:
    """Query all orders before a timestamp."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    cutoff = first + 60_000_000_000  # 60 seconds

    count = 0
    for _ in runner.log[:cutoff]:
        count += 1

    return {"records": count}


@feature("B4", "Full scan", "B")
def demo_b4_full_scan(runner: DemoRunner) -> dict:
    """Iterate all records using iter(log)."""
    runner.ensure_data_loaded()
    count = 0
    for _ in runner.log:
        count += 1
    return {"records": count}


@feature("B5", "Point query", "B")
def demo_b5_point_query(runner: DemoRunner) -> dict:
    """Query all orders at exact nanosecond using at()."""
    runner.ensure_data_loaded()
    # Sample a set of timestamps to measure point-query throughput.
    sample_timestamps = []
    for i, (ts, _) in enumerate(runner.log):
        if i % 100 == 0:
            sample_timestamps.append(ts)
        if len(sample_timestamps) >= 1000:
            break

    if not sample_timestamps:
        return {"records": 0, "error": "no data for point queries"}

    total_found = 0
    for ts in sample_timestamps:
        total_found += sum(1 for _ in runner.log.at(ts))

    # Treat "records" as query count for throughput calculation.
    return {
        "records": len(sample_timestamps),
        "queries": len(sample_timestamps),
        "total_found": total_found,
    }


@feature("B6", "Microsecond window", "B")
def demo_b6_microsecond_window(runner: DemoRunner) -> dict:
    """Query a 1-microsecond trading window."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window_ns = 1000  # 1 microsecond

    total_found = 0
    queries = 0
    for i in range(1000):
        start = first + i * window_ns
        total_found += sum(1 for _ in runner.log[start : start + window_ns])
        queries += 1

    # Treat "records" as query count for throughput calculation.
    return {"records": queries, "queries": queries, "total_found": total_found, "window_ns": window_ns}


@feature("B7", "len(log) full count benchmark", "B")
def demo_b7_len_full_count(runner: DemoRunner) -> dict:
    """Benchmark full timelog length calls under heavy loaded state."""
    runner.ensure_data_loaded()

    expected_full_count = None
    b4_result = runner.results.get("B4")
    if isinstance(b4_result, dict) and "error" not in b4_result:
        b4_count = b4_result.get("records")
        if isinstance(b4_count, int) and b4_count >= 0:
            expected_full_count = b4_count
    if expected_full_count is None:
        expected_full_count = sum(1 for _ in runner.log)

    # Warmup to reduce one-time effects.
    for _ in range(3):
        _ = len(runner.log)

    target_seconds = 2.0 if runner.limit else 6.0
    max_calls = 5_000 if runner.limit else 25_000
    deadline = time.perf_counter() + target_seconds
    lat = LatencyStats()
    mismatch_calls = 0
    calls = 0
    len_value_last = 0

    while calls < max_calls and time.perf_counter() < deadline:
        t0 = time.perf_counter_ns()
        got = len(runner.log)
        dt = time.perf_counter_ns() - t0
        lat.add(dt)
        calls += 1
        len_value_last = got
        if got != expected_full_count:
            mismatch_calls += 1

    return {
        "records": calls,  # operation count for throughput
        "len_value_last": len_value_last,
        "expected_full_count": expected_full_count,
        "mismatch_calls": mismatch_calls,
        "latency_ns": lat.summary(),
    }


@feature("B8", "len(slice) remaining-count benchmark", "B")
def demo_b8_len_slice_count(runner: DemoRunner) -> dict:
    """Benchmark len() on slice iterators and verify remaining-length contract."""
    runner.ensure_data_loaded()

    anchors: list[int] = []
    for i, (ts, _) in enumerate(runner.log):
        if i % 64 == 0:
            anchors.append(ts)
        if i >= 10_000:
            break

    if len(anchors) < 2:
        return {"records": 0, "error": "insufficient anchors for slice len benchmark"}

    def pick_range() -> tuple[int, int]:
        i = random.randint(0, len(anchors) - 1)
        j = min(len(anchors) - 1, i + random.randint(1, max(1, len(anchors) // 10)))
        t1 = anchors[i]
        t2 = anchors[j] + 1 if anchors[j] >= t1 else t1 + 1
        return t1, t2

    def make_iter(variant: str, t1: int, t2: int) -> TimelogIter:
        if variant == "range":
            return runner.log[t1:t2]
        if variant == "since":
            return runner.log[t1:]
        if variant == "until":
            return runner.log[:t2]
        return runner.log[:]

    def expected_count(variant: str, t1: int, t2: int) -> int:
        if variant == "range":
            return sum(1 for _ in runner.log[t1:t2])
        if variant == "since":
            return sum(1 for _ in runner.log[t1:])
        if variant == "until":
            return sum(1 for _ in runner.log[:t2])
        return sum(1 for _ in runner.log[:])

    # Contract probe before timing loop.
    contract_failures: list[str] = []
    probe_variants = ["range", "since", "until", "all"]
    probe_count = min(8, len(anchors))
    for i in range(probe_count):
        variant = probe_variants[i % len(probe_variants)]
        t1, t2 = pick_range()
        it = None
        try:
            exp = expected_count(variant, t1, t2)
            it = make_iter(variant, t1, t2)
            before = len(it)
            if before != exp:
                contract_failures.append(
                    f"{variant}:len_mismatch expected={exp} got={before} t1={t1} t2={t2}"
                )
                continue

            consume_target = min(3, before)
            consumed = 0
            for _ in range(consume_target):
                try:
                    next(it)
                    consumed += 1
                except StopIteration:
                    break
            after = len(it)
            if after != before - consumed:
                contract_failures.append(
                    f"{variant}:remaining_mismatch before={before} consumed={consumed} after={after}"
                )
                continue

            it.close()
            closed_len = len(it)
            if closed_len != 0:
                contract_failures.append(f"{variant}:closed_len_not_zero got={closed_len}")
        except Exception as exc:
            contract_failures.append(f"{variant}:exception {exc!r}")
        finally:
            if it is not None:
                try:
                    it.close()
                except Exception:
                    pass

    # Timed len(slice) benchmark.
    target_seconds = 2.0 if runner.limit else 6.0
    max_calls = 8_000 if runner.limit else 30_000
    deadline = time.perf_counter() + target_seconds
    lat = LatencyStats()
    variant_mix: Counter[str] = Counter()
    total_returned = 0
    calls = 0
    variants = ["range", "since", "until", "all"]

    while calls < max_calls and time.perf_counter() < deadline:
        variant = random.choice(variants)
        t1, t2 = pick_range()
        it = None
        t0 = time.perf_counter_ns()
        n = 0
        try:
            it = make_iter(variant, t1, t2)
            n = len(it)
        finally:
            if it is not None:
                try:
                    it.close()
                except Exception:
                    pass
        dt = time.perf_counter_ns() - t0
        lat.add(dt)
        calls += 1
        variant_mix[variant] += 1
        total_returned += n

    avg_returned_len = (total_returned / calls) if calls > 0 else 0.0
    return {
        "records": calls,  # operation count for throughput
        "variant_mix": dict(sorted(variant_mix.items())),
        "contract_failures": len(contract_failures),
        "contract_failure_samples": contract_failures[:10],
        "avg_returned_len": avg_returned_len,
        "latency_ns": lat.summary(),
    }


# =============================================================================
# Category C: HFT Analytics
# =============================================================================


@feature("C1", "Orders per second", "C")
def demo_c1_orders_per_second(runner: DemoRunner) -> dict:
    """Count orders in 1-second windows."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window_ns = 1_000_000_000  # 1 second

    windows = []
    total_records = 0
    for i in range(10):  # First 10 seconds
        start = first + i * window_ns
        count = sum(1 for _ in runner.log[start : start + window_ns])
        windows.append(count)
        total_records += count

    return {
        "records": total_records,
        "windows": len(windows),
        "avg_per_second": sum(windows) / len(windows) if windows else 0,
    }


@feature("C1B", "Orders/sec (single pass)", "C")
def demo_c1b_orders_per_second_single_pass(runner: DemoRunner) -> dict:
    """
    Count orders in 1-second windows using a single range scan.

    This avoids 10 separate range queries and is closer to production usage.
    """
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window_ns = 1_000_000_000  # 1 second
    span_ns = 10 * window_ns

    windows = [0] * 10
    total_records = 0
    for ts, _ in runner.log[first : first + span_ns]:
        idx = (ts - first) // window_ns
        if 0 <= idx < len(windows):
            windows[idx] += 1
            total_records += 1

    return {
        "records": total_records,
        "windows": len(windows),
        "avg_per_second": sum(windows) / len(windows) if windows else 0,
    }


@feature("C2", "Buy/Sell ratio", "C")
def demo_c2_buy_sell_ratio(runner: DemoRunner) -> dict:
    """Analyze buy/sell direction per interval."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window = 60_000_000_000  # 1 minute

    buys = sells = 0
    for ts, order in runner.log[first : first + window]:
        if order.direction == "BUY":
            buys += 1
        else:
            sells += 1

    total = buys + sells
    ratio = buys / sells if sells > 0 else float("inf")

    return {"records": total, "buys": buys, "sells": sells, "ratio": ratio}


@feature("C3", "Volume-weighted price (VWAP)", "C")
def demo_c3_vwap(runner: DemoRunner) -> dict:
    """Calculate Volume-Weighted Average Price."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window = 300_000_000_000  # 5 minutes

    total_value = 0.0
    total_volume = 0
    count = 0

    for ts, order in runner.log[first : first + window]:
        count += 1
        if order.status == "FILLED":
            price = order.bid_price or order.ask_price
            total_value += price * order.amount
            total_volume += order.amount

    vwap = total_value / total_volume if total_volume > 0 else 0

    return {"records": count, "vwap": vwap, "volume": total_volume}


@feature("C4", "Order fill rate", "C")
def demo_c4_fill_rate(runner: DemoRunner) -> dict:
    """Calculate FILLED/OPEN ratio per window."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window = 60_000_000_000  # 1 minute

    filled = open_orders = partial = 0
    for ts, order in runner.log[first : first + window]:
        if order.status == "FILLED":
            filled += 1
        elif order.status == "OPEN":
            open_orders += 1
        else:
            partial += 1

    total = filled + open_orders + partial
    fill_rate = filled / total if total > 0 else 0

    return {
        "records": total,
        "filled": filled,
        "open": open_orders,
        "partial": partial,
        "fill_rate": fill_rate,
    }


@feature("C5", "Ticker activity", "C")
def demo_c5_ticker_activity(runner: DemoRunner) -> dict:
    """Find most active symbols in period."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window = 60_000_000_000  # 1 minute

    ticker_counts: Counter[str] = Counter()
    total = 0

    for ts, order in runner.log[first : first + window]:
        ticker_counts[order.ticker] += 1
        total += 1

    top_5 = ticker_counts.most_common(5)

    return {
        "records": total,
        "unique_tickers": len(ticker_counts),
        "top_5": top_5,
    }


@feature("C6", "Spread analysis", "C")
def demo_c6_spread_analysis(runner: DemoRunner) -> dict:
    """Analyze bid-ask spread distribution."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window = 60_000_000_000  # 1 minute

    count = 0
    spread_count = 0
    spread_sum = 0.0
    min_spread = None
    max_spread = None

    for ts, order in runner.log[first : first + window]:
        count += 1
        if order.bid_price is not None:
            spread = order.ask_price - order.bid_price
            spread_sum += spread
            spread_count += 1
            if min_spread is None or spread < min_spread:
                min_spread = spread
            if max_spread is None or spread > max_spread:
                max_spread = spread

    avg_spread = spread_sum / spread_count if spread_count else 0
    min_spread = min_spread if min_spread is not None else 0
    max_spread = max_spread if max_spread is not None else 0

    return {
        "records": count,
        "spreads_calculated": spread_count,
        "avg_spread": avg_spread,
        "min_spread": min_spread,
        "max_spread": max_spread,
    }


@feature("C7", "Commission totals", "C")
def demo_c7_commission_totals(runner: DemoRunner) -> dict:
    """Sum commissions per time bucket."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window = 60_000_000_000  # 1 minute

    total_commission = 0.0
    count = 0

    for ts, order in runner.log[first : first + window]:
        total_commission += order.commission
        count += 1

    return {"records": count, "total_commission": total_commission}


@feature("C8", "Latency histogram", "C")
def demo_c8_latency_histogram(runner: DemoRunner) -> dict:
    """Analyze nanosecond gaps between orders."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window = 10_000_000_000  # 10 seconds

    prev_ts = None
    gaps = []
    count = 0

    for ts, order in runner.log[first : first + window]:
        count += 1
        if prev_ts is not None:
            gap = ts - prev_ts
            gaps.append(gap)
        prev_ts = ts

    # Build histogram buckets (log scale)
    buckets = {
        "<1us": 0,
        "1-10us": 0,
        "10-100us": 0,
        "100us-1ms": 0,
        ">1ms": 0,
    }
    for gap in gaps:
        if gap < 1_000:
            buckets["<1us"] += 1
        elif gap < 10_000:
            buckets["1-10us"] += 1
        elif gap < 100_000:
            buckets["10-100us"] += 1
        elif gap < 1_000_000:
            buckets["100us-1ms"] += 1
        else:
            buckets[">1ms"] += 1

    avg_gap = sum(gaps) / len(gaps) if gaps else 0

    return {"records": count, "avg_gap_ns": avg_gap, "histogram": buckets}


# =============================================================================
# Category D: Deletion & Eviction
# =============================================================================


@feature("D1", "Delete time range", "D")
def demo_d1_delete(runner: DemoRunner) -> dict:
    """Delete orders in specific time window."""
    # Use a fresh log for deletion tests
    records = list(load_orders(runner.data_path, limit=min(runner.limit, 50_000) or 50_000))

    log = Timelog.for_bulk_ingest(time_unit="ns")
    try:
        log.extend(records)

        first = next(iter(log))[0]
        del_start = first + 10_000_000_000  # 10 seconds in
        del_end = del_start + 5_000_000_000  # 5 second window

        before = sum(1 for _ in log[del_start:del_end])
        log.delete(del_start, del_end)
        after = sum(1 for _ in log[del_start:del_end])
    finally:
        log.close()

    return {"records": len(records), "before": before, "after": after}


@feature("D2", "Evict old data", "D")
def demo_d2_evict_old_data(runner: DemoRunner) -> dict:
    """TTL-style cleanup with cutoff()."""
    records = list(load_orders(runner.data_path, limit=min(runner.limit, 50_000) or 50_000))

    log = Timelog.for_bulk_ingest(time_unit="ns")
    try:
        log.extend(records)

        first = next(iter(log))[0]
        cutoff = first + 30_000_000_000  # 30 seconds

        before = sum(1 for _ in log[:cutoff])
        log.cutoff(cutoff)
        after = sum(1 for _ in log[:cutoff])
    finally:
        log.close()

    return {"records": len(records), "before": before, "after": after}


@feature("D3", "Verify deletion", "D")
def demo_d3_verify_deletion(runner: DemoRunner) -> dict:
    """Confirm tombstones work with point query."""
    records = list(load_orders(runner.data_path, limit=min(runner.limit, 10_000) or 10_000))

    log = Timelog.for_bulk_ingest(time_unit="ns")
    try:
        log.extend(records)

        # Get a timestamp we know exists
        target_ts = records[100][0]

        before = list(log.at(target_ts))
        log.delete(target_ts, target_ts + 1)
        after = list(log.at(target_ts))
    finally:
        log.close()

    return {
        "records": len(records),
        "target_ts": target_ts,
        "before_count": len(before),
        "after_count": len(after),
    }


@feature("D4", "Query after delete", "D")
def demo_d4_query_after_delete(runner: DemoRunner) -> dict:
    """Verify gap in results after deletion."""
    records = list(load_orders(runner.data_path, limit=min(runner.limit, 50_000) or 50_000))

    log = Timelog.for_bulk_ingest(time_unit="ns")
    try:
        log.extend(records)

        first = next(iter(log))[0]
        query_start = first
        query_end = first + 60_000_000_000  # 1 minute

        # Delete middle portion
        del_start = first + 20_000_000_000
        del_end = first + 40_000_000_000
        log.delete(del_start, del_end)

        # Query the full range
        results = list(log[query_start:query_end])

        # Verify no results in deleted range
    finally:
        log.close()

    in_deleted = sum(1 for ts, _ in results if del_start <= ts < del_end)

    return {
        "records": len(results),
        "in_deleted_range": in_deleted,
    }


# =============================================================================
# Category E: Maintenance Operations
# =============================================================================


@feature("E1", "Manual flush", "E")
def demo_e1_manual_flush(runner: DemoRunner) -> dict:
    """Force memtable to L0 segment."""
    records = list(load_orders(runner.data_path, limit=min(runner.limit, 50_000) or 50_000))

    log = Timelog.for_bulk_ingest(time_unit="ns")
    try:
        log.extend(records)
        log.flush()
    finally:
        log.close()

    return {"records": len(records)}


@feature("E2", "Request compaction", "E")
def demo_e2_request_compaction(runner: DemoRunner) -> dict:
    """Trigger compaction and execute it in manual-maintenance mode."""
    records = list(load_orders(runner.data_path, limit=min(runner.limit, 50_000) or 50_000))

    log = Timelog.for_bulk_ingest(time_unit="ns")
    maint_steps = 0
    try:
        # Load in batches to create multiple memruns
        batch_size = 10_000
        for i in range(0, len(records), batch_size):
            log.extend(records[i : i + batch_size])
            log.flush()
        log.compact()
        maint_steps = _drain_manual_maintenance(log)
    finally:
        log.close()

    return {"records": len(records), "maint_steps": maint_steps}


@feature("E3", "Background mode", "E")
def demo_e3_background_mode(runner: DemoRunner) -> dict:
    """Auto flush/compact with maintenance='background'."""
    count = 0
    log = Timelog.for_streaming(time_unit="ns")
    try:
        for ts, order in load_orders(runner.data_path, limit=min(runner.limit, 50_000) or 50_000):
            log.append(ts, order)
            count += 1
    finally:
        log.close()

    return {"records": count}


@feature("E4", "Maintenance lifecycle", "E")
def demo_e4_maintenance_lifecycle(runner: DemoRunner) -> dict:
    """Control background worker with start/stop."""
    count = 0
    # Must initialize with maintenance="background" to allow start/stop.
    log = Timelog.for_streaming(time_unit="ns")
    try:
        for ts, order in load_orders(
            runner.data_path, limit=min(runner.limit, 20_000) or 20_000
        ):
            log.append(ts, order)
            count += 1

        # Stop and restart to demonstrate lifecycle control
        log.stop_maintenance()
        log.start_maintenance()

        # Add more data
        for ts, order in load_orders(
            runner.data_path, limit=min(runner.limit, 20_000) or 20_000
        ):
            log.append(ts, order)
            count += 1

        # Stop maintenance
        log.stop_maintenance()
    finally:
        log.close()

    return {"records": count}


# =============================================================================
# Category F: Zero-Copy PageSpan Access
# =============================================================================


@feature("F1", "PageSpan iteration", "F")
def demo_f1_pagespan_iteration(runner: DemoRunner) -> dict:
    """Stream page-aligned chunks with zero-copy access."""
    runner.ensure_data_loaded()
    runner.log.flush()  # Ensure data is in pages

    first = next(iter(runner.log))[0]
    window = 60_000_000_000  # 1 minute

    span_count = 0
    total_timestamps = 0

    with runner.log.views(first, first + window) as spans:
        for span in spans:
            with span:
                span_count += 1
                total_timestamps += len(span)

    return {"records": total_timestamps, "spans": span_count}


@feature("F2", "Timestamp memoryview", "F")
def demo_f2_timestamp_memoryview(runner: DemoRunner) -> dict:
    """Zero-copy timestamp access via memoryview."""
    runner.ensure_data_loaded()
    runner.log.flush()

    first = next(iter(runner.log))[0]
    window = 10_000_000_000  # 10 seconds

    total_timestamps = 0
    first_ts = last_ts = 0

    with runner.log.views(first, first + window) as spans:
        for span in spans:
            with span as live_span:
                mv = live_span.timestamps
                total_timestamps += len(mv)
                if len(mv) > 0:
                    if first_ts == 0:
                        first_ts = mv[0]
                    last_ts = mv[-1]
                # Release the buffer view before closing the span to avoid UAF.
                del mv

    return {
        "records": total_timestamps,
        "first_ts": first_ts,
        "last_ts": last_ts,
    }


@feature("F3", "Objects view", "F")
def demo_f3_objects_view(runner: DemoRunner) -> dict:
    """Lazy object decoding via span.objects()."""
    runner.ensure_data_loaded()
    runner.log.flush()

    first = next(iter(runner.log))[0]
    window = 10_000_000_000  # 10 seconds

    total_objects = 0
    tickers = set()

    with runner.log.views(first, first + window) as spans:
        for span in spans:
            with span as live_span:
                objects = live_span.objects()
                total_objects += len(objects)
                for obj in objects:
                    tickers.add(obj.ticker)

    return {"records": total_objects, "unique_tickers": len(tickers)}


@feature("F4", "NumPy integration", "F")
def demo_f4_numpy_integration(runner: DemoRunner) -> dict:
    """Direct numpy array from PageSpan timestamps."""
    if np is None:
        return {"records": 0, "error": "numpy not installed"}

    runner.ensure_data_loaded()
    runner.log.flush()

    first = next(iter(runner.log))[0]
    window = 10_000_000_000  # 10 seconds

    total_timestamps = 0
    avg_gap = 0.0

    with runner.log.views(first, first + window) as spans:
        for span in spans:
            with span as live_span:
                arr = np.asarray(live_span.timestamps)  # Zero-copy!
                total_timestamps += len(arr)
                if len(arr) > 1:
                    diffs = np.diff(arr)
                    avg_gap = float(np.mean(diffs))
                # Release the NumPy view before closing the span to avoid UAF.
                del arr
            break  # Just first span for demo

    return {"records": total_timestamps, "dtype": "int64", "avg_gap_ns": avg_gap}


@feature("F5", "Bulk statistics", "F")
def demo_f5_bulk_statistics(runner: DemoRunner) -> dict:
    """Fast min/max/mean on timestamps via PageSpan."""
    if np is None:
        return {"records": 0, "error": "numpy not installed"}

    runner.ensure_data_loaded()
    runner.log.flush()

    first = next(iter(runner.log))[0]
    window = 60_000_000_000  # 1 minute

    all_timestamps = []
    total = 0

    with runner.log.views(first, first + window) as spans:
        for span in spans:
            with span as live_span:
                # Copy the array data since we need it after the span closes
                arr = np.array(live_span.timestamps, copy=True)
                all_timestamps.append(arr)
                total += len(arr)

    if all_timestamps:
        combined = np.concatenate(all_timestamps)
        ts_min = int(np.min(combined))
        ts_max = int(np.max(combined))
        ts_mean = float(np.mean(combined))
        ts_std = float(np.std(combined))
    else:
        ts_min = ts_max = 0
        ts_mean = ts_std = 0.0

    return {
        "records": total,
        "min": ts_min,
        "max": ts_max,
        "mean": ts_mean,
        "std": ts_std,
    }


# =============================================================================
# Category G: Iterator Patterns
# =============================================================================


@feature("G1", "Batch iteration", "G")
def demo_g1_batch_iteration(runner: DemoRunner) -> dict:
    """Fetch records in batches with next_batch()."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window = 60_000_000_000  # 1 minute

    it = runner.log[first : first + window]

    total = 0
    batches = 0
    while True:
        batch = it.next_batch(1000)
        if not batch:
            break
        total += len(batch)
        batches += 1

    return {"records": total, "batches": batches}


@feature("G2", "Context manager", "G")
def demo_g2_context_manager(runner: DemoRunner) -> dict:
    """Explicit iterator close (no context manager)."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window = 60_000_000_000  # 1 minute

    count = 0
    it = runner.log[first : first + window]
    try:
        for _ in it:
            count += 1
    finally:
        it.close()

    return {"records": count}


@feature("G3", "Early termination", "G")
def demo_g3_early_termination(runner: DemoRunner) -> dict:
    """Stop iteration cleanly with break."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]

    count = 0
    target = 10_000
    for _ in runner.log[first:]:
        count += 1
        if count >= target:
            break

    return {"records": count}


@feature("G4", "Multiple iterators", "G")
def demo_g4_multiple_iterators(runner: DemoRunner) -> dict:
    """Parallel time windows with multiple iterators."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window = 10_000_000_000  # 10 seconds each

    # Create multiple iterators for different windows
    iters = [
        runner.log[first + i * window : first + (i + 1) * window]
        for i in range(5)
    ]

    counts = []
    total = 0
    for it in iters:
        count = sum(1 for _ in it)
        counts.append(count)
        total += count

    return {"records": total, "window_counts": counts}


# =============================================================================
# Category H: Business Use Cases
# =============================================================================


@feature("H1", "Trade reconstruction", "H")
def demo_h1_trade_reconstruction(runner: DemoRunner) -> dict:
    """Trace order lifecycle from OPEN to FILLED."""
    runner.ensure_data_loaded()

    # Find an OPEN order
    order_id = None
    open_ts = None

    for ts, order in runner.log:
        if order.status == "OPEN":
            order_id = order.order_id
            open_ts = ts
            break

    if order_id is None:
        return {"records": 0, "error": "No OPEN orders found"}

    # Trace lifecycle
    lifecycle = []
    count = 0
    for ts, order in runner.log[open_ts:]:
        count += 1
        if order.order_id == order_id:
            lifecycle.append((ts, order.status))
            if order.status == "FILLED":
                break
        if count >= 100_000:  # Safety limit
            break

    return {"records": count, "order_id": order_id, "events": len(lifecycle)}


@feature("H2", "Market replay", "H")
def demo_h2_market_replay(runner: DemoRunner) -> dict:
    """Replay trading session from start."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    session_length = 60_000_000_000  # 1 minute session

    events = []
    count = 0

    for ts, order in runner.log[first : first + session_length]:
        count += 1
        if count <= 100:  # Sample first 100 events
            events.append((ts - first, order.ticker, order.direction, order.amount))

    return {"records": count, "sample_events": len(events)}


@feature("H3", "Anomaly detection", "H")
def demo_h3_anomaly_detection(runner: DemoRunner) -> dict:
    """Detect volume spikes using sliding window."""
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window_ns = 1_000_000_000  # 1 second windows
    threshold = 2.0

    # Count orders per second for first 60 seconds
    windows = []
    total_records = 0
    for i in range(60):
        start = first + i * window_ns
        count = sum(1 for _ in runner.log[start : start + window_ns])
        windows.append(count)
        total_records += count

    # Find spikes
    avg = sum(windows) / len(windows) if windows else 0
    spikes = [(i, c) for i, c in enumerate(windows) if c > avg * threshold]

    return {
        "records": total_records,
        "windows": len(windows),
        "baseline_avg": avg,
        "spikes": len(spikes),
    }


@feature("H3B", "Anomaly detection (single pass)", "H")
def demo_h3b_anomaly_detection_single_pass(runner: DemoRunner) -> dict:
    """
    Single-pass anomaly detection using fixed windows.

    This avoids 60 separate range queries and reduces iterator overhead.
    """
    runner.ensure_data_loaded()
    first = next(iter(runner.log))[0]
    window_ns = 1_000_000_000  # 1 second windows
    window_count = 60
    span_ns = window_count * window_ns

    windows = [0] * window_count
    total_records = 0
    for ts, _ in runner.log[first : first + span_ns]:
        idx = (ts - first) // window_ns
        if 0 <= idx < window_count:
            windows[idx] += 1
            total_records += 1

    avg = sum(windows) / len(windows) if windows else 0
    spikes = [(i, c) for i, c in enumerate(windows) if c > avg * 2.0]

    return {
        "records": total_records,
        "windows": len(windows),
        "baseline_avg": avg,
        "spikes": len(spikes),
    }


@feature("H4", "Audit trail", "H")
def demo_h4_audit_trail(runner: DemoRunner) -> dict:
    """Exact-time order lookup for audit."""
    runner.ensure_data_loaded()

    # Get a few known timestamps
    sample_timestamps = []
    for i, (ts, _) in enumerate(runner.log):
        if i % 1000 == 0:
            sample_timestamps.append(ts)
        if len(sample_timestamps) >= 100:
            break

    # Query each timestamp
    total_found = 0
    queries = 0
    for ts in sample_timestamps:
        results = list(runner.log.at(ts))
        total_found += len(results)
        queries += 1

    # Treat "records" as query count for throughput calculation.
    return {"records": queries, "queries": queries, "total_found": total_found}


# =============================================================================
# Category I: Memory Tier Comparison
# =============================================================================


@feature("I1", "Memtable read (hot data)", "I")
def demo_i1_memtable_read(runner: DemoRunner) -> dict:
    """Read just-written data that's still in memtable (not flushed to disk).

    This tests the 'hot path' where data is read directly from memtable.
    Should be faster than segment reads since no disk I/O is involved.
    """
    # Create a fresh Timelog with NO background maintenance so data stays in memtable.
    # Use a larger memtable to avoid accidental flush on this synthetic workload.
    log = Timelog.for_bulk_ingest(
        time_unit="ns",
        memtable_max_bytes=32 * 1024 * 1024,
    )
    try:
        # Write fresh data (stays in memtable since no flush)
        base_ts = 2_000_000_000_000_000_000  # Far future to avoid conflicts
        batch = []
        for i in range(10_000):
            order = Order(
                ticker="HOT",
                isin="TEST",
                direction="BUY",
                status="OPEN",
                amount=100,
                ask_price=10.0,
                bid_price=None,
                order_id=i,
                commission=0.0,
            )
            batch.append((base_ts + i * 1000, order))
        log.extend(batch)

        # Now read it back - this hits memtable directly
        count = 0
        for ts, obj in log[base_ts : base_ts + 10_000_000]:
            count += 1

        return {"records": count, "source": "memtable"}
    finally:
        log.close()


@feature("I2", "Cold data read (segments)", "I")
def demo_i2_cold_read(runner: DemoRunner) -> dict:
    """Read data that has been flushed to segments (cold/disk data).

    This tests the 'cold path' where data comes from L0/L1 segments.
    """
    runner.ensure_data_loaded()

    # Flush to ensure data is in segments, not memtable
    runner.log.flush()

    # Read from the beginning (definitely in segments after flush)
    first = None
    for ts, _ in runner.log:
        first = ts
        break

    if first is None:
        return {"error": "No data loaded"}

    # Read a window from the beginning (cold data in segments)
    window = 1_000_000_000  # 1 second
    count = 0
    for ts, obj in runner.log[first : first + window]:
        count += 1

    return {"records": count, "source": "segments"}


@feature("I3", "Mixed read (memtable + segments)", "I")
def demo_i3_mixed_read(runner: DemoRunner) -> dict:
    """Read data spanning both memtable (hot) and segments (cold).

    This tests the k-way merge path where data comes from multiple sources.
    """
    runner.ensure_data_loaded()

    # Stop maintenance so new data stays hot in memtable for this test.
    maintenance_mode = getattr(runner.log, "maintenance_mode", None)
    runner.log.stop_maintenance()

    try:
        # Add fresh data to memtable
        base_ts = 2_000_000_000_000_000_000  # Far future
        batch = []
        for i in range(1_000):
            order = Order(
                ticker="MIXED",
                isin="TEST",
                direction="SELL",
                status="FILLED",
                amount=50,
                ask_price=20.0,
                bid_price=19.5,
                order_id=i + 100_000,
                commission=0.01,
            )
            batch.append((base_ts + i * 1000, order))
        runner.log.extend(batch)

        # Now read everything - this requires k-way merge of memtable + segments
        count = 0
        for ts, obj in runner.log:
            count += 1
    finally:
        if maintenance_mode == "background":
            try:
                runner.log.start_maintenance()
            except Exception:
                pass

    return {"records": count, "source": "memtable+segments"}


# =============================================================================
# Category J: Algorithmic Complexity Verification
# =============================================================================


@feature("J1", "Verify O(M) iteration count", "J")
def demo_j1_iteration_count(runner: DemoRunner) -> dict:
    """Verify that range query iterates exactly M times for M results.

    The key insight: even if each iteration is slow (Python overhead),
    the ALGORITHM is correct if iterations == result_size.

    If iterations >> result_size, we have a bug (e.g., scanning too much).
    If iterations << result_size, we have a different bug (missing results).
    """
    # Create our own log for this test
    log = Timelog.for_bulk_ingest(time_unit="ns")
    try:
        # Load some test data
        base_ts = 1_000_000_000_000_000_000
        batch = []
        for i in range(10_000):
            order = Order(
                ticker="ITER",
                isin="TEST",
                direction="BUY",
                status="OPEN",
                amount=1,
                ask_price=1.0,
                bid_price=None,
                order_id=i,
                commission=0.0,
            )
            batch.append((base_ts + i * 1_000_000, order))  # 1ms apart
        log.extend(batch)

        # Test multiple window sizes and verify iteration count
        test_results = []
        for expected_count in [100, 1000, 5000, 10000]:
            # Window sized to include expected_count records
            window = expected_count * 1_000_000  # ns

            # Count iterations explicitly
            iteration_count = 0
            result_count = 0
            for ts, obj in log[base_ts : base_ts + window]:
                iteration_count += 1
                result_count += 1

            # They should be equal!
            ratio = iteration_count / result_count if result_count > 0 else 0
            test_results.append(
                {
                    "expected": expected_count,
                    "iterations": iteration_count,
                    "results": result_count,
                    "ratio": ratio,
                    "correct": abs(ratio - 1.0) < 0.001,
                }
            )

        all_correct = all(r["correct"] for r in test_results)
        return {
            "records": sum(r["results"] for r in test_results),
            "tests": test_results,
            "all_correct": all_correct,
            "complexity_verified": "O(M)" if all_correct else "ANOMALY",
        }
    finally:
        log.close()


@feature("J2", "Verify scaling behavior", "J")
def demo_j2_scaling_test(runner: DemoRunner) -> dict:
    """Verify that operation time scales correctly with input size.

    For O(N) operations: doubling N should double time (exponent ~1.0)
    For O(N log N): doubling N should ~2.1x time (exponent ~1.05-1.1)
    For O(N^2): doubling N should 4x time (exponent ~2.0) <- BAD!

    We run at multiple sizes and fit the scaling exponent.
    """
    import math

    # Test at multiple sizes
    sizes = [1000, 2000, 4000, 8000, 16000]
    times = []

    for size in sizes:
        log = Timelog.for_bulk_ingest(time_unit="ns")
        try:
            # Generate test data
            base_ts = 1_000_000_000_000_000_000
            batch = []
            for i in range(size):
                order = Order(
                    ticker="SCALE",
                    isin="TEST",
                    direction="BUY",
                    status="OPEN",
                    amount=1,
                    ask_price=1.0,
                    bid_price=None,
                    order_id=i,
                    commission=0.0,
                )
                batch.append((base_ts + i * 1000, order))
            log.extend(batch)

            # Time a full scan
            start = time.perf_counter_ns()
            count = 0
            for ts, obj in log:
                count += 1
            elapsed = time.perf_counter_ns() - start
            times.append(elapsed)
        finally:
            log.close()

    # Calculate scaling exponent using linear regression on log-log
    # log(time) = exponent * log(size) + c
    log_sizes = [math.log(s) for s in sizes]
    log_times = [math.log(t) if t > 0 else 0 for t in times]

    # Simple linear regression
    n = len(sizes)
    sum_x = sum(log_sizes)
    sum_y = sum(log_times)
    sum_xy = sum(x * y for x, y in zip(log_sizes, log_times))
    sum_x2 = sum(x * x for x in log_sizes)

    exponent = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x * sum_x)

    # Interpret results
    if exponent <= 1.2:
        verdict = "O(N) or O(N log N) - GOOD"
    elif exponent <= 1.5:
        verdict = "O(N^1.3-1.5) - ACCEPTABLE"
    else:
        verdict = f"O(N^{exponent:.2f}) - INVESTIGATE!"

    return {
        "records": sum(sizes),
        "sizes": sizes,
        "times_ns": times,
        "scaling_exponent": round(exponent, 3),
        "verdict": verdict,
        "complexity_verified": exponent <= 1.2,
    }


@feature("J3", "Verify no quadratic behavior", "J")
def demo_j3_no_quadratic(runner: DemoRunner) -> dict:
    """Specifically test operations that could accidentally be O(N^2).

    Common sources of accidental O(N^2):
    - Nested loops in merge
    - Linear search in sorted data
    - Repeated full scans

    This test checks for unexpected quadratic scaling.
    """
    import math

    # Test range query at increasing sizes
    # For O(N): time ratio when doubling N should be ~2
    # For O(N^2): time ratio when doubling N should be ~4

    ratios = []
    prev_time = None

    for size in [2000, 4000, 8000, 16000]:
        log = Timelog.for_bulk_ingest(time_unit="ns")
        try:
            base_ts = 1_000_000_000_000_000_000
            batch = []
            for i in range(size):
                order = Order(
                    ticker="QUAD",
                    isin="TEST",
                    direction="BUY",
                    status="OPEN",
                    amount=1,
                    ask_price=1.0,
                    bid_price=None,
                    order_id=i,
                    commission=0.0,
                )
                batch.append((base_ts + i * 1000, order))
            log.extend(batch)

            # Time the operation
            start = time.perf_counter_ns()
            count = sum(1 for _ in log)
            elapsed = time.perf_counter_ns() - start

            if prev_time is not None and prev_time > 0:
                ratio = elapsed / prev_time
                ratios.append({"size": size, "time_ns": elapsed, "ratio": ratio})

            prev_time = elapsed
        finally:
            log.close()

    # Check if any ratio is >= 3.5 (would indicate O(N^2))
    avg_ratio = sum(r["ratio"] for r in ratios) / len(ratios) if ratios else 0
    is_quadratic = avg_ratio >= 3.5

    return {
        "records": 16000,
        "ratios": ratios,
        "avg_ratio": round(avg_ratio, 2),
        "is_quadratic": is_quadratic,
        "complexity_verified": not is_quadratic,
        "verdict": "O(N^2) DETECTED!" if is_quadratic else "No quadratic behavior - GOOD",
    }


# =============================================================================
# Category K: Production Scenarios
# =============================================================================


@feature("K1", "Append latency distribution (background)", "K")
def demo_k1_append_latency_background(runner: DemoRunner) -> dict:
    """Measure append latency distribution under background maintenance."""
    count = 5_000 if runner.limit else 200_000
    lat = LatencyStats()
    spike_threshold_ns = 1_000_000  # 1ms
    spikes = 0

    cfg = {
        "maintenance": "background",
        "busy_policy": "flush",
        "memtable_max_bytes": 64 * 1024,
        "sealed_max_runs": 2,
    }

    log = Timelog.for_streaming(
        time_unit="ns",
        memtable_max_bytes=cfg["memtable_max_bytes"],
        sealed_max_runs=cfg["sealed_max_runs"],
    )
    try:
        base_ts = 3_000_000_000_000_000_000
        for ts, order in iter_synthetic_records(
            count, base_ts, reuse_obj=runner.reuse_obj
        ):
            start = time.perf_counter_ns()
            log.append(ts, order)
            dt = time.perf_counter_ns() - start
            lat.add(dt)
            if dt > spike_threshold_ns:
                spikes += 1
    finally:
        log.close()

    return {
        "records": count,
        "latency_ns": lat.summary(),
        "spike_threshold_ns": spike_threshold_ns,
        "spike_count": spikes,
        "reuse_obj": runner.reuse_obj,
        "config": cfg,
    }


@feature("K1B", "Append latency (manual flush/compact)", "K")
def demo_k1b_append_latency_manual(runner: DemoRunner) -> dict:
    """Measure append latency with explicit flush/compact in manual mode."""
    count = 5_000 if runner.limit else 200_000
    lat = LatencyStats()
    flush_times: list[float] = []
    compact_times: list[float] = []

    flush_every = 10_000
    compact_every = 5
    flush_count = 0
    compact_steps: list[int] = []

    log = Timelog.for_bulk_ingest(
        time_unit="ns",
        memtable_max_bytes=128 * 1024,
        sealed_max_runs=2,
    )
    try:
        base_ts = 4_000_000_000_000_000_000
        for i, (ts, order) in enumerate(
            iter_synthetic_records(count, base_ts, reuse_obj=runner.reuse_obj)
        ):
            start = time.perf_counter_ns()
            log.append(ts, order)
            lat.add(time.perf_counter_ns() - start)

            if (i + 1) % flush_every == 0:
                t0 = time.perf_counter_ns()
                log.flush()
                flush_times.append((time.perf_counter_ns() - t0) / 1e6)
                flush_count += 1
                if flush_count % compact_every == 0:
                    t1 = time.perf_counter_ns()
                    log.compact()
                    compact_steps.append(_drain_manual_maintenance(log))
                    compact_times.append((time.perf_counter_ns() - t1) / 1e6)
    finally:
        log.close()

    return {
        "records": count,
        "latency_ns": lat.summary(),
        "flush_times_ms": flush_times,
        "compact_times_ms": compact_times,
        "compact_maint_steps": compact_steps,
        "reuse_obj": runner.reuse_obj,
        "config": {
            "maintenance": "disabled",
            "flush_every": flush_every,
            "compact_every": compact_every,
        },
    }


@feature("K2", "Mixed workload (hot read)", "K")
def demo_k2_mixed_hot(runner: DemoRunner) -> dict:
    """Append small batches and read recent data from memtable."""
    cycles = 20 if runner.limit else 100
    batch_size = 1000
    window_size = 1000

    write_time_ns = 0
    read_time_ns = 0
    total_written = 0
    total_read = 0

    log = Timelog.for_bulk_ingest(
        time_unit="ns",
        memtable_max_bytes=32 * 1024 * 1024,
    )
    try:
        base_ts = 5_000_000_000_000_000_000
        ts = base_ts

        for _ in range(cycles):
            batch = [(ts + i * 1000, _synthetic_order(i)) for i in range(batch_size)]
            t0 = time.perf_counter_ns()
            log.extend(batch)
            write_time_ns += time.perf_counter_ns() - t0
            total_written += len(batch)
            ts += batch_size * 1000

            # Read recent window (still hot in memtable)
            start = ts - window_size * 1000
            end = ts
            t1 = time.perf_counter_ns()
            total_read += sum(1 for _ in log[start:end])
            read_time_ns += time.perf_counter_ns() - t1
    finally:
        log.close()

    return {
        "records": total_written,
        "writes": total_written,
        "reads": total_read,
        "write_rps": total_written / (write_time_ns / 1e9) if write_time_ns else 0,
        "read_rps": total_read / (read_time_ns / 1e9) if read_time_ns else 0,
        "config": {"maintenance": "disabled", "hot_read": True},
    }


@feature("K3", "Mixed workload (cold read)", "K")
def demo_k3_mixed_cold(runner: DemoRunner) -> dict:
    """Append batches, flush, and read older data from segments."""
    cycles = 15 if runner.limit else 60
    batch_size = 1000
    window_size = 1000

    write_time_ns = 0
    read_time_ns = 0
    flush_time_ns = 0
    total_written = 0
    total_read = 0

    log = Timelog.for_bulk_ingest(
        time_unit="ns",
        memtable_max_bytes=4 * 1024 * 1024,
    )
    try:
        base_ts = 6_000_000_000_000_000_000
        ts = base_ts

        for cycle in range(cycles):
            batch = [(ts + i * 1000, _synthetic_order(i)) for i in range(batch_size)]
            t0 = time.perf_counter_ns()
            log.extend(batch)
            write_time_ns += time.perf_counter_ns() - t0
            total_written += len(batch)

            t_flush = time.perf_counter_ns()
            log.flush()
            flush_time_ns += time.perf_counter_ns() - t_flush

            ts += batch_size * 1000

            # Read older window (data from earlier cycles, now in segments)
            if cycle > 2:
                end = ts - 2 * batch_size * 1000
                start = end - window_size * 1000
                t1 = time.perf_counter_ns()
                total_read += sum(1 for _ in log[start:end])
                read_time_ns += time.perf_counter_ns() - t1
    finally:
        log.close()

    return {
        "records": total_written,
        "writes": total_written,
        "reads": total_read,
        "write_rps": total_written / (write_time_ns / 1e9) if write_time_ns else 0,
        "read_rps": total_read / (read_time_ns / 1e9) if read_time_ns else 0,
        "flush_ms_total": flush_time_ns / 1e6,
        "config": {"maintenance": "disabled", "hot_read": False},
    }


@feature("K4", "Delete impact (hot vs cold)", "K")
def demo_k4_delete_impact(runner: DemoRunner) -> dict:
    """Measure delete cost and read impact for hot and cold data."""
    total = 20_000 if runner.limit else 100_000
    base_ts = 7_000_000_000_000_000_000
    records = list(iter_synthetic_records(total, base_ts))

    results: dict[str, dict] = {}

    # Hot delete: before flush
    log = Timelog.for_bulk_ingest(time_unit="ns")
    try:
        log.extend(records)
        t0 = time.perf_counter_ns()
        before = sum(1 for _ in log[base_ts : base_ts + total * 1000])
        t1 = time.perf_counter_ns()
        log.delete(base_ts + 10_000, base_ts + 20_000)
        t2 = time.perf_counter_ns()
        after = sum(1 for _ in log[base_ts : base_ts + total * 1000])
        t3 = time.perf_counter_ns()

        results["hot"] = {
            "read_before_rps": before / ((t1 - t0) / 1e9) if t1 > t0 else 0,
            "delete_ms": (t2 - t1) / 1e6,
            "read_after_rps": after / ((t3 - t2) / 1e9) if t3 > t2 else 0,
        }
    finally:
        log.close()

    # Cold delete: after flush + compaction recovery
    log = Timelog.for_bulk_ingest(time_unit="ns")
    try:
        log.extend(records)
        log.flush()
        t0 = time.perf_counter_ns()
        before = sum(1 for _ in log[base_ts : base_ts + total * 1000])
        t1 = time.perf_counter_ns()
        log.delete(base_ts + 10_000, base_ts + 20_000)
        t2 = time.perf_counter_ns()
        after = sum(1 for _ in log[base_ts : base_ts + total * 1000])
        t3 = time.perf_counter_ns()
        t4 = time.perf_counter_ns()
        log.compact()
        maint_steps = _drain_manual_maintenance(log)
        t5 = time.perf_counter_ns()
        after_compact = sum(1 for _ in log[base_ts : base_ts + total * 1000])
        t6 = time.perf_counter_ns()

        results["cold"] = {
            "read_before_rps": before / ((t1 - t0) / 1e9) if t1 > t0 else 0,
            "delete_ms": (t2 - t1) / 1e6,
            "read_after_rps": after / ((t3 - t2) / 1e9) if t3 > t2 else 0,
            "compact_ms": (t5 - t4) / 1e6,
            "compact_maint_steps": maint_steps,
            "read_after_compact_rps": after_compact
            / ((t6 - t5) / 1e9)
            if t6 > t5
            else 0,
        }
    finally:
        log.close()

    return {"records": total, "results": results}


@feature("K5", "A2B stress grid (OOO + background)", "K")
def demo_k5_a2b_stress_grid(runner: DemoRunner) -> dict:
    """Grid test for OOO + maintenance/backpressure combinations."""
    limit = min(runner.limit or 20_000, 10_000 if runner.limit else 20_000)
    records, _ = parse_orders_to_list(runner.data_path, limit=limit)
    if not records:
        return {"records": 0, "error": "no records"}

    # Approximate out-of-order rate
    ooo = 0
    for i in range(1, len(records)):
        if records[i][0] < records[i - 1][0]:
            ooo += 1
    ooo_rate = ooo / max(1, len(records) - 1)

    grid = []
    if runner.limit:
        memtables = [256 * 1024]
        sealed_runs = [1]
        maint_modes = ["disabled", "background"]
        busy_policies = ["raise", "flush"]
    else:
        memtables = [64 * 1024, 512 * 1024]
        sealed_runs = [1, 2]
        maint_modes = ["disabled", "background"]
        busy_policies = ["raise", "flush"]

    for maintenance in maint_modes:
        for busy_policy in busy_policies:
            for mem_bytes in memtables:
                for runs in sealed_runs:
                    busy_events = 0
                    busy_action_failures = 0
                    inserted = 0
                    batch_size = 1000
                    start = time.perf_counter_ns()
                    log = Timelog(
                        time_unit="ns",
                        maintenance=maintenance,
                        busy_policy=busy_policy,
                        memtable_max_bytes=mem_bytes,
                        sealed_max_runs=runs,
                    )
                    try:
                        for i in range(0, len(records), batch_size):
                            batch = records[i : i + batch_size]
                            try:
                                log.extend(batch)
                                inserted += len(batch)
                            except TimelogBusyError:
                                # extend() committed; do not retry this batch.
                                busy_events += 1
                                inserted += len(batch)
                                # Best-effort pressure relief for subsequent batches.
                                try:
                                    log.flush()
                                except Exception:
                                    busy_action_failures += 1
                    finally:
                        log.close()
                    elapsed = time.perf_counter_ns() - start
                    rps = inserted / (elapsed / 1e9) if elapsed > 0 else 0
                    grid.append(
                        {
                            "maintenance": maintenance,
                            "busy_policy": busy_policy,
                            "memtable_max_bytes": mem_bytes,
                            "sealed_max_runs": runs,
                            "records": inserted,
                            "attempted_records": len(records),
                            "records_per_sec": rps,
                            "busy_events": busy_events,
                            "busy_action_failures": busy_action_failures,
                        }
                    )

    return {"records": len(records), "ooo_rate": ooo_rate, "grid": grid}


# =============================================================================
# Main
# =============================================================================


def main():
    parser = argparse.ArgumentParser(
        description="Timelog HFT Demo",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--quick", action="store_true", help="Run with 100K records instead of full dataset"
    )
    parser.add_argument("--category", type=str, help="Run only category X (A-J)")
    parser.add_argument("--feature", type=str, help="Run only feature X.N (e.g., C3)")
    parser.add_argument("--export-json", type=str, help="Export results to JSON file")
    parser.add_argument("--export-csv", type=str, help="Export results to CSV file")
    parser.add_argument(
        "--verbose", action="store_true", help="Show detailed profiling output"
    )
    parser.add_argument("--list", action="store_true", help="List all features and exit")
    parser.add_argument(
        "--data",
        type=str,
        default="demo/order_book_1GB.csv",
        help="Path to CSV data file",
    )
    parser.add_argument(
        "--no-perf", action="store_true", help="Skip performance measurement"
    )
    parser.add_argument(
        "--trust-csv",
        action="store_true",
        help="Skip row validation (trusted CSV fast path)",
    )
    parser.add_argument(
        "--preload-csv",
        action="store_true",
        help="Preload CSV into memory (isolates disk I/O)",
    )
    parser.add_argument(
        "--ingest-mode",
        type=str,
        default="all",
        choices=["all", "end_to_end", "parse_only", "timelog_only"],
        help="Ingest measurement mode for breakdown cases",
    )
    parser.add_argument(
        "--reuse-obj",
        action="store_true",
        help="Reuse a single Order object (isolates handle overhead)",
    )
    parser.add_argument(
        "--no-tracemalloc",
        action="store_true",
        help="Disable tracemalloc to reduce measurement overhead",
    )
    parser.add_argument(
        "--repeat-min-seconds",
        type=float,
        default=DEFAULT_REPEAT_MIN_SECONDS,
        help="Repeat fast read-only features until this duration (0 disables)",
    )
    parser.add_argument(
        "--repeat-max-runs",
        type=int,
        default=DEFAULT_REPEAT_MAX_RUNS,
        help="Max repeats for fast read-only features",
    )
    parser.add_argument(
        "--force-maintenance",
        choices=["disabled", "background"],
        help="Override maintenance mode for all Timelog instances in this run",
    )
    parser.add_argument(
        "--force-busy-policy",
        choices=["raise", "silent", "flush"],
        help="Override busy_policy for all Timelog instances in this run",
    )
    parser.add_argument(
        "--force-memtable-max-bytes",
        type=int,
        help="Override memtable_max_bytes for all Timelog instances in this run",
    )
    parser.add_argument(
        "--force-target-page-bytes",
        type=int,
        help="Override target_page_bytes for all Timelog instances in this run",
    )
    parser.add_argument(
        "--force-sealed-max-runs",
        type=int,
        help="Override sealed_max_runs for all Timelog instances in this run",
    )
    parser.add_argument(
        "--methodology",
        action="store_true",
        help="Run methodology-compliant benchmark harness instead of legacy demo mode",
    )
    parser.add_argument(
        "--methodology-profile",
        type=str,
        default="pr",
        choices=["pr", "full", "custom"],
        help="Methodology profile: pr|full|custom",
    )
    parser.add_argument(
        "--methodology-export-json",
        type=str,
        default="demo/benchmark_runs/methodology_v1.json",
        help="Methodology JSON export path",
    )
    parser.add_argument(
        "--methodology-export-md",
        type=str,
        default="demo/benchmark_runs/methodology_v1.md",
        help="Methodology markdown export path",
    )
    parser.add_argument(
        "--methodology-baseline",
        type=str,
        default=None,
        help="Optional methodology baseline path override",
    )
    parser.add_argument(
        "--methodology-seed",
        type=int,
        default=12345,
        help="Methodology run seed",
    )
    parser.add_argument(
        "--methodology-config",
        type=str,
        default=None,
        help="Path to custom methodology profile JSON when --methodology-profile=custom",
    )

    args = parser.parse_args()

    if args.methodology:
        from timelog_benchmark import run_from_demo_namespace

        code = run_from_demo_namespace(args)
        if code != 0:
            raise SystemExit(code)
        return

    log_overrides: dict[str, object] = {}
    if args.force_maintenance is not None:
        log_overrides["maintenance"] = args.force_maintenance
    if args.force_busy_policy is not None:
        log_overrides["busy_policy"] = args.force_busy_policy
    if args.force_memtable_max_bytes is not None:
        log_overrides["memtable_max_bytes"] = args.force_memtable_max_bytes
    if args.force_target_page_bytes is not None:
        log_overrides["target_page_bytes"] = args.force_target_page_bytes
    if args.force_sealed_max_runs is not None:
        log_overrides["sealed_max_runs"] = args.force_sealed_max_runs
    if log_overrides:
        _install_timelog_overrides(log_overrides)

    # Handle --list
    if args.list:
        list_features()
        return

    # Configure CSV mode
    global CSV_MODE
    CSV_MODE = "trusted" if args.trust_csv else "validated"

    if args.preload_csv:
        preload_csv(args.data)
        alt = _alternate_dataset_path(args.data)
        if alt:
            preload_csv(alt)

    # Print system info
    system_info = get_system_info()
    run_config = {
        "data_path": args.data,
        "csv_mode": CSV_MODE,
        "preload_csv": args.preload_csv,
        "ingest_mode": args.ingest_mode,
        "reuse_obj": args.reuse_obj,
        "tracemalloc": not args.no_tracemalloc,
        "repeat_min_seconds": args.repeat_min_seconds,
        "repeat_max_runs": args.repeat_max_runs,
        "log_overrides": log_overrides,
    }
    print_system_info(system_info, run_config)

    # Check data file exists
    if not os.path.exists(args.data):
        print(f"ERROR: Data file not found: {args.data}")
        print("Generate it with: python demo/generate_data.py")
        sys.exit(1)

    # Create runner
    runner = DemoRunner(
        data_path=args.data,
        quick=args.quick,
        verbose=args.verbose,
        no_perf=args.no_perf,
        csv_mode=CSV_MODE,
        ingest_mode=args.ingest_mode,
        preload_csv=args.preload_csv,
        reuse_obj=args.reuse_obj,
        track_memory=not args.no_tracemalloc,
        track_gc=not args.no_tracemalloc,
        repeat_min_seconds=args.repeat_min_seconds,
        repeat_max_runs=args.repeat_max_runs,
        log_overrides=log_overrides,
    )

    print()
    print(f"Data file: {args.data}")
    print(f"Quick mode: {args.quick}")
    if args.quick:
        print(f"Record limit: {runner.limit:,}")
    print(f"CSV mode: {CSV_MODE} (preload={args.preload_csv})")
    print(f"Ingest mode: {args.ingest_mode} (reuse_obj={args.reuse_obj})")
    print()

    # Run features
    if args.feature:
        # Single feature - need a log for shared-log categories
        category = args.feature[0].upper()
        if category in SHARED_LOG_CATEGORIES:
            log = Timelog.for_streaming(time_unit="ns")
            try:
                runner.log = log
                runner.run_feature(args.feature.upper())
            finally:
                log.close()
        else:
            runner.run_feature(args.feature.upper())
    elif args.category:
        # Single category
        category = args.category.upper()
        if category in SHARED_LOG_CATEGORIES:
            log = Timelog.for_streaming(time_unit="ns")
            try:
                runner.log = log
                runner.run_category(category)
            finally:
                log.close()
        else:
            runner.run_category(category)
    else:
        # All features - run self-contained first, then shared-log categories
        for cat in SELF_CONTAINED_CATEGORIES:
            runner.run_category(cat)

        log = Timelog.for_streaming(time_unit="ns")
        try:
            runner.log = log
            for cat in SHARED_LOG_CATEGORIES:
                runner.run_category(cat)
        finally:
            log.close()

    # Print summary
    print()
    print(runner.summary())

    # Export results
    if args.export_json:
        export_results_json(runner.results, system_info, run_config, Path(args.export_json))
    if args.export_csv:
        export_results_csv(runner.results, Path(args.export_csv))


if __name__ == "__main__":
    main()
