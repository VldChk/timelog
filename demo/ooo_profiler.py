#!/usr/bin/env python3
"""
OOO (Out-of-Order) Profiler for Timelog A2B Investigation

This tool provides real-time profiling of Timelog ingestion performance
with focus on out-of-order timestamp handling.

Key Metrics Tracked:
- Real-time throughput (records/sec, rolling average)
- OOO rate (percentage of out-of-order timestamps per batch)
- Memory usage (RSS, tracemalloc if enabled)
- GC pressure (collections per gen)
- Batch-level latency distribution
- Background maintenance worker activity (CPU efficiency > 1.0)

Usage:
    python demo/ooo_profiler.py --dataset=more_ordered --records=1000000
    python demo/ooo_profiler.py --dataset=less_ordered --records=500000
    python demo/ooo_profiler.py --synthetic --ooo-rate=0.2 --records=500000
    python demo/ooo_profiler.py --grid  # Run OOO rate sweep
"""

from __future__ import annotations

import argparse
import csv
import gc
import io
import os
import platform
import random
import sys
import threading
import time
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterator, NamedTuple, Optional

# Add parent directory for timelog import
sys.path.insert(0, str(Path(__file__).parent.parent / "python"))

from timelog import Timelog, TimelogBusyError

# =============================================================================
# Configuration
# =============================================================================

BATCH_SIZE = 10_000  # Records per batch
REPORT_INTERVAL_SEC = 5.0  # Print stats every N seconds
ROLLING_WINDOW_BATCHES = 20  # Batches for rolling average

# Dataset paths
DATA_DIR = Path(__file__).parent
MORE_ORDERED_CSV = DATA_DIR / "order_book_more_ordered_clean.csv"
LESS_ORDERED_CSV = DATA_DIR / "order_book_less_ordered_clean.csv"
TINY_MORE_ORDERED = DATA_DIR / "tiny_order_book_mostly_ordered_clean.csv"
TINY_LESS_ORDERED = DATA_DIR / "tiny_order_book_less_ordered_clean.csv"

# =============================================================================
# Data Structures
# =============================================================================


class Order(NamedTuple):
    """Minimal order for testing."""
    ticker: str
    order_id: int


@dataclass
class BatchStats:
    """Statistics for a single batch."""
    batch_id: int
    records: int
    wall_ns: int
    ooo_count: int
    ooo_rate: float
    memory_mb: float
    is_slow: bool = False  # Batch took >10x expected time

    @property
    def records_per_sec(self) -> float:
        if self.wall_ns <= 0:
            return 0.0
        return self.records * 1e9 / self.wall_ns

    @property
    def wall_ms(self) -> float:
        return self.wall_ns / 1e6


@dataclass
class ProfilerState:
    """Mutable profiler state for real-time tracking."""
    start_time_ns: int = 0
    total_records: int = 0
    total_ooo_adjacent: int = 0
    total_ooo_global: int = 0
    batch_history: deque = field(default_factory=lambda: deque(maxlen=ROLLING_WINDOW_BATCHES))
    gc_baseline: tuple[int, int, int] = (0, 0, 0)
    last_report_time: float = 0.0
    last_ts: int = 0  # For OOO detection
    max_ts: int = 0  # For global OOO detection
    phase: str = "init"
    # Detailed timing tracking
    all_batch_times_ms: list = field(default_factory=list)
    slow_batch_count: int = 0
    slow_batch_total_ms: float = 0.0
    fast_batch_median_ns: int = 0  # Baseline for "slow" detection
    busy_events: int = 0
    flush_times_ms: list = field(default_factory=list)

    def rolling_rps(self) -> float:
        """Calculate rolling average records/sec from recent batches."""
        if not self.batch_history:
            return 0.0
        total_records = sum(b.records for b in self.batch_history)
        total_ns = sum(b.wall_ns for b in self.batch_history)
        if total_ns <= 0:
            return 0.0
        return total_records * 1e9 / total_ns

    def overall_ooo_rate(self) -> float:
        """Overall OOO rate across all records."""
        if self.total_records <= 0:
            return 0.0
        return self.total_ooo_global / self.total_records

    def adjacent_ooo_rate(self) -> float:
        """Adjacent inversion rate (ts < previous)."""
        if self.total_records <= 0:
            return 0.0
        return self.total_ooo_adjacent / self.total_records


# =============================================================================
# Display Functions
# =============================================================================


def clear_line():
    """Clear current terminal line."""
    print("\r" + " " * 120 + "\r", end="", flush=True)


def format_rate(rps: float) -> str:
    """Format records/sec with appropriate suffix."""
    if rps >= 1_000_000:
        return f"{rps/1_000_000:.2f}M"
    elif rps >= 1_000:
        return f"{rps/1_000:.1f}K"
    else:
        return f"{rps:.0f}"


def format_memory(mb: float) -> str:
    """Format memory with appropriate suffix."""
    if mb >= 1024:
        return f"{mb/1024:.2f}GB"
    else:
        return f"{mb:.1f}MB"


def get_memory_rss_mb() -> float:
    """Get current process RSS memory in MB."""
    try:
        import psutil
        return psutil.Process().memory_info().rss / (1024 * 1024)
    except ImportError:
        return 0.0


def get_gc_counts() -> tuple[int, int, int]:
    """Get cumulative GC collection counts."""
    stats = gc.get_stats()
    return (stats[0]["collections"], stats[1]["collections"], stats[2]["collections"])


def print_header():
    """Print profiler header."""
    print("=" * 100)
    print("TIMELOG OOO PROFILER - Real-time Ingestion Analysis")
    print("=" * 100)
    print(f"Python: {platform.python_version()}")
    print(f"Platform: {platform.platform()}")
    print(f"CPU cores: {os.cpu_count()}")
    print("=" * 100)
    print()


def print_stats_line(state: ProfilerState, current_batch: Optional[BatchStats] = None):
    """Print single-line real-time stats."""
    elapsed = (time.perf_counter_ns() - state.start_time_ns) / 1e9
    rolling_rps = state.rolling_rps()
    overall_rps = state.total_records / elapsed if elapsed > 0 else 0
    ooo_pct = state.overall_ooo_rate() * 100
    ooo_adj_pct = state.adjacent_ooo_rate() * 100

    gc_now = get_gc_counts()
    gc_delta = (
        gc_now[0] - state.gc_baseline[0],
        gc_now[1] - state.gc_baseline[1],
        gc_now[2] - state.gc_baseline[2],
    )

    mem_mb = get_memory_rss_mb()

    batch_rps = ""
    slow_marker = ""
    if current_batch:
        batch_rps = f" | batch: {format_rate(current_batch.records_per_sec)}/s"
        if current_batch.is_slow:
            slow_marker = f" [SLOW: {current_batch.wall_ms:.0f}ms]"

    clear_line()
    print(
        f"[{elapsed:6.1f}s] "
        f"rec: {state.total_records:>10,} | "
        f"rps: {format_rate(rolling_rps):>7}/s (avg: {format_rate(overall_rps):>7}/s){batch_rps} | "
        f"OOO: {ooo_pct:5.2f}% (adj {ooo_adj_pct:5.2f}%) | "
        f"busy: {state.busy_events:>5} | "
        f"slow: {state.slow_batch_count:>3} | "
        f"GC: {gc_delta[0]}/{gc_delta[1]}/{gc_delta[2]}{slow_marker}",
        end="", flush=True
    )


def print_phase_summary(state: ProfilerState, phase_name: str, records: int, wall_sec: float):
    """Print summary for a completed phase."""
    print()  # Newline after real-time line
    print()
    print("-" * 80)
    print(f"PHASE COMPLETE: {phase_name}")
    print("-" * 80)

    rps = records / wall_sec if wall_sec > 0 else 0
    ooo_pct = state.overall_ooo_rate() * 100
    ooo_adj_pct = state.adjacent_ooo_rate() * 100

    gc_now = get_gc_counts()
    gc_delta = (
        gc_now[0] - state.gc_baseline[0],
        gc_now[1] - state.gc_baseline[1],
        gc_now[2] - state.gc_baseline[2],
    )

    print(f"  Records:     {records:>12,}")
    print(f"  Wall time:   {wall_sec:>12.2f}s")
    print(f"  Throughput:  {format_rate(rps):>12}/s")
    print(f"  OOO rate:    {ooo_pct:>12.2f}% (adjacent {ooo_adj_pct:.2f}%)")
    if state.busy_events:
        print(f"  Busy events: {state.busy_events:>12}")
    print(f"  Memory RSS:  {format_memory(get_memory_rss_mb()):>12}")
    print(f"  GC (g0/g1/g2): {gc_delta[0]:>4} / {gc_delta[1]:>4} / {gc_delta[2]:>4}")

    # Batch timing analysis
    if state.all_batch_times_ms:
        times = sorted(state.all_batch_times_ms)
        n = len(times)
        p50 = times[int(n * 0.50)]
        p95 = times[int(n * 0.95)]
        p99 = times[int(n * 0.99)]
        max_ms = times[-1]
        min_ms = times[0]

        print()
        print("  BATCH TIMING (per 10K records):")
        print(f"    Batches:    {n:>8}")
        print(f"    Min:        {min_ms:>8.1f} ms")
        print(f"    p50:        {p50:>8.1f} ms")
        print(f"    p95:        {p95:>8.1f} ms")
        print(f"    p99:        {p99:>8.1f} ms")
        print(f"    Max:        {max_ms:>8.1f} ms")

        if state.slow_batch_count > 0:
            slow_pct = 100.0 * state.slow_batch_count / n
            slow_time_pct = 100.0 * state.slow_batch_total_ms / (wall_sec * 1000)
            print()
            print(f"  SLOW BATCHES (>10x median):")
            print(f"    Count:      {state.slow_batch_count:>8} ({slow_pct:.1f}% of batches)")
            print(f"    Time spent: {state.slow_batch_total_ms:>8.0f} ms ({slow_time_pct:.1f}% of total)")

    if state.flush_times_ms:
        times = sorted(state.flush_times_ms)
        n = len(times)
        p50 = times[int(n * 0.50)]
        p95 = times[int(n * 0.95)]
        p99 = times[int(n * 0.99)]
        print()
        print("  FLUSH TIMING:")
        print(f"    Flushes:    {n:>8}")
        print(f"    p50:        {p50:>8.1f} ms")
        print(f"    p95:        {p95:>8.1f} ms")
        print(f"    p99:        {p99:>8.1f} ms")

    print("-" * 80)
    print()


# =============================================================================
# Data Loading
# =============================================================================


def load_csv_streaming(path: Path, limit: int = 0) -> Iterator[tuple[int, Order]]:
    """Stream records from CSV file."""
    count = 0
    with open(path, "r", newline="") as f:
        reader = csv.reader(f)
        header = next(reader)

        # Find column indices
        ts_idx = header.index("timestamp")
        ticker_idx = header.index("ticker")
        oid_idx = header.index("order_id")

        for row in reader:
            ts = int(row[ts_idx])
            order = Order(ticker=row[ticker_idx], order_id=int(row[oid_idx]))
            yield ts, order
            count += 1
            if limit > 0 and count >= limit:
                break


def generate_synthetic(
    count: int,
    ooo_rate: float = 0.0,
    base_ts: int = 1609459200_000_000_000,  # 2021-01-01
    step_ns: int = 1000,
    jitter_ns: int = 100_000_000,  # 100ms jitter for OOO
) -> Iterator[tuple[int, Order]]:
    """
    Generate synthetic records with controllable OOO rate.

    Args:
        count: Number of records to generate
        ooo_rate: Fraction of records to make out-of-order (0.0-1.0)
        base_ts: Starting timestamp
        step_ns: Nominal timestamp step
        jitter_ns: How far back OOO records can go
    """
    prev_ts = base_ts
    for i in range(count):
        if random.random() < ooo_rate:
            # Out-of-order: go back in time
            ts = prev_ts - random.randint(1, jitter_ns)
        else:
            # In-order: advance
            ts = prev_ts + step_ns

        prev_ts = max(prev_ts, ts)  # Track max for next iteration
        order = Order(ticker="SYN", order_id=i)
        yield ts, order


# =============================================================================
# Profiling Core
# =============================================================================


def profile_ingestion(
    log: Timelog,
    records_iter: Iterator[tuple[int, Order]],
    state: ProfilerState,
    batch_size: int = BATCH_SIZE,
    report_interval: float = REPORT_INTERVAL_SEC,
    flush_interval: int = 0,  # Flush every N batches (0=never)
    allow_busy_exceptions: bool = False,
) -> int:
    """
    Profile ingestion with real-time stats.

    Args:
        log: Timelog instance
        records_iter: Iterator of (timestamp, Order) tuples
        state: ProfilerState for tracking
        batch_size: Records per batch
        report_interval: Seconds between status updates
        flush_interval: Batches between manual flush calls (0=disabled)

    Returns total records processed.
    """
    state.start_time_ns = time.perf_counter_ns()
    state.gc_baseline = get_gc_counts()
    state.last_report_time = time.time()

    batch: list[tuple[int, Order]] = []
    batch_id = 0
    total = 0

    for ts, order in records_iter:
        batch.append((ts, order))

        # Detect OOO
        if state.max_ts == 0:
            state.max_ts = ts
        if ts < state.last_ts:
            state.total_ooo_adjacent += 1
        if ts < state.max_ts:
            state.total_ooo_global += 1
        else:
            state.max_ts = ts
        state.last_ts = ts

        if len(batch) >= batch_size:
            # Process batch
            batch_start = time.perf_counter_ns()
            try:
                log.extend(batch)
            except TimelogBusyError:
                state.busy_events += 1
                if allow_busy_exceptions:
                    raise
                # Record inserted; flush to relieve pressure and continue.
                flush_start = time.perf_counter_ns()
                log.flush()
                flush_end = time.perf_counter_ns()
                state.flush_times_ms.append((flush_end - flush_start) / 1e6)
            batch_end = time.perf_counter_ns()

            # Calculate batch OOO
            batch_ooo = 0
            prev = 0
            for bts, _ in batch:
                if bts < prev:
                    batch_ooo += 1
                prev = bts

            batch_wall_ns = batch_end - batch_start
            batch_wall_ms = batch_wall_ns / 1e6

            # Track batch timing
            state.all_batch_times_ms.append(batch_wall_ms)

            # Determine if this is a "slow" batch (>10x the current median)
            # Use first 10 batches to establish baseline
            is_slow = False
            if batch_id >= 10:
                if state.fast_batch_median_ns == 0:
                    # Calculate initial baseline from first 10 batches
                    sorted_times = sorted(state.all_batch_times_ms[:10])
                    state.fast_batch_median_ns = int(sorted_times[5] * 1e6)  # median in ns

                if batch_wall_ns > state.fast_batch_median_ns * 10:
                    is_slow = True
                    state.slow_batch_count += 1
                    state.slow_batch_total_ms += batch_wall_ms

            batch_stats = BatchStats(
                batch_id=batch_id,
                records=len(batch),
                wall_ns=batch_wall_ns,
                ooo_count=batch_ooo,
                ooo_rate=batch_ooo / len(batch) if batch else 0,
                memory_mb=get_memory_rss_mb(),
                is_slow=is_slow,
            )

            state.batch_history.append(batch_stats)
            state.total_records += len(batch)
            total += len(batch)
            batch_id += 1
            batch.clear()

            # Manual flush at interval
            if flush_interval > 0 and batch_id % flush_interval == 0:
                flush_start = time.perf_counter_ns()
                log.flush()
                flush_end = time.perf_counter_ns()
                state.flush_times_ms.append((flush_end - flush_start) / 1e6)

            # Report periodically
            now = time.time()
            if now - state.last_report_time >= report_interval:
                print_stats_line(state, batch_stats)
                state.last_report_time = now

    # Final partial batch
    if batch:
        batch_start = time.perf_counter_ns()
        log.extend(batch)
        batch_end = time.perf_counter_ns()

        state.total_records += len(batch)
        total += len(batch)
        batch.clear()

    return total


# =============================================================================
# Investigation Modes
# =============================================================================


def investigate_dataset(
    dataset: str,
    record_limit: int,
    use_tiny: bool = False,
    maintenance_mode: str = "background",
    busy_policy: str = "flush",
) -> None:
    """Profile ingestion on a real dataset."""

    if dataset == "more_ordered":
        path = TINY_MORE_ORDERED if use_tiny else MORE_ORDERED_CSV
        name = "More Ordered"
    elif dataset == "less_ordered":
        path = TINY_LESS_ORDERED if use_tiny else LESS_ORDERED_CSV
        name = "Less Ordered"
    else:
        raise ValueError(f"Unknown dataset: {dataset}")

    maint_label = f" [maint={maintenance_mode}]" if maintenance_mode != "background" else ""
    print(f"\n{'='*80}")
    print(f"INVESTIGATION: {name} Dataset{maint_label}")
    print(f"{'='*80}")
    print(f"  Source: {path}")
    print(f"  Limit:  {record_limit:,} records")
    print(f"  Maintenance: {maintenance_mode}")
    print(f"  Busy policy: {busy_policy}")
    print()

    state = ProfilerState(phase=f"{dataset}_ingest")

    with Timelog(time_unit="ns", maintenance=maintenance_mode, busy_policy=busy_policy) as log:
        records_iter = load_csv_streaming(path, limit=record_limit)

        start = time.perf_counter_ns()
        total = profile_ingestion(log, records_iter, state)
        elapsed = (time.perf_counter_ns() - start) / 1e9

        print_phase_summary(state, f"{name}{maint_label}", total, elapsed)

        # Let maintenance catch up
        if maintenance_mode == "background":
            print("  Waiting for maintenance to settle (5s)...")
            time.sleep(5.0)
        print(f"  Final memory: {format_memory(get_memory_rss_mb())}")


def investigate_synthetic_ooo(
    ooo_rate: float,
    record_count: int,
    busy_policy: str = "flush",
) -> dict:
    """
    Profile synthetic data with specific OOO rate.

    Returns metrics dict for grid analysis.
    """
    print(f"\n{'='*80}")
    print(f"SYNTHETIC OOO TEST: {ooo_rate*100:.1f}% out-of-order")
    print(f"{'='*80}")
    print(f"  Records: {record_count:,}")
    print()

    state = ProfilerState(phase=f"synthetic_ooo_{ooo_rate:.2f}")

    with Timelog(time_unit="ns", maintenance="background", busy_policy=busy_policy) as log:
        records_iter = generate_synthetic(record_count, ooo_rate=ooo_rate)

        start = time.perf_counter_ns()
        total = profile_ingestion(log, records_iter, state)
        elapsed = (time.perf_counter_ns() - start) / 1e9

        print_phase_summary(state, f"OOO {ooo_rate*100:.1f}%", total, elapsed)

        rps = total / elapsed if elapsed > 0 else 0
        return {
            "ooo_rate": ooo_rate,
            "records": total,
            "wall_sec": elapsed,
            "rps": rps,
            "memory_mb": get_memory_rss_mb(),
        }


def run_ooo_grid(record_count: int = 500_000) -> None:
    """
    Run OOO rate sweep to find performance boundaries.

    Tests OOO rates from 0% to 50% in increments.
    """
    print("\n" + "=" * 100)
    print("OOO RATE GRID SWEEP")
    print("=" * 100)
    print(f"Testing {record_count:,} records at various OOO rates")
    print()

    # OOO rates to test
    rates = [0.0, 0.01, 0.02, 0.05, 0.10, 0.15, 0.20, 0.30, 0.40, 0.50]

    results = []
    for rate in rates:
        gc.collect()
        gc.collect()
        gc.collect()
        time.sleep(1.0)  # Let system settle

        result = investigate_synthetic_ooo(rate, record_count, busy_policy="flush")
        results.append(result)

    # Print summary table
    print("\n" + "=" * 100)
    print("GRID RESULTS SUMMARY")
    print("=" * 100)
    print(f"{'OOO Rate':>10} {'Records':>12} {'Wall (s)':>10} {'RPS':>12} {'Memory':>10} {'vs 0% OOO':>10}")
    print("-" * 100)

    baseline_rps = results[0]["rps"] if results else 0

    for r in results:
        ratio = r["rps"] / baseline_rps if baseline_rps > 0 else 0
        print(
            f"{r['ooo_rate']*100:>9.1f}% "
            f"{r['records']:>12,} "
            f"{r['wall_sec']:>10.2f} "
            f"{format_rate(r['rps']):>12}/s "
            f"{format_memory(r['memory_mb']):>10} "
            f"{ratio:>9.1%}"
        )

    print("=" * 100)


def compare_datasets(record_limit: int, use_tiny: bool = False) -> None:
    """
    Run side-by-side comparison of ordered vs less-ordered datasets.
    """
    print("\n" + "=" * 100)
    print("DATASET COMPARISON: Ordered vs Less-Ordered")
    print("=" * 100)

    # Test more ordered
    gc.collect()
    gc.collect()
    gc.collect()
    investigate_dataset("more_ordered", record_limit, use_tiny=use_tiny, busy_policy="flush")

    # Test less ordered
    gc.collect()
    gc.collect()
    gc.collect()
    time.sleep(2.0)
    investigate_dataset("less_ordered", record_limit, use_tiny=use_tiny, busy_policy="flush")


def investigate_maintenance_impact(record_limit: int, use_tiny: bool = False) -> None:
    """
    Compare background vs manual-flush maintenance to isolate slow batch source.
    """
    print("\n" + "=" * 100)
    print("MAINTENANCE IMPACT ANALYSIS")
    print("=" * 100)
    print(f"Records: {record_limit:,}")
    print()
    print("This test compares less-ordered ingestion with different maintenance modes")
    print("to determine the source of slow batches:")
    print("  1. Background maintenance (async flush/compact)")
    print("  2. Manual flush every 5 batches (explicit flush timing visible)")
    print()

    # Test with background maintenance
    gc.collect()
    gc.collect()
    gc.collect()
    investigate_dataset("less_ordered", record_limit, use_tiny=use_tiny, maintenance_mode="background", busy_policy="flush")

    # Test with manual flush (disabled background, explicit flush every 20 batches)
    gc.collect()
    gc.collect()
    gc.collect()
    time.sleep(2.0)
    investigate_dataset_with_manual_flush("less_ordered", record_limit, use_tiny=use_tiny, flush_interval=5)

    print()
    print("=" * 100)
    print("ANALYSIS:")
    print("  If manual-flush mode shows similar slow batches concentrated at flush points,")
    print("  then flush operations themselves are the bottleneck.")
    print("  If background mode shows MORE slow batches spread throughout,")
    print("  then concurrent flush/compact is contending with ingestion.")
    print("=" * 100)


def investigate_dataset_with_manual_flush(
    dataset: str,
    record_limit: int,
    use_tiny: bool = False,
    flush_interval: int = 5,
) -> None:
    """Profile ingestion with manual flush at specified interval."""

    if dataset == "more_ordered":
        path = TINY_MORE_ORDERED if use_tiny else MORE_ORDERED_CSV
        name = "More Ordered"
    elif dataset == "less_ordered":
        path = TINY_LESS_ORDERED if use_tiny else LESS_ORDERED_CSV
        name = "Less Ordered"
    else:
        raise ValueError(f"Unknown dataset: {dataset}")

    print(f"\n{'='*80}")
    print(f"INVESTIGATION: {name} Dataset [busy_policy=flush, no background maint]")
    print(f"{'='*80}")
    print(f"  Source: {path}")
    print(f"  Limit:  {record_limit:,} records")
    print(f"  Mode: Synchronous flush on backpressure + manual flush every {flush_interval} batches")
    print()

    state = ProfilerState(phase=f"{dataset}_sync_flush")

    # Use busy_policy="flush" to automatically flush when backpressure hits
    with Timelog(time_unit="ns", maintenance="disabled", busy_policy="flush") as log:
        records_iter = load_csv_streaming(path, limit=record_limit)

        start = time.perf_counter_ns()
        total = profile_ingestion(
            log,
            records_iter,
            state,
            flush_interval=flush_interval,
        )
        elapsed = (time.perf_counter_ns() - start) / 1e9

        print_phase_summary(state, f"{name} [sync-flush]", total, elapsed)
        print(f"  Final memory: {format_memory(get_memory_rss_mb())}")


def continuous_monitor(
    dataset: str,
    duration_sec: float = 900.0,  # 15 minutes
    use_tiny: bool = False,
) -> None:
    """
    Run continuous ingestion with detailed monitoring for specified duration.

    This mode loops through the dataset as needed to fill the time window,
    providing long-term behavior observation.
    """
    print("\n" + "=" * 100)
    print(f"CONTINUOUS MONITORING MODE ({duration_sec/60:.0f} minutes)")
    print("=" * 100)

    if dataset == "more_ordered":
        path = TINY_MORE_ORDERED if use_tiny else MORE_ORDERED_CSV
        name = "More Ordered"
    else:
        path = TINY_LESS_ORDERED if use_tiny else LESS_ORDERED_CSV
        name = "Less Ordered"

    print(f"  Dataset: {name}")
    print(f"  Source:  {path}")
    print(f"  Duration: {duration_sec:.0f} seconds")
    print()
    print("Press Ctrl+C to stop early")
    print()

    state = ProfilerState(phase=f"continuous_{dataset}")

    overall_start = time.perf_counter_ns()
    deadline = time.time() + duration_sec

    with Timelog(time_unit="ns", maintenance="background", busy_policy="flush") as log:
        pass_num = 0

        try:
            while time.time() < deadline:
                pass_num += 1
                print(f"\n--- Pass {pass_num} ---")

                records_iter = load_csv_streaming(path, limit=0)  # Full pass

                pass_start = time.perf_counter_ns()
                total = profile_ingestion(
                    log, records_iter, state,
                    report_interval=2.0,  # More frequent updates
                )
                pass_elapsed = (time.perf_counter_ns() - pass_start) / 1e9

                # Brief summary per pass
                rps = total / pass_elapsed if pass_elapsed > 0 else 0
                print()
                print(f"  Pass {pass_num}: {total:,} records in {pass_elapsed:.1f}s ({format_rate(rps)}/s)")

                # Check if we're past deadline
                if time.time() >= deadline:
                    break

                # Brief pause between passes
                time.sleep(1.0)

        except KeyboardInterrupt:
            print("\n\nStopped by user.")

        overall_elapsed = (time.perf_counter_ns() - overall_start) / 1e9

        print()
        print("=" * 100)
        print("CONTINUOUS MONITORING COMPLETE")
        print("=" * 100)
        print(f"  Total time:   {overall_elapsed:.1f}s ({overall_elapsed/60:.1f} minutes)")
        print(f"  Total records: {state.total_records:,}")
        print(f"  Overall RPS:  {format_rate(state.total_records / overall_elapsed)}/s")
        print(f"  Overall OOO:  {state.overall_ooo_rate()*100:.2f}%")
        print(f"  Final memory: {format_memory(get_memory_rss_mb())}")
        print(f"  Passes:       {pass_num}")
        print("=" * 100)


# =============================================================================
# Main
# =============================================================================


def main():
    parser = argparse.ArgumentParser(
        description="OOO Profiler for Timelog A2B Investigation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Compare ordered vs less-ordered (500K records)
  python demo/ooo_profiler.py --compare --records=500000

  # Profile specific dataset
  python demo/ooo_profiler.py --dataset=less_ordered --records=1000000

  # Run OOO rate grid sweep
  python demo/ooo_profiler.py --grid --records=200000

  # Continuous monitoring for 15 minutes
  python demo/ooo_profiler.py --monitor --dataset=less_ordered --duration=900

  # Synthetic with specific OOO rate
  python demo/ooo_profiler.py --synthetic --ooo-rate=0.15 --records=500000
        """,
    )

    parser.add_argument(
        "--dataset", choices=["more_ordered", "less_ordered"],
        help="Dataset to profile",
    )
    parser.add_argument(
        "--records", type=int, default=500_000,
        help="Number of records to process (default: 500000)",
    )
    parser.add_argument(
        "--tiny", action="store_true",
        help="Use tiny dataset variants (faster, ~1.5M records max)",
    )
    parser.add_argument(
        "--compare", action="store_true",
        help="Compare ordered vs less-ordered datasets",
    )
    parser.add_argument(
        "--grid", action="store_true",
        help="Run OOO rate grid sweep",
    )
    parser.add_argument(
        "--synthetic", action="store_true",
        help="Use synthetic data with controlled OOO rate",
    )
    parser.add_argument(
        "--ooo-rate", type=float, default=0.1,
        help="OOO rate for synthetic mode (default: 0.1)",
    )
    parser.add_argument(
        "--monitor", action="store_true",
        help="Continuous monitoring mode",
    )
    parser.add_argument(
        "--duration", type=float, default=900.0,
        help="Duration for continuous monitoring in seconds (default: 900 = 15 min)",
    )
    parser.add_argument(
        "--maint-impact", action="store_true",
        help="Compare background vs disabled maintenance to isolate slow batch source",
    )
    parser.add_argument(
        "--busy-policy",
        choices=["raise", "silent", "flush"],
        default="flush",
        help="Backpressure policy for profiling runs (default: flush)",
    )

    args = parser.parse_args()

    print_header()

    if args.grid:
        run_ooo_grid(args.records)
    elif args.compare:
        compare_datasets(args.records, use_tiny=args.tiny)
    elif args.maint_impact:
        investigate_maintenance_impact(args.records, use_tiny=args.tiny)
    elif args.synthetic:
        investigate_synthetic_ooo(args.ooo_rate, args.records, busy_policy=args.busy_policy)
    elif args.monitor:
        dataset = args.dataset or "less_ordered"
        continuous_monitor(dataset, args.duration, use_tiny=args.tiny)
    elif args.dataset:
        investigate_dataset(args.dataset, args.records, use_tiny=args.tiny, busy_policy=args.busy_policy)
    else:
        # Default: quick comparison
        print("No mode specified. Running quick comparison (100K records each)...")
        compare_datasets(100_000, use_tiny=True)


if __name__ == "__main__":
    main()
