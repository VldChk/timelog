"""
Dataset validator for the synthetic HFT order-book CSV.

The script streams the CSV to keep memory low and reports:
* Row counts per status and aggregate totals.
* Detected data-quality glitches (missing/extra columns, empty tickers, NaNs, etc.).
* Timestamp monotonicity checks.
* Ticker ↔ ISIN consistency statistics.
* Order lifecycle validation (OPEN/PARTIAL/FILLED sequencing, volume mismatches).
* Commission distribution metrics for fills only.

Example:
    python validate_hft_dataset.py --csv order_book_10GB.csv --max-rows 2000000
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, Optional, Tuple

EXPECTED_COLUMNS = [
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

VALID_STATUSES = {"OPEN", "PARTIAL", "FILLED"}


@dataclass
class RunningStats:
    count: int = 0
    total: float = 0.0
    total_sq: float = 0.0
    min_val: Optional[float] = None
    max_val: Optional[float] = None

    def add(self, value: float) -> None:
        self.count += 1
        self.total += value
        self.total_sq += value * value
        if self.min_val is None or value < self.min_val:
            self.min_val = value
        if self.max_val is None or value > self.max_val:
            self.max_val = value

    def mean(self) -> Optional[float]:
        return self.total / self.count if self.count else None

    def stddev(self) -> Optional[float]:
        if self.count < 2:
            return None
        mean = self.total / self.count
        variance = (self.total_sq / self.count) - mean * mean
        return math.sqrt(max(variance, 0.0))


@dataclass
class OrderTrack:
    ticker: str
    isin: str
    direction: str
    open_amount: Optional[int]
    limit_price: Optional[float]
    cumulative_fill: int = 0
    last_status: str = "OPEN"


def parse_int(value: Optional[str]) -> Tuple[Optional[int], Optional[str]]:
    if value is None or value == "":
        return None, "empty"
    try:
        return int(value), None
    except ValueError:
        return None, "format"


def parse_float(value: Optional[str]) -> Tuple[Optional[float], Optional[str]]:
    if value is None or value == "":
        return None, "empty"
    try:
        result = float(value)
    except ValueError:
        return None, "format"
    if not math.isfinite(result):
        return None, "nonfinite"
    return result, None


def analyze(csv_path: Path, max_rows: Optional[int], progress_every: int) -> Dict[str, object]:
    metrics: Dict[str, object] = {}
    status_counts: Counter[str] = Counter()
    glitch_counts: Counter[str] = Counter()
    ticker_isin: Dict[str, str] = {}
    ticker_isin_conflicts: Counter[str] = Counter()
    timestamps_out_of_order = 0
    missing_columns_rows = 0
    extra_columns_rows = 0
    blank_ticker_isin_rows = 0
    bad_timestamp_rows = 0
    numeric_anomalies: Counter[str] = Counter()
    lifecycle_counts: Counter[str] = Counter()
    order_tracker: Dict[str, OrderTrack] = {}
    orphan_fill_rows = 0
    duplicate_open_rows = 0
    amount_shortfall_rows = 0
    commission_stats = RunningStats()
    amount_stats = RunningStats()

    total_rows = 0
    prev_timestamp: Optional[int] = None

    with csv_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        header = reader.fieldnames or []
        missing_header_cols = [col for col in EXPECTED_COLUMNS if col not in header]
        extra_header_cols = [col for col in header if col not in EXPECTED_COLUMNS]
        metrics["header_missing_columns"] = missing_header_cols
        metrics["header_extra_columns"] = extra_header_cols

        for row in reader:
            total_rows += 1
            if progress_every and total_rows % progress_every == 0:
                print(f"Analyzed {total_rows:,} rows...")
            if max_rows and total_rows > max_rows:
                break

            if None in row and row[None]:
                extra_columns_rows += 1

            row_missing = False
            for column in EXPECTED_COLUMNS:
                if row.get(column) is None:
                    row_missing = True
                    break
            if row_missing:
                missing_columns_rows += 1

            ticker = (row.get("ticker") or "").strip()
            isin = (row.get("isin") or "").strip()
            if not ticker and not isin:
                blank_ticker_isin_rows += 1

            if ticker and isin:
                if ticker not in ticker_isin:
                    ticker_isin[ticker] = isin
                elif ticker_isin[ticker] != isin:
                    ticker_isin_conflicts[ticker] += 1

            timestamp_value, ts_err = parse_int(row.get("timestamp"))
            if ts_err:
                bad_timestamp_rows += 1
            elif prev_timestamp is not None and timestamp_value < prev_timestamp:
                timestamps_out_of_order += 1
            else:
                prev_timestamp = timestamp_value

            status = (row.get("status") or "").upper()
            status_counts[status] += 1

            order_id = (row.get("order_id") or "").strip()

            amount_value, amount_err = parse_int(row.get("amount"))
            if amount_err:
                numeric_anomalies["amount"] += 1
            elif amount_value is not None:
                amount_stats.add(float(amount_value))
                if amount_value < 0:
                    numeric_anomalies["amount_negative"] += 1

            ask_price, ask_err = parse_float(row.get("ask_price"))
            if ask_err not in (None, "empty"):
                numeric_anomalies["ask_price"] += 1

            bid_price, bid_err = parse_float(row.get("bid_price"))
            if bid_err not in (None, "empty"):
                numeric_anomalies["bid_price"] += 1

            commission_value, commission_err = parse_float(row.get("commission"))
            if commission_err not in (None, "empty"):
                numeric_anomalies["commission"] += 1

            lifecycle_counts[f"status_{status or 'UNKNOWN'}"] += 1

            if status == "OPEN":
                if not order_id:
                    glitch_counts["open_missing_order_id"] += 1
                elif order_id in order_tracker:
                    duplicate_open_rows += 1
                else:
                    order_tracker[order_id] = OrderTrack(
                        ticker=ticker,
                        isin=isin,
                        direction=(row.get("direction") or "").upper(),
                        open_amount=amount_value,
                        limit_price=ask_price,
                        last_status="OPEN",
                    )
            elif status in {"PARTIAL", "FILLED"}:
                if commission_value is not None:
                    commission_stats.add(commission_value)
                if not order_id or order_id not in order_tracker:
                    orphan_fill_rows += 1
                else:
                    tracked = order_tracker[order_id]
                    if amount_value is not None:
                        tracked.cumulative_fill += amount_value
                    tracked.last_status = status
                    if status == "FILLED":
                        if (
                            tracked.open_amount is not None
                            and tracked.cumulative_fill != tracked.open_amount
                        ):
                            amount_shortfall_rows += 1
                        order_tracker.pop(order_id, None)
            else:
                glitch_counts["unknown_status_rows"] += 1

    metrics.update(
        {
            "total_rows": total_rows,
            "status_counts": status_counts,
            "rows_with_extra_columns": extra_columns_rows,
            "rows_missing_columns": missing_columns_rows,
            "rows_blank_ticker_isin": blank_ticker_isin_rows,
            "timestamp_regressions": timestamps_out_of_order,
            "bad_timestamp_rows": bad_timestamp_rows,
            "numeric_anomalies": numeric_anomalies,
            "ticker_isin_conflicts": ticker_isin_conflicts,
            "orphan_fill_rows": orphan_fill_rows,
            "duplicate_open_rows": duplicate_open_rows,
            "orders_left_open": len(order_tracker),
            "amount_shortfall_rows": amount_shortfall_rows,
            "glitch_counts": glitch_counts,
            "commission_stats": {
                "count": commission_stats.count,
                "mean": commission_stats.mean(),
                "stddev": commission_stats.stddev(),
                "min": commission_stats.min_val,
                "max": commission_stats.max_val,
            },
            "amount_stats": {
                "count": amount_stats.count,
                "mean": amount_stats.mean(),
                "stddev": amount_stats.stddev(),
                "min": amount_stats.min_val,
                "max": amount_stats.max_val,
            },
        }
    )
    return metrics


def format_report(result: Dict[str, object]) -> str:
    lines = []
    lines.append("=== DATASET VALIDATION REPORT ===")
    lines.append(f"Total rows analyzed: {result['total_rows']:,}")

    header_missing = result.get("header_missing_columns") or []
    header_extra = result.get("header_extra_columns") or []
    if header_missing:
        lines.append(f"Header missing columns: {header_missing}")
    if header_extra:
        lines.append(f"Header extra columns: {header_extra}")

    lines.append("\n-- Status counts --")
    for status, count in sorted(result["status_counts"].items()):
        lines.append(f"{status or 'UNKNOWN'}: {count:,}")

    lines.append("\n-- Structural issues --")
    lines.append(f"Rows with missing columns: {result['rows_missing_columns']:,}")
    lines.append(f"Rows with extra columns: {result['rows_with_extra_columns']:,}")
    lines.append(f"Rows blank ticker & isin: {result['rows_blank_ticker_isin']:,}")

    lines.append("\n-- Timestamp checks --")
    lines.append(f"Timestamps regressions: {result['timestamp_regressions']:,}")
    lines.append(f"Bad timestamp rows: {result['bad_timestamp_rows']:,}")

    lines.append("\n-- Numeric anomalies --")
    for key, value in sorted(result["numeric_anomalies"].items()):
        lines.append(f"{key}: {value:,}")

    lines.append("\n-- Ticker / ISIN consistency --")
    lines.append(f"Tickers with conflicting ISINs: {len(result['ticker_isin_conflicts'])}")

    lines.append("\n-- Order lifecycle --")
    lines.append(f"Orphan PARTIAL/FILLED rows: {result['orphan_fill_rows']:,}")
    lines.append(f"Duplicate OPEN rows: {result['duplicate_open_rows']:,}")
    lines.append(f"Orders still open at EOF: {result['orders_left_open']:,}")
    lines.append(f"Filled rows with volume shortfall: {result['amount_shortfall_rows']:,}")

    lines.append("\n-- Commission stats (fills only) --")
    cstats = result["commission_stats"]
    lines.append(f"Count: {cstats['count']:,}")
    lines.append(f"Mean: {cstats['mean']:.6f}" if cstats["mean"] is not None else "Mean: N/A")
    lines.append(
        f"Stddev: {cstats['stddev']:.6f}" if cstats["stddev"] is not None else "Stddev: N/A"
    )
    lines.append(f"Min: {cstats['min']:.6f}" if cstats["min"] is not None else "Min: N/A")
    lines.append(f"Max: {cstats['max']:.6f}" if cstats["max"] is not None else "Max: N/A")

    lines.append("\n-- Amount stats --")
    astats = result["amount_stats"]
    lines.append(f"Count: {astats['count']:,}")
    lines.append(f"Mean: {astats['mean']:.2f}" if astats["mean"] is not None else "Mean: N/A")
    lines.append(
        f"Stddev: {astats['stddev']:.2f}" if astats["stddev"] is not None else "Stddev: N/A"
    )
    lines.append(f"Min: {astats['min']:.0f}" if astats["min"] is not None else "Min: N/A")
    lines.append(f"Max: {astats['max']:.0f}" if astats["max"] is not None else "Max: N/A")

    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Validate generated HFT CSV output.")
    parser.add_argument("--csv", type=Path, required=True, help="Path to the CSV file to check.")
    parser.add_argument(
        "--max-rows",
        type=int,
        default=None,
        help="Optional limit on rows to scan (useful for quick sampling).",
    )
    parser.add_argument(
        "--progress-every",
        type=int,
        default=1_000_000,
        help="Print a progress update every N rows (0 disables).",
    )
    parser.add_argument(
        "--summary-only",
        action="store_true",
        help="Only print the summary counts, omit per-category breakdowns.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    csv_path = args.csv.resolve()
    if not csv_path.exists():
        raise FileNotFoundError(csv_path)
    result = analyze(csv_path, args.max_rows, args.progress_every)
    if args.summary_only:
        print("=== DATASET VALIDATION SUMMARY ===")
        print(f"Total rows analyzed: {result['total_rows']:,}")
        print("Status counts:")
        for status, count in sorted(result["status_counts"].items()):
            print(f"  {status or 'UNKNOWN'}: {count:,}")
        print("Missing columns rows:", result["rows_missing_columns"])
        print("Extra columns rows:", result["rows_with_extra_columns"])
        print("Timestamp regressions:", result["timestamp_regressions"])
        print("Ticker/ISIN conflicts:", len(result["ticker_isin_conflicts"]))
        print("Orphan fills:", result["orphan_fill_rows"])
        mean = result["commission_stats"]["mean"]
        print("Commission mean:", f"{mean:.6f}" if mean is not None else "N/A")
    else:
        print(format_report(result))


if __name__ == "__main__":
    main()
