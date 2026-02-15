"""
High-frequency order book simulator that writes a ~10GB CSV with mostly clean data,
occasional glitches, and realistic ticker/ISIN relationships derived from real
NASDAQ + NYSE universes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

COLUMNS = [
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

NUMERIC_COLUMNS = {"amount", "ask_price", "bid_price", "commission"}
STRING_COLUMNS = {"ticker", "isin", "direction", "status"}

DEFAULT_ROWS = 150_000_000  # ~10GB depending on glitch frequency and row width
DEFAULT_OUTPUT = Path("order_book_10GB.csv")
DEFAULT_START_TIMESTAMP = 1_609_459_200_000_000_000  # 2021-01-01 00:00:00 UTC (ns)
DEFAULT_FLUSH_EVERY = 1_000_000
DEFAULT_LOG_INTERVAL = 5_000_000
TARGET_TICKER_COUNT = 1_000

DATA_FILES = (
    Path(__file__).resolve().parent / "data" / "nasdaq_full_tickers.json",
    Path(__file__).resolve().parent / "data" / "nyse_full_tickers.json",
)

GLITCH_PROBABILITIES = {
    "missing_column": 0.0005,
    "bad_character": 0.0005,
    "bad_numeric": 0.0005,
    "timestamp_break": 0.0005,
    "empty_ticker_isin": 0.0005,
    "ticker_isin_mismatch": 0.0005,
    "skip_open_order": 0.0005,
    "skip_final_fill": 0.0005,
    "short_final_fill": 0.0005,
}


@dataclass(frozen=True)
class TickerMeta:
    symbol: str
    isin: str
    base_price: float


@dataclass
class OrderState:
    symbol: str
    isin: str
    direction: str
    initial_amount: int
    remaining: int
    limit_price: float


def parse_price(value: str | float | int | None) -> float | None:
    """Convert the NASDAQ/NYSE last sale field into a float (None if missing)."""
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value) if value > 0 else None
    cleaned = value.strip().replace("$", "").replace(",", "")
    if not cleaned or cleaned.upper() in {"N/A", "NA", "-", "NULL"}:
        return None
    try:
        price = float(cleaned)
    except ValueError:
        return None
    return price if price > 0 else None


def build_isin(symbol: str) -> str:
    """Generate a deterministic pseudo-ISIN for the supplied ticker symbol."""
    digest = hashlib.sha256(symbol.encode("utf-8")).hexdigest()
    country_codes = ["US", "CA", "GB", "FR", "DE", "JP"]
    country = country_codes[int(digest[:2], 16) % len(country_codes)]
    digits = "".join(str(int(digest[i : i + 2], 16) % 10) for i in range(2, 20, 2))
    check_digit = str(int(digest[20:22], 16) % 10)
    return country + digits[:9] + check_digit


def load_price_map(paths: Sequence[Path]) -> Dict[str, float]:
    """Load ticker -> closing price from the supplied JSON files."""
    price_by_symbol: Dict[str, float] = {}
    for path in paths:
        with path.open("r", encoding="utf-8") as handle:
            payload = json.load(handle)
        for entry in payload:
            symbol = str(entry.get("symbol", "")).strip().upper()
            price = parse_price(entry.get("lastsale"))
            if not symbol or price is None:
                continue
            price_by_symbol[symbol] = price
    return price_by_symbol


def select_tickers(
    price_map: Dict[str, float], ticker_count: int, rng: random.Random
) -> List[TickerMeta]:
    """Pick the requested number of tickers and attach deterministic ISINs."""
    if len(price_map) < ticker_count:
        raise ValueError(
            f"Not enough tickers available ({len(price_map)}) to pick {ticker_count} unique symbols."
        )
    symbols = rng.sample(list(price_map.keys()), ticker_count)
    return [
        TickerMeta(symbol=s, isin=build_isin(s), base_price=price_map[s])
        for s in symbols
    ]


class OrderBookGenerator:
    """Stateful generator that produces realistic order book events."""

    def __init__(
        self,
        tickers: Sequence[TickerMeta],
        num_lines: int,
        output_path: Path,
        glitch_probs: Dict[str, float],
        rng: random.Random,
        flush_every: int,
        start_timestamp: int,
        log_interval: int,
    ) -> None:
        self.tickers = list(tickers)
        self.num_lines = num_lines
        self.output_path = output_path
        self.glitch_probs = glitch_probs
        self.rng = rng
        self.flush_every = max(1, flush_every)
        self.last_timestamp = start_timestamp
        self.log_interval = log_interval
        self.price_state: Dict[str, float] = {
            ticker.symbol: ticker.base_price for ticker in self.tickers
        }
        self.orders: Dict[int, OrderState] = {}
        self.next_order_id = 1

    def generate(self) -> None:
        """Stream rows to disk until the requested line count is reached."""
        self.output_path.parent.mkdir(parents=True, exist_ok=True)
        emitted = 0
        buffer: List[str] = []
        with self.output_path.open("w", buffering=1024 * 1024, encoding="utf-8") as fh:
            fh.write(",".join(COLUMNS) + "\n")
            while emitted < self.num_lines:
                row = self._next_event_row()
                if row is None:
                    continue
                buffer.append(row)
                emitted += 1
                if self.log_interval and emitted % self.log_interval == 0:
                    print(f"Emitted {emitted:,} rows...")
                if len(buffer) >= self.flush_every:
                    fh.write("\n".join(buffer) + "\n")
                    buffer.clear()
            if buffer:
                fh.write("\n".join(buffer) + "\n")

    def _next_event_row(self) -> str | None:
        if not self.orders:
            return self._open_order_event()

        # Bias towards fills so book doesn't explode while still keeping new orders flowing.
        order_pressure = min(0.95, 0.4 + len(self.orders) / 500)
        if self.rng.random() < order_pressure:
            return self._fill_order_event()
        return self._open_order_event()

    def _open_order_event(self) -> str | None:
        ticker = self.rng.choice(self.tickers)
        direction = "BUY" if self.rng.random() < 0.5 else "SELL"
        amount = self.rng.randint(10, 15_000)
        ask_price, bid_price = self._next_prices(ticker.symbol)
        order_id = self.next_order_id
        self.next_order_id += 1
        self.orders[order_id] = OrderState(
            symbol=ticker.symbol,
            isin=ticker.isin,
            direction=direction,
            initial_amount=amount,
            remaining=amount,
            limit_price=ask_price,
        )
        row_map = {
            "timestamp": self._next_timestamp(),
            "ticker": ticker.symbol,
            "isin": ticker.isin,
            "direction": direction,
            "status": "OPEN",
            "amount": amount,
            "ask_price": ask_price,
            "bid_price": "",
            "order_id": order_id,
            "commission": 0.0,
        }
        if self._chance("skip_open_order"):
            return None
        return self._format_row(row_map)

    def _fill_order_event(self) -> str | None:
        if not self.orders:
            return None
        order_id = self.rng.choice(tuple(self.orders.keys()))
        state = self.orders[order_id]
        market_ask, market_bid = self._next_prices(state.symbol)

        max_fill = state.remaining
        if max_fill <= 1:
            fill_amount = max_fill
        elif self.rng.random() < 0.6:
            fill_amount = self.rng.randint(1, max(1, max_fill - 1))
        else:
            fill_amount = max_fill
        fill_amount = max(1, fill_amount)
        remaining_after = max(state.remaining - fill_amount, 0)
        status = "FILLED" if remaining_after == 0 else "PARTIAL"

        if status == "FILLED" and self._chance("skip_final_fill"):
            del self.orders[order_id]
            return None

        if status == "FILLED" and self._chance("short_final_fill") and fill_amount > 0:
            reduction = self.rng.randint(1, fill_amount)
            fill_amount -= reduction
            remaining_after = 0
            status = "FILLED"

        state.remaining = remaining_after
        if state.remaining == 0:
            del self.orders[order_id]

        limit_price = state.limit_price
        execution_price = self._execution_price(state, market_ask, market_bid)
        commission = self._commission(fill_amount)
        row_map = {
            "timestamp": self._next_timestamp(),
            "ticker": state.symbol,
            "isin": state.isin,
            "direction": state.direction,
            "status": status,
            "amount": fill_amount,
            "ask_price": limit_price,
            "bid_price": execution_price,
            "order_id": order_id,
            "commission": commission,
        }
        return self._format_row(row_map)

    def _format_row(self, row_map: Dict[str, float | int | str]) -> str:
        pairs: List[Tuple[str, str]] = []
        for column in COLUMNS:
            value = row_map[column]
            if column == "timestamp":
                formatted = str(int(value))
            elif column == "amount":
                formatted = str(int(value))
            elif column in {"ask_price", "bid_price", "commission"}:
                if value == "" or value is None:
                    formatted = ""
                else:
                    formatted = f"{float(value):.6f}"
            elif column == "order_id":
                formatted = str(int(value))
            else:
                formatted = str(value)
            pairs.append((column, formatted))

        pairs = self._apply_row_glitches(pairs)
        return ",".join(value for _, value in pairs)

    def _apply_row_glitches(self, pairs: List[Tuple[str, str]]) -> List[Tuple[str, str]]:
        if self._chance("empty_ticker_isin"):
            pairs = [
                (col, "" if col in {"ticker", "isin"} else value)
                for col, value in pairs
            ]

        if self._chance("ticker_isin_mismatch"):
            isin_index = next((i for i, (c, _) in enumerate(pairs) if c == "isin"), None)
            if isin_index is not None and self.tickers:
                alt = self.rng.choice(self.tickers)
                new_isin = alt.isin
                pairs[isin_index] = ("isin", new_isin)
                if self.rng.random() < 0.3:
                    ticker_index = next(
                        (i for i, (c, _) in enumerate(pairs) if c == "ticker"), None
                    )
                    if ticker_index is not None:
                        pairs[ticker_index] = ("ticker", "")

        if self._chance("bad_numeric"):
            numeric_slots = [
                idx for idx, (col, _) in enumerate(pairs) if col in NUMERIC_COLUMNS
            ]
            if numeric_slots:
                idx = self.rng.choice(numeric_slots)
                glitch_options = ["", "-5", "NaN", "Infinity", f"-{self.rng.randint(1, 1_000_000)}"]
                pairs[idx] = (pairs[idx][0], self.rng.choice(glitch_options))

        if self._chance("bad_character"):
            str_slots = [
                idx
                for idx, (col, value) in enumerate(pairs)
                if col in STRING_COLUMNS and value
            ]
            if str_slots:
                idx = self.rng.choice(str_slots)
                value = pairs[idx][1]
                insert_at = self.rng.randint(0, len(value))
                glitchy = value[:insert_at] + ",," + value[insert_at:]
                pairs[idx] = (pairs[idx][0], glitchy)

        if self._chance("missing_column") and len(pairs) > 1:
            drop_index = self.rng.randrange(len(pairs))
            del pairs[drop_index]

        return pairs

    def _execution_price(
        self, state: OrderState, market_ask: float, market_bid: float
    ) -> float:
        limit = state.limit_price
        jitter = self.rng.uniform(-0.0003, 0.0003) * max(limit, 0.01)
        if state.direction == "BUY":
            baseline = min(limit, market_bid)
            price = max(0.01, baseline + jitter)
            return min(price, limit)
        baseline = max(limit, market_ask)
        price = baseline + abs(jitter)
        return max(price, limit)

    def _commission(self, amount: int) -> float:
        k = self.rng.uniform(0.0002, 0.001)
        scale = self.rng.uniform(0.4, 0.95)
        value = (1 - math.exp(-k * max(amount, 1))) * scale
        value = min(0.999999, value)
        return max(value, 0.000001)

    def _next_prices(self, symbol: str) -> Tuple[float, float]:
        price = self.price_state[symbol]
        drift = self.rng.uniform(-0.0005, 0.0005)
        shock = self.rng.gauss(0, 0.0015)
        price = max(0.01, price * (1 + drift + shock))
        self.price_state[symbol] = price
        spread = max(price * self.rng.uniform(0.00005, 0.0015), 0.0001)
        ask = price + spread / 2
        bid = max(0.01, price - spread / 2)
        return ask, bid

    def _next_timestamp(self) -> int:
        # Dense bursts with occasional larger gaps to mimic frantic HFT intervals.
        r = self.rng.random()
        if r < 0.6:
            gap = self.rng.randint(1, 500)  # Sub-microsecond gaps dominate.
        elif r < 0.9:
            gap = self.rng.randint(500, 200_000)
        else:
            gap = self.rng.randint(200_000, 5_000_000)  # Occasional breathing room.

        if self.rng.random() < 0.05:
            gap = max(1, gap // 10)  # Compress bursts to squeeze 1 min into ~5 mins.

        intended = self.last_timestamp + gap
        if self._chance("timestamp_break"):
            offset = self.rng.randint(1, min(500_000, intended))
            return max(0, intended - offset)
        self.last_timestamp = intended
        return intended

    def _chance(self, name: str) -> bool:
        return self.rng.random() < self.glitch_probs.get(name, 0.0)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate a synthetic HFT-scale CSV (default ~10GB) with realistic tickers, "
            "order lifecycles, and low-probability data quality issues."
        )
    )
    parser.add_argument("--rows", type=int, default=DEFAULT_ROWS, help="Number of CSV rows to emit.")
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Destination CSV file (default: order_book_10GB.csv).",
    )
    parser.add_argument(
        "--ticker-count",
        type=int,
        default=TARGET_TICKER_COUNT,
        help="Number of real tickers to sample from the exchanges (default: 1000).",
    )
    parser.add_argument(
        "--flush-every",
        type=int,
        default=DEFAULT_FLUSH_EVERY,
        help="Write buffer flush interval to balance speed vs memory.",
    )
    parser.add_argument(
        "--start-timestamp",
        type=int,
        default=DEFAULT_START_TIMESTAMP,
        help="Starting nanosecond timestamp for the stream.",
    )
    parser.add_argument(
        "--log-interval",
        type=int,
        default=DEFAULT_LOG_INTERVAL,
        help="Emit a progress log every N rows (0 disables logging).",
    )
    parser.add_argument(
        "--timestamp-break-prob",
        type=float,
        default=None,
        help=(
            "Probability that a row's timestamp goes backwards "
            "(default: uses built-in glitch probability)."
        ),
    )
    parser.add_argument(
        "--clean-rows",
        action="store_true",
        help=(
            "Disable all data glitches so every row is consistent and parsable. "
            "Use --timestamp-break-prob to re-enable out-of-order timestamps."
        ),
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=None,
        help="Optional RNG seed to reproduce the same dataset.",
    )
    parser.add_argument(
        "--data-source",
        action="append",
        dest="sources",
        default=[],
        help=(
            "Optional path(s) to additional ticker universe JSON files. When omitted, "
            "the bundled NASDAQ + NYSE files are used."
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.rows <= 0:
        raise ValueError("Number of rows must be positive.")
    if args.ticker_count <= 0:
        raise ValueError("Ticker count must be positive.")
    if args.timestamp_break_prob is not None and not (0 <= args.timestamp_break_prob <= 1):
        raise ValueError("timestamp-break-prob must be between 0 and 1.")

    rng = random.Random(args.seed)

    source_paths: Sequence[Path]
    if args.sources:
        source_paths = [Path(src).expanduser().resolve() for src in args.sources]
    else:
        source_paths = DATA_FILES

    price_map = load_price_map(source_paths)
    tickers = select_tickers(price_map, args.ticker_count, rng)

    glitch_probs = dict(GLITCH_PROBABILITIES)
    if args.clean_rows:
        for key in glitch_probs:
            glitch_probs[key] = 0.0
    if args.timestamp_break_prob is not None:
        glitch_probs["timestamp_break"] = args.timestamp_break_prob

    generator = OrderBookGenerator(
        tickers=tickers,
        num_lines=args.rows,
        output_path=args.output.resolve(),
        glitch_probs=glitch_probs,
        rng=rng,
        flush_every=args.flush_every,
        start_timestamp=args.start_timestamp,
        log_interval=args.log_interval,
    )
    generator.generate()
    print(f"CSV generation complete -> {args.output.resolve()} (rows: {args.rows:,}).")


if __name__ == "__main__":
    main()
