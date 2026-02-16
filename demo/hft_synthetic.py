#!/usr/bin/env python3
"""
In-process HFT order book synthetic data generator.

Embeds realistic ticker data, order lifecycle state machine, price dynamics,
and hierarchical timestamp distributions. Replaces external CSV files for
correctness and benchmark pipelines.

Three APIs:
  - HFTSyntheticSource: correctness checker protocol (next_records -> SourceRecord)
  - generate_orders():  benchmark protocol (Iterator[(timestamp, Order)])
  - generate_csv():     CI CSV generation (writes file to disk)
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import math
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator


# ---------------------------------------------------------------------------
# Ticker universe (embedded, no external JSON files)
# ---------------------------------------------------------------------------

def _build_isin(symbol: str) -> str:
    """Deterministic pseudo-ISIN from SHA256."""
    digest = hashlib.sha256(symbol.encode("utf-8")).hexdigest()
    country_codes = ["US", "CA", "GB", "FR", "DE", "JP"]
    country = country_codes[int(digest[:2], 16) % len(country_codes)]
    digits = "".join(str(int(digest[i : i + 2], 16) % 10) for i in range(2, 20, 2))
    check_digit = str(int(digest[20:22], 16) % 10)
    return country + digits[:9] + check_digit


@dataclass(frozen=True)
class TickerMeta:
    symbol: str
    isin: str
    base_price: float


# Representative sample spanning penny stocks through blue chips.
# Prices are approximate and used only as starting points for simulation.
_TICKER_DATA: list[tuple[str, float]] = [
    # Mega-cap tech
    ("AAPL", 178.50), ("MSFT", 378.91), ("GOOGL", 141.80), ("AMZN", 178.25),
    ("NVDA", 495.22), ("META", 390.10), ("TSLA", 248.42), ("AVGO", 1210.99),
    ("ADBE", 570.50), ("CRM", 272.30),
    # Large-cap financials
    ("JPM", 196.41), ("BAC", 33.72), ("WFC", 48.15), ("GS", 385.10),
    ("MS", 87.65), ("C", 53.28), ("BLK", 815.20), ("SCHW", 68.90),
    ("AXP", 187.45), ("USB", 42.10),
    # Healthcare / pharma
    ("JNJ", 157.38), ("UNH", 527.60), ("PFE", 28.74), ("ABBV", 154.30),
    ("MRK", 108.12), ("LLY", 620.15), ("TMO", 530.88), ("ABT", 104.62),
    ("BMY", 51.24), ("AMGN", 278.90),
    # Industrials
    ("CAT", 287.50), ("BA", 215.78), ("HON", 202.15), ("GE", 122.35),
    ("UPS", 155.90), ("RTX", 88.42), ("DE", 380.65), ("LMT", 448.20),
    ("MMM", 102.55), ("EMR", 98.30),
    # Consumer / retail
    ("WMT", 165.20), ("HD", 345.80), ("PG", 152.40), ("KO", 59.85),
    ("PEP", 170.30), ("COST", 572.10), ("NKE", 108.45), ("MCD", 295.60),
    ("SBUX", 98.75), ("TGT", 142.30),
    # Energy
    ("XOM", 104.25), ("CVX", 152.80), ("COP", 118.95), ("SLB", 52.40),
    ("EOG", 122.10), ("PSX", 128.55), ("MPC", 148.70), ("VLO", 132.45),
    ("OXY", 62.15), ("HAL", 38.90),
    # Mid-cap tech
    ("SNAP", 12.45), ("PINS", 38.20), ("SQ", 68.50), ("ROKU", 92.35),
    ("TWLO", 68.80), ("DDOG", 118.40), ("NET", 78.55), ("ZS", 205.10),
    ("MDB", 395.20), ("SNOW", 162.80),
    # Small-cap / volatile
    ("PLTR", 17.85), ("SOFI", 8.92), ("RIVN", 18.45), ("LCID", 5.28),
    ("MARA", 14.62), ("RIOT", 12.35), ("HOOD", 11.80), ("WISH", 6.15),
    ("OPEN", 3.42), ("CLOV", 1.85),
    # International ADRs
    ("BABA", 78.60), ("TSM", 102.35), ("NVO", 118.90), ("ASML", 685.40),
    ("SAP", 162.75), ("TM", 178.20), ("SNY", 48.55), ("SHOP", 62.40),
    ("SE", 42.15), ("MELI", 1580.30),
    # REITs / utilities
    ("AMT", 202.50), ("PLD", 128.75), ("CCI", 112.40), ("EQIX", 792.60),
    ("SPG", 142.80), ("NEE", 72.35), ("DUK", 98.15), ("SO", 72.90),
    ("D", 48.60), ("AEP", 85.40),
]

TICKERS: list[TickerMeta] = [
    TickerMeta(symbol=sym, isin=_build_isin(sym), base_price=price)
    for sym, price in _TICKER_DATA
]


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

COLUMNS = [
    "timestamp", "ticker", "isin", "direction", "status",
    "amount", "ask_price", "bid_price", "order_id", "commission",
]


@dataclass
class HFTEvent:
    """Single structured HFT order book event."""
    timestamp: int
    ticker: str
    isin: str
    direction: str
    status: str
    amount: int
    ask_price: float
    bid_price: float | None
    order_id: int
    commission: float


@dataclass
class _OrderState:
    symbol: str
    isin: str
    direction: str
    initial_amount: int
    remaining: int
    limit_price: float


# ---------------------------------------------------------------------------
# HFTOrderBookEngine — iterator-based order book simulator
# ---------------------------------------------------------------------------

class HFTOrderBookEngine:
    """
    Stateful order book event generator with realistic HFT dynamics.

    Produces an infinite stream of HFTEvent objects with:
    - Realistic order lifecycle (OPEN -> PARTIAL/FILLED)
    - Price dynamics with drift, Gaussian shock, and bid-ask spread
    - Hierarchical timestamp distribution (bursts + gaps)
    - Controllable out-of-order rate
    """

    def __init__(
        self,
        *,
        tickers: list[TickerMeta] | None = None,
        ooo_rate: float = 0.05,
        seed: int | None = None,
        start_timestamp: int = 1_609_459_200_000_000_000,
    ) -> None:
        self.rng = random.Random(seed)
        self.tickers = tickers or TICKERS
        self.ooo_rate = ooo_rate
        self.last_timestamp = start_timestamp
        self.price_state: dict[str, float] = {
            t.symbol: t.base_price for t in self.tickers
        }
        self.orders: dict[int, _OrderState] = {}
        self.next_order_id = 1

    def __iter__(self) -> Iterator[HFTEvent]:
        return self

    def __next__(self) -> HFTEvent:
        while True:
            event = self._next_event()
            if event is not None:
                return event

    # -- Event dispatch -----------------------------------------------------

    def _next_event(self) -> HFTEvent | None:
        if not self.orders:
            return self._open_order_event()
        # Bias towards fills so book doesn't explode.
        order_pressure = min(0.95, 0.4 + len(self.orders) / 500)
        if self.rng.random() < order_pressure:
            return self._fill_order_event()
        return self._open_order_event()

    def _open_order_event(self) -> HFTEvent | None:
        ticker = self.rng.choice(self.tickers)
        direction = "BUY" if self.rng.random() < 0.5 else "SELL"
        amount = self.rng.randint(10, 15_000)
        ask_price, _ = self._next_prices(ticker.symbol)
        order_id = self.next_order_id
        self.next_order_id += 1
        self.orders[order_id] = _OrderState(
            symbol=ticker.symbol,
            isin=ticker.isin,
            direction=direction,
            initial_amount=amount,
            remaining=amount,
            limit_price=ask_price,
        )
        return HFTEvent(
            timestamp=self._next_timestamp(),
            ticker=ticker.symbol,
            isin=ticker.isin,
            direction=direction,
            status="OPEN",
            amount=amount,
            ask_price=ask_price,
            bid_price=None,
            order_id=order_id,
            commission=0.0,
        )

    def _fill_order_event(self) -> HFTEvent | None:
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

        state.remaining = remaining_after
        if state.remaining == 0:
            del self.orders[order_id]

        execution_price = self._execution_price(state, market_ask, market_bid)
        commission = self._commission(fill_amount)
        return HFTEvent(
            timestamp=self._next_timestamp(),
            ticker=state.symbol,
            isin=state.isin,
            direction=state.direction,
            status=status,
            amount=fill_amount,
            ask_price=state.limit_price,
            bid_price=execution_price,
            order_id=order_id,
            commission=commission,
        )

    # -- Price dynamics -----------------------------------------------------

    def _next_prices(self, symbol: str) -> tuple[float, float]:
        price = self.price_state[symbol]
        drift = self.rng.uniform(-0.0005, 0.0005)
        shock = self.rng.gauss(0, 0.0015)
        price = max(0.01, price * (1 + drift + shock))
        self.price_state[symbol] = price
        spread = max(price * self.rng.uniform(0.00005, 0.0015), 0.0001)
        ask = price + spread / 2
        bid = max(0.01, price - spread / 2)
        return ask, bid

    def _execution_price(
        self, state: _OrderState, market_ask: float, market_bid: float
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

    # -- Timestamp generation -----------------------------------------------

    def _next_timestamp(self) -> int:
        # Hierarchical distribution: dense bursts with occasional gaps.
        r = self.rng.random()
        if r < 0.6:
            gap = self.rng.randint(1, 500)            # Sub-microsecond
        elif r < 0.9:
            gap = self.rng.randint(500, 200_000)      # Medium (0.5-200 µs)
        else:
            gap = self.rng.randint(200_000, 5_000_000) # Breathing room

        # Occasional burst compression.
        if self.rng.random() < 0.05:
            gap = max(1, gap // 10)

        intended = self.last_timestamp + gap

        # Always advance the timeline so subsequent events stay monotonic.
        self.last_timestamp = intended

        # Out-of-order: return a backwards-jumped timestamp.
        if self.rng.random() < self.ooo_rate:
            max_back = min(500_000, intended)
            if max_back > 1:
                offset = self.rng.randint(1, max_back)
                return max(0, intended - offset)

        return intended


# ---------------------------------------------------------------------------
# HFTSyntheticSource — correctness checker protocol
# ---------------------------------------------------------------------------

@dataclass
class SourceRecord:
    """Compatible with correctness_checker.SourceRecord."""
    ts: int
    payload: Any
    src: str
    cycle: int
    source_file: str


class HFTSyntheticSource:
    """
    Correctness-checker compatible synthetic source with HFT order book dynamics.

    Produces SourceRecord objects where payload is a dict matching the
    normalized CSV row format (ints/floats, not strings).
    """

    def __init__(
        self,
        rng: random.Random,
        base_ts: int = 1_000_000,
        ooo_rate: float = 0.05,
    ) -> None:
        self.engine = HFTOrderBookEngine(
            ooo_rate=ooo_rate,
            start_timestamp=base_ts,
        )
        # Share the caller's rng for seed consistency.
        self.engine.rng = rng
        self.total = 0
        self.cycle = 0

    def next_records(self, count: int) -> list[SourceRecord]:
        out: list[SourceRecord] = []
        for _ in range(count):
            event = next(self.engine)
            self.total += 1
            if self.total % 1_000_000 == 0:
                self.cycle += 1
            payload = {
                "timestamp": event.timestamp,
                "ticker": event.ticker,
                "isin": event.isin,
                "direction": event.direction,
                "status": event.status,
                "amount": event.amount,
                "ask_price": event.ask_price,
                "bid_price": event.bid_price,
                "order_id": event.order_id,
                "commission": event.commission,
            }
            out.append(SourceRecord(
                ts=event.timestamp,
                payload=payload,
                src="hft_syn",
                cycle=self.cycle,
                source_file="<hft_synthetic>",
            ))
        return out


# ---------------------------------------------------------------------------
# generate_orders() — benchmark protocol
# ---------------------------------------------------------------------------

def generate_orders(
    *,
    count: int = 0,
    ooo_rate: float = 0.05,
    seed: int = 42,
    start_timestamp: int = 1_609_459_200_000_000_000,
) -> Iterator[tuple[int, Any]]:
    """
    Generate (timestamp, Order) tuples compatible with timelog_demo.load_orders().

    Args:
        count: Number of records (0 = unlimited).
        ooo_rate: Out-of-order rate (0.05 = 5%, 0.20 = 20%).
        seed: RNG seed for reproducibility.
        start_timestamp: Starting nanosecond timestamp.

    Yields:
        (timestamp, Order) tuples.
    """
    from timelog_demo import Order  # Lazy import to avoid circular dependency

    engine = HFTOrderBookEngine(
        ooo_rate=ooo_rate,
        seed=seed,
        start_timestamp=start_timestamp,
    )
    emitted = 0
    for event in engine:
        order = Order(
            ticker=event.ticker,
            isin=event.isin,
            direction=event.direction,
            status=event.status,
            amount=event.amount,
            ask_price=event.ask_price,
            bid_price=event.bid_price if event.bid_price is not None else 0.0,
            order_id=event.order_id,
            commission=event.commission,
        )
        yield event.timestamp, order
        emitted += 1
        if count > 0 and emitted >= count:
            return


# ---------------------------------------------------------------------------
# generate_csv() — CI CSV file generation
# ---------------------------------------------------------------------------

def generate_csv(
    output_path: str | Path,
    *,
    rows: int = 581_400,
    ooo_rate: float = 0.05,
    seed: int = 42,
    start_timestamp: int = 1_609_459_200_000_000_000,
    log_interval: int = 100_000,
) -> None:
    """
    Write a CSV file with HFT order book data.

    Used by CI benchmark pipelines that still require CSV input.
    """
    output_path = Path(output_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    engine = HFTOrderBookEngine(
        ooo_rate=ooo_rate,
        seed=seed,
        start_timestamp=start_timestamp,
    )

    with output_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(COLUMNS)
        for i, event in enumerate(engine):
            writer.writerow([
                event.timestamp,
                event.ticker,
                event.isin,
                event.direction,
                event.status,
                event.amount,
                f"{event.ask_price:.6f}",
                f"{event.bid_price:.6f}" if event.bid_price is not None else "",
                event.order_id,
                f"{event.commission:.6f}",
            ])
            if i + 1 >= rows:
                break
            if log_interval and (i + 1) % log_interval == 0:
                print(f"  Generated {i + 1:,} / {rows:,} rows...")

    print(f"CSV generated: {output_path} ({rows:,} rows)")


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate HFT synthetic order book CSV"
    )
    parser.add_argument("--output", type=str, required=True,
                        help="Output CSV file path")
    parser.add_argument("--rows", type=int, default=581_400,
                        help="Number of rows to generate (default: 581400)")
    parser.add_argument("--ooo-rate", type=float, default=0.05,
                        help="Out-of-order rate (0.0 to 1.0, default: 0.05)")
    parser.add_argument("--seed", type=int, default=42,
                        help="RNG seed for reproducibility (default: 42)")
    parser.add_argument("--start-timestamp", type=int,
                        default=1_609_459_200_000_000_000,
                        help="Starting nanosecond timestamp")
    return parser.parse_args()


if __name__ == "__main__":
    args = _parse_args()
    if not (0.0 <= args.ooo_rate <= 1.0):
        raise SystemExit("--ooo-rate must be between 0.0 and 1.0")
    if args.rows <= 0:
        raise SystemExit("--rows must be positive")
    generate_csv(
        args.output,
        rows=args.rows,
        ooo_rate=args.ooo_rate,
        seed=args.seed,
        start_timestamp=args.start_timestamp,
    )
