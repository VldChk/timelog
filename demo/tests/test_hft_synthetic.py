#!/usr/bin/env python3

from __future__ import annotations

import io
import random
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from hft_synthetic import (  # noqa: E402
    COLUMNS,
    HFTOrderBookEngine,
    HFTSyntheticSource,
    SourceRecord,
    generate_csv,
)


class SeedDeterminismTests(unittest.TestCase):
    def test_same_seed_same_output(self) -> None:
        records_a = list(zip(range(100), HFTOrderBookEngine(seed=42)))
        records_b = list(zip(range(100), HFTOrderBookEngine(seed=42)))
        for (_, a), (_, b) in zip(records_a, records_b):
            self.assertEqual(a.timestamp, b.timestamp)
            self.assertEqual(a.ticker, b.ticker)
            self.assertEqual(a.order_id, b.order_id)
            self.assertEqual(a.status, b.status)

    def test_different_seed_different_output(self) -> None:
        a = next(iter(HFTOrderBookEngine(seed=1)))
        b = next(iter(HFTOrderBookEngine(seed=2)))
        # Extremely unlikely to match on both fields
        self.assertTrue(
            a.timestamp != b.timestamp or a.ticker != b.ticker,
            "Different seeds should produce different events",
        )


class OOORateTests(unittest.TestCase):
    def test_ooo_rate_approximate(self) -> None:
        engine = HFTOrderBookEngine(ooo_rate=0.20, seed=99)
        events = [next(engine) for _ in range(10_000)]
        ooo_count = sum(
            1
            for i in range(1, len(events))
            if events[i].timestamp < events[i - 1].timestamp
        )
        rate = ooo_count / (len(events) - 1)
        self.assertGreater(rate, 0.10, f"OOO rate {rate:.3f} too low")
        self.assertLess(rate, 0.30, f"OOO rate {rate:.3f} too high")

    def test_zero_ooo_monotonic(self) -> None:
        engine = HFTOrderBookEngine(ooo_rate=0.0, seed=7)
        prev = 0
        for _, event in zip(range(1_000), engine):
            self.assertGreaterEqual(event.timestamp, prev)
            prev = event.timestamp

    def test_full_ooo_no_crash(self) -> None:
        engine = HFTOrderBookEngine(ooo_rate=1.0, seed=3)
        for _, event in zip(range(100), engine):
            self.assertIsInstance(event.timestamp, int)


class EdgeCaseTests(unittest.TestCase):
    def test_single_event(self) -> None:
        event = next(iter(HFTOrderBookEngine(seed=0)))
        self.assertIsInstance(event.timestamp, int)
        self.assertEqual(event.status, "OPEN")


class CSVSchemaTests(unittest.TestCase):
    def test_csv_header_and_columns(self) -> None:
        with tempfile.NamedTemporaryFile(suffix=".csv", delete=False) as f:
            path = Path(f.name)
        try:
            generate_csv(path, rows=50, seed=10, log_interval=0)
            lines = path.read_text(encoding="utf-8").strip().splitlines()
            self.assertEqual(lines[0], ",".join(COLUMNS))
            # 50 data rows + 1 header
            self.assertEqual(len(lines), 51)
            for line in lines[1:]:
                fields = line.split(",")
                self.assertEqual(len(fields), len(COLUMNS))
        finally:
            path.unlink(missing_ok=True)


class HFTSyntheticSourceTests(unittest.TestCase):
    def test_returns_correct_count(self) -> None:
        rng = random.Random(42)
        src = HFTSyntheticSource(rng, base_ts=1_000_000, ooo_rate=0.05)
        records = src.next_records(25)
        self.assertEqual(len(records), 25)
        for rec in records:
            self.assertIsInstance(rec, SourceRecord)
            self.assertIsInstance(rec.ts, int)
            self.assertIsInstance(rec.payload, dict)
            self.assertEqual(rec.src, "hft_syn")
            self.assertEqual(rec.source_file, "<hft_synthetic>")

    def test_payload_fields(self) -> None:
        rng = random.Random(99)
        src = HFTSyntheticSource(rng, base_ts=1_000_000, ooo_rate=0.05)
        records = src.next_records(50)
        expected_keys = {
            "timestamp", "ticker", "isin", "direction", "status",
            "amount", "ask_price", "bid_price", "order_id", "commission",
        }
        for rec in records:
            self.assertEqual(set(rec.payload.keys()), expected_keys)


class OrderLifecycleTests(unittest.TestCase):
    def test_valid_statuses_and_directions(self) -> None:
        engine = HFTOrderBookEngine(seed=55, ooo_rate=0.05)
        statuses = set()
        directions = set()
        for _, event in zip(range(500), engine):
            statuses.add(event.status)
            directions.add(event.direction)
        self.assertTrue(statuses <= {"OPEN", "PARTIAL", "FILLED"})
        self.assertTrue(directions <= {"BUY", "SELL"})
        # With 500 events we should see all statuses
        self.assertIn("OPEN", statuses)
        self.assertIn("FILLED", statuses)


if __name__ == "__main__":
    unittest.main()
