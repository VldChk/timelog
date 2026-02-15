#!/usr/bin/env python3

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from benchmark_baseline import compare_to_baseline  # noqa: E402


class BenchmarkBaselineTests(unittest.TestCase):
    def test_no_match_is_na(self) -> None:
        baseline = {"schema_version": "methodology_v1", "scenarios": {}}
        gate, detail = compare_to_baseline(
            baseline,
            scenario_id="A2",
            contract={"measurement_type": "e2e"},
            median_rate=100.0,
        )
        self.assertEqual(gate, "na")
        self.assertIn("reason", detail)

    def test_regression_warn(self) -> None:
        baseline = {
            "schema_version": "methodology_v1",
            "scenarios": {
                "A2": [
                    {
                        "apples_contract": {"measurement_type": "e2e"},
                        "median_rate": 100.0,
                    }
                ]
            },
        }
        gate, detail = compare_to_baseline(
            baseline,
            scenario_id="A2",
            contract={"measurement_type": "e2e"},
            median_rate=85.0,
        )
        self.assertEqual(gate, "warn")
        self.assertTrue(detail["regressed"])

    def test_non_regression_pass(self) -> None:
        baseline = {
            "schema_version": "methodology_v1",
            "scenarios": {
                "A2": [
                    {
                        "apples_contract": {"measurement_type": "e2e"},
                        "median_rate": 100.0,
                    }
                ]
            },
        }
        gate, detail = compare_to_baseline(
            baseline,
            scenario_id="A2",
            contract={"measurement_type": "e2e"},
            median_rate=101.0,
        )
        self.assertEqual(gate, "pass")
        self.assertFalse(detail["regressed"])

    def test_ms_per_op_lower_is_better(self) -> None:
        baseline = {
            "schema_version": "methodology_v1",
            "scenarios": {
                "E1": [
                    {
                        "apples_contract": {"measurement_type": "api_overhead"},
                        "median_rate": 10.0,
                    }
                ]
            },
        }
        gate_bad, detail_bad = compare_to_baseline(
            baseline,
            scenario_id="E1",
            contract={"measurement_type": "api_overhead"},
            median_rate=12.0,
            primary_unit="ms_per_op",
        )
        gate_good, detail_good = compare_to_baseline(
            baseline,
            scenario_id="E1",
            contract={"measurement_type": "api_overhead"},
            median_rate=9.0,
            primary_unit="ms_per_op",
        )
        self.assertEqual(gate_bad, "warn")
        self.assertTrue(detail_bad["regressed"])
        self.assertEqual(gate_good, "pass")
        self.assertFalse(detail_good["regressed"])


if __name__ == "__main__":
    unittest.main()
