#!/usr/bin/env python3

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from benchmark_scenarios import build_scenario_registry  # noqa: E402


class BenchmarkScenarioRegistryTests(unittest.TestCase):
    def test_registry_contains_features(self) -> None:
        reg = build_scenario_registry()
        self.assertIn("A2", reg)
        self.assertIn("D3", reg)
        self.assertIn("J3", reg)

    def test_required_fields_present(self) -> None:
        reg = build_scenario_registry()
        for spec in reg.values():
            self.assertTrue(spec.measurement_type)
            self.assertTrue(spec.primary_unit)
            self.assertIsNotNone(spec.setup_fn)
            self.assertIsNotNone(spec.measure_fn)
            self.assertIsNotNone(spec.teardown_fn)

    def test_corrected_cases_use_custom_boundaries(self) -> None:
        reg = build_scenario_registry()
        for code in ("A2B", "A6", "D3", "D4", "E3", "E4", "F4"):
            spec = reg[code]
            self.assertNotEqual(spec.setup_fn.__name__, "_default_setup")
            self.assertNotEqual(spec.measure_fn.__name__, "_default_measure")

    def test_corrected_case_units(self) -> None:
        reg = build_scenario_registry()
        expected = {
            "A2B": "records_in_per_sec",
            "D3": "ops_per_sec",
            "D4": "records_out_per_sec",
            "E3": "records_in_per_sec",
            "E4": "records_in_per_sec",
            "F4": "timestamps_per_sec",
        }
        for code, unit in expected.items():
            self.assertEqual(reg[code].primary_unit, unit)

    def test_numpy_optional_correctness_hook(self) -> None:
        reg = build_scenario_registry()
        for code in ("F4", "F5"):
            ok, _ = reg[code].correctness_assert_fn({"error": "numpy not installed"})  # type: ignore[misc]
            self.assertTrue(ok)


if __name__ == "__main__":
    unittest.main()
