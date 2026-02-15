#!/usr/bin/env python3

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from benchmark_models import (  # noqa: E402
    compute_scenario_stats,
    fit_loglog_exponent,
    fit_linear_slope,
    mad,
    percentile,
)


class BenchmarkModelsTests(unittest.TestCase):
    def test_percentile(self) -> None:
        vals = [1.0, 2.0, 3.0, 4.0, 5.0]
        self.assertAlmostEqual(percentile(vals, 0.5), 3.0)
        self.assertAlmostEqual(percentile(vals, 0.95), 4.8)

    def test_mad(self) -> None:
        vals = [10.0, 11.0, 9.0, 50.0]
        self.assertGreater(mad(vals), 0.0)

    def test_compute_stats(self) -> None:
        rates = [100.0, 101.0, 99.0, 102.0, 98.0]
        lat = [10.0, 9.5, 10.5, 9.8, 10.2]
        stats = compute_scenario_stats(rates, lat, seed=123)
        self.assertEqual(stats.samples, 5)
        self.assertGreater(stats.median_rate, 0.0)
        self.assertGreaterEqual(stats.p99_rate, stats.p95_rate)

    def test_loglog_fit(self) -> None:
        xs = [1, 2, 4, 8, 16]
        ys = [1, 2, 4, 8, 16]
        fit = fit_loglog_exponent(xs, ys)
        self.assertAlmostEqual(fit["slope"], 1.0, delta=0.1)

    def test_linear_fit(self) -> None:
        xs = [1, 2, 3, 4, 5]
        ys = [2, 4, 6, 8, 10]
        fit = fit_linear_slope(xs, ys)
        self.assertAlmostEqual(fit["slope"], 2.0, delta=0.01)


if __name__ == "__main__":
    unittest.main()
