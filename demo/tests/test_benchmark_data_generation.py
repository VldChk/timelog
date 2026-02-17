#!/usr/bin/env python3

from __future__ import annotations

import argparse
import tempfile
import unittest
from pathlib import Path

import sys

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "demo"))

import timelog_benchmark as tb  # noqa: E402


class BenchmarkDataGenerationTests(unittest.TestCase):
    def test_generate_data_creates_primary_and_a6_pair_from_5pct(self) -> None:
        with tempfile.TemporaryDirectory() as td_tmp:
            primary = Path(td_tmp) / "generated_5pct.csv"
            alt = Path(td_tmp) / "generated_20pct.csv"
            args = argparse.Namespace(
                generate_data=True,
                data=str(primary),
                ooo_rate=0.05,
                generate_rows=40,
                seed=123,
            )
            tb._ensure_data_generated(args)
            self.assertTrue(primary.exists())
            self.assertTrue(alt.exists())

    def test_generate_data_creates_primary_and_a6_pair_from_20pct(self) -> None:
        with tempfile.TemporaryDirectory() as td_tmp:
            primary = Path(td_tmp) / "generated_20pct.csv"
            alt = Path(td_tmp) / "generated_5pct.csv"
            args = argparse.Namespace(
                generate_data=True,
                data=str(primary),
                ooo_rate=0.20,
                generate_rows=40,
                seed=123,
            )
            tb._ensure_data_generated(args)
            self.assertTrue(primary.exists())
            self.assertTrue(alt.exists())


if __name__ == "__main__":
    unittest.main()
