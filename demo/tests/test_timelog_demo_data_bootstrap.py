#!/usr/bin/env python3

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "demo"))

import timelog_demo as td  # noqa: E402


class TimelogDemoDataBootstrapTests(unittest.TestCase):
    def test_missing_default_generated_csv_triggers_generation(self) -> None:
        with tempfile.TemporaryDirectory() as td_tmp:
            path = Path(td_tmp) / "generated_5pct.csv"
            self.assertFalse(path.exists())
            created = td._maybe_generate_default_dataset(str(path), rows=50, seed=7)
            self.assertTrue(created)
            self.assertTrue(path.exists())
            lines = path.read_text(encoding="utf-8").splitlines()
            self.assertGreaterEqual(len(lines), 2)
            self.assertEqual(lines[0], ",".join(td.CSV_COLUMNS))

    def test_non_default_missing_path_is_not_auto_generated(self) -> None:
        with tempfile.TemporaryDirectory() as td_tmp:
            path = Path(td_tmp) / "custom_orders.csv"
            created = td._maybe_generate_default_dataset(str(path), rows=10, seed=1)
            self.assertFalse(created)
            self.assertFalse(path.exists())

    def test_non_default_missing_path_still_fails_with_hft_hint(self) -> None:
        with tempfile.TemporaryDirectory() as td_tmp:
            missing = Path(td_tmp) / "custom_orders.csv"
            cmd = [
                sys.executable,
                "demo/timelog_demo.py",
                "--quick",
                "--feature",
                "A1",
                "--data",
                str(missing),
            ]
            proc = subprocess.run(
                cmd,
                cwd=str(REPO_ROOT),
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertNotEqual(proc.returncode, 0)
            combined = proc.stdout + proc.stderr
            self.assertIn("demo/hft_synthetic.py", combined)
            self.assertIn(f"--output {missing}", combined)


if __name__ == "__main__":
    unittest.main()
