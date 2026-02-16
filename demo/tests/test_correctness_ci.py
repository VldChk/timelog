#!/usr/bin/env python3

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "demo"))

import correctness_ci as cci  # noqa: E402


class CorrectnessCIOrchestratorTests(unittest.TestCase):
    def test_nightly_profile_includes_mixed_leg_config(self) -> None:
        legs = cci._profile_legs("nightly", duration_override_seconds=1)
        mixed = [leg for leg in legs if leg.source_mode == "mixed"]
        self.assertEqual(len(mixed), 1)
        self.assertAlmostEqual(mixed[0].ooo_rate, 0.05)
        self.assertAlmostEqual(mixed[0].mixed_alt_ooo_rate or 0.0, 0.20)

    def test_pr_profile_smoke(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            out_dir = root / "out"
            export_json = root / "correctness_ci_pr.json"
            export_md = root / "correctness_ci_pr.md"
            cmd = [
                sys.executable,
                "demo/correctness_ci.py",
                "--profile",
                "pr",
                "--duration-override-seconds",
                "2",
                "--out-dir",
                str(out_dir),
                "--export-json",
                str(export_json),
                "--export-md",
                str(export_md),
            ]
            proc = subprocess.run(cmd, cwd=str(REPO_ROOT), check=False)
            self.assertTrue(export_json.exists())
            self.assertTrue(export_md.exists())
            payload = json.loads(export_json.read_text(encoding="utf-8"))
            self.assertEqual(payload.get("profile"), "pr")
            self.assertEqual(len(payload.get("legs", [])), 1)
            self.assertEqual(proc.returncode, int(payload.get("exit_code")))

    def test_nightly_profile_dry_run(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            out_dir = root / "out"
            export_json = root / "correctness_ci_nightly.json"
            export_md = root / "correctness_ci_nightly.md"
            cmd = [
                sys.executable,
                "demo/correctness_ci.py",
                "--profile",
                "nightly",
                "--duration-override-seconds",
                "1",
                "--out-dir",
                str(out_dir),
                "--export-json",
                str(export_json),
                "--export-md",
                str(export_md),
            ]
            proc = subprocess.run(cmd, cwd=str(REPO_ROOT), check=False)
            self.assertTrue(export_json.exists())
            self.assertTrue(export_md.exists())
            payload = json.loads(export_json.read_text(encoding="utf-8"))
            self.assertEqual(payload.get("profile"), "nightly")
            self.assertEqual(len(payload.get("legs", [])), 3)
            self.assertEqual(sum(1 for leg in payload.get("legs", []) if leg.get("source_mode") == "mixed"), 1)
            self.assertEqual(proc.returncode, int(payload.get("exit_code")))


if __name__ == "__main__":
    unittest.main()
