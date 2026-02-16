#!/usr/bin/env python3

from __future__ import annotations

import json
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "demo"))

import correctness_checker as cc  # noqa: E402


class CorrectnessCheckerCITests(unittest.TestCase):
    def test_compute_exit_code_confirmed_only_fails(self) -> None:
        out = cc._compute_exit_code(
            {"CONFIRMED_ENGINE_BUG": 1, "CHECKER_BUG": 0},
            {"CONFIRMED_ENGINE_BUG"},
        )
        self.assertEqual(out.exit_code, 2)
        self.assertEqual(out.result, "fail")

    def test_compute_exit_code_checker_status_fails_when_configured(self) -> None:
        out = cc._compute_exit_code(
            {"CONFIRMED_ENGINE_BUG": 0, "CHECKER_BUG": 3},
            {"CONFIRMED_ENGINE_BUG", "CHECKER_BUG"},
        )
        self.assertEqual(out.exit_code, 2)
        self.assertEqual(out.result, "fail")

    def test_compute_exit_code_transient_only_passes(self) -> None:
        out = cc._compute_exit_code(
            {"UNCONFIRMED_TRANSIENT": 7},
            {"CONFIRMED_ENGINE_BUG", "CHECKER_BUG"},
        )
        self.assertEqual(out.exit_code, 0)
        self.assertEqual(out.result, "pass")

    def test_artifact_policy_minimal_removes_detail_files(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            run_dir = Path(td) / "run"
            run_dir.mkdir(parents=True, exist_ok=True)
            detail_files = [
                run_dir / "ops.jsonl",
                run_dir / "checks.jsonl",
                run_dir / "issues.jsonl",
            ]
            for f in detail_files:
                f.write_text("x\n", encoding="utf-8")
            issues_dir = run_dir / "issues"
            issues_dir.mkdir(parents=True, exist_ok=True)
            (issues_dir / "report.md").write_text("issue\n", encoding="utf-8")

            manifest = cc._apply_artifact_policy(
                run_dir=run_dir,
                artifact_mode="minimal",
                result="pass",
                detail_paths=detail_files + [issues_dir],
                failure_bundle_out=None,
            )
            for f in detail_files:
                self.assertFalse(f.exists())
            self.assertFalse(issues_dir.exists())
            self.assertEqual(manifest.get("bundle_path"), None)

    def test_artifact_policy_fail_bundle_creates_tar_and_removes_details(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            run_dir = Path(td) / "run"
            run_dir.mkdir(parents=True, exist_ok=True)
            detail_files = [
                run_dir / "ops.jsonl",
                run_dir / "checks.jsonl",
                run_dir / "issues.jsonl",
            ]
            for f in detail_files:
                f.write_text("x\n", encoding="utf-8")
            issues_dir = run_dir / "issues"
            issues_dir.mkdir(parents=True, exist_ok=True)
            (issues_dir / "report.md").write_text("issue\n", encoding="utf-8")
            bundle_out = run_dir / "bundle.tar.gz"

            manifest = cc._apply_artifact_policy(
                run_dir=run_dir,
                artifact_mode="fail-bundle",
                result="fail",
                detail_paths=detail_files + [issues_dir],
                failure_bundle_out=bundle_out,
            )
            self.assertTrue(bundle_out.exists())
            for f in detail_files:
                self.assertFalse(f.exists())
            self.assertFalse(issues_dir.exists())
            self.assertEqual(manifest.get("bundle_path"), str(bundle_out))
            with tarfile.open(bundle_out, "r:gz") as tf:
                names = tf.getnames()
            self.assertTrue(any("ops.jsonl" in n for n in names))
            self.assertTrue(any("issues/report.md" in n for n in names))

    def test_integration_short_run_minimal_has_schema_fields(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            summary_json = root / "summary.json"
            summary_md = root / "summary.md"
            run_dir = root / "runs"

            cmd = [
                sys.executable,
                "demo/correctness_checker.py",
                "--duration-seconds",
                "2",
                "--source-mode",
                "synthetic",
                "--ooo-rate",
                "0.05",
                "--out-dir",
                str(run_dir),
                "--ci-profile",
                "pr",
                "--artifact-mode",
                "minimal",
                "--summary-json-out",
                str(summary_json),
                "--summary-md-out",
                str(summary_md),
                "--run-id",
                "cc_test_minimal",
            ]
            proc = subprocess.run(cmd, cwd=str(REPO_ROOT), check=False)
            self.assertIn(proc.returncode, (0, 2))
            self.assertTrue(summary_json.exists())
            self.assertTrue(summary_md.exists())
            payload = json.loads(summary_json.read_text(encoding="utf-8"))
            self.assertIn("result", payload)
            self.assertIn("gate", payload)
            self.assertIn("exit_code", payload)
            self.assertIn("artifact_manifest", payload)
            run_path = Path(payload["artifact_paths"]["run_dir"])
            self.assertFalse((run_path / "ops.jsonl").exists())
            self.assertFalse((run_path / "checks.jsonl").exists())
            self.assertFalse((run_path / "issues.jsonl").exists())
            self.assertFalse((run_path / "issues").exists())


if __name__ == "__main__":
    unittest.main()
