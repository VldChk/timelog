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
            self.assertIn("source_contract", payload)
            self.assertIn("source_counters", payload)
            run_path = Path(payload["artifact_paths"]["run_dir"])
            self.assertFalse((run_path / "ops.jsonl").exists())
            self.assertFalse((run_path / "checks.jsonl").exists())
            self.assertFalse((run_path / "issues.jsonl").exists())
            self.assertFalse((run_path / "issues").exists())

    def test_csv_mode_without_csv_paths_fails_fast(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            run_dir = Path(td) / "runs"
            cmd = [
                sys.executable,
                "demo/correctness_checker.py",
                "--duration-seconds",
                "1",
                "--source-mode",
                "csv",
                "--out-dir",
                str(run_dir),
                "--run-id",
                "cc_test_csv_missing",
            ]
            proc = subprocess.run(
                cmd,
                cwd=str(REPO_ROOT),
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("requires at least one existing --csv path", proc.stderr + proc.stdout)

    def test_invalid_ooo_rates_are_rejected(self) -> None:
        base = [
            sys.executable,
            "demo/correctness_checker.py",
            "--duration-seconds",
            "1",
            "--out-dir",
            "/tmp/cc_invalid_rates",
            "--run-id",
            "cc_invalid_rates",
        ]
        proc1 = subprocess.run(
            base + ["--ooo-rate", "1.5"],
            cwd=str(REPO_ROOT),
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertNotEqual(proc1.returncode, 0)
        self.assertIn("--ooo-rate must be between 0.0 and 1.0", proc1.stderr + proc1.stdout)

        proc2 = subprocess.run(
            base + ["--mixed-alt-ooo-rate", "-0.1"],
            cwd=str(REPO_ROOT),
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertNotEqual(proc2.returncode, 0)
        self.assertIn("--mixed-alt-ooo-rate must be between 0.0 and 1.0", proc2.stderr + proc2.stdout)

    def test_mixed_synthetic_mode_reports_both_sources(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            summary_json = root / "summary.json"
            run_dir = root / "runs"
            cmd = [
                sys.executable,
                "demo/correctness_checker.py",
                "--duration-seconds",
                "2",
                "--source-mode",
                "mixed",
                "--ooo-rate",
                "0.05",
                "--mixed-alt-ooo-rate",
                "0.20",
                "--out-dir",
                str(run_dir),
                "--artifact-mode",
                "minimal",
                "--summary-json-out",
                str(summary_json),
                "--run-id",
                "cc_test_mixed_syn",
            ]
            proc = subprocess.run(cmd, cwd=str(REPO_ROOT), check=False)
            self.assertIn(proc.returncode, (0, 2))
            payload = json.loads(summary_json.read_text(encoding="utf-8"))
            self.assertEqual(payload.get("source_contract"), "mixed_syn_syn")
            counters = payload.get("source_counters", {})
            self.assertGreater(counters.get("hft_syn_primary", 0), 0)
            self.assertGreater(counters.get("hft_syn_alt", 0), 0)


if __name__ == "__main__":
    unittest.main()
