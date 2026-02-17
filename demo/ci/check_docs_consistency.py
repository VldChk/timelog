#!/usr/bin/env python3
"""Basic docs quality checks.

Checks:
1) Markdown links inside docs/ resolve.
2) Core API symbols referenced by docs baseline exist in timelog.h.
3) Python facade symbols referenced by docs baseline exist in python/timelog/__init__.py.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

LINK_RE = re.compile(r"\[[^\]]+\]\(([^)]+)\)")

REQUIRED_C_SYMBOLS = [
    "tl_open",
    "tl_close",
    "tl_append",
    "tl_append_batch",
    "tl_delete_range",
    "tl_delete_before",
    "tl_flush",
    "tl_compact",
    "tl_snapshot_acquire",
    "tl_iter_range",
    "tl_iter_point",
    "tl_maint_start",
    "tl_maint_stop",
    "tl_maint_step",
    "tl_stats",
]

REQUIRED_PY_SYMBOLS = [
    "class Timelog",
    "def append(",
    "def extend(",
    "def __getitem__(",
    "def at(",
    "def delete(",
    "def cutoff(",
    "def views(",
    "def reopen(",
    "def configure(",
    "def for_streaming(",
    "def for_bulk_ingest(",
    "def for_low_latency(",
]


def _iter_md_files(root: Path) -> list[Path]:
    return sorted(p for p in root.rglob("*.md") if p.is_file())


def _check_links(repo_root: Path, docs_root: Path) -> list[str]:
    errors: list[str] = []
    all_files = {p.resolve() for p in repo_root.rglob("*") if p.is_file()}

    for md in _iter_md_files(docs_root):
        text = md.read_text(encoding="utf-8", errors="replace")
        for match in LINK_RE.finditer(text):
            target = match.group(1).strip()
            if not target or target.startswith("#"):
                continue
            if target.startswith("http://") or target.startswith("https://"):
                continue
            target = target.split("#", 1)[0].strip()
            if not target:
                continue
            resolved = (md.parent / target).resolve()
            if resolved.is_dir():
                continue
            if resolved not in all_files:
                errors.append(f"Broken link: {md.as_posix()} -> {target}")

    return errors


def _check_c_symbols(repo_root: Path) -> list[str]:
    errors: list[str] = []
    header = repo_root / "core/include/timelog/timelog.h"
    text = header.read_text(encoding="utf-8", errors="replace")
    for sym in REQUIRED_C_SYMBOLS:
        if re.search(rf"\b{re.escape(sym)}\b", text) is None:
            errors.append(f"Missing C symbol in header: {sym}")
    return errors


def _check_python_symbols(repo_root: Path) -> list[str]:
    errors: list[str] = []
    py_api = repo_root / "python/timelog/__init__.py"
    text = py_api.read_text(encoding="utf-8", errors="replace")
    for sym in REQUIRED_PY_SYMBOLS:
        if sym not in text:
            errors.append(f"Missing Python API symbol: {sym}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description="Run docs consistency checks.")
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="Repository root path.",
    )
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    docs_root = repo_root / "docs"

    issues: list[str] = []
    issues.extend(_check_links(repo_root, docs_root))
    issues.extend(_check_c_symbols(repo_root))
    issues.extend(_check_python_symbols(repo_root))

    if issues:
        print("Docs consistency check failed:")
        for issue in issues:
            print(f"- {issue}")
        return 1

    print("Docs consistency check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
