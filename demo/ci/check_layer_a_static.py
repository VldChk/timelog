#!/usr/bin/env python3
"""Production-source regression checks for per-interpreter isolation.

Scans the CPython binding sources for patterns that would break heap-type
isolation across subinterpreters (static type objects, cached module
globals, GIL-only claims in docs, etc.).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[2]
SCAN_ROOTS = (
    ROOT / "bindings" / "cpython" / "src",
    ROOT / "bindings" / "cpython" / "include",
)

EXTRA_TEXT_SCAN_FILES = (
    ROOT / "python" / "timelog" / "__init__.py",
    ROOT / "bindings" / "cpython" / "include" / "timelogpy" / "py_timelog.h",
)


@dataclass(frozen=True)
class Rule:
    name: str
    pattern: re.Pattern[str]


RULES = (
    Rule(
        "static extension type address",
        re.compile(r"&Py[A-Za-z0-9_]+_Type\b"),
    ),
    Rule(
        "extern static extension type declaration",
        re.compile(r"\bextern\s+PyTypeObject\s+Py[A-Za-z0-9_]+_Type\b"),
    ),
    Rule(
        "production static extension type object",
        re.compile(r"^\s*(?:static\s+)?PyTypeObject\s+Py[A-Za-z0-9_]+_Type\b"),
    ),
    Rule(
        "static type ready path",
        re.compile(r"\bPyType_Ready\s*\(\s*&Py"),
    ),
    Rule(
        "Step 3 module binding scaffold",
        re.compile(r"\btl_py_timelog_bind_module_context\b"),
    ),
    Rule(
        "production sys.modules binding lookup",
        re.compile(r"\bsys\.modules\b|\"sys\.modules\""),
    ),
    Rule(
        "legacy sys.modules lookup primitive",
        re.compile(r"\bPyImport_GetModule(?:Dict)?\b"),
    ),
    Rule(
        "cached owning module field",
        re.compile(r"\bowning_module\b"),
    ),
    Rule(
        "cached exception context",
        re.compile(r"\b(?:exc_ctx|TlPy_ExcContext|tl_py_exc_ctx_t)\b"),
    ),
    Rule(
        "manual weakref list field",
        re.compile(r"\bweakreflist\b"),
    ),
    Rule(
        "old global exception object",
        re.compile(r"\bPyTimelog(?:Busy)?Error\b"),
    ),
    Rule(
        "false subinterpreter support declaration",
        re.compile(r"\bPy_MOD_MULTIPLE_INTERPRETERS_NOT_SUPPORTED\b"),
    ),
    Rule(
        "false no-subinterpreter wording",
        re.compile(r"\bdeclares no subinterpreters\b", re.IGNORECASE),
    ),
)

TEXT_RULES = (
    Rule(
        "stale GIL-only claim",
        re.compile(
            r"(?:"
            r"\b(?:requires|needs|depends\s+on)\s+"
            r"(?:the\s+)?(?:CPython\s+)?GIL\b"
            r"|\bmust\s+(?:hold|be\s+held)\s+(?:the\s+)?(?:CPython\s+)?GIL\b"
            r"|\b(?:called|run|runs|running)\s+with\s+"
            r"(?:the\s+)?(?:CPython\s+)?GIL\s+held\b"
            r"|\bwith\s+(?:the\s+)?(?:CPython\s+)?GIL\s+held\b"
            r"|\b(?:currently|still)\s+(?:relies|rely|assumes|assume|depends)\s+"
            r"(?:on\s+)?(?:the\s+)?(?:CPython\s+)?GIL\b"
            r"|\bGIL[- ](?:only|based)\b"
            r")",
            re.IGNORECASE,
        ),
    ),
)


def iter_source_files() -> list[Path]:
    files: list[Path] = []
    for root in SCAN_ROOTS:
        files.extend(
            path
            for path in root.rglob("*")
            if path.suffix in {".c", ".h"} and path.is_file()
        )
    return sorted(files)


def iter_text_files() -> list[Path]:
    files = {
        path for path in EXTRA_TEXT_SCAN_FILES
        if path.is_file()
    }
    files.update(
        path for path in ROOT.glob("*.md")
        if path.is_file()
    )
    files.update(iter_source_files())
    docs_root = ROOT / "docs"
    if docs_root.is_dir():
        # Scan user-facing docs only. Internal planning/acceptance artifacts
        # under docs/superpowers/ legitimately quote historical "GIL-required"
        # criterion names and migration-blocker descriptions, so they would
        # produce false positives against the stale-claim text rules.
        plans_root = docs_root / "superpowers"
        files.update(
            path for path in docs_root.rglob("*.md")
            if path.is_file() and plans_root not in path.parents
        )
    ideas_root = ROOT / "ideas-lab"
    if ideas_root.is_dir():
        files.update(
            path for path in ideas_root.rglob("*.md")
            if path.is_file()
        )
    return sorted(files)


def strip_c_comments(text: str) -> str:
    """Remove C comments so rationale comments can mention forbidden tokens."""
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    text = re.sub(r"//.*", "", text)
    return text


def check_heap_traverse_invariants(path: Path, text: str) -> list[str]:
    if "PyType_FromModuleAndSpec" not in text:
        return []

    rel = path.relative_to(ROOT)
    violations: list[str] = []
    pattern = re.compile(
        r"static\s+int\s+([A-Za-z0-9_]*traverse)\s*\([^)]*\)\s*\{",
        re.MULTILINE,
    )

    for match in pattern.finditer(text):
        start = match.end()
        depth = 1
        pos = start
        while pos < len(text) and depth > 0:
            char = text[pos]
            if char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
            pos += 1

        body = text[start:pos - 1]
        if "Py_VISIT(Py_TYPE(" not in body:
            lineno = text.count("\n", 0, match.start()) + 1
            violations.append(
                f"{rel}:{lineno}: heap-type traverse must visit Py_TYPE: "
                f"{match.group(1)}"
            )

    return violations


def main() -> int:
    violations: list[str] = []

    for path in iter_source_files():
        rel = path.relative_to(ROOT)
        raw = path.read_text(encoding="utf-8")
        text = strip_c_comments(raw)
        for lineno, line in enumerate(text.splitlines(), 1):
            for rule in RULES:
                if rule.pattern.search(line):
                    violations.append(f"{rel}:{lineno}: {rule.name}: {line.strip()}")
        violations.extend(check_heap_traverse_invariants(path, text))

    for path in iter_text_files():
        rel = path.relative_to(ROOT)
        for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            for rule in TEXT_RULES:
                if rule.pattern.search(line):
                    violations.append(f"{rel}:{lineno}: {rule.name}: {line.strip()}")

    if violations:
        print("Layer A static regression check failed:", file=sys.stderr)
        for violation in violations:
            print(f"  {violation}", file=sys.stderr)
        return 1

    print("Layer A static regression check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
