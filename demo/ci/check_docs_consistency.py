#!/usr/bin/env python3
"""Basic docs quality checks.

Checks:
1) Markdown links inside docs/ resolve.
2) Core API symbols referenced by docs baseline exist in timelog.h.
3) Python facade symbols referenced by docs baseline exist in python/timelog/__init__.py.
"""

from __future__ import annotations

import argparse
import ast
import re
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

REQUIRED_PY_CLASS = "Timelog"
REQUIRED_PY_METHODS = [
    "extend",
    "__setitem__",
    "__len__",
    "__iter__",
    "__getitem__",
    "at",
    "delete",
    "__delitem__",
    "cutoff",
    "views",
    "reopen",
    "configure",
    "for_streaming",
    "for_bulk_ingest",
    "for_low_latency",
]

# Methods exposed through the C extension base class rather than as Python
# ``def`` statements. The docs intentionally present the public facade and
# inherited binding as one API, so guard the complete public method-table surface
# instead of only the newly folded append path.
REQUIRED_BINDING_METHODS = [
    "append",
    "bulk_append",
    "extend",
    "delete_range",
    "delete_before",
    "flush",
    "compact",
    "maint_step",
    "stats",
    "start_maintenance",
    "stop_maintenance",
    "close",
    "range",
    "since",
    "until",
    "all",
    "equal",
    "point",
    "min_ts",
    "max_ts",
    "next_ts",
    "prev_ts",
    "validate",
    "page_spans",
    "views",
    "__enter__",
    "__exit__",
]

REQUIRED_BINDING_PATTERNS = {
    "append": re.compile(
        r'\{\s*"append"\s*,\s*\(PyCFunction\).*?PyTimelog_append\s*,\s*'
        r'METH_FASTCALL\s*\|\s*METH_KEYWORDS',
        re.DOTALL,
    ),
    "bulk_append": re.compile(
        r'\{\s*"bulk_append"\s*,\s*\(PyCFunction\).*?PyTimelog_bulk_append\s*,\s*'
        r'METH_VARARGS\s*\|\s*METH_KEYWORDS',
        re.DOTALL,
    ),
}

METHOD_TABLE_RE = re.compile(
    r"static\s+PyMethodDef\s+PyTimelog_methods\[\]\s*=\s*\{(?P<body>.*?)\n\s*\};",
    re.DOTALL,
)


def _strip_c_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    return re.sub(r"//[^\n]*", "", text)


def _strip_inactive_preprocessor_blocks(text: str) -> str:
    lines = text.splitlines()
    out: list[str] = []
    disabled_depth = 0
    for line in lines:
        stripped = line.strip()
        if re.match(r"#\s*if\s+0\b", stripped):
            disabled_depth += 1
            continue
        if disabled_depth:
            if re.match(r"#\s*if(?:def|ndef)?\b", stripped):
                disabled_depth += 1
            elif re.match(r"#\s*endif\b", stripped):
                disabled_depth -= 1
            continue
        out.append(line)
    return "\n".join(out)


def _active_c_text(text: str) -> str:
    return _strip_c_comments(_strip_inactive_preprocessor_blocks(text))


def _declares_tl_api(text: str, sym: str) -> bool:
    return re.search(rf"\bTL_API\b[^;{{}}]*\b{re.escape(sym)}\s*\(", text) is not None


def _iter_md_files(root: Path) -> list[Path]:
    return sorted(p for p in root.rglob("*.md") if p.is_file())


def _check_links(docs_root: Path) -> list[str]:
    errors: list[str] = []

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
            if not resolved.is_file():
                errors.append(f"Broken link: {md.as_posix()} -> {target}")

    return errors


def _check_c_symbols(repo_root: Path) -> list[str]:
    errors: list[str] = []
    header = repo_root / "core/include/timelog/timelog.h"
    try:
        text = header.read_text(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return [f"Missing required file: {header.as_posix()}"]
    except OSError as exc:
        return [f"Failed reading {header.as_posix()}: {exc}"]
    text = _active_c_text(text)
    for sym in REQUIRED_C_SYMBOLS:
        if not _declares_tl_api(text, sym):
            errors.append(f"Missing active TL_API declaration in header: {sym}")
    return errors


def _check_python_symbols(repo_root: Path) -> list[str]:
    errors: list[str] = []
    py_api = repo_root / "python/timelog/__init__.py"
    try:
        text = py_api.read_text(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return [f"Missing required file: {py_api.as_posix()}"]
    except OSError as exc:
        return [f"Failed reading {py_api.as_posix()}: {exc}"]
    try:
        tree = ast.parse(text, filename=py_api.as_posix())
    except SyntaxError as exc:
        return [f"Failed parsing {py_api.as_posix()}: {exc}"]

    timelog_class = next(
        (
            node for node in tree.body
            if isinstance(node, ast.ClassDef) and node.name == REQUIRED_PY_CLASS
        ),
        None,
    )
    if timelog_class is None:
        return [f"Missing Python API class: {REQUIRED_PY_CLASS}"]

    methods = {
        node.name for node in timelog_class.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    for method in REQUIRED_PY_METHODS:
        if method not in methods:
            errors.append(
                f"Missing Python API method: {REQUIRED_PY_CLASS}.{method}"
            )
    return errors


def _check_binding_methods(repo_root: Path) -> list[str]:
    errors: list[str] = []
    binding = repo_root / "bindings/cpython/src/py_timelog.c"
    try:
        text = binding.read_text(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return [f"Missing required file: {binding.as_posix()}"]
    except OSError as exc:
        return [f"Failed reading {binding.as_posix()}: {exc}"]
    text = _active_c_text(text)
    match = METHOD_TABLE_RE.search(text)
    if match is None:
        return ["Missing PyTimelog_methods method table"]
    body = match.group("body")
    method_names = set(re.findall(r'\{\s*"([^"]+)"\s*,', body))
    for name in REQUIRED_BINDING_METHODS:
        if name not in method_names:
            errors.append(f"Missing or misconfigured binding method-table entry: {name}")
    for name, pattern in REQUIRED_BINDING_PATTERNS.items():
        if pattern.search(body) is None:
            errors.append(f"Binding method-table entry has wrong flags/callee: {name}")
    return errors


def _run_self_check() -> int:
    good = '''
    static PyMethodDef PyTimelog_methods[] = {
        {"append", (PyCFunction)(void(*)(void))PyTimelog_append,
         METH_FASTCALL | METH_KEYWORDS, "doc"},
        {NULL, NULL, 0, NULL}
    };
    '''
    bad_comment = '''
    static PyMethodDef PyTimelog_methods[] = {
        /* {"append", (PyCFunction)(void(*)(void))PyTimelog_append,
           METH_FASTCALL | METH_KEYWORDS, "doc"}, */
        {NULL, NULL, 0, NULL}
    };
    '''
    bad_if0 = '''
    static PyMethodDef PyTimelog_methods[] = {
    #if 0
        {"append", (PyCFunction)(void(*)(void))PyTimelog_append,
         METH_FASTCALL | METH_KEYWORDS, "doc"},
    #endif
        {NULL, NULL, 0, NULL}
    };
    '''

    def has_append(src: str) -> bool:
        match = METHOD_TABLE_RE.search(_active_c_text(src))
        if match is None:
            return False
        body = match.group("body")
        return REQUIRED_BINDING_PATTERNS["append"].search(body) is not None

    if not has_append(good):
        print("Self-check failed: active append entry was not detected")
        return 1
    if has_append(bad_comment):
        print("Self-check failed: commented append entry was detected")
        return 1
    if has_append(bad_if0):
        print("Self-check failed: #if 0 append entry was detected")
        return 1

    good_c_api = "TL_API tl_status_t tl_open(const tl_config_t* cfg, tl_timelog_t** out);"
    bad_c_api_comment = "/* TL_API tl_status_t tl_open(const tl_config_t* cfg, tl_timelog_t** out); */"
    bad_c_api_if0 = "#if 0\nTL_API tl_status_t tl_open(const tl_config_t* cfg, tl_timelog_t** out);\n#endif"
    if not _declares_tl_api(_active_c_text(good_c_api), "tl_open"):
        print("Self-check failed: active TL_API declaration was not detected")
        return 1
    if _declares_tl_api(_active_c_text(bad_c_api_comment), "tl_open"):
        print("Self-check failed: commented TL_API declaration was detected")
        return 1
    if _declares_tl_api(_active_c_text(bad_c_api_if0), "tl_open"):
        print("Self-check failed: #if 0 TL_API declaration was detected")
        return 1

    good_py = '''
class Timelog:
    def extend(self): pass
    def __setitem__(self): pass
    def __len__(self): pass
    def __iter__(self): pass
    def __getitem__(self): pass
    def at(self): pass
    def delete(self): pass
    def __delitem__(self): pass
    def cutoff(self): pass
    def views(self): pass
    def reopen(self): pass
    def configure(self): pass
    def for_streaming(self): pass
    def for_bulk_ingest(self): pass
    def for_low_latency(self): pass
'''
    bad_py_comment = '''
class Timelog:
    # def extend(self): pass
    def __setitem__(self): pass
    def __len__(self): pass
    def __iter__(self): pass
    def __getitem__(self): pass
    def at(self): pass
    def delete(self): pass
    def __delitem__(self): pass
    def cutoff(self): pass
    def views(self): pass
    def reopen(self): pass
    def configure(self): pass
    def for_streaming(self): pass
    def for_bulk_ingest(self): pass
    def for_low_latency(self): pass
'''

    def has_required_python_methods(src: str) -> bool:
        tree = ast.parse(src)
        cls = next(
            node for node in tree.body
            if isinstance(node, ast.ClassDef) and node.name == REQUIRED_PY_CLASS
        )
        methods = {
            node.name for node in cls.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        }
        return all(method in methods for method in REQUIRED_PY_METHODS)

    if not has_required_python_methods(good_py):
        print("Self-check failed: active Python methods were not detected")
        return 1
    if has_required_python_methods(bad_py_comment):
        print("Self-check failed: commented Python method was detected")
        return 1
    print("Docs consistency self-check passed.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Run docs consistency checks.")
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="Repository root path.",
    )
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="Run internal parser self-check fixtures.",
    )
    args = parser.parse_args()
    if args.self_check:
        return _run_self_check()

    repo_root = args.repo_root.resolve()
    docs_root = repo_root / "docs"

    issues: list[str] = []
    issues.extend(_check_links(docs_root))
    issues.extend(_check_c_symbols(repo_root))
    issues.extend(_check_python_symbols(repo_root))
    issues.extend(_check_binding_methods(repo_root))

    if issues:
        print("Docs consistency check failed:")
        for issue in issues:
            print(f"- {issue}")
        return 1

    print("Docs consistency check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
