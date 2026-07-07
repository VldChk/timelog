# Ponytail Simplification & Prior-Art Audit — Campaign State

Branch: `audit/ponytail-simplification` (off main @ 751a1cc / v1.3.0)
Goal: module-by-module audit of all production C (~29.7K LOC, 84 files) asking
(a) can it be simpler with zero functional/perf regression, and
(b) does existing prior art (C libraries/tools) already solve the sub-problem.
"No and no" is acceptable but must be grounded in real code (file:line).
All findings must survive a hostile cross-review panel including Codex CLI.

## Phases

- [x] P1 Scope: branch created, inventory measured (core 21.8K + bindings 7.8K prod C; 26K test C; MIT license)
- [x] P2 Module audits: 12 Claude auditors (112 findings, audit/modules/*.md + audit/fleet-summary.md) + 3 independent Codex audits (audit/codex/independent-*.md). Convergent verdict: zero library adoptions; debt is speculative completeness (dead code, unused knobs), not reinvention.
- [x] P3 Prior-art research: audit/prior-art/landscape-facts.md (18 libraries fact-checked 2026-07-07). Key: MSVC C11 atomics STILL experimental in VS2026; liburcu LGPL; CK requires __GNUC__; liblfds/munit dead; no pure-C interval/LSM/CPython-helper lib exists.
- [ ] P4 Hostile panel: RUNNING — workflow wf_e3656272-367 (10 cluster verifiers, REFUTE-by-default) + Codex cross-review (audit/codex/cross-review.md). Draft under test: audit/REPORT-draft.md (clusters A-G, ~4.4-5.2K LOC claimed).
- [ ] P5 Synthesis: `audit/REPORT.md` ranked adopt / consider / no-and-no; commit to branch

## Adoption constraints (any library recommendation must pass ALL)

- MIT-compatible license (MIT/BSD/ISC/zlib/Apache-2; no GPL/LGPL)
- Pure C (C17), builds under GCC/Clang/MSVC with -Werror | /WX
- In-memory only (no disk I/O paths pulled in)
- Respects custom allocator wrappers (tl__malloc/tl__free) or allows allocator injection
- Concurrency-touching code: TSan-clean incl. free-threaded CPython 3.14t
- Zero performance regression (v1.3 shipped append 4.3x, branchless search — perf IS the product)
- Vendorable or FetchContent-able under scikit-build-core wheels (manylinux/macOS/Windows, cp312–cp314 + cp314t)

## Audit units (P2)

| # | Unit | Files | ~LOC |
|---|------|-------|------|
| 1 | internal-datastructures | tl_intervals, tl_heap, tl_recvec, tl_seqvec, tl_tombstone_utils.h, tl_range.h, tl_search.h, tl_records.h | 2.2K |
| 2 | internal-platform | tl_sync, tl_atomic.h, tl_alloc, tl_defs.h, tl_platform.h, tl_locks.h, tl_seqlock.h, tl_math.h, tl_log, tl_refcount.h, tl_timelog_internal.h, tl_test_hooks.c | 2.5K |
| 3 | storage | tl_page, tl_segment, tl_manifest, tl_window | 3.1K |
| 4 | delta | tl_memtable, tl_memview, tl_memrun, tl_flush, tl_ooorun | 4.1K |
| 5 | query | tl_count.h, tl_pagespan_iter, tl_point, tl_plan, tl_merge_iter, tl_snapshot, tl_segment_iter, tl_submerge, tl_memrun_iter, tl_active_iter, tl_iter_build, tl_filter, tl_segment_range.h | 4.8K |
| 6 | maint | tl_compaction, tl_adaptive | 2.4K |
| 7 | orchestrator-api | tl_timelog.c, include/timelog/timelog.h, tl_export.h | 2.9K |
| 8 | bindings-timelog | py_timelog.c | 3.9K |
| 9 | bindings-infra | py_handle.c, module.c, py_errors.c | 1.9K |
| 10 | bindings-views | py_span.c, py_iter.c, py_span_iter.c, py_span_objects.c | 2.0K |
| 11 | build-test-harness | CMakeLists.txt (root+bindings), core/tests/test_harness.h + test_main.c, workflow/CI shape | 1.9K |
| 12 | cross-cutting | repo-wide duplication patterns (goto-cleanup, refcount idiom, iterator vtables, error macros, duplicated searches) | — |

Scoping note: the 26K LOC of C test *bodies* are audited via the harness pattern +
duplication sampling (unit 11/12), not line-by-line; the 761-line Python facade is
out of scope (ask was C boilerplate).
