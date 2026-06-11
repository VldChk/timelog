# Productionization — Master Plan & Tracker

**Scope (ONLY the 🟩 "Worth productionizing — measured wins" from `AUDIT_REPORT.md`):**
1. **Branchless `lower_bound`** extended to all 5 search seams (core, lowest risk → first).
2. **`METH_FASTCALL`** across all positional query/delete methods (binding).
3. **Fold facade `append` into C** (`METH_FASTCALL|METH_KEYWORDS`, all 3 signatures, auto-ts, drop override).
4. **Document/tune `max_delta_segments`** (docs/config guidance).
5. **Cheap hardening/docs bundle** (PEP 688 annotation+test, FT-wheel GIL-disabled import check,
   tp_vectorcall-avoidance note, h[]-non-export safety note, positioning precision).

*Out of scope:* C2-bulk, C3-arrow, C3-dlpack (🟦 "validate first").

**Branch:** `feat/perf-wins` @ worktree `/home/vldvhk/Documents/tl-feat-perf`, off pristine baseline `e7e7efb`.

## Per-idea rigor loop (mandatory, every idea)
1. **Detailed plan** — exact files/functions, the transform, correctness argument, risks, measurement,
   the test that would catch a regression.
2. **Hostile plan review** — ≥2 independent adversarial subagents try to break the plan (correctness holes,
   missed call sites, ABI/FT hazards, measurement flaws). Incorporate or rebut each finding.
3. **Implementation** — minimal, idiomatic, matches surrounding code.
4. **Hostile implementation review** — ≥2 independent adversarial subagents attack the diff (UB, refcount,
   off-by-one, FT, ABI, test-weakening). Fix or rebut each.
5. **Gate** — full green: 480 core, 9/9 ctest, 98 pytest, + idea-specific differential/measurement. Commit.

## Known-green baseline (the regression bar — confirmed before any change)
- `./build-rel/test_timelog` → **480 passed, 0 failed**
- `ctest` → **9/9 suites passed**
- `pytest python/tests` → **98 passed, 16 skipped**
- (validation phase adds: Debug ASan/UBSan, 3.14t free-threaded, the lab/ differential+property suite.)

## Final E2E (after all ideas) — extreme rigor, zero regression
- Release + Debug(ASan/UBSan) core + binding + pytest on 3.13.
- Free-threaded 3.14t: pytest + binding + lab concurrency.
- The `lab/` differential+property suite (oracle-checked) on 3.13 & 3.14t.
- All `ideas-lab/` harnesses re-run green.
- Perf re-confirmation of each win (no measurement regression).
- Static/docs/lint gates (`check_layer_a_static.py`, `check_docs_consistency.py`, `git diff --check`).
- **Acceptance:** every suite ≥ baseline counts; zero new failures, leaks, or accuracy deltas.

## Status
| # | Idea | Plan | Plan-review | Impl | Impl-review | Gate |
|---|------|:----:|:-----------:|:----:|:-----------:|:----:|
| 1 | Branchless lower_bound (5 seams) | ✅ | ✅ | ✅ | ✅ | ✅ commit 01ca67b |
| 2 | METH_FASTCALL all positional | ✅ | ✅✅ | ✅ | ✅✅ | ✅ commit 30d1c7e |
| 3 | Facade-fold append into C | ✅ | ✅✅ | ✅ | ✅✅ | ✅ commit e0d6925 (A) + 786725e (B); ci-fix e0868d0 |
| 4 | max_delta_segments docs | ✅ | ✅✅ | ✅ | ✅✅✅ | ✅ commit b3ff179 |
| 5 | Cheap hardening/docs bundle | ✅ | ✅✅ | ✅ | ✅✅ | ✅ commit 1b74c3e |

**All 5 ideas committed.** Branch `feat/perf-wins`: 01ca67b, 30d1c7e, e0d6925, 786725e, e0868d0, b3ff179, 1b74c3e.

## Current verification status after dirty-tree review/fix pass (2026-06-09)

The seven committed ideas remain the intended productionization scope, but the
worktree under review has additional dirty edits after those commits. The older
"ALL GREEN, ZERO REGRESSION" table is therefore historical provenance, not a
current merge claim. This pass fixed the confirmed dirty-tree compatibility/docs
issues and reran regular, ASan/UBSan, release free-threaded, focused
free-threaded TSan, and same-harness perf A/B gates. This pass also found and
fixed a critical free-threaded build-system issue: binding objects compiled
against a free-threaded interpreter were not receiving `Py_GIL_DISABLED=1`, so
CPython object critical sections could compile out. Native/core TSan is now
confirmed after fixing sanitizer build wiring; focused free-threaded Python TSan
is confirmed with Clang 19 plus narrow CPython-runtime suppressions.

| Area | Current status |
|------|----------------|
| Regular CPython 3.13 | Fresh dirty-tree evidence: release configure/build passed without `Py_GIL_DISABLED`; append/FASTCALL contract slice `77 passed`; full Python `183 passed / 16 skipped`; CTest `9/9`; storage branchless group `1/1` with summary preserved under `ideas-lab/verification`; direct five-seam branchless benchmark exit 0 with no correctness mismatches and `1` advisory fallback timing warning; docs/static/diff checks passed; recovered naked-unlocked-context lint clean against its 17-site baseline; docs benchmark JSON artifacts are visible to Git after the narrow `.gitignore` whitelist. |
| ASan/UBSan | Fresh dirty-tree evidence: sanitizer build passed; ASan/UBSan CTest `9/9`; ASan/UBSan full Python `183 passed / 16 skipped`. |
| 3.14t free-threaded | Fresh dirty-tree evidence: release configure/build passed with generated `_timelog` flags showing `-DPy_GIL_DISABLED=1`; staged extension has no ASan/UBSan/TSan dependency; `PYTHON_GIL=0` full Python suite `198 passed / 1 skipped`; CTest `9/9`; focused free-threaded TSan suite `9 passed` with no TSan report files under Clang 19 and narrow CPython-runtime suppressions. The valid TSan artifact is `ideas-lab/verification/clang19_tsan_freethreaded_repo_suppressions_valid_2026-06-10.txt`, which verifies the staged package extension matched the TSan-built `.so`. |
| Lab correctness | Temp lab runner `python/` symlink resolves to `tl-feat-perf/python`. Branch-specific reports are preserved under `ideas-lab/verification`: 3.13 June 9 lab `112/112`, `2858 cases`; fresh post-`Py_GIL_DISABLED` release 3.14t GIL-off June 10 lab `112/112`, `2867 cases`, `54.9s` wall (`lab_3.14t_tl_feat_release_after_pygil_fix_2026-06-10.md`). Fresh supplemental PR-profile oracle check: 30s synthetic 5% OOO, seed `12345`, `380` ops, `723` checks, `558713` inserts, `59425` deletes, `0` issues. |
| Perf A/B | Fresh clean-baseline A/B: baseline worktree at `e7e7efb`, current `tl-feat-perf`, same Python microbench harness, CPU pinning succeeded. Raw median artifacts are preserved under `ideas-lab/verification/perf_ab_extended_*_2026-06-09.json`. Facade append signatures: `append(obj)` `4.39x`, `append(ts,obj)` `3.39x`, `append(obj, ts=...)` `3.33x`. Raw changed call surfaces all faster: `point` `1.36x`, `equal` `1.28x`, `next_ts` `1.31x`, `prev_ts` `1.15x`, `range` `1.26x`, `since` `1.27x`, `until` `1.23x`, `delete_before` `1.36x`, `delete_range` `1.36x`. |
| TSan | Native/core TSan: generated flags show `-fsanitize=thread` for core, `_timelog`, and `test_py_handle`; direct `test_py_handle` passed `13/13` under TSan with no report files; core `timelog_tests` passed under TSan with no report files. Free-threaded Python TSan: GCC libtsan still aborts Python startup with `unexpected memory mapping`; Clang 19 TSan starts Python, unsuppressed runs report CPython BRC/dict internals even without Timelog, and the focused Timelog suite passes `9/9` after narrow CPython-runtime suppressions plus Timelog TSan annotations for CPython critical-section wrappers. |
| Remaining final matrix | No local product blocker remains from this pass. For CI hardening, keep the free-threaded TSan leg using a runtime/suppression setup that can distinguish CPython-runtime reports from Timelog frames. |
| Append C-fold | Text signature now matches keyword-bindable legacy names; runtime keyword compatibility is probed; lifecycle/reopen races are documented as externally serialized rather than claimed safe. |
| FASTCALL methods | Focused binding review found no refcount/UAF blocker; regular and focused 3.14t gates passed after dirty fixes. |
| Branchless search | Correctness coverage reaches the five changed seams. The opt-in benchmark now directly times all five seams and exits 0 with no correctness mismatches. It shows `1.93x-4.98x` wins at the gated sizes across all seams, but records `1` advisory timing warning on a recvec fallback size above the gate; keep the large-size fallback claim bounded until a cleaner A/B benchmark confirms the warning is noise rather than a real recvec fallback cost. |
| `max_delta_segments` docs | Conceptual guidance is sound; raw JSON artifacts, replay commands, seeds, and `compact()` request wording are now in docs. |
| Static/docs guards | Docs checker now strips comments/`#if 0`, validates active `TL_API` declarations, checks facade AST methods, and guards the public binding method table. |

Do not claim unsuppressed CPython free-threaded TSan is clean on this host:
unsuppressed TSan reports CPython runtime internals before Timelog-specific
analysis is useful. With narrow CPython-runtime suppressions, the focused
Timelog free-threaded TSan suite is now clean on the current tree.

Order chosen by **risk-ascending** so each idea builds on a validated foundation: core algorithm (1) →
binding convention (2) → binding+facade semantics (3) → docs (4,5).

### Idea 3 outcome note (for the record)
Hostile review found a **MAJOR** free-threading defect the single-threaded first
reviewer could not see: the folded append read the new C floor fields
(`has_min_ts_floor` / `min_ts_floor`) and `time_unit` on the hot path before
`core_lock`, as plain fields written unsynchronized in `_set_min_ts_floor` /
`PyTimelog_init` -> torn-read UB and a fail-open window during lifecycle races.

The atomic-field fix addresses the torn-read class. The current branch does not
attempt to support concurrent lifecycle/reopen: Python and C docs now state that
`close`/`reopen`/`configure` must be externally serialized against other users
of the same instance. Do not present concurrent lifecycle/reopen as supported
unless the floor/config application moves into the C reopen path before
`closed=0`.
