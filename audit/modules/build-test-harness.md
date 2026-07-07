# Ponytail Audit — Unit: build-test-harness

Auditor persona: lazy senior dev. Scope: root + bindings CMakeLists, hand-rolled C test
harness (`test_harness.h` / `test_main.c`), binding test mini-harnesses, CI helper scripts,
17-workflow fleet shape. All four assigned files read line-by-line in full; supporting
files (representative test files, workflows, demo/ci scripts) read or diffed as evidence.

## Executive Summary

The core C harness is small, honest, and earns its keep — **NO and NO** on replacing it
with Unity/greatest/µnit. The real fat is elsewhere:

1. **~700–850 LOC of copy-pasted mini-harness across the 8 binding test files** (identical
   `tlpy_set_pythonhome`, TEST/ASSERT macros, counters, summary epilogue in every file).
2. **~250–280 LOC of copy-pasted CMake target blocks** in `bindings/cpython/CMakeLists.txt`
   (8 near-identical test-executable stanzas + 9 repetitions of the same compile-options block).
3. **A 298-line Python script (`run_core_test_groups.py`) that reimplements what CTest
   already does natively** (per-test env properties, per-test pass/fail/timing, `-j`).
4. Small but clean deletions: a byte-identical duplicated function in `test_main.c`, dead
   macros in `test_harness.h`, a never-enabled CMake option/target, and two
   CI-dead platform-support blocks (Windows-Clang) in the root CMakeLists.
5. The "17 workflows" question, LOC-weighed honestly: **1836 LOC total, median ~104; most
   legs are genuinely distinct.** Realistic dedup is ~250–300 LOC (compat pr/main pair via
   `workflow_call`, a shared setup composite action, dropping redundant `tee`-to-.log
   plumbing) — worth doing opportunistically, not a rewrite.

Total realistic savings in this unit: **~1,400–1,700 LOC**, none of it on any hot path
(build/test/CI infrastructure only — zero engine perf exposure by construction).

---

## Per-File Walkthrough

### 1. `core/tests/test_harness.h` (181 lines)

Hand-rolled xUnit-style harness: global context, result array, assertion macros with
type-safe variants, forward decls for fail-reporting helpers.

**Findings:**

- **[F2, rung 1 — dead code]** `TEST_MAX_NAME_LEN` (line 14) is defined and never used
  anywhere (`grep -rn TEST_MAX_NAME_LEN core/ bindings/` → only the definition).
  `test_entry_t` / `TEST_ENTRY` (lines 46–52, "{ #name, test_##name }") are never
  instantiated anywhere in the tree — a registration-table design that was abandoned in
  favor of `RUN_TEST` lists. `test_result_t.file`/`.line` (lines 23–24) are written by
  `test_fail` (test_main.c:50–51) but never read: `test_report` prints only
  `name` + `message` (test_main.c:118–123), and the file:line is already printed inline at
  failure time (test_main.c:56). Delete all three. **~15 LOC saved. Risk: low.**

- **[F3, rung 7 — minimal rewrite]** `test_context_t.results[TEST_MAX_TESTS]`
  (lines 30–35) is a `1000 × ~544 B ≈ 544 KB` static array holding a record for *every*
  test, pass or fail (`test_run` pushes on pass, test_main.c:39; `test_fail` pushes on
  fail, test_main.c:48). Both writes are **unbounded**: `results[g_test_ctx.count++]` has
  no cap check, and the Debug/ASan suite is already at ~497 of the 1000 cap ("Counts drift
  as suites grow" — CLAUDE.md). When the suite crosses 1000, this is a silent global-array
  overflow *inside the test framework* (ASan will catch it, confusingly). The pass records
  are pure waste: only the failure recap loop (test_main.c:118) reads the array.
  Store failures only (passes need only the counter), or at minimum bounds-check.
  **~10 LOC saved + latent overflow removed. Risk: low; behavior identical for all
  passing runs.**

- **Known limitation noted for the record (not a finding):** `TEST_ASSERT*` `return`s out
  of the *current function*, so an assert inside a helper function fails the message but
  lets the test continue — the same limitation greatest/Unity have without their
  assert-propagation idioms. No evidence it has bitten; fixing it is what a framework
  adoption would buy (see Prior Art).

### 2. `core/tests/test_main.c` (357 lines)

Framework implementation (~130 lines) + group-gated dispatch of 15 suite runners.

**Findings:**

- **[F1, rung 6 — one-liner]** `test_group_enabled` (lines 134–164) and
  `test_name_enabled` (lines 166–196) are **byte-identical** functions (same
  comma-separated exact-match scan; only the parameter name differs: `groups` vs
  `filter`). Delete one, call the survivor from both sites (lines 23 and 269–350).
  **~30 LOC saved. Risk: low** — filter behavior covered by CI, which drives
  `TL_TEST_GROUPS` through `run_core_test_groups.py` on every PR (tests-pr.yml:50).

- **[F9-adjacent, rung 7]** `main()` (lines 253–357) is 15 copies of the same 5-line
  pattern: `if (test_group_enabled(groups, "X")) { printf(banner); run_X_tests(); }`.
  A static table `{const char* group; const char* banner; void (*fn)(void);}` + one loop
  collapses ~100 lines to ~35. Also gives `run_core_test_groups.py` (or its CTest
  replacement, F9) one obvious place to stay in sync with. **~55 LOC saved. Risk: low.**

- **Registration drift check (evidence for Prior Art fit notes):** per-file
  `TEST_DECLARE` vs `RUN_TEST` counts currently match exactly in all 14 test files
  (86/86, 27/27, 18/18, 6/6, 86/86, 71/71, 62/62, 21/21, 11/11, 22/22, 5/5, 4/4, 82/82,
  4/4 — verified by grep). The hazard (a `TEST_DECLARE`'d test silently never run) is
  structural but has not materialized. 505 manual `RUN_TEST` lines exist tree-wide.

### 3. Root `CMakeLists.txt` (403 lines)

Mostly disciplined. Sanitizer plumbing (lines 100–133) is verbose but deliberate — the
per-build-type loop exists to instrument the RelWithDebInfo FT-TSan CI leg (comment at
114–118) while keeping Release clean. Keep.

**Findings:**

- **[F7, rung 1 — speculative platform support]** Two blocks exist solely for
  "Clang on Windows (non-MSVC driver)":
  - lines 262–267: manual CRT lib injection (`msvcrtd.lib vcruntimed.lib ...`);
  - lines 364–390: 27 lines of clang resource-dir spelunking to put the ASan runtime DLL
    on `PATH` for `timelog_tests`.
  **No CI leg builds this configuration** (`grep -rn clang .github/workflows/` → zero
  hits; windows-latest jobs use the default MSVC generator; docs never mention
  Windows-Clang; maintainer's dev box is Linux). **~35 LOC deletion candidate. Risk:
  medium** — may be a past local-dev convenience; needs a maintainer "do you still build
  this way?" before deletion.

- **[F8, rung 1 — knob nothing sets]** `TIMELOG_BUILD_PY_FACADE_TESTS` (option at
  lines 20–21, target at 350–360). Default OFF; **every** CI configure step passes
  `-DTIMELOG_BUILD_PY_FACADE_TESTS=OFF` explicitly; nothing anywhere sets ON
  (grep across .github/, pyproject.toml, docs/, demo/ → zero); docs and CLAUDE.md tell
  users to run `PYTHONPATH=python python3 -m pytest python/tests/` directly. The target
  is a 10-line wrapper around exactly that command. **~14 LOC saved. Risk: low.**

- Minor (bundled with F5): `test_timelog`'s include-dir list (253–259) duplicates the
  timelog target's (191–198); a `TIMELOG_INTERNAL_INCLUDE_DIRS` variable dedupes ~8 lines.

- `TIMELOG_BUILD_SHARED` (line 15, + 182–186, 205–210): never ON in CI or pyproject, but
  it is a legitimate public build option for a C library and costs ~14 lines including the
  export-macro wiring. **NO-and-NO with caveat** (untested in CI — either add a cheap CI
  configure-only check or accept the risk consciously).

### 4. `bindings/cpython/CMakeLists.txt` (749 lines)

**Findings:**

- **[F5, rung 7 — minimal rewrite]** Eight test-executable stanzas
  (test_py_handle 264–300, test_py_timelog 305–352, test_py_iter 357–405,
  test_py_span 410–457, test_py_maint_b5 462–509, test_py_errors 514–558,
  test_py_module 563–596, test_py_module_exec 601–648) are structurally identical:
  `add_executable` + same 3 include dirs + `TIMELOG_PYTHON_EXECUTABLE` define +
  `target_link_libraries(timelog ${Python3_LIBRARIES})` + `timelog_copy_python_runtime` +
  a **14-line MSVC/else compile-options block repeated verbatim 9 times** (8 tests +
  `_timelog` itself, lines 204–218, 287–300, 339–352, 392–405, 444–457, 496–509, 545–558,
  583–596, 635–648). The only real variance: source list and 0–2 extra
  `TL_PY_*_TEST_HOOKS` defines. A `timelog_add_py_test(<name> SOURCES ... DEFS ...)`
  function (~35 lines) + 8 calls (~5 lines each) + the existing add_test/env epilogue
  replaces ~390 lines with ~110. **~270 LOC saved. Risk: low** — build config only; CI
  builds Linux + Windows/MSVC on every PR, breakage is loud and immediate.

- **[F6, rung 1 — speculative flexibility]** The standalone-build mode (lines 24–67):
  hunts for a prebuilt `timelog.lib`/`libtimelog.a` across four hardcoded directories
  (`build_x64/Release`, `build_x64/Debug`, `build/Release`, `build/Debug`) and imports it.
  **Nothing uses it**: scikit-build-core builds from the repo root
  (pyproject.toml:40 `cmake.source-dir = "."`), all CI configures `-S .`, no doc describes
  the standalone flow. Killing it also removes the duplicated
  `option(TIMELOG_BUILD_PY_TESTS ...)` (line 239 vs root line 17) and duplicated
  `option(TIMELOG_STAGE_PYTHON_MODULE ...)` (189–190 vs root 18–19), which exist only to
  make standalone work. **~50 LOC saved. Risk: medium** (historical Windows dev
  convenience — the `build_x64` paths suggest it was once real; ask before deleting).

### 5. Binding test files (`bindings/cpython/tests/`, 8,559 LOC total)

Read: test_py_handle.c (head), test_py_timelog.c (lines 1–200 + tail),
test_py_errors.c (tail), grep-verified across all 8 compiled files.

**Findings:**

- **[F4, rung 2 — duplicate of what should exist once in this codebase]** Every one of
  the 8 compiled test files carries its own private copy of the same mini-harness:
  - `tlpy_set_pythonhome()` — 33 identical lines in all 8 files (verified at
    test_py_timelog.c:33–65, test_py_handle.c:32–63, plus grep hits in iter/span/
    maint_b5/errors/module/module_exec);
  - `tlpy_init_python`/`tlpy_finalize_python` (~10 lines × 8);
  - `static int tests_run/tests_failed` counters (× 8);
  - `TEST`, `ASSERT`, `ASSERT_EQ` (and in most files `ASSERT_NOT_NULL`, `ASSERT_NULL`,
    `ASSERT_EXCEPTION`) macro sets, ~50–90 lines each — test_py_timelog.c:131–207 even
    says "same as test_py_handle.c" (line 23);
  - the `main()` epilogue (summary printf + `tlpy_finalize_python` + exit-code mapping);
  - `tlpy_init_test_module`/`tlpy_clear_test_module` module-bootstrap helpers duplicated
    in ≥5 files (grep: timelog=3 uses, iter=3, span=3, maint_b5=1, module_exec=12).

  Macro variance is small and unifiable to the superset (test_py_timelog's `TEST` also
  checks `PyErr_Occurred()` — strictly better; adopt everywhere). Extract
  `bindings/cpython/tests/py_test_harness.h` (~150 lines). Duplicated mass is ~900–1,050
  lines; **net ~700–850 LOC saved. Risk: low** — the tests validate themselves, run in CI
  on every PR (tests-pr.yml:65, sanitizers.yml:83), and this is compile-time-only glue.
  Note: `test_py_main.c` is a deliberate 28-line documentation stub (`#error` guarded,
  never compiled) — fine, leave it or fold its text into a README; not counted.

### 6. `demo/ci/*.py` (1,239 LOC) and the CTest boundary

- **[F9, rung 4 — platform (CTest) already provides it]** `run_core_test_groups.py`
  (298 lines) exists because CMake registers the whole core suite as **one** CTest entry
  (`add_test(NAME timelog_tests ...)`, root CMakeLists:280), so the script re-invokes
  `ctest -R '^timelog_tests$'` 13 times with `TL_TEST_GROUPS=<g>` (script line 122) to
  get per-group granularity, then hand-rolls JSON/MD summaries. CTest natively supports
  exactly this: per-test `ENVIRONMENT` properties, per-test pass/fail/duration,
  `-j` parallelism across groups (the script runs groups serially!), and
  `--output-junit`. Replacement:

  ```cmake
  foreach(g IN LISTS TIMELOG_TEST_GROUPS)   # 13 names, single source of truth
    add_test(NAME timelog_tests_${g} COMMAND test_timelog)
    set_tests_properties(timelog_tests_${g} PROPERTIES ENVIRONMENT "TL_TEST_GROUPS=${g}")
  endforeach()
  ```

  (~10 lines). This also deletes the **group-name list duplicated between
  `test_main.c:269–350` and the script's `DEFAULT_GROUPS` (lines 17–31)** — a real drift
  hazard: add a new suite today and you must edit both or CI silently skips it.
  Remaining script value is the JSON/MD `GITHUB_STEP_SUMMARY` payload consumed by
  tests-pr.yml:104–144 and sanitizers.yml artifacts; replace with `ctest --output-junit`
  + a ~40-line converter, or accept ctest's native log. **Net ~200–250 LOC saved, plus
  groups run in parallel under `ctest -j`. Risk: medium** — two workflows and
  docs/CI_TESTS.md reference the script and its summary shape; CI iteration needed.

- **[F11, rung 4/5 — platform/dependency]** `run_compat_baseline.py` (322 lines) embeds
  a pytest plugin as a source string (`_subprocess_pytest_script`, lines 129–170),
  launches `python -c <plugin>` subprocesses, and parses `TL-SUMMARY`-prefixed stdout
  lines back into a dict — a hand-rolled result protocol. pytest already ships
  `--junitxml` (stdlib-parseable), and `pytest-json-report` (MIT) emits exactly the JSON
  this script builds by hand. Leg config + markdown writer stay (~120 lines).
  **~130–160 LOC saved. Risk: medium** — summary schema is consumed by 3 workflows'
  Append-summary steps; needs coordinated change. Lower priority than F9.

- `check_layer_a_static.py` (224) and `check_docs_consistency.py` (395): purpose-built
  regex/AST checkers with no off-the-shelf equivalent at this specificity. **NO and NO**
  (glanced, structure is proportionate to the job).

### 7. `.github/workflows/` — the 17-workflow question, LOC-weighed

17 files, **1,836 LOC total, median ~104**. Verdict: the *count* is not the problem;
each file is a genuinely distinct concern (sanitizers matrix, packaging, codeql,
dependency-review at 21 lines, coverage, 2× claude automation, 2× release). Honest dedup
inventory **[F10, rung 4 — platform: reusable workflows / composite actions]**:

- **compat pr/main pair** (124 + 133 lines): `diff` = **27 lines** — triggers,
  concurrency, cron, names only. Textbook `workflow_call` reusable workflow:
  ~110 shared lines once + two ~15-line trigger shims. **~100 LOC saved.**
- **correctness pr/main pair** (95 + 108): diff shows real divergence (matrix os,
  profile pr/nightly, schedule) but the step bodies are parameterizable. **~50 LOC.**
- **benchmark pr/main pair** (101 + 126): diff = 114 lines — mostly different; leave.
- **shared setup preamble** (checkout → setup-python → pip install -r requirements-test
  → cmake configure → build timelog_e2e_build) appears in ≥8 jobs across tests-pr,
  sanitizers (×3 jobs), compat (×2), correctness (×2). A composite action
  (`.github/actions/setup-timelog`) is the platform feature for this. **~100–120 LOC.**
- **`set +e … | tee …; exit ${PIPESTATUS[0]}` blocks** (~12 occurrences, ~8 lines each):
  exist only to copy step output into uploaded `.log` artifacts, duplicating Actions'
  native per-step log capture. The JSON/MD summaries are the real artifacts; the `.log`
  tees are redundant. **~80 LOC**, but weakest claim — downloading raw logs via UI/API
  is clunkier than an artifact; maintainer preference call.

Realistic total: **~250–300 LOC (~15%)** at the cost of indirection (reusable workflows
are harder to grep/debug, `workflow_call` has permissions/secrets sharp edges). Do the
compat pair and composite action; skip the rest. **The "17 workflows = bloat" instinct
does not survive the weighing.**

---

## Prior-Art Leads (leads, not verdicts — later phases verify)

1. **C unit test framework** (subproblem: assertion macros + registration + runner +
   filtering; currently 538 owned LOC + 505 manual RUN_TEST lines):
   - `sheredom/utest.h` — single header, **Unlicense (public domain)**, GCC/Clang/MSVC
     including `-Werror`/`/WX` claims, **auto-registration** via linker sections, built-in
     `--filter=`, per-test timing. Best structural fit: deletes all 505 RUN_TEST lines,
     15 `run_*_tests` shells, and most of test_main.c; would fix the helper-assert
     limitation and the F3 overflow by construction. Cost: vendors ~1.3k lines (repo LOC
     *rises*), mechanical macro rename across ~17.5k test LOC, must verify MSVC
     `/experimental:c11atomics` + section-attribute interplay and TL-specific
     `TEST_ASSERT_STATUS`/`tl_strerror` assert would become a thin custom macro on top.
   - `silentbicycle/greatest` — single header, **ISC**, suites + `RUN_TEST` (still manual
     registration → doesn't fix the drift hazard), strong shuffling/filtering.
   - `nemequ/munit` — **MIT**, .c+.h, PRNG/params/timing; manual registration arrays.
   - `ThrowTheSwitch/Unity` — **MIT**, but auto-registration needs Ruby runner-generation
     scripts; poor fit for this repo's CMake-only, no-scripting-deps posture.
   - Honest counterweight: the current harness already passes the hard constraints
     (C17, 3 compilers, -Werror, zero deps, allocator-irrelevant, sanitizer-transparent)
     and the registration drift it risks has *not* occurred (counts verified equal).
     This is a lead for *if and when* the suite outgrows the harness, not a debt today.
2. **Per-group test orchestration**: CTest itself (`set_tests_properties ENVIRONMENT`,
   `ctest -j`, `--output-junit`) vs `run_core_test_groups.py` — see F9. Platform rung;
   no third-party code needed.
3. **pytest result capture**: pytest built-in `--junitxml`, or `pytest-json-report`
   (MIT, pure Python, already-compatible with requirements-test.txt flow) vs the
   hand-rolled stdout protocol in `run_compat_baseline.py` — see F11.
4. **Workflow dedup**: GitHub-native `workflow_call` reusable workflows + composite
   actions vs copy-pasted pr/main pairs and setup preambles — see F10. Platform rung.
5. **Embedded-Python test bootstrap** (`tlpy_set_pythonhome` + `Py_Initialize`): CPython
   ≥3.8 provides `PyConfig`/`Py_InitializeFromConfig` with `config.home` /
   `config.program_name`, which is the supported way to do what the env-var dance does;
   worth folding into the shared header of F4 rather than adopting anything external.

## Explicit NO-and-NO (earns its keep)

- **Core harness replacement (wholesale)**: NO simpler / NO adoption *today*. 538 LOC,
  3-compiler `-Werror`-clean, zero deps, domain assert (`TEST_ASSERT_STATUS` prints
  `tl_strerror` both sides), sanitizer-transparent. Any framework swap is a 17.5k-LOC
  mechanical diff churning the exact safety net (≈497 C tests) the audit relies on.
  Fix the small things (F1–F3) in place.
- **Sanitizer flag plumbing** (root CMakeLists:100–133): the build-type loop exists so the
  FT-TSan leg (RelWithDebInfo) cannot silently produce an uninstrumented build
  (comment 114–118, enforced by sanitizers.yml:224–233). Deliberate, load-bearing. Keep.
- **`TL_TEST_GROUPS`/`TL_TEST_FILTER` env filtering** (test_main.c): 30 LOC (post-F1)
  enabling the group-split CI strategy and targeted local runs; cheapest possible design
  (env var beats argv parsing here since ctest owns argv). Keep.
- **17 separate workflow files as an architecture**: distinct triggers, concurrency
  groups, and failure ownership per concern; merging beyond F10's pairs trades grep-ability
  for YAML indirection. Keep the shape.
- **`check_layer_a_static.py` / `check_docs_consistency.py`**: bespoke invariant checkers
  (heap-type isolation contract; docs/symbol drift) with no generic replacement at equal
  precision. Proportionate. Keep.
- **`TIMELOG_BUILD_SHARED`**: never exercised in CI but a legitimate ~14-line public build
  option for a C library; deleting it is an API-adjacent change for trivial savings. Keep
  (optionally add a configure-only CI smoke).
- **`timelog_copy_python_runtime` Windows DLL staging** (bindings CMakeLists:114–157):
  looks baroque but Windows CI genuinely runs embedded-Python test exes that need the
  runtime DLL beside them; the fallback chain handles setup-python layouts. Keep.
- **`bench_search_lower_bound` target** (root:282–288): EXCLUDE_FROM_ALL, supports the
  v1.3 branchless-search perf work (perf is the product). Keep.

## Findings Index (LOC honest, includes new glue)

| ID | Where | Rung | Save | Risk | API change |
|----|-------|------|------|------|-----------|
| F4 | bindings/cpython/tests/*.c ×8 | 2 already-in-codebase | ~750 | low | no |
| F5 | bindings/cpython/CMakeLists.txt:264–648 | 7 minimal-rewrite | ~270 | low | no |
| F9 | demo/ci/run_core_test_groups.py + root CMakeLists:280 | 4 platform (CTest) | ~220 | medium | no |
| F10 | .github/workflows (compat pair + setup preamble + tee) | 4 platform (GH Actions) | ~270 | medium | no |
| F11 | demo/ci/run_compat_baseline.py:92–189 | 4/5 platform/dep (pytest) | ~140 | medium | no |
| F1 | core/tests/test_main.c:134–196 | 6 one-liner | ~30 | low | no |
| F6 | bindings/cpython/CMakeLists.txt:24–67,189,239 | 1 dead/speculative | ~50 | medium | no |
| F7 | CMakeLists.txt:262–267,364–390 | 1 speculative platform | ~35 | medium | no |
| F12 | core/tests/test_main.c:253–357 table-driven main | 7 minimal-rewrite | ~55 | low | no |
| F2 | core/tests/test_harness.h:14,23–24,46–52 | 1 dead code | ~15 | low | no |
| F8 | CMakeLists.txt:20–21,350–360 | 1 knob nothing sets | ~14 | low | no |
| F3 | test_harness.h:29–35 + test_main.c:39,48 | 7 minimal-rewrite | ~10 | low | no |

All findings are off the engine hot path by construction (build/test/CI only); zero
performance exposure. Existing test coverage: F1–F5, F12 are self-verifying (the tests
themselves + CI build matrix); F6–F11 need one green CI cycle each as verification.
