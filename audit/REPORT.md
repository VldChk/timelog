# Timelog Simplification & Prior-Art Audit — Final Report

**Branch**: `audit/ponytail-simplification` (off main @ v1.3.0) · **Date**: 2026-07-07
**Scope**: all production C — core 21.8K LOC + CPython bindings 7.8K LOC (84 files),
plus build/test/CI infrastructure. Line-by-line, module-by-module.

**Method**: 12-unit Claude auditor fleet (ponytail ladder, 112 raw findings) + 3
independent Codex audits, cross-checked against a live-verified prior-art landscape
(18 libraries), then every consolidated finding adversarially verified by a 10-agent
hostile panel (refute-by-default; caller hunts included `lab/`, `ideas-lab/`,
benchmarks, workflows, the perf-wins worktree, X-macros, `#if` branches) and a Codex
cross-examination of the draft. Verdicts: **30 CONFIRMED, 19 MODIFIED, 0 REFUTED**.
Every number below is panel-revised, not fleet-claimed.

Full evidence trail: `audit/modules/*.md` (fleet), `audit/codex/*.md` (independent +
cross-review), `audit/prior-art/landscape-facts.md`, `audit/panel-verdicts.md`,
`audit/fleet-summary.md`, `audit/LEDGER.md`, `audit/REPORT-draft.md`.

---

## The two answers

### (a) Can it be simpler, with zero functional/performance regression? — **YES, by ~3,100–3,400 LOC of production C (~11%) plus ~1,600–1,800 LOC of test/CI infra.**

But not where "reinvented wheels" intuition points. The engine's hot machinery —
interval skyline, k-merge heaps, OOO mini-LSM, memview capture, compaction protocol,
handle table, buffer protocol — is justified line-for-line by invariants, TSan
constraints, and measured perf wins. The fat is **speculative completeness**:

- **~37 production-dead internal functions** (panel verified each one individually,
  including in `lab/`, `ideas-lab/`, and the perf-wins worktree),
- **V2 row-delete plumbing** that today costs one branch *per record in every merge loop*,
- a **production-dead two-way merge iterator**, dead thread-naming/atomics surface,
  write-only "diagnostic" fields, no-op knobs,
- and heavy **copy-paste in the binding layer and test/CI infrastructure**.

Two findings are **strictly perf-positive** (simpler AND faster): the seal-path
double-sort elimination and the compaction retry-loop restructure.

### (b) Did others already solve parts of this — should timelog outsource? — **NO. Zero external library adoptions recommended. This verdict is unanimous across both independent fleets and survived the hostile panel.**

This is a *grounded* no, not a reflexive one. 18 libraries were fact-checked live
(licenses, MSVC CI evidence, maintenance state, allocator hooks) and each candidate
fails at least one hard constraint or loses to reuse of code timelog already has:

| Candidate | Why not |
|---|---|
| klib (kvec/khash/ksort/kbtree) | kvec/kbtree hardcode libc alloc (breaks `tl_alloc_ctx_t` seam, frozen since ~2015); khash's table mechanics aren't the hard part of the live-handle table — the lock-free GC-traversal contract is, and khash frees on resize, breaking it |
| stb_ds | needs `typeof`, breaks under strict `-std=c17` (open issue), allocator context always NULL, frozen since 2021 |
| uthash family | alive again (v2.4.0, 2026) but only uthash.h has allocator injection; solves ordinary tables, not this one |
| Concurrency Kit | `ck_pr.h` requires `__GNUC__` (open issue, no Windows CI) — hard MSVC fail; custom fences are exactly what GCC TSan can't see |
| liburcu | superbly maintained, real TSan mode — and LGPL-2.1 + Cygwin-only Windows: double disqualification for static wheels |
| liblfds | public domain but abandoned 9.5 years; site archived |
| tinycthread / C11 `<threads.h>` | no macOS SDK `<threads.h>`, glibc 2.28+ vs manylinux floor, MSVC 17.8+, `cnd_timedwait` is TIME_UTC-only (regresses deliberately-monotonic waits); tinycthread unmaintained |
| interval-tree libs (cgranges/AIList/NCLS) | all build-once/query-many static indexes; **no C library supports online coalescing insert**, let alone seq-tagged skyline semantics |
| LSM/k-way-merge components | none exist in pure C; SQLite's lsm1 is disowned by its own developers |
| test frameworks (Unity/greatest/munit/cmocka/utest.h/Criterion) | munit abandoned, greatest dormant, Criterion fork-per-test breaks ASan/TSan, Unity workable but auto-registration needs Ruby tooling; swapping 538 in-house LOC churns the 17.5K-LOC test safety net for ≤0 net gain. cmocka and utest.h are the live future leads if the suite outgrows the harness |
| pybind11/nanobind/Argument Clinic/HPy | C++ / in-tree-only / dormant-alpha; **no pure-C CPython boilerplate helper exists** — the hand-rolled Layer A/B binding is the state of the art |
| pthreadpool etc. | the maintenance worker's value is domain policy (flush-drain with compaction cut-in), not thread plumbing |

The only "adoptions" that survive are **platform rungs already shipped with CPython or
the toolchain** (zero new dependencies): `PyErr_FormatV`, `Py_BuildValue`,
CTest-native group tests, and MSVC `/experimental:c11atomics` for the core (see D1).

**On the user's fear of "ignoring 20+ years of prior art"**: the audit's honest
conclusion is the opposite of the fear. The sub-problems where prior art is mature
(dynamic arrays, heaps, sorts) are exactly where timelog's versions are thin wrappers
already centralized around `tl__grow_capacity`/`tl_search.h`/`tl_refcount.h`; the
sub-problems where timelog carries real weight (seq-tagged coalescing intervals,
free-threaded handle lifetime, snapshot publication) have **no C prior art at all** —
verified, not assumed.

---

## Verified findings (panel-final numbers)

### Tier 1 — dead code, delete with zero behavior change (~1,690 LOC prod)

| ID | Finding | LOC | Verdict |
|----|---------|-----|---------|
| A1 | 37-function dead sweep across internal/ + storage/ headers (recvec search/insert/shrink tail, heap_build/len, intervals contains/union/covered_span/max_seq, range predicates, alloc getters + reallocarray, lock-tracker queries, seqlock reader half, window helpers, page_upper_bound, dead accessors, …) | 500 | CONFIRMED |
| A2 | Dead platform surface (thread naming, ptr/store/fence atomics, unreachable 3rd backend) — **keep `store_release_u32`/`load_acquire_u32`** (live in stress/concurrency tests) | 240 | MODIFIED |
| A3 | V2 row-delete machinery — removes one branch/record from both merge loops; 3 extra sites beyond fleet list (pagespan gate, test assert, catalog flags cache) | 115 | CONFIRMED |
| A4 | Flush-layer two-way merge iterator (production-dead) + stale header comment | 140 | CONFIRMED |
| A5 | Adaptive dead surface (wants_resize, RESHAPE_L0, has_records, stale doc block) | 60 | CONFIRMED |
| A6 | Test-only constructors → test tree (memrun_create, ooorunset_create, seal shim) | 90 | CONFIRMED |
| A8 | Storage write-only fields, dead window helpers, dead zeroing, page_builder collapse | 100 | CONFIRMED |
| A9 | Query dead-state sweep (6 items incl. provably-unreachable tl_point branch) | 32 | CONFIRMED |
| A11 | Orchestrator: dead NULL-tolerant seal branches, status_strings switch | 35 | CONFIRMED |
| A10 | Build-system dead (standalone bindings mode, Windows-Clang blocks, facade option, harness scraps) — maintainer confirm on the first two | 120 | CONFIRMED |
| A7′ | Bindings dead code, uncontested subset (error-pair validation, ModuleMatchesTimelogDef, drop-node ts, remaining_valid, unreachable h==NULL branches, micro) | ~150 | MODIFIED |

### Tier 2 — reuse what the repo already has (~440 LOC)

B1 drop-buffer containers → `tl_recvec`/`tl__grow_capacity` (~200, incl. resolving the
CX-vs-CL divergence: foundation modules already use the helper; the wins are in
delta/query/maint); B2 lower_bound single tuning point (net ~8 LOC but unifies the
measured branchless gate — value is the single tuning point, empirically
codegen-equivalent on GCC 13/Clang 18); B3 tombstone-union helper (20); B4 drop-callback
helper (14, third free-without-emit site must stay free-only); B5 count consolidation
(110 — stats keeps slim page/tombstone loops); B6 segment-builder cleanup consolidation
(65, three load-bearing conditions incl. explicit `*out=NULL`); B7 default_window_size
drift fix (12 — a real latent 1000× disagreement, currently unreachable); B8 exception
macro migration (12).

### Tier 3 — structural merges (~1,200 LOC, C9 excluded)

C1 delta-iterator merge (190; conservative version only; consumer set is exactly
tl_plan.c+tl_merge_iter.c — smaller than fleet claimed; 43 test renames); C2 memview
dedups (105); C3 orchestrator dedups (160; epilogue merge gated by append benchmark);
C4 compaction restructure (70, **perf-positive**, plus contract-conformance fix:
exhaustion now always returns the header-documented TL_EBUSY); C5 seal double-sort
elimination (60, **perf-positive** with two guards: keep the tombs-empty short-circuit
and the sorted-head exact count); C6 py_timelog.c consolidation (~590 total: late-hctx
move kills 34 error-path calls; config table; stats via Py_BuildValue; FASTCALL fold —
preserve per-method CHECK_CLOSED asymmetry and arg-name strings; extend epilogue —
**fixes a real latent SystemError bug**; KW enum; bulk_append PyArg with 2 test-regex
relaxations); C7 PyErr_FormatV (35); C8 views boilerplate (80); C10 query micro (97,
with the 32-bit saturation guard).

### Tier 4 — platform adoption, one item (135 LOC + MSVC perf)

**D1: switch core atomics to C11 on MSVC** (`/experimental:c11atomics`). Panel
adjudicated **adopt-now for the in-repo build matrix** — the shipping Windows wheel
already hard-depends on the flag (binding CMake + `py_handle.c` `#error` guard,
verified compiling clean under VS 2026 in the v1.3.0 release log), so this widens an
existing dependency rather than creating one. Deletes the 139-line Interlocked backend;
MSVC relaxed loads stop being lock-cmpxchg RMWs (benefits `TL_REFCOUNT_ACQUIRE` on the
query/snapshot path). **Gates before landing**: one Windows `/W4 /WX` compile check of
`<stdatomic.h>` on the core target; a manual Windows wheel run (packaging-pr is
Linux-only — itself a gap worth fixing); document the raised MSVC floor for standalone
core builds.

### Tier 5 — test/CI infrastructure (~1,600–1,800 LOC)

E1 shared binding-test harness header (750; md5-verified duplication; unification is
behavior-*tightening* — one green CI cycle required); E2 CMake test-target function
(290); E3 test_main.c cleanup (85, **fixes the latent results[] overflow** — suite at
~50% of the 1000 cap and one failing helper-assert can record multiple entries);
D2 CTest-native groups (220; closes the group-list drift hazard); D3 compat-baseline
protocol (~110; **only** via `pytest-json-report` — a new test-only dependency, flagged
honestly; plain junitxml loses xpassed/zero-collected semantics); D4 workflow dedup
(270; compat pair diff is 19 lines — stronger than drafted).

### Honest totals

Tiers 1–4 (production C): **~3,100–3,400 net LOC** (~11% of 29.7K), zero new runtime
dependencies, nothing on a hot path except two strictly-positive changes and three
codegen-equivalent ones (B2, C1, C3 — the last benchmark-gated). Tier 5 (infra):
**~1,600–1,800 LOC** (one optional test-only dependency). Numbers are *not* blindly
additive across every optional variant (C1-deep excluded; D2/E3 overlap ~50; A7
judgment items excluded) — the ranges above already account for that.

---

## Explicit NO-AND-NO (earns its keep — grounded, panel-checked)

Tombstone interval skyline (seq-tagged, cursor-based, no C prior art exists);
window/range math (signed floor division, unbounded encodings); page/segment/manifest
immutable-publication semantics; OOO mini-LSM memtable (+ H-07 ring, H-09 capture);
compaction select/merge/publish (H-17/H-18/H-19); k-merge heap (payload + replace_top,
comparator inlined on the hottest loop); submerge/kmerge duality (infallible-flat vs
fallible-iterator sources); point-lookup fast path; sync/atomic/seqlock-writer/refcount
platform layer (acq_rel-in-RMW is the GCC-TSan workaround); goto-cleanup idiom (58
sites — C17 has no defer); no TL_CHECK macro (control-flow visibility is a project
value); handle lifetime subsystem (lock-free tp_traverse is the v1.2 deadlock fix);
PageSpan buffer protocol (BufferError-on-close contract); append/bulk_append parsers
(measured −23.7% FASTCALL win); module multi-phase init; per-type release ordering
choreography (the duplication IS the invariant).

## Blocked / downgraded to maintainer flags

- **C9 PySeqIter swap** (140 LOC): blocked by Codex, blast radius confirmed by panel
  (2 test asserts, ~6 C-test sites, 3 LLD doc sites). Optional; only with a deliberate
  compat note.
- **A7 reload-rollback deletion** (~170 + ~200-260 test LOC): deliberate design,
  observable on `importlib.reload()` failure; maintainer judgment call.
  `TimelogIter.view()` deletion is API-CHANGE (README advertises it) — or keep it and
  add the missing lifetime test (it has never been executed by any harness).
- **G1 adaptive subsystem** effectively fires once (window_grid_frozen latches; ~660
  LOC + 10 C knobs + 10 Python kwargs feed a mostly-inert loop) — scope decision for
  v2.0, not a zero-regression edit.
- **G2 mostly_ordered hint** is a fully-plumbed public no-op; minimum action: fix the
  false docstring promise (py_timelog.c:3675) and docs. Full excision breaks lab/
  workflows and conflicts with the ideas-lab N28 backlog.
- **G3 seqlock Tier B**, **G4 public-API deletions** (tl_count/tl_count_range/
  tl_scan_range + typedefs, kind="segment", REQUIRE_ZEROCOPY, hint flags), **G5
  TIMELOG_BUILD_SHARED** (never CI-compiled): major-version bucket.

## Bugs & hazards discovered as by-products (fix regardless of adoption)

1. **extend() latent SystemError** (py_timelog.c:2121-2123, 2154-2156): chunk/tail
   paths return NULL without setting an exception on non-EBUSY engine failure.
2. **CI test-skip hole (live today)**: core suite runs only through the hardcoded
   13-group list in run_core_test_groups.py; a new suite in test_main.c is silently
   never CI-run; an unmatched group silently "passes". Add a
   nonzero-exit-on-empty-group guard even if D2 never lands.
3. **Test-harness results[] overflow** (~50% consumed; multi-record-per-failing-test
   accelerates it) + duplicate filter function.
4. **default_window_size drift** (1H_S vs 1H_MS between the two copies).
5. **Doc drift**: CLAUDE.md's compaction_publish_ebusy gloss contradicts header+tests;
   CLAUDE.md still teaches the deprecated PyErr_Fetch idiom; tl_recvec_take NULL-vs-
   empty doc; stale covered_span/seal-sort/flush-merge-iter comments; LLD hard-codes
   module-state types that no checker polices; py_timelog.c:3675 false hint promise.
6. **bench_search_lower_bound has zero build coverage** (EXCLUDE_FROM_ALL, no CI leg).
7. **Windows wheel coverage gap**: packaging-pr.yml is Linux-only; the cibuildwheel
   Windows path runs only at release time.

## Recommended execution order (each step its own PR, full matrix per house rules)

1. A1+A2+A8+A9+A5+A11 zero-ref dead code (mechanical; prune bench legs in-commit;
   sequence AFTER any perf-wins worktree merge to avoid churn) → ~970 LOC.
2. B4+B7+B3+B8 + doc-drift fixes + extend() bug fix (small, surgical) → ~90 LOC + bugs.
3. A4+A6 + B1 + C2 + C5 (delta cluster, one reviewer pass, C5 with its two guards).
4. A3 (V2 machinery) + B6 + B2 (storage cluster; A3 wants a perf sanity run).
5. C6+C7+C8 + A7′ (bindings cluster; fixes the SystemError bug).
6. C1 alone (read-path plumbing; full validation matrix per project memory).
7. C4 + C3 (maint/orchestrator; C3 epilogue benchmark-gated).
8. E1+E2+E3 then D2/D4 (infra; D3 only if the test-only dependency is acceptable).
9. D1 (atomics) behind its Windows gates.

---
*Campaign artifacts and every intermediate verdict are committed on this branch.
"No and no" was an acceptable answer; where we say it, it is grounded in file:line
evidence and a hostile panel failed to break it. Where we say "yes", every claim
survived refute-by-default verification, and three claims were corrected in the
process — the corrections are in the numbers above.*
