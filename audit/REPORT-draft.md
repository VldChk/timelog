# DRAFT — Consolidated Audit Findings (pre-panel)

Status: DRAFT for hostile-panel verification. Sources: 3 independent Codex audits +
12-unit Claude fleet (details in audit/modules/*.md, audit/codex/*.md,
audit/fleet-summary.md). LOC = net estimate incl. new glue. Convergence column:
CX+CL = found independently by both fleets.

## Headline (pre-verification)

1. **Library adoption: NONE recommended — unanimous across both fleets.** Every classic
   candidate (klib, stb_ds, uthash, CCAN, Concurrency Kit, liburcu, tinycthread,
   interval-tree libs, test frameworks) fails at least one hard constraint or loses to
   an in-repo rung-2 reuse. The load-bearing constraints: per-instance `tl_alloc_ctx_t`
   allocator seam, MSVC C17 `/WX`, GCC-TSan fence blindness (acq_rel idiom), free-threaded
   CPython contracts, zero hot-path regression, LGPL disqualifications.
2. **The real debt is speculative completeness, not reinvention**: ~30 production-dead
   internal functions, V2 row-delete plumbing costing live read-path branches, a dead
   two-way merge iterator, dead atomics/sync surface, unused knobs and write-only fields.
3. **Two simplifications are PERF-POSITIVE** (seal double-sort elimination; compaction
   retry-loop restructure) — simpler AND faster.
4. Platform rungs not fully exploited: `PyErr_FormatV`, `Py_BuildValue`, `PySeqIter`,
   CTest-native group tests, MSVC `/experimental:c11atomics` (bindings already require it
   on Windows; core still hand-rolls an Interlocked backend).
5. Test/CI infra carries the single largest one-shot win: 8 binding test files duplicate
   an identical ~95-line harness preamble (~750 LOC).

## A. Dead code (rung 1 — delete, zero behavior change)

| ID | Finding | LOC | Risk | Src |
|----|---------|-----|------|-----|
| A1 | Core internal dead-function sweep: recvec (insert/shrink/sort/lower/upper/range_bounds), tl_heap_build, intervals (max_seq/imm_contains/contains/union/covered_span), 3 tl_range predicates, alloc getters + tl__reallocarray, locks is_held/highest_held/TL_TRYLOCK, seqlock reader half, tl_window_contains{,_bounded}/bounds_for_ts, tl_page_upper_bound, segment prefix-counts accessor, dead inline accessors (ooorun_gen, memview shared_epoch/min/max, memrun is_empty/tombs_data), snapshot_alloc, point_result_empty, manifest_version, memtable_insert_tombstone_unbounded | ~500 net | low | CX+CL |
| A2 | Dead platform surface: thread_set_name (50-line Win32 mech), mutex_is_held, thread_self_id, cond_broadcast; tl_atomic ptr family + all store ops + fence + unused macros; unreachable 3rd `__atomic` backend → #error | ~250 | low | CL |
| A3 | V2 row-delete machinery (rowbitset, row_del fields, per-record `row_is_deleted` branch in merge loop) — "never instantiated in V1" per its own header | ~110 | med | CX+CL |
| A4 | Dead two-way merge iterator in flush layer (+ stale comment in query/tl_merge_iter.h claiming flush uses it) | ~140 | low | CX+CL |
| A5 | Dead adaptive surface: tl_adaptive_wants_resize, TL_WORK_RESHAPE_L0, has_records field; stale trigger-coupling doc block | ~60 | low | CX+CL |
| A6 | Test-only constructors: tl_memrun_create, tl_ooorunset_create, tl_memtable_seal wrapper (move to test tree) | ~70 | low-med | CX+CL |
| A7 | Bindings dead code: module reload-rollback machinery (~170 + ~400 test LOC; judgment call — deliberate design), by-construction error-pair validation (~35), TlPy_ModuleMatchesTimelogDef, never-read drop-node ts field, TimelogIter.view() [API], remaining_valid field, unreachable h==NULL branches, micro-deletions | ~330 | low-med | CL |
| A8 | Storage dead state: cap_l0/cap_l1 write-only fields, dead window helpers, redundant zeroing after TL_NEW(calloc), page_builder collapse | ~100 | low | CL |
| A9 | Query dead-state sweep: kmerge.alloc, tomb_capacity, segments/memruns_pruned, head_watermark always-0, unreachable tl_point branch, TL_PAGESPAN_REQUIRE_ZEROCOPY | ~30 | low | CL |
| A10 | Build-system dead: standalone bindings build mode (~50), Windows-Clang blocks (~35), facade-tests option (~14), harness dead machinery (~15) | ~115 | med (confirm no local workflow) | CL |
| A11 | Orchestrator: seal NULL-tolerant dead branches + duplicated seal block (~25), status_strings table→switch (~10) | ~35 | low | CL |

## B. Rung-2 reuse (helper already exists in-repo)

| ID | Finding | LOC | Risk | Src |
|----|---------|-----|------|-----|
| B1 | Drop-buffer containers reuse tl_recvec/tl__grow_capacity: memtable_collect_drop/reserve_drops, flush inline doubling, compaction dropped_records (+ tl__grow_array then inlines), tl_point result array, plan ensure_source_capacity, 2 verbatim straggler grow loops. NOTE: resolves CX-vs-CL divergence — foundation modules already use tl__grow_capacity; the wins are container-level reuse in delta/query/maint | ~200 | low-med | CX+CL |
| B2 | tl_page_lower_bound delegates to new tl_ts_lower_bound beside tl_record_lower_bound in tl_search.h — single tuning point for the measured branchless gate | ~25 | low (codegen-identical) | CX+CL |
| B3 | tl__tombs_union_into duplicates tl_tombstone_utils.h::tl_tombstones_add_intervals (7 existing callers) | ~20 | low | CL |
| B4 | flush_one_memrun re-inlines tl__emit_drop_callbacks twice | ~15 | low | CX+CL |
| B5 | Full-extent count helpers = range variants at [TL_TS_MIN,+inf); tl_stats reimplements snapshot count inline | ~110 | low | CX+CL |
| B6 | Segment builder: 5 hand-rolled cleanup blocks → segment_destroy; dedupe 18-line prefix-count block; reuse tl_intervals_arr_validate for build_l0 validation | ~65 | med (needs ENOMEM-injection tests) | CX+CL |
| B7 | default_window_size duplicated & drifted (1H_S vs 1H_MS) between tl_window.c and tl_timelog.c | ~12 | low | CL |
| B8 | Finish TL_PY_PRESERVE_EXC_* migration at 4 straggler sites | ~12 | low | CL |

## C. Structural merges (rung 6-7)

| ID | Finding | LOC | Risk | Src |
|----|---------|-----|------|-----|
| C1 | Merge tl_memrun_iter + tl_active_iter → tl_delta_iter (structs field-identical, next/seek/destroy token-identical; plan union 3→2 kinds; optional deeper cut: submerge directly in plan union ~350) | ~180-200 | med | CX+CL |
| C2 | tl_memview dedups: 5× bounds-merge tail, copy_intervals+copy_seqs→dup helper, H-09 retry/fallback body unification, micro | ~130 | low-med | CL |
| C3 | Orchestrator dedups: shared write-path epilogue (4 entrypoints), ts-navigation quartet→2 helpers, open/init_locks goto ladders, iter_range empty-range delegation | ~160 | low-med | CL |
| C4 | Compaction: retry-loop restructure (**PERF-POSITIVE**: kills wasted final k-way merge), watermarks side-array removal (one less malloc/free per compaction), one-pass L1 selection, sat-arith helpers | ~70 | low | CL |
| C5 | Seal path: kill copy-and-sort drop pre-count (**PERF-POSITIVE**: removes one O(H log H) sort per seal + per gated chunk) | ~60 | med | CL |
| C6 | py_timelog.c: table-driven config validation + late hctx creation (~200), stats via Py_BuildValue (~85), FASTCALL ts-parse fold across 11 methods (~120), extend epilogue ×3→1 (~40), 27-member KW_ enum→2 constants (~26), bulk_append via PyArg (~50, 2 test regexes), make_iter switch merge, now_ts pre-check, __enter__ reuse | ~540 | low-med | CX+CL |
| C7 | py_errors: PyErr_FormatV replaces both hand-rolled 512-byte vsnprintf raisers (kills truncation; 1 test update) | ~35 | low | CX+CL |
| C8 | bindings-views boilerplate: shared __enter__, ts-getter macro, redundant closed pre-checks, FromView checks→asserts, failpoint stubs→#define NULL | ~90 | low | CX+CL |
| C9 | Replace custom ObjectsViewIter with CPython PySeqIter fallback (kills a type, a module-state slot, TL_PY_OBJ_LOCK2) — iter type name observable (1 test asserts it) [API-observable] | ~140 | med | CL |
| C10 | Query micro: count_sources two-pass removal, base_priority hoist, 3 single-use tombstone-adder wrappers, shared L0/L1 loop-body helper, NULL-seqs absorb in count | ~100 | low | CL |

## D. Platform adoptions (rung 3-4)

| ID | Finding | LOC | Risk | Src |
|----|---------|-----|------|-----|
| D1 | Core atomics on MSVC via /experimental:c11atomics — bindings ALREADY require it on Windows wheels; deletes 140-line Interlocked backend; MSVC relaxed loads stop being lock-cmpxchg RMWs (**MSVC perf win**). Open question: flag maturity for standalone core builds | ~135 | med | CL (CX hedged) |
| D2 | CTest-native per-group tests replace demo/ci/run_core_test_groups.py (parallelism + junit for free) | ~220 | med | CL |
| D3 | pytest --junitxml / pytest-json-report replaces hand-rolled TL-SUMMARY subprocess protocol | ~140 | med | CL |
| D4 | Workflows: compat pr/main pair → workflow_call; setup preamble → composite action (selective) | ~270 | med | CL |
| D5 | PyConfig/Py_InitializeFromConfig replaces 8× PYTHONHOME env dance (fold into E1) | incl. E1 | low | CL |

## E. Test/build infrastructure

| ID | Finding | LOC | Risk | Src |
|----|---------|-----|------|-----|
| E1 | Extract shared binding-test harness header (8 files × ~95 identical lines: set_pythonhome, init/finalize, TEST/ASSERT macros, counters, main epilogue) | ~750 | low | CL |
| E2 | CMake function for 8-9 copy-pasted test-target stanzas (root+bindings; 14-line MSVC block ×9) | ~270-390 | low | CX+CL |
| E3 | test_main.c: table dispatch (15 if-blocks), delete byte-identical duplicate filter fn, store only failures in results[] (**fixes latent silent overflow at 1000 results, suite at ~497**) | ~95 | low | CL |
| E4 | utest.h (Unlicense, auto-registration) as future lead if suite outgrows harness — NOT now (17.5K-LOC mechanical churn) | 0 | — | CL |

## F. Library adoption verdicts (all NO — grounded)

klib kvec/khash/ksort (allocator seam, global realloc, comparator indirection on hot paths);
stb_ds (global allocator override); uthash (ordinary tables ≠ lock-free GC-traversal
contract); CCAN (per-module licensing, same shape problems); Concurrency Kit (partial MSVC,
custom fences vs GCC-TSan blindness, mixed licenses); liburcu (LGPL — hard fail);
tinycthread (unmaintained, no monotonic timedwait, misses debug tracking; weak);
C11 threads.h (no macOS SDK support, glibc 2.28+ vs manylinux floor, MSVC 17.8+,
TIME_UTC-only cnd_timedwait regresses monotonic waits); interval-tree libs incl. cgranges
(no seq-tagged coalescing canonical sets); pthreadpool (domain policy is the value, not
plumbing); Unity (Ruby codegen), greatest/munit (manual registration keeps the real cost),
cmocka (heavier); Argument Clinic (in-tree tool), nanobind/pybind11 (C++), private CPython
APIs (unshippable). Interval skyline, window math, OOO mini-LSM, memview capture, compaction,
k-merge heap, handle table, buffer protocol, module init: NO-and-NO (see module reports).

## G. Maintainer flags (not zero-regression; decisions, not actions)

| ID | Flag |
|----|------|
| G1 | Adaptive subsystem effectively fires once: window_grid_frozen latches on first L1 publish; EWMA/hysteresis/backoff act only pre-first-compaction; 10 C knobs + 10 Python kwargs feed a mostly-inert loop (~660 LOC subsystem). Free micro-win: gate metrics capture on !frozen |
| G2 | TL_APPEND_HINT_MOSTLY_IN_ORDER: fully-plumbed public no-op (core mandates full sortedness verification); minimum action: document as ignored |
| G3 | Seqlock is write-only in production (reader half is the deleted hook); Tier B removal (~170 LOC) contradicts documented invariant #6 wording — maintainer call |
| G4 | Public API candidates for a major version: tl_count/tl_count_range, tl_scan_range (test-only consumers), kind="segment" one-value kwarg, TL_PAGESPAN_REQUIRE_ZEROCOPY, batch-append hint flags |
| G5 | TIMELOG_BUILD_SHARED never compiled in CI: add a CI leg or delete the option |

## Pre-verification totals

Production C (core+bindings): ~2,900–3,300 net LOC removable across A–D.
Test/build/CI: ~1,500–1,900. Combined ≈ 4,400–5,200 (~15% of the 29.7K prod + harness).
External dependencies added: **zero**. Perf: two strictly-positive changes; everything else
constrained to off-hot-path or codegen-identical.
