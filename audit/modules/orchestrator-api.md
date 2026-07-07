# Ponytail Audit — Unit: orchestrator-api

**Files read in full** (2,958 LOC):
- `core/src/tl_timelog.c` (2,227)
- `core/include/timelog/timelog.h` (711)
- `core/include/timelog/tl_export.h` (20)

**Cross-checked** (grep + targeted reads, not counted): `bindings/cpython/src/*.c`, `python/timelog/`, `core/src/delta/tl_memtable.c`, `core/src/query/tl_plan.c`, `core/src/maint/tl_compaction.c`, `core/src/internal/tl_timelog_internal.h`, `CMakeLists.txt`, `.github/workflows/`, `pyproject.toml`, `docs/python-api.md`.

---

## Executive Summary

The orchestrator is disciplined about its invariants (lock order, seqlock windows, deferred signalling) and none of the findings below touch them. The real fat is in three places:

1. **A public API hint that provably does nothing.** `TL_APPEND_HINT_MOSTLY_IN_ORDER` is plumbed from Python kwarg → binding → C flags parameter → `(void)flags;`. The core's own test asserts the hint must never be trusted, which means it can never do anything. It is the single largest does-not-need-to-exist finding in this unit.
2. **Public C API surface with zero non-test consumers**: `tl_scan_range`, `tl_count`, `tl_count_range` are called only by `core/tests/test_functional.c`. The binding uses `tl_snapshot_count_range` and iterators exclusively.
3. **In-file duplication**: the four write entrypoints share a ~30-line epilogue verbatim; `flush_one_memrun` re-inlines the `tl__emit_drop_callbacks` helper twice; `tl_iter_range` special-cases the empty range that `tl_plan_build` already short-circuits; `handle_seal_with_backpressure` carries NULL-tolerant out-params no caller exercises plus a duplicated seal-attempt block.

Config knobs are in good shape: every `tl_config_t` field is read by the core and exposed by the binding (verified `compaction_target_bytes` at tl_compaction.c:583, `max_compaction_inputs` at :714, `max_compaction_windows` at :582, `window_origin` via tl_window.h, adaptive.* via py_timelog.c:1295-1395). Stats plumbing is fully wired end-to-end (all `tl_stats_t` fields → binding dicts at py_timelog.c:2790-2827). The one config-shaped dead spot is `TIMELOG_BUILD_SHARED`: OFF by default, forced false in wheels and every CI workflow, so the `TL_BUILD_SHARED` branch of `tl_export.h` is never compiled anywhere.

Estimated honest total if all no-api-change findings land: **~200 LOC**. With the api-change deletions: **~350+ LOC** across the repo.

---

## Per-file walkthrough

### `core/include/timelog/tl_export.h` (20 lines)

Standard DLL export ladder. `TL_API` expands to nothing in every build that actually happens:

- `CMakeLists.txt:15` — `option(TIMELOG_BUILD_SHARED ... OFF)`
- `pyproject.toml:53` — `TIMELOG_BUILD_SHARED = false`
- `release-pypi.yml:100`, `release-testpypi.yml:66`, `packaging-pr.yml:75` — all `false`
- No CI workflow enables it.

**Finding S-13 (rung 1, api-change, low-medium risk):** the shared-build configuration is *supported-looking but never CI-tested*. Ponytail verdict: either add one CI leg that compiles `-DTIMELOG_BUILD_SHARED=ON` or delete the option, the `tl_export.h` `#if defined(TL_BUILD_SHARED)` ladder, the `TL_API` token on ~45 declarations, and the CMake export block (CMakeLists.txt:182-186, 205-210). Deletion is lazier (~30 LOC + tokens), but a published C library shipping export macros has genuine option value for embedders; if the maintainer intends the C API to be consumable as a DLL, the *test* is the right fix, not the deletion. Flagged, not urged.

**Prior art note:** CMake's `GenerateExportHeader` generates exactly this file. It is *more* machinery than the hand-written 20-liner (generated file must be wired into the scikit-build wheel include path). NO — the hand-rolled version is already the minimal form.

### `core/include/timelog/timelog.h` (711 lines)

Well-documented contract header. Findings:

**S-1 (rung 1, api-change, THE headline): `tl_append_flags_t` hint is a no-op by design.**
- `timelog.h:384-388` defines `TL_APPEND_NONE`, `TL_APPEND_HINT_MOSTLY_IN_ORDER`, and alias `TL_APPEND_HINT_MOSTLY_ORDER`.
- `tl_append_batch(..., uint32_t flags)` (timelog.h:398-399) carries it.
- The sole consumer, `tl_memtable_insert_batch`, discards it: `core/src/delta/tl_memtable.c:655` — `(void)flags;`. The fast path is chosen by *actually verifying* sortedness (`batch_is_sorted(records, n)` at tl_memtable.c:676-678), never by the hint.
- The core's own test locks this in: `core/tests/test_delta_internal.c:757` — *"With MOSTLY_IN_ORDER hint, must still detect the unsorted pair"*. If the hint must never be trusted (correct, since a lying caller would corrupt sortedness — invariant 3), it can never change behavior. A hint that cannot ever be acted on does not need to exist.
- Downstream plumbing that exists solely to feed this no-op: binding `mostly_ordered` kwarg parsing (py_timelog.c:1868-1872, 1955, 2036, 2240-2455 — the bulk_append resolution block alone is ~40 lines), facade `mostly_ordered_default` ctor/configure/reopen kwarg (python/timelog/__init__.py:224, 235, 257), `.pyi` stubs (_timelog.pyi:95, 101), and tests asserting default-resolution semantics of a no-op (python/tests/test_bulk_append.py:230-242).
- **Cost of removal:** loud api-change at both C and Python levels (`mostly_ordered` is a documented kwarg). Honest LOC: ~10 in this unit's files; ~100+ repo-wide. Alternatives, laziest first: (a) leave C core as-is, document the flag as "reserved, currently ignored" — zero code, honest docs; (b) drop only the unused alias (S-2); (c) full excision — biggest win, biggest churn. Note Python-level `mostly_ordered` could be kept accepting-and-ignoring for compat while the C enum dies, but the C header is also a contract. Later phases should decide; the grounding is solid either way.

**S-2 (rung 1, api-change, trivial): `TL_APPEND_HINT_MOSTLY_ORDER` alias has zero users.** Only occurrence in the entire repo is its own definition (timelog.h:387). 1 LOC. Technically public API; realistically nobody can be using a v1.x alias that no doc, test, binding, or benchmark mentions.

**S-3 (rungs 7 / 1): `tl_count` / `tl_count_range` have no non-test consumers.**
- Declared timelog.h:490-494; implemented tl_timelog.c:1526-1563.
- The binding calls only `tl_snapshot_count_range` (grep of bindings/cpython/src: `tl_snapshot_count_range` present; `tl_count(`/`tl_count_range` absent). Users: `core/tests/test_functional.c` only (lines 566-748).
- Lazy option A (no api change, rung 7): the two implementations are line-for-line identical except one argument (`(t1, t2, false)` vs `(TL_TS_MIN, 0, true)`); fold into one static helper → ~15 LOC saved.
- Lazy option B (rung 1, api-change): delete both from the public API; callers hold a 3-line recipe (`acquire → tl_snapshot_count_range → release`). ~50 LOC (impl + header docs + test updates). Flagged loudly as api-change.

**S-4 (rung 1, api-change): `tl_scan_range` visitor API has no non-test consumers.**
- Declared timelog.h:474-483 (enum + callback typedef + function); implemented tl_timelog.c:1500-1522 as a thin loop over `tl_iter_range`/`tl_iter_next`.
- Grep: only `test_functional.c` uses it. Binding, facade, benchmarks, lab: zero hits.
- It is 23 lines of implementation + ~10 of header for something any C caller writes in 6 lines with the iterator API. Deletion candidate; api-change.

**NO-and-NO: `tl_iter_equal` + `tl_iter_point` coexistence.** Docs call them equivalent (docs/python-api.md:86 — "`point(ts)` / `equal(ts)` (iterators over one timestamp's records)"), which smells like duplicate surface. But they have genuinely different profiles: `equal` streams through the plan/kmerge/filter pipeline (O(K) memory), `point` eagerly materialises the match set (`tl_point_lookup`, tl_timelog.c:1421 — O(M) memory, faster per-lookup). Both are wired through the binding (`ITER_MODE_EQUAL` py_timelog.c:3253/3477, `ITER_MODE_POINT` :3256) and the facade. The fix, if any, is a one-line doc clarification of the memory trade-off — not code.

**Header hygiene notes (keep):** the status-code semantics block (timelog.h:109-146), the TL_EBUSY means-accepted contract, and the O(N) warnings on `tl_max_ts`/`tl_prev_ts` (timelog.h:553-597) are load-bearing documentation; leave them alone.

### `core/src/tl_timelog.c` (2,227 lines)

**S-5 (rung 2): `tl_iter_range`'s empty-range special case duplicates machinery that already exists.**
- tl_timelog.c:1350-1367: 17 lines hand-building a done-iterator for `t1 >= t2`.
- `tl_plan_build` already short-circuits empty ranges *before any allocation*: tl_plan.c:206-209 (`if (tl_range_is_empty(t1, t2, t2_unbounded)) return TL_OK;`), and `iter_create_internal` already turns an empty plan into a done iterator with the same debug hook (tl_timelog.c:1307-1315).
- Proof it's safe: `tl_iter_until(snap, TL_TS_MIN, ...)` (tl_timelog.c:1381-1388) *already* routes the empty range through `iter_create_internal` with no special case. `tl_iter_range` can be the same one-liner. ~16 LOC saved. Covered by `test_functional.c:150` ("Invalid range t1 >= t2 should return empty iterator") and the pagespan empty-range suites. Not a hot path (empty-range queries), and the added cost is one call into a function that memsets a struct and returns — nil.

**S-6 (rung 2): `flush_one_memrun` re-inlines `tl__emit_drop_callbacks` twice.**
- Helper: tl_timelog.c:466-479 (emit loop guarded by `on_drop_handle != NULL`, then free).
- Duplicate 1: tl_timelog.c:999-1008 (seg == NULL path) — byte-for-byte the helper's body.
- Duplicate 2: tl_timelog.c:1019-1029 (publish-OK path) — same loop, followed by the same free.
- Replace duplicate 1 with `tl__emit_drop_callbacks(tl, dropped, dropped_len); return TL_OK;`. For duplicate 2: `if (st == TL_OK) tl__emit_drop_callbacks(...); else if (dropped) tl__free(...);` — note the failure path must free *without* emitting (records were not published; emitting would violate the "AFTER successful manifest publish" contract, timelog.h:214-216), which the current code honors and the reshaped code must too. ~14 LOC. Off hot path (flush). Existing drop-callback tests cover both branches.

**S-7 (rungs 1 + 7): `handle_seal_with_backpressure` over-generality and internal duplication.**
- NULL-tolerant out-params: tl_timelog.c:536-539, 560-565, 616-621 all branch on `out_dropped != NULL && out_dropped_len != NULL`. All four callers (tl_timelog.c:659, 706, 752, 789) pass non-NULL. The `else`/free branches are dead. Make the params mandatory (`TL_ASSERT`), delete the branches: ~12 LOC.
- The seal-attempt block appears twice verbatim (tl_timelog.c:551-567 pre-wait and :605-623 post-wait): a tiny static `try_seal(tl, need_signal, out_dropped, out_dropped_len)` removes ~13 more.
- Combined the function drops from ~100 to ~65 lines with zero semantic change. The backpressure wait choreography itself (drop writer_mu → wait on memtable_cond → reacquire, tl_timelog.c:585-599) is invariant-mandated and untouched.

**S-8 (rung 7): the four write entrypoints share a verbatim epilogue.**
- `tl_append` (634-674), `tl_append_batch` (676-721), `tl_delete_range` (723-761), `tl_delete_before` (763-799) all repeat: `TL_LOCK_WRITER` → `tl__next_op_seq` (+unlock-and-return on failure) → insert → `handle_seal_with_backpressure` → `TL_UNLOCK_WRITER` → `if (need_signal) tl__maint_request_flush` → `tl__emit_drop_callbacks` → EBUSY-combine. Lines 659-673 and 706-720 are identical; the delete variants differ only in not needing the insert-EBUSY combine (tombstone insert returns early on non-OK, so passing `insert_st = TL_OK` reproduces `return st` exactly).
- A `static tl_status_t tl__finish_write(tl_timelog_t*, tl_status_t insert_st)` called with writer_mu held (documented in its comment, mirroring `handle_seal_with_backpressure`'s existing "called with writer_mu held" contract at tl_timelog.c:515) collapses ~140 lines of entrypoints to ~80 including the helper. Net ~60 LOC.
- Perf: static function in the same TU; GCC/Clang/MSVC inline it; the append hot path executes the same instructions. Risk: the EBUSY-means-committed semantics are the most heavily tested contract in the codebase (C tests + Python facade tests + lab personas), so a regression would be caught loudly.

**S-9 (rung 7): the timestamp-navigation quartet is two functions wearing four coats.**
- tl_timelog.c:1576-1706 (~130 lines). `tl_min_ts` = first record of `iter_since(TL_TS_MIN)`; `tl_next_ts` = first record of `iter_since(ts+1)` (plus the `tl__inc_ts_safe` guard); `tl_max_ts` = last record of the unbounded scan; `tl_prev_ts` = last record of `[TL_TS_MIN, ts)`.
- Two static helpers — `nav_first_since(snap, t1, out)` and `nav_last_of(snap, iter-ctor-args, out)` — collapse this to ~70 lines incl. helpers. ~55 LOC.
- These are documented diagnostics ("intended for diagnostic/debugging use cases", timelog.h:516) — explicitly off hot path. `test_functional.c` exercises them 18 times; binding smoke tests cover the Python surface (py_timelog.c:2895-3042).

**S-10 (rung 7): `tl_open` / `init_locks` unwind ladders vs the house goto-cleanup pattern.**
- `init_locks` (tl_timelog.c:218-267) re-enumerates the teardown list in each failure branch — 5 progressively longer copies. `tl_open` (282-399) repeats its own teardown sequence 4 times, the last (380-387) being 6 lines.
- CLAUDE.md's own "Cleanup Pattern" prescribes goto-cleanup. Applying it here: `init_locks` ~50→~32 lines, `tl_open` saves ~12 more. Net ~25-30 LOC. Cold path (open), zero risk beyond mechanical transcription; the existing open-failure tests (ENOMEM injection) cover it.

**S-11 (rung 6): `status_strings` NULL-gapped array → switch.**
- tl_timelog.c:65-90: a 32-slot array where 24 slots are NULL padding, plus a bounds check, a NULL check, and a special case for `TL_EINTERNAL = 90` that doesn't fit the table. A plain `switch (s)` with 8 cases + default is shorter (~14 lines vs ~26), cannot drift when enum values move, and compiles to the same or better code. `tl_strerror` is error-path-only. ~10 LOC.

**S-12 (rung 1): `TL_WORK_RESHAPE_L0` — "Reserved for future use."**
- tl_timelog.c:1738. Speculative enum value, zero references. Delete the line. YAGNI in its purest form. 1 LOC.

**Minor (detail-only, rung 1): `tl__next_op_seq` overflow guard.**
- tl_timelog.c:484-486 returns `TL_EOVERFLOW` when `op_seq == UINT64_MAX`. At 10^9 appends/sec that is ~585 years of uptime for an *in-memory* engine whose data dies at close. This is an error path for an impossible state, and it sits on the append hot path (one perfectly-predicted branch — cost unmeasurable, which is also why removing it buys nothing). No test can reach it (no test hook sets op_seq near MAX; only test_compaction_internal.c:504 touches op_seq, at small values). Verdict: harmless either way; listed for completeness, not action.

**Minor (detail-only, rung 6): `tl_config_init_defaults` re-zeroes after memset.**
- tl_timelog.c:112 memsets the struct, then :117, :120, :122-127 assign 0/0.0 to seven fields. The assignments are documentation ("these defaults are deliberate"), and `0.0`-via-memset is fine on every supported target (IEEE 754 all-bits-zero). ~8 LOC if deleted; defensible to keep as docs. No action urged.

**Stats plumbing — checked, clean.** All 11 atomic counters initialised at open (tl_timelog.c:353-363), stored in the internal struct (tl_timelog_internal.h:192-202), read in `tl_stats` (tl_timelog.c:2164-2174), and exported to Python dicts (py_timelog.c:2790-2827, including all four `compaction_select_*`). No orphaned counter. The `compaction_select_*` quartet is incremented in tl_compaction.c (verified by header comment + grep). Nothing to delete.

**Config knobs — checked, clean.** Every `tl_config_t` field has a reader in core and a setter in the binding (py_timelog.c:1097-1400), except `allocator`/`log_fn`/`log_ctx`/`log_level`, which are deliberately C-embedder-only (the binding installs its own drop callback and the facade has no business exposing a C allocator). The only knob-shaped findings are S-1 (the append hint) and S-13 (`TIMELOG_BUILD_SHARED`).

---

## Prior-art leads (with honest fit notes)

1. **Background maintenance worker** (tl_timelog.c:1741-1883: thread + condvar + pending flags + exponential backoff).
   Candidates: pthreadpool (BSD-2), CK `ck_*` primitives (BSD-2), liburcu workqueue (**LGPL — fails license gate**), tinycthread/c11 threads shims.
   Fit: **poor**. The loop's value is the *policy*, not the plumbing: flush-drain with compaction cut-in (1810-1817), heuristic re-evaluation on every wake (1801-1805), backoff on transient failures only, and plain-bools-under-maint_mu specifically to close the lost-wakeup race (1723-1725) in a TSan-clean way including 3.14t. A generic pool provides none of that and adds a dependency to a project whose platform shim (`tl_sync.h`) already exists and is audited elsewhere. Lead recorded for completeness; expected verdict NO.

2. **DLL export header** (tl_export.h). Candidate: CMake `GenerateExportHeader` (already in the build, rung 5). Fit: works, but generates a larger file and adds a build-time include-path wrinkle for scikit-build wheels; the hand-written 20-liner is the canonical minimal form. Expected verdict NO (or moot if S-13 deletes it).

3. **Status-string mapping** (tl_timelog.c:65-90). Prior art is an idiom, not a library: X-macro enum/string tables (used by sqlite, CPython). For 8 codes a switch (S-11) is lazier than an X-macro. No library lead.

4. **Bounded-retry publish loop** (tl_timelog.c:1015-1032, TL_COMPACT_MAX_RETRIES at :808). This is optimistic-concurrency retry; libraries exist for CAS loops (CK) but the retried operation is a manifest rebuild — domain logic. No fit.

5. **Exponential backoff** (tl_timelog.c:1730-1731, 1822-1824). Two constants and a multiply-with-clamp. Any dependency would be net-negative LOC. No fit.

---

## Explicit NO-and-NO (machinery that earns its keep)

- **Deferred signalling choreography** (`tl__maint_request_flush`/`_compact` called only after `TL_UNLOCK_WRITER`, tl_timelog.c:664-666, 711-713, 755-757, 793-795): mandated by lock order `maint_mu → … → writer_mu` (CLAUDE.md). Any "simplification" that signals under writer_mu is a deadlock. Untouchable.
- **`flush_publish` three-phase pin/build/CAS** (tl_timelog.c:838-905): implements invariant 6 (snapshot consistency) — the memrun pop *must* share the seqlock write window with the manifest swap (comment at 886-890 explains the double/zero-count hazard). The explicit non-combined writer_mu+seqlock steps are justified by the file's closing comment (2223-2228). No shortcut exists that preserves the invariant.
- **Plain bools under maint_mu instead of atomics** (tl_timelog_internal.h:119-127, tl_timelog.c:1723-1725): the mutex doubles as the condvar predicate barrier; atomics would *reintroduce* the lost-wakeup race. Deliberate, documented, TSan-relevant. Keep.
- **Worker state machine STOPPED/RUNNING/STOPPING** (tl_timelog_internal.h:40-44): the third state exists to prevent double-join and double-spawn (comment 34-38); collapsing to a bool re-opens both races. Keep.
- **EBUSY remapping in the seal path** (tl_timelog.c:573-579): looks like error-swallowing, is actually the contract — the write already succeeded, and surfacing ENOMEM would trigger caller rollback of a committed record (binding rule 18). Keep.
- **`tl_iter_equal` vs `tl_iter_point`**: different memory/latency profiles (streaming vs eager); both consumed by the binding. Docs could state the trade-off; code stays.
- **`tl_stats` skyline-based estimate** (tl_timelog.c:2062-2118): O(pages+tombstones) instead of O(N) is the point; the three-way component walk mirrors the LSM structure and each arm calls a distinct counter. No collapse available without losing the short-circuits.
- **`tl_validate` release-mode no-op** (tl_timelog.c:2191-2220): public debugging affordance the binding exposes; 4 lines of release-mode cost. Keep.
- **`handle_seal_with_backpressure` drop-and-reacquire of writer_mu** (tl_timelog.c:585-599): the worker needs writer_mu to publish the flush that frees queue space; waiting while holding it is a livelock. Comment grounds it. Keep (S-7 trims around it, not through it).

---

## Test-coverage notes

- S-5, S-6, S-8: covered by existing C suites (test_functional.c empty-range at :150; drop-callback and EBUSY contracts across test_api_semantics.c / delta suites) plus the Python facade tests — safe mechanical refactors.
- S-9: 18 call sites in test_functional.c + binding tests; safe.
- S-3/S-4 (deletions): would *remove* the only tests using them (test_functional.c:566-748); no new tests needed.
- S-1: python/tests/test_bulk_append.py:230-242 currently asserts kwarg-resolution behavior of the no-op; excision removes those tests. Any "keep kwarg, ignore it" middle path needs no new tests.
- S-13: if the option is kept, it needs a CI leg (currently zero coverage of the `TL_BUILD_SHARED` preprocessor branch); if deleted, nothing.
