# Ponytail Audit — Unit: bindings-infra

Files: `bindings/cpython/src/py_handle.c` (1108 LOC), `bindings/cpython/src/module.c` (635 LOC),
`bindings/cpython/src/py_errors.c` (204 LOC). Context also read in full:
`bindings/cpython/include/timelogpy/py_handle.h`, `py_module_state.h`, `py_compat.h`,
plus targeted reads of `py_timelog.c` call sites and the four binding test suites that
exercise this unit (`test_py_handle.c`, `test_py_maint_b5.c`, `test_py_module.c`,
`test_py_module_exec.c`, `test_py_errors.c`).

## Executive Summary

This unit is the most concurrency-hardened corner of the bindings, and most of its
machinery earns its keep: the lock-free retired queue, the traverse_readers handshake,
the retired-tables chain, and the pin/drain handoff all exist to solve a documented
production deadlock class (v1.2 free-threaded stop-the-world GC, `py_handle.c:1005-1011`)
and are load-bearing under TSan on 3.14t. Prior-art replacement of the hash table or the
Treiber stack is a bad trade — the table mechanics are trivial; the concurrency contract
wrapped around them is the actual content, and no MIT-compatible C library ships that
contract.

The real wins are elsewhere:

1. **`PyErr_FormatV` replaces the hand-rolled vsnprintf raisers** (rung 4, ~35 LOC,
   kills a 512-byte truncation and a copy-pasted function body).
2. **Dead code**: `TlPy_ModuleMatchesTimelogDef` (zero callers), the never-read
   `ts` field in every drop node, a dead `list_tail = NULL` store, a stale include,
   duplicated doc comments.
3. **`module.c` reload-rollback machinery** (~170 LOC of export snapshot/restore +
   state-validity predicates + the `initialized` flag) hardens a path — failed
   `importlib.reload()` of a C extension — that CPython's own stdlib extensions do not
   harden. This is the unit's one big "does-not-need-to-exist" judgment call; it is fully
   tested, so the cost is purely maintenance weight, and the maintainer may legitimately
   keep it.

Total realistic savings: **~230 LOC of source** (plus ~400 LOC of tests if the module.c
rollback deletion is accepted), with zero hot-path impact — nothing in this unit's
proposals touches append/query/merge.

---

## Per-file walkthrough

### py_handle.c — retired queue, pins, live-handle multiset

**Machinery inventory:**

| Piece | Lines | Verdict |
|---|---|---|
| Platform yield shim | 31-37 | keep (see N5) |
| Live-entry state machine + table struct | 44-77 | keep (see N1/P1) |
| Interp probe helpers | 89-129 | keep; delete orphaned duplicate comment 79-96 |
| Unsafe-destroy warning | 131-167 | keep (finalization-silence is a documented usability fix, 144-154) |
| Pointer hash | 169-179 | keep (see P3) |
| Rehash + retired-tables chain | 181-234 | keep (see N4) |
| Treiber push | 250-270 | keep (see P2) |
| Retired-list processing | 272-345 | dead store at 313-316 (S9) |
| Drain claim/guard | 347-377 | keep |
| Load-factor ensure | 379-405 | keep |
| C11 checks | 415-421 | micro-deletable (S8) |
| Lifecycle init/new/incref/decref/destroy | 427-593 | `ctx_init`/`heap_allocated` marginal (S7) |
| Pins enter/exit | 607-659 | keep (see N2) |
| on_drop callback | 680-706 | `ts` field dead (S3) |
| Drain entry | 716-747 | keep |
| Live insert/drop/release_all/traverse | 763-1079 | keep (see N1/N3) |
| Metrics | 1085-1108 | keep (see N6) |

### module.c — multi-phase init

Type registry table (73-101) with offset accessors: reasonable table-driven init; the
`_Static_assert(TIMELOG_TYPE_COUNT == 6)` at 100 keeps it honest. The heavy machinery is
the **reload-hardening**: export snapshot/restore (278-347), state-validity predicates
(195-257), and the exec paths that re-export on complete state (448-456). See S1.
`timelog_free` is an empty stub (172-175). `TlPy_ModuleMatchesTimelogDef` (517-520) is
dead. `managed_export_names[]` (40-48) duplicates the names in `entries[]` (351-365),
lock-stepped only by count, not by name (S5).

### py_errors.c — exception creation + status mapping

`tlpy_validate_error_pair` (18-39) plus the incomplete-pair check (52-57) validate facts
true by construction (S6). The two `*Fmt` raisers (137-164, 175-204) are a copy-pasted
vsnprintf idiom that CPython already provides as `PyErr_FormatV` (S2 — the unit's best
finding). `tlpy_status_to_exception_type` (99-123) is already minimal.

---

## Findings — SIMPLER?

### S1. Delete the module reload-rollback machinery — rung 1 (does-not-need-to-exist)
**Where:** `module.c:278-347` (`timelog_snapshot_exports` / `timelog_discard_export_snapshots`
/ `timelog_restore_exports`), `module.c:195-257` (`timelog_state_has_empty_errors`,
`timelog_state_has_empty_types`, `timelog_state_has_complete_types` retained,
`timelog_state_is_invalid`), the `initialized` flag (written 7×, read exactly once at
`module.c:253`, inside the validity checker itself), and the export failpoints
(`py_module_state.h:66-70`).

**Evidence:** The snapshot/restore machinery only matters when `Py_mod_exec` runs on a
module object that already has exports — i.e. `importlib.reload()` of the C extension —
and then *fails mid-export*. On first import, a failed exec causes the import system to
discard the module entirely; rollback is unobservable. CPython's own multi-phase stdlib
extensions (`_sqlite3`, `_ssl`) implement no export rollback. The state-validity
predicates guard "partially initialized module state," which is only reachable via that
same failed-reload path (state is written exclusively by `timelog_exec` and cleared
whole by `timelog_clear`, `module.c:159-170`).

**What stays:** the idempotent complete-state re-exec (`module.c:448-456`) is 9 lines and
handles benign re-exec; keep it. `timelog_remove_managed_exports` + `timelog_clear_state_refs`
on the error path (479-481) remain as the whole failure story.

**LOC saved:** ~170 in module.c, ~400 in `test_py_module_exec.c`
(`export_failure_restores_previous_module_attrs`:634, `complete_state_reexec_restores_missing_exports`:600,
`same_module_reexec_after_manual_reset_preserves_exports`:683, part of
`retry_after_each_failpoint`:765), 5 failpoint enum rows.
**Risk:** medium — not because anything breaks (observable delta: a failed reload leaves
the module dict partially updated, matching stdlib behavior), but because this was built
deliberately and is fully tested; it is a philosophy call for the maintainer.
**Perf:** zero (import-time only). **api-change:** no.

### S2. Replace vsnprintf raisers with `PyErr_FormatV` — rung 4 (platform)
**Where:** `py_errors.c:137-164` (`TlPy_RaiseFromStateFmt`), `py_errors.c:175-204`
(`TlPy_RaiseFromObjectFmt` — a full copy of the body because varargs cannot be forwarded
to a `...` function).

**Evidence:** CPython has provided `PyErr_FormatV(exception, format, va_list)` since 3.5.
Every format string in the codebase is within `PyUnicode_FromFormat`'s supported set:
`"%s"` (`py_timelog.c:457,3143`), literals (`py_timelog.c:484,2681,3090`, `py_timelog.h:234,247`),
and `"%llu"` with an explicit `(unsigned long long)` cast (`py_timelog.c:1593-1597`).
Rewrite:

```c
static PyObject* tlpy_raise_v(const tl_py_module_state_t* st, tl_status_t status,
                              const char* format, va_list args) {
    PyObject* type = tlpy_status_to_exception_type(st, status);
    if (format == NULL || format[0] == '\0') PyErr_SetString(type, tl_strerror(status));
    else PyErr_FormatV(type, format, args);
    return NULL;
}
```
Both public Fmt functions become 6-line wrappers; the ObjectFmt duplicate body vanishes.

**Behavior deltas (both improvements):** (a) messages longer than 511 bytes are no longer
truncated — `test_py_errors.c:372` (`raise_formatted_long_message_truncates_safely`,
asserts `strlen(text) < 512`) must be updated to assert the full message; (b) the
empty-*format* fallback is preserved by the 2-line check (test at `py_errors.c` /
`test_py_errors.c:344` keeps passing), but a format like `"%s"` with an empty argument
now produces an empty message instead of the status text — no caller does this.
**Caveat for future callers:** `PyErr_FormatV` uses `PyUnicode_FromFormat`'s specifier
set (no `%f`/`%g`); a one-line comment on the helper covers it.

**LOC saved:** ~35 net (68 → ~28 in py_errors.c, minus test tweak).
**Risk:** low. **Perf:** error paths only. **api-change:** no (exception text for
>511-char messages changes; Python API promises no truncation).

### S3. Delete the dead `ts` field from drop nodes — rung 1
**Where:** `py_handle.h:90` (`tl_ts_t ts; /**< Timestamp for debugging/metrics */`),
`py_handle.c:699` (`node->ts = ts;`).
**Evidence:** repo-wide grep: written once, read nowhere (no metric, no debug printer).
Saves 8 bytes per retired node and one store on the on_drop path — that path runs once
per physically dropped record during compaction/flush, so this is a (small) strict win
on a warm path, not just LOC. The callback signature keeps taking `ts` (fixed by the
core `on_drop` contract); it just stops storing it.
**LOC saved:** 4. **Risk:** none. Existing tests unaffected (verified: no test reads it).

### S4. Delete dead `TlPy_ModuleMatchesTimelogDef` — rung 1
**Where:** `module.c:517-520`, declaration `py_module_state.h:41`.
**Evidence:** zero callers across src/tests/python (`grep -rn ModuleMatchesTimelogDef`
finds only the definition and declaration).
**LOC saved:** 7. **Risk:** none (compile-verified by build).

### S5. Merge `managed_export_names[]` into a single export table — rung 7
**Where:** `module.c:40-51` vs `module.c:351-365`.
**Evidence:** the same 7 names appear twice; the `_Static_assert` at 366-368 pins only the
*count*. `timelog_restore_exports` keys off `managed_export_names[i]` while the add loop
keys off `entries[i].name` — a silent-drift hazard if orders ever diverge. One static
table `{name, offsetof(tl_py_module_state_t, member), failpoint, stage}` serves export,
remove, snapshot, and restore. (If S1 is accepted, snapshot/restore disappear and this
shrinks to trivial.)
**LOC saved:** ~15. **Risk:** low; covered by `test_py_module.c:211`
(`extension_exports_expected_names`).

### S6. Delete by-construction validation in error init — rung 1
**Where:** `py_errors.c:18-39` (`tlpy_validate_error_pair`), calls at 59-61 and 75-79,
incomplete-pair check at 52-57.
**Evidence:** on the fresh path, `busy` is created with `error` as its base
(`py_errors.c:69`), so `PyObject_IsSubclass(busy, error)` is true by construction, and
`PyErr_NewException` returns exception classes by contract. On the re-exec path, state
is written only by this function and cleared pairwise by `TlPy_ClearErrors`
(`py_errors.c:93-96`), so a half-populated or non-subclass pair is unreachable.
Tests never seed invalid state — `test_py_errors.c` only exercises the happy re-init
(`ClearErrors` then `InitErrors == 0`, lines 224-250) and the *outcome* subclass
property (line 194), both of which keep passing.
**LOC saved:** ~35. **Risk:** low (import-time; unreachable branches).

### S7. Test-only `tl_py_handle_ctx_init` / `heap_allocated` flag — rung 7, marginal
**Where:** `py_handle.c:427-483,529-533`, `py_handle.h:110,235-244`.
**Evidence:** production creates contexts solely via `tl_py_handle_ctx_new`
(`py_timelog.c:1085`); `ctx_init` + stack allocation is used only by
`test_py_handle.c` / `test_py_maint_b5.c` (~30 call sites). Folding init into new and
deleting the flag saves ~12 source LOC but forces heap+decref rewrites across those
tests, and stack contexts genuinely simplify the C tests.
**Honest verdict:** not worth the churn — recorded so nobody re-litigates it. Skip.

### S8. Micro: C11 `#error` guards — rung 1
**Where:** `py_handle.c:410-421`. `<stdatomic.h>` is already included via
`py_handle.h:34`; a compiler without C11 atomics fails there first. 7 LOC of
belt-and-suspenders. Delete or keep — noise either way.

### S9. Micro: dead store in retired-list loop — rung 1
**Where:** `py_handle.c:313-316` (`if (list == NULL) { list_tail = NULL; }`).
**Evidence:** `list_tail` is only read by the two `tl_py_retired_push(ctx, list, list_tail)`
re-push calls (291, 302), both executed at the top of an iteration while `list != NULL`,
where the original tail is still the tail (head pops don't move it). After the pop that
nulls `list`, the loop exits and `list_tail` is never read. 3 LOC dead.

### S10. Micro: comment/include cruft — rung 1
`py_handle.c:79-96`: two stacked doc comments; the first ("Returns 1 if...") describes
`tl_py_attached_to_interp` but sits orphaned above `tl_py_current_interp_or_null`, which
has its own correct comment. ~10 comment lines. `py_handle.c:29`:
`#include <string.h> /* memset */` — no `memset` in the file.

---

## Findings — PRIOR ART? (leads with fit notes)

### P1. Live-handle open-addressing multiset → khash / verstable / stb_ds — POOR FIT
**Where:** `py_handle.c:62-76, 169-234, 379-405, 763-845`.
Candidates: khash (klib, MIT, header-only, MSVC-clean, allocator-redefinable),
Verstable (MIT), stb_ds (MIT/PD), CC (MIT).
**Fit notes (honest):** the table mechanics — linear probing, tombstones, 0.7 load
factor, doubling — are textbook and any of these covers them in principle. But the
load-bearing 40% of this code is a concurrency contract no generic table has: per-entry
atomic state machine with release-publication and seq_cst retirement
(`py_handle.c:48-61`), stale tables chained rather than freed so a lock-free
`tp_traverse` can keep walking them (`py_handle.c:71-76, 224-227`), and the
`traverse_readers` reader-gate protocol (`py_handle.c:295-330, 977-983, 1027-1057`).
This exists because of the v1.2 free-threaded stop-the-world GC deadlock
(`py_handle.c:1005-1011`): tp_traverse must never park or malloc. Bolting atomics onto
khash's entry layout means forking it, at which point nothing is saved. Would also need
TSan-clean verification on 3.14t per the hard constraints. **Verdict: NO** — the extra
instructions asked for an honest weighing; the PyMutex/free-threading integration is the
hard part and it is bespoke by necessity.

### P2. Treiber stack → Concurrency Kit `ck_stack` — POOR FIT
**Where:** `py_handle.c:250-270, 355-357, 680-706`.
`ck_stack` (BSD-2) is the canonical implementation. But: (a) the whole stack here is
~25 lines; (b) the one non-obvious choice — ACQ_REL CAS instead of release-only — is
deliberate and documented as a TSan/C++20-release-sequence workaround
(`py_handle.c:243-248`), which stock lock-free libraries do not guarantee to satisfy;
(c) CK's MSVC support is historically weak and it is a whole dependency for one MPSC
push/exchange pair. liburcu is LGPL — license fail. **Verdict: NO.**

### P3. Pointer hash mix — already IS prior art
`py_handle.c:169-179` uses hash-prospector-style avalanche constants
(0xed5ad4bb, 0xac4c1b51 — Wellons' lowbias32 family). 10 lines, correct, nothing to
import. **Verdict: NO.**

### P4. printf-style exception raising → `PyErr_FormatV` — GOOD FIT (adopted as S2)
Platform (rung 4). CPython's own API replaces the whole buffer/vsnprintf/truncate dance.

### P5. CPU-yield shim → duplicate of core `tl_sync.c` — rung-2 lead, REJECTED
`py_handle.c:31-37` duplicates the platform switch in
`core/src/internal/tl_sync.c:267,591` (SwitchToThread/sched_yield). Sharing would mean
exporting a core-internal `tl__` symbol to the binding for 6 lines — inverts the
public-API layering for negative value. **Verdict: NO**, but named per the rung-2 rule.

### P6. Multi-phase module init — prior art is CPython's own idiom (feeds S1)
The platform pattern (e.g. `_sqlite3`'s `module_exec`) is a linear create-and-add with
`Py_CLEAR`-on-failure and no export rollback. Timelog's extra machinery beyond that idiom
is exactly what S1 proposes deleting.

---

## NO and NO — machinery that earns its keep

- **N1. Lock-free tp_traverse + traverse_readers gates** (`py_handle.c:993-1079`,
  `295-330`, `977-983`): must never park or allocate during free-threaded stop-the-world
  GC — a frozen thread can hold live_lock or the libc arena lock forever (v1.2
  production deadlock, `py_handle.c:1005-1011`). The double reader-gate in the drain
  (pre-check + post-TOMBSTONE seq_cst gate, 295-330) closes a real check-then-act
  window. Any "simplification" here reintroduces the deadlock class. Covered by
  free-threading/stress test legs.
- **N2. pin_lock around the pins counter** (`py_handle.c:607-651`, `py_handle.h:163-170`):
  serializes the pins 0→1 transition against a drainer that observed zero and is about
  to claim the retired list. Held for a few instructions; runs per snapshot
  acquire/release, not per record — off the hot iteration path. Do not weaken; this is
  precisely the TOCTOU family the maintainer's hostile reviews exist to catch.
- **N3. drain_batch_limit + suffix re-push** (`py_handle.c:287-292`): not a speculative
  knob — it is user-configurable from Python (`py_timelog.c:1075-1085`) and covered by
  `test_py_maint_b5.c:387-419`. The upfront O(n) tail walk (281-284) could be deferred
  to the rare re-push path, but that adds code for a non-hot path; not a finding.
- **N4. retired_tables chain** (`py_handle.c:68-76, 224-227`): "never free a resized-out
  table until teardown" is the cheapest correct answer to lock-free readers on stale
  tables; memory is bounded by the doubling schedule. The library alternatives
  (RCU/hazard pointers) are heavier and liburcu is LGPL.
- **N5. tl_py_cpu_yield shim** (`py_handle.c:31-37`): 6 lines; see P5.
- **N6. retired_queue_len underflow clamp** (`py_handle.c:1096-1098`): looks like
  impossible-state defense but is reachable — `retired_count` increments *after* the
  push (`py_handle.c:702-705`), so a racing drain can transiently make
  drained > retired. Earns its keep as-is.
- **N7. tl_py_mutex_t / critical-section compat shims** (`py_compat.h:54-107, 175-203`):
  forced by the 3.12 floor (PyMutex is 3.13+); deletable only when 3.12 support drops —
  flag for that day, not now.
- **N8. drain_guard atomic_flag** (`py_handle.c:359-377`): reentrancy guard against
  `__del__`-driven recursive drains; one flag, no simpler correct form.
- **N9. Unsafe-destroy warning split** (`py_handle.c:131-167` release-mode vs
  `549-574` NDEBUG): overlapping but differently-audienced diagnostics; the
  finalization-silence behavior at 144-154 is a documented usability fix (v1.3 lab).
  Consolidation would save ~15 LOC at the cost of re-deriving which warning fires when;
  not worth it.

## Aside (not a simplification — perf note for the perf-wins branch)

`py_handle.c:787` (`e->obj = obj;`) and `py_handle.c:798` (`e->obj == obj`) use plain
assignment/comparison on an `_Atomic(PyObject*)` field, which C11 makes **seq_cst** — a
full barrier store on x86 for every *new* distinct object inserted on the append path
(`tl_py_live_note_insert` is called per append/bulk element, `py_timelog.c:1823-2523`).
The publication contract (`py_handle.c:48-51`) only requires the obj store to precede the
release store of `state`; an explicit `atomic_store_explicit(..., memory_order_relaxed)`
(ordered by the subsequent release) would shave a fence per insert. Same for the rehash
loads at 201. Zero LOC change; belongs to a perf pass, not this audit.

## Test-coverage notes

- S2 requires editing one assertion (`test_py_errors.c:372` truncation test).
- S1 deletes ~400 LOC of tests that test the deleted machinery itself.
- S3/S4/S9/S10 need no test changes (verified no readers).
- Everything kept under NO-and-NO is exercised by `test_py_handle.c`,
  `test_py_maint_b5.c`, the freethreading/stress pytest legs, and the (local) resilience
  lab.
