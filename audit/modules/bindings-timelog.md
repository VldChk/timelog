# Ponytail Audit — Unit: bindings-timelog

**File:** `bindings/cpython/src/py_timelog.c` (3,866 lines, read in full)
**Persona:** lazy senior dev. Laziness never applied to reading; every line was read.
**Date:** 2026-07-07

## Executive Summary

This file is the PyTimelog type: lifecycle (`tp_init`/`close`/`tp_dealloc`/GC), the
core_lock + snapshot-pin protocol, the append/extend/bulk_append write paths, tombstone
writes, maintenance control, stats, and eleven query entry points. The concurrency
machinery (pin protocol, owned-ctx capture, trylock traverse, two-phase close) is
**dense but earns its keep** — nearly every "weird" branch is annotated with the race it
kills, and the project history (5 TOCTOU blockers caught in review) says simplifying it
is how you get hurt. The fat is elsewhere: **method boilerplate**. Three clusters
dominate:

1. `PyTimelog_init` has ~280 lines of copy-pasted sentinel/range-check/`drop_handle_ctx`
   blocks for 20 numeric config kwargs — the single biggest deletion target in the file
   (~200 LOC with an X-macro table + moving `handle_ctx` creation after validation).
2. `stats()` hand-builds five nested dicts with three local macros and a goto ladder;
   `Py_BuildValue` (platform) does the whole thing in one call (~85 LOC).
3. Eleven FASTCALL entry points repeat the same NARGS-check → `tl_py_fast_i64` →
   `tl_py_validate_ts` → snapshot-acquire/release choreography (~120 LOC foldable into
   two small helpers with zero hot-path cost).

Total honest estimate: **~450–550 LOC** removable with zero functional and zero
performance regression, all off the append/query-iteration hot paths. No external
dependency is worth adopting anywhere in this file; every prior-art lead below is either
"CPython already provides it" (Py_BuildValue, O& converters) or a bad trade (Argument
Clinic, Concurrency Kit).

---

## Per-file walkthrough

### 1. Engine/handle context plumbing (lines 81–170)

`tl_py_engine_ctx_new/incref/close/decref` — a 70-line refcounted wrapper around
`tl_timelog_t*` so iterators/spans can outlive `close()`. Atomics are C11
(`atomic_fetch_sub_explicit(..., acq_rel)` at 141–142) — this matches the documented
TSan fence limitation (decrement must be acq_rel). **NO and NO**: prior art (liburcu
`urcu/ref.h`, CK) fails the MSVC + TSan-clean-on-3.14t + tiny-usage test; C11 atomics
are already the minimal answer.

### 2. Config parsing helpers (172–765)

* `parse_time_unit` / `parse_maint_mode` / `parse_busy_policy` (187–245): three tiny
  string-table parsers with *distinct* default semantics (`was_set` out-param only on
  time_unit). A generic table function saves ~15 lines and costs equal glue. **NO** —
  wash.
* `tl_py_dict_get_item_string_ref` (247–261): 3.12-compat shim for
  `PyDict_GetItemStringRef` (3.13+). Needed while requires-python is >= 3.12. **NO.**
* `kwarg_was_provided` (281–298): used exactly twice (`delete_debt_threshold`,
  `adaptive_alpha`) because doubles have no clean sentinel. A NaN sentinel would delete
  it, **but** an explicit `delete_debt_threshold=float('nan')` currently raises
  `ValueError("must be finite")` (line 1237–1241) and would silently become "unset" —
  an observable API behavior change. **NO** (grounded behavior difference).
* `tl_py_fast_i64` (324–332) vs `tl_py_coerce_ts` (342–387): two deliberate coercers
  with documented, different contracts (facade `_coerce_ts` parity incl. bool rejection
  and teaching errors vs `PyArg "L"` parity). Unifying changes public exception
  behavior. **NO** (would be api-change).
* `tl_py_now_ts` (402–441): **FINDING S6** — the `long double` pre-check at 410–414
  ("`sec_ld > (long double)LLONG_MAX / 1e9`") is fully subsumed by the exact integer
  overflow guards at 420–431 (`sec > (LLONG_MAX - nsec)/1e9` etc.; since `sec` is an
  integer and the divisions truncate, the integer checks are complete for
  `sec*1e9 + nsec`). Dead defense for an already-defended impossible state
  (system clock past year 2262). Delete ~8 lines. Rung 1.
* `dict_get_ssize/llong/double` (684–734): three 12-line siblings. Macro-generating
  them saves ~15 lines at readability cost. Marginal — noted, not recommended.

### 3. `PyTimelog_init` (771–1443) — THE fat target

* **FINDING S5**: the `enum { KW_TIME_UNIT ... KW_COMPACTION_DICT }` (806–836, 30 lines)
  has exactly **two** used members: `KW_DELETE_DEBT_THRESHOLD` (line 921) and
  `KW_ADAPTIVE_ALPHA` (line 925) — verified by grep. 27 enumerators exist only to keep
  two indices honest. Two named constants with a "must match kwlist order" comment do
  the same job in 4 lines. Rung 1 (~26 LOC).
* **FINDING S1a**: `tl_py_handle_ctx_new` is called at line 1085, *before* ~280 lines of
  config validation — so **every one of the ~28 subsequent error paths** must call
  `tl_py_timelog_drop_handle_ctx(self)` (e.g. 1098, 1104, 1110, 1119, 1134, 1149, 1165,
  1181, 1191, 1201, 1217, 1228, 1238, 1244, 1254, 1260, 1270, 1280, 1290, 1300, 1310,
  1320, 1330, 1340, 1346, 1356, 1366, 1377, 1389, 1409, 1421). Nothing between 1085 and
  the `cfg.on_drop_ctx = hctx` wiring at 1400 needs the context (verified: the region
  only writes `cfg.*`, `self->busy_policy`, `self->busy_events`). Create the context
  *after* validation, immediately before `tl_open`, and all those drop calls vanish
  (~28 LOC + one whole class of leak-on-error hazards). Rung 7, zero behavior change.
* **FINDING S1b**: the numeric-override blocks (1116–1396) are one 9–15-line template
  stamped 20 times in three shapes:
  - size_t shape (memtable_max_bytes 1117–1131, target_page_bytes 1132–1146,
    sealed_max_runs 1147–1161, ooo_budget_bytes 1163–1177, max_delta_segments
    1199–1213, compaction_target_bytes 1252–1266): `< 0` ValueError +
    `(size_t)x != (uint64_t)x` OverflowError ("too large for this platform").
  - u32 shape (sealed_wait_ms 1179–1187, maintenance_wakeup_ms 1189–1197,
    max_compaction_inputs 1268–1276, max_compaction_windows 1278–1286,
    adaptive_hysteresis_pct 1318–1326, adaptive_warmup_flushes 1354–1362,
    adaptive_stale_flushes 1364–1372, adaptive_failure_backoff_threshold 1374–1384,
    adaptive_failure_backoff_pct 1386–1396): "must be 0-4294967295".
  - ts shape (window_size 1215–1223, adaptive_min_window 1298–1306, adaptive_max_window
    1308–1316, adaptive_window_quantum 1328–1336): "[0, INT64_MAX]".
  Three X-macro/`APPLY_*` helpers (name string, source var, dest field) collapse
  ~240 lines to ~60 (macros + 20 invocation lines), **preserving every error message
  byte-for-byte** (messages like "must be 0-4294967295" are asserted in Python tests).
  Combined S1a+S1b: **~200 LOC**, init-only (off all hot paths), risk low; existing
  C-level (`test_py_timelog.c`) and Python config tests are the net.
  Prior-art alternative (rung 4): `PyArg_ParseTupleAndKeywords` `O&` converter
  functions, passing a `{name, kind, dest}` descriptor through the `void*` — eliminates
  the sentinel dance entirely, but reproducing exact messages costs comparable glue;
  the X-macro form is the lower-risk version of the same idea.
* `CHECK_ADAPTIVE_CONFLICT` / `CHECK_COMPACTION_CONFLICT` (954–994, 1038–1061): already
  macro-ized; unifying the two into one parameterized macro saves ~12 lines. Marginal.

### 4. Close / dealloc / GC (1445–1683)

`pytimelog_close_no_raise` (1453–1571) is 120 lines where every branch is annotated
with the exact race it prevents: unlocked idempotence fast path with the engine_ctx
data-race note (1460–1469), pins sampled under core_lock (1483–1496),
handle_ctx detached under the same lock the mutation paths use for owned capture
(1502–1510), deferred engine close for finalizer-with-pins (1513–1515), degradation
ResourceWarning (1547–1557), and the explicit "do NOT free core_lock here" UAF comment
(1559–1569). **NO and NO** — this is the residue of the TOCTOU review cycle; any
"simpler" close reintroduces one of those windows, and the free-threaded stress suites
(`test_freethreaded_stress.py`) are the only thing standing between a refactor and a
heisen-crash. Same verdict for `PyTimelog_traverse`'s trylock (1652–1669) — parking in
tp_traverse deadlocks a free-threaded stop-the-world GC (documented at 523–529).

### 5. Write path (1685–2553)

* `PyTimelog_append` (1693–1850): hand-rolled vectorcall + kwnames parsing (1705–1752).
  **NO and NO** — this *is* the hot path (METH_FASTCALL fold measured −23.7% append
  latency per project memory); `PyArg_ParseTupleAndKeywords` would force METH_VARARGS
  tuple/dict packing per call; CPython's `_PyArg_UnpackKeywords` is private API and
  off-limits for shipped wheels. Argument Clinic is the only "library" answer and it's
  a codegen step designed for the CPython tree — bad trade for two methods (lead
  recorded, expected verdict: reject).
* `PyTimelog_extend` (1862–2174): **FINDING S4** — the batch-commit epilogue
  (`st==TL_OK||TL_EBUSY` → `tl_py_live_note_insert` loop → EBUSY policy → drain/decref)
  is stamped **three times**: sequence path 1970–2004, chunk path 2100–2123, tail path
  2137–2157. The file already established the pattern for factoring exactly this:
  `tl_py_finish_tombstone_write` (2570–2590) exists because delete_range/delete_before
  shared the same epilogue. A `tl_py_finish_batch_insert(self, hctx, objs, n, st)`
  returning success / raise-no-rollback / true-failure collapses ~40 LOC and puts the
  EBUSY-is-committed contract (the #1 documented footgun) in ONE place instead of
  three. Rung 2 (already-in-this-codebase twin). Risk low-medium — refcount rollback
  paths need care, but `test_append_contract.py` + ASan builds cover exactly this.
  Minor note: extend uses raw `malloc/free` (1896–1897) while bulk_append uses
  `PyMem_Malloc` (2474) — harmless inconsistency, unify while touching it.
* `PyTimelog_bulk_append` (2228–2553): **FINDING S7** — the hand-rolled kwnames loop
  (2235–2294, ~60 lines) mirrors append's, but here it is *not* hot: one call per
  batch of thousands of records. `PyArg_ParseTupleAndKeywords("OO|$O:bulk_append",...)`
  under METH_VARARGS|METH_KEYWORDS deletes ~50 lines. **Caveat (why risk=medium):**
  `test_bulk_append.py:217–219` asserts message fragments "unexpected keyword" and
  "multiple values", which CPython's PyArg words differently ("invalid keyword
  argument", "given by name ... and position") — the swap requires those two test
  regexes to be relaxed. Flag loudly: test-visible message change, not an API change.
  The rest of bulk_append (buffer validation 2319–2405, dtype-'M' error rewrite
  2325–2345, alignment check 2369–2380, `_mostly_ordered_default` resolution
  2431–2460) earns its keep: each check has a real UB or usability justification and
  `test_bulk_append.py` pins the behavior. `tl_py_buffer_fmt_is_native_i64`
  (2201–2226): **NO and NO** — CPython has no public API to validate a buffer format
  string, and the tri-state return powers the endianness-specific error message.
* min_ts floor guard duplication between append (1785–1794) and bulk_append
  (2467–2471): 6 lines, deliberate (per-call snapshot semantics documented at
  2462–2466). Not worth glue.

### 6. Tombstones, flush/compact/maint, stats (2555–2875)

* `tl_py_finish_tombstone_write` (2570–2590): good existing factoring — cited as the
  in-file precedent for S4.
* `flush`/`compact`/`maint_step`/`stop_maint` all ride `tl_py_core_call_strict`;
  `tl_py_core_call_strict` vs `_best_effort` (556–600): **NO** — strict must
  distinguish "closed" (raise ESTATE from `tl_py_lock_checked`) from a core-returned
  ESTATE; best_effort deliberately conflates them for the EBUSY→flush policy path
  (462). Merging them loses that distinction.
* `PyTimelog_stats` (2751–2847) + `TL_PY_SET_U64/I64/DBL` macros (2724–2749):
  **FINDING S2** — 127 lines of dict assembly, three throwaway macros, a
  6-way `Py_XDECREF` error ladder repeated twice (2779–2787, 2839–2846). CPython's
  `Py_BuildValue` builds the whole nested structure in one call:
  `Py_BuildValue("{s:{s:K,...},s:{...},...}", "storage", "segments_l0",
  (unsigned long long)stats.segments_l0, ...)` — it allocates, populates, and cleans up
  on failure internally. ~40 lines replace ~127. Rung 3/4 (platform). stats() is a
  diagnostics call — provably off hot path. Tests assert stats keys; format-string
  typos would be caught immediately.

### 7. Query entry points (2877–3548)

* **FINDING S3a**: `min_ts` (2881–2905) and `max_ts` (2907–2931) are byte-identical
  except `tl_min_ts` vs `tl_max_ts`; `next_ts` (2972–3011) and `prev_ts` (3013–3052)
  are byte-identical except `tl_next_ts`/`tl_prev_ts` and the arg-name string. Two
  helpers — `tl_py_snap_query_ts0(self, fn)` and `tl_py_snap_query_ts1(self, fn, ts)` —
  fold the acquire-pinned/call/release/EOF→None/status→raise choreography once.
  ~85 lines → ~35.
* **FINDING S3b**: `since`/`until`/`equal`/`point` (3399–3504) and the scalar-parse
  prefix of `next_ts`/`prev_ts`/`delete_before` all repeat the same 14-line
  "NARGS!=1 → TypeError; `tl_py_fast_i64`; `tl_py_validate_ts`" block (e.g. 3401–3414,
  3426–3439, 3462–3475, 3488–3501, 2977–2990, 3018–3031, 2640–2652); `range` and
  `delete_range` share the 2-arg + `t1<=t2` variant (3370–3389, 2597–2617). One
  `tl_py_parse_ts_args(name, args, nargs, n_expected, out1, out2)` helper: 11 sites
  × ~10 lines → 11 × 2–3 lines + ~20-line helper. S3a+S3b ≈ **120 LOC**, all on
  per-call setup (one extra static-function call, inlined or negligible next to
  snapshot acquisition + count precompute). Zero regression on query *iteration* —
  this code runs once per iterator creation, not per record.
* **FINDING S8**: `pytimelog_make_iter` switches over `mode` twice — range
  normalization (3293–3300) and count parameters (3307–3326). One switch setting all
  five fields does both (~14 LOC). **Do not** try to *derive* count params from
  range_t1/range_t2 instead: `SINCE` sets `range_t2 = TL_TS_MAX` but counts
  *unbounded* (includes TS_MAX), while `RANGE(t1, TS_MAX)` must stay bounded
  (excludes TS_MAX, half-open invariant) — the two switches encode a real one-record
  difference at the boundary. Merge the switches, keep the distinct fields.
* The deliberate no-detach comment for count precompute (3328–3336, the 461× GIL
  starvation measurement) — load-bearing, untouchable.
* `PyTimelog_enter` (3139–3161) re-implements `start_maintenance`'s lock/call/check
  (3094–3107) inline; a shared 8-line static helper saves ~8 LOC. Minor.

### 8. Properties, method table, type spec (3550–3866)

Straight-line. `views` aliasing `page_spans` by reusing the same C function (3807) is
already the lazy solution. The "deliberately NO vectorcall slot" comment (3841–3845) is
regression-guarded by test_hardening.py. Nothing to cut.

---

## Findings table

| # | Title | Where | Rung | LOC saved | Risk | Perf note |
|---|-------|-------|------|-----------|------|-----------|
| S1 | Table-driven config validation + create handle_ctx after validation | init, 806–1421 | 7 minimal-rewrite | ~200 | low | init-only, off hot path |
| S2 | stats() via Py_BuildValue | 2724–2851 | 4 platform | ~85 | low | diagnostics path |
| S3 | Fold FASTCALL ts-parse + snapshot-query boilerplate (11 methods) | 2592–3052, 3368–3504 | 7 minimal-rewrite | ~120 | low | per-iterator setup, not per-record |
| S4 | extend() batch-commit epilogue helper (3 copies → 1, twin of tl_py_finish_tombstone_write) | 1970–2004, 2100–2123, 2137–2157 | 2 already-in-codebase | ~40 | medium | write path but identical codegen |
| S5 | Delete 27-member KW_ enum (2 used) | 806–836, 921, 925 | 1 dead code | ~26 | low | none |
| S6 | Delete redundant long-double clock overflow pre-check | 402–441 (410–414) | 1 dead code | ~8 | low | none |
| S7 | bulk_append arg parsing → PyArg_ParseTupleAndKeywords "OO|$O" | 2235–2294 | 4 platform | ~50 | medium (2 test regexes assert exact fragments) | one PyArg call per multi-thousand-record batch |
| S8 | Merge dual mode-switches in pytimelog_make_iter | 3293–3326 | 6 one-liner | ~14 | low | iterator creation only |
| S9 | __enter__ reuses start_maintenance helper | 3094–3107 vs 3147–3157 | 6 one-liner | ~8 | low | none |

**Total: ~550 LOC (honest range 450–550 after macro/helper glue).** None change the
public Python API; S7 changes two *error-message strings* asserted by tests (flagged).

## Prior-art leads (for later verification, not verdicts)

1. **FASTCALL kwnames parsing** (append 1705–1752, bulk_append 2235–2288) →
   CPython **Argument Clinic** (Tools/clinic, PSF license) or private
   `_PyArg_UnpackKeywords`. Fit notes: AC is a codegen step designed for the CPython
   tree; usable externally but adds tooling for exactly two methods; the private API is
   disqualified for shipped wheels. Expected: reject for append (hot path already
   optimal), moot for bulk_append if S7 lands.
2. **Nested dict construction** (stats, 2751–2847) → `Py_BuildValue` — platform,
   in-tree, zero new deps. Strong fit (this is S2).
3. **Kwarg conversion/validation** (init, 1116–1396) → `PyArg` `O&` converter
   functions with a `{name,kind,dest}` descriptor — platform alternative to the
   X-macro table; equal capability, slightly more glue to preserve exact messages.
4. **Refcounted contexts / lifetime pinning** (81–170, 500–672) → Concurrency Kit
   (`ck_pr`, BSD) or liburcu (`urcu/ref.h`, LGPL — license fails outright). Fit notes:
   CK's MSVC story is partial, LGPL is disqualified, and both would wrap ~60 lines of
   already-TSan-validated C11 atomics. Expected: reject.
5. **Monotonic/wall clock scaling** (402–441) — already uses C11 `timespec_get`
   (stdlib); the only alternative inside CPython (`_PyTime_*`) is private. Already at
   the right rung.

## Explicit NO-and-NO (earns its keep)

| Machinery | Where | Why prior art / simplification loses |
|---|---|---|
| append() hand-rolled vectorcall parse | 1705–1777 | Hot path; METH_FASTCALL fold measured −23.7% append; PyArg needs METH_VARARGS packing; `_PyArg_UnpackKeywords` is private |
| Snapshot pin protocol (`tl_py_acquire/release_snapshot_pinned`) | 621–672 | TOCTOU-hardened close-vs-pin window; already the shared helper for 6+ sites; documented release ordering (663–666) is load-bearing |
| Two-phase close (`pytimelog_close_no_raise`) | 1453–1571 | Every branch annotates a specific race (pins under lock 1483–1496, ctx detach under lock 1502–1510, core_lock kept until dealloc 1559–1569) |
| tp_traverse trylock | 526–538, 1652–1669 | Free-threaded stop-the-world GC deadlock if traverse parks; under-report is documented sound |
| `tl_py_core_call_strict` vs `_best_effort` | 556–600 | Must distinguish closed-ESTATE (raise) from core ESTATE; best_effort's conflation is required by busy_policy="flush" (462) |
| Double closed check (CHECK_CLOSED + tl_py_lock_checked) | e.g. 1803+1812 | Deliberate unlocked fast-fail + authoritative locked re-check; removing either is a perf or correctness loss |
| `tl_py_buffer_fmt_is_native_i64` | 2201–2226 | No public CPython API validates buffer format strings; tri-state powers endian-specific error |
| Dual ts coercers (`fast_i64` vs `coerce_ts`) | 324–387 | Documented distinct contracts (facade parity vs "L" parity); unifying = public exception-behavior change |
| `kwarg_was_provided` (vs NaN sentinel) | 281–298 | NaN sentinel silently converts explicit `float('nan')` from ValueError to "unset" — API behavior change |
| `_mostly_ordered_default` GetAttrString | 2431–2460 | Layering smell but contract-tested (test_bulk_append.py:230); alternative is an internal API change |
| Count-precompute stays GIL-attached | 3328–3336 | Measured 461× ingest collapse when detaching; comment is the receipt |
| Two distinct TS_MAX treatments in make_iter switches | 3293–3326 | SINCE-unbounded vs RANGE-bounded differ by exactly one record at TS_MAX (half-open invariant) — merge the switches (S8) but never derive one from the other |

## Test-coverage notes

- S1/S5: config error *types* covered by C binding tests (`test_py_timelog.c`
  ASSERT_EXCEPTION Overflow/ValueError) and Python tests grep-confirmed to assert the
  exact strings ("must be 0-4294967295", "Cannot specify both", "too large for this
  platform") — the macro rewrite must and can preserve them verbatim.
- S2: stats keys asserted in Python facade tests; a Py_BuildValue typo fails loudly.
- S3/S8: iterator boundary behavior covered by C tests (range t1>t2 ValueError at
  test_py_timelog.c:1258–1269) and facade tests.
- S4: `test_append_contract.py` + ASan/LSan CI leg cover the EBUSY/rollback contract.
- S6: the deleted branch is untestable without a post-2262 system clock; the surviving
  integer guards keep the same protection.
- S7: requires relaxing two regexes in `test_bulk_append.py:217–219`.
