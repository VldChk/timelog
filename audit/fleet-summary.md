# Claude Fleet — Structured Summaries (extracted from workflow journal)

## bindings-infra (2685 LOC reviewed)

### Simplifications
- **Replace vsnprintf raisers with PyErr_FormatV** [platform] ~35 LOC, risk=low
  - where: py_errors.c:137-204
  - Both Fmt raisers hand-roll a 512-byte vsnprintf buffer and duplicate their body (varargs can't be forwarded). PyErr_FormatV collapses both to wrappers around one va_list helper; all call-site specifiers (%s, %llu, literals) are in PyUnicode_FromFormat's set. Kills the 512-byte truncation; keep 2-line empty-format fallback.
  - perf: error paths only; zero hot-path impact. One test asserts truncation (test_py_errors.c:372) and needs updating.
- **Delete module reload-rollback machinery** [does-not-need-to-exist] ~170 LOC, risk=medium
  - where: module.c:195-257, 278-347 + initialized flag + 5 failpoints
  - Export snapshot/restore and state-validity predicates only matter when importlib.reload() of the C extension fails mid-export; first-import failure discards the module wholesale. CPython's own stdlib extensions (_sqlite3, _ssl) do no export rollback. Keep the 9-line idempotent re-exec; keep remove-exports-on-error.
  - perf: import-time only. Also deletes ~400 LOC of tests that test the machinery itself; maintainer built this deliberately - judgment call flagged, not a defect.
- **Delete by-construction error-pair validation** [does-not-need-to-exist] ~35 LOC, risk=low
  - where: py_errors.c:18-39, 52-61, 75-79
  - Validates that busy subclasses error and both are exception classes - guaranteed because busy is created with error as base (line 69) and state is written only by this function, cleared pairwise by TlPy_ClearErrors. Unreachable error path; tests never seed invalid state.
  - perf: import-time only.
- **Delete dead TlPy_ModuleMatchesTimelogDef** [does-not-need-to-exist] ~7 LOC, risk=low
  - where: module.c:517-520, py_module_state.h:41
  - Public function with zero callers repo-wide (src, tests, python).
  - perf: none
- **Merge managed_export_names into one export table** [minimal-rewrite] ~15 LOC, risk=low
  - where: module.c:40-51 vs 351-365
  - Same 7 names listed twice, lock-stepped only by count; restore keys off one array while add keys off the other - silent order-drift hazard. One static {name, state-offset, failpoint} table serves export/remove/snapshot/restore.
  - perf: import-time only; covered by extension_exports_expected_names test.
- **Delete never-read ts field from drop nodes** [does-not-need-to-exist] ~4 LOC, risk=low
  - where: py_handle.h:90, py_handle.c:699
  - 'Timestamp for debugging/metrics' is written once and read nowhere. Saves 8 bytes/node and one store per dropped record on the on_drop path.
  - perf: small strict win on the compaction drop path.
- **Micro deletions: dead store, empty m_free, stale include, C11 #error guards, orphaned comment** [does-not-need-to-exist] ~26 LOC, risk=low
  - where: py_handle.c:313-316, 29, 79-96, 410-421; module.c:172-175
  - list_tail=NULL dead store (never read after); timelog_free empty stub (m_free may be NULL); string.h included 'for memset' with no memset; stdatomic.h include already enforces C11; duplicated doc comment block.
  - perf: none

### Prior-art leads
- **live-handle open-addressing multiset**: khash (klib, MIT), Verstable (MIT), stb_ds (MIT/PD), CC (MIT)
  - fit: POOR FIT despite being the classic candidate: table mechanics are textbook, but the load-bearing part is the concurrency contract no generic table has - atomic per-entry EMPTY/FULL/TOMBSTONE publication (py_handle.c:48-61), stale-table chain for lock-free tp_traverse (71-76), traverse_readers gates. Exists because of the v1.2 free-threaded stop-the-world GC deadlock (1005-1011); adopting khash means forking its entry layout, saving nothing. PyMutex integration weighed honestly per instructions: verdict NO.
- **lock-free MPSC retired stack**: Concurrency Kit ck_stack (BSD-2), liburcu (LGPL - license fail)
  - fit: ~25 hand-rolled lines; the one subtle choice (ACQ_REL CAS for TSan/C++20 release-sequence safety, py_handle.c:243-248) is deliberate and not guaranteed by stock libraries; CK's MSVC support is weak. A dependency for 25 lines fails the laziness test. NO.
- **printf-style exception raising**: PyErr_FormatV (CPython, platform)
  - fit: GOOD FIT - adopted as the S2 simplification; covers all current format specifiers, removes buffer/truncation code.
- **pointer hash mix**: hash-prospector / lowbias32 constants (already what it is)
  - fit: py_handle.c:169-179 already uses Wellons prospector constants (0xed5ad4bb/0xac4c1b51); 10 lines, nothing to import. NO.
- **CPU yield shim**: core/src/internal/tl_sync.c:267,591 (same platform switch, rung-2 duplicate)
  - fit: Sharing would export a core-internal tl__ symbol to the binding for 6 lines - inverts public-API layering. Named per rung-2 rule, rejected.
- **multi-phase module init pattern**: CPython stdlib idiom (_sqlite3/_ssl module_exec)
  - fit: The platform idiom is linear create-and-add with Py_CLEAR on failure and no export rollback; the delta between that and module.c is exactly the S4-deletion candidate.

### No-and-no
- **lock-free tp_traverse + traverse_readers double gate (py_handle.c:295-330, 993-1079)**: tp_traverse must never park or malloc during free-threaded stop-the-world GC - a frozen thread can hold live_lock or the libc arena lock forever (documented v1.2 production deadlock). The second seq_cst gate closes a real check-then-act window; any simplification reintroduces the deadlock class.
- **pin_lock around atomic pins counter (py_handle.c:607-651)**: Serializes the pins 0->1 transition against a drainer that observed zero and is about to claim retired objects - the exact TOCTOU family hostile review exists to catch. Held for a few instructions, per snapshot acquire not per record; off hot path.
- **retired_tables chain / never-free-resized-tables (py_handle.c:68-76, 224-227)**: Cheapest correct answer to lock-free readers on stale tables; memory bounded by doubling schedule. Library alternatives (RCU/hazard pointers) are heavier and liburcu is LGPL.
- **drain_batch_limit + suffix re-push (py_handle.c:287-292)**: Not a speculative knob: user-configurable from Python (py_timelog.c:1075-1085), documented, and covered by test_py_maint_b5.c batch tests.
- **retired_queue_len underflow clamp (py_handle.c:1096-1098)**: Looks like impossible-state defense but is reachable: retired_count increments AFTER the push (702-705), so a racing drain can transiently make drained > retired.
- **tl_py_mutex_t / critical-section compat shims (py_compat.h:54-107, 175-203)**: Forced by the Python 3.12 floor (PyMutex is 3.13+); deletable only when 3.12 support drops.
- **drain_guard atomic_flag (py_handle.c:359-377)**: Reentrancy guard against __del__-driven recursive drains; one flag is the minimal correct form.
- **test-only tl_py_handle_ctx_init + heap_allocated flag (py_handle.c:427-483)**: Production uses only ctx_new, but folding init away saves ~12 LOC while forcing heap+decref rewrites across ~30 C-test sites that legitimately benefit from stack contexts. Not worth the churn - recorded to prevent re-litigation.

---

## bindings-timelog (3866 LOC reviewed)

### Simplifications
- **Table-driven config validation + create handle_ctx after validation** [minimal-rewrite] ~200 LOC, risk=low
  - where: py_timelog.c:806-1421 (blocks 1116-1396; hctx created early at 1085 forcing ~28 drop_handle_ctx error-path calls)
  - Three X-macro APPLY_* helpers (size_t/u32/ts shapes) replace 20 stamped 9-15 line validation blocks preserving messages byte-for-byte; moving tl_py_handle_ctx_new to just before tl_open (nothing in 1085-1397 uses it) deletes every drop-on-error call.
  - perf: tp_init only; off all hot paths
- **stats() via Py_BuildValue** [platform] ~85 LOC, risk=low
  - where: py_timelog.c:2724-2851
  - One Py_BuildValue("{s:{s:K,...},...}") call replaces 3 local macros, 5 PyDict_New, and two 6-way XDECREF error ladders; CPython handles allocation and failure cleanup internally.
  - perf: diagnostics path, not hot
- **Fold FASTCALL ts-parse + snapshot-query boilerplate across 11 methods** [minimal-rewrite] ~120 LOC, risk=low
  - where: py_timelog.c:2592-3052, 3368-3504 (min_ts/max_ts identical modulo fn; next_ts/prev_ts identical; since/until/equal/point/delete_before share 14-line parse prefix; range/delete_range share 2-arg variant)
  - One tl_py_parse_ts_args helper + two snapshot-query helpers (0-arg and 1-arg core fn) collapse the repeated NARGS-check/fast_i64/validate/acquire-pinned/release/EOF-to-None choreography.
  - perf: per-iterator-creation setup, not per-record iteration
- **extend() batch-commit epilogue helper (3 copies to 1)** [already-in-this-codebase] ~40 LOC, risk=medium
  - where: py_timelog.c:1970-2004, 2100-2123, 2137-2157; precedent tl_py_finish_tombstone_write at 2570-2590
  - The OK/EBUSY note_insert + busy-policy + drain/decref epilogue is stamped 3x; the file already factored the identical twin for tombstone writes. Centralizes the EBUSY-is-committed contract in one place.
  - perf: write path but identical generated code; covered by test_append_contract.py + ASan
- **Delete 27-member KW_ enum (2 members used)** [does-not-need-to-exist] ~26 LOC, risk=low
  - where: py_timelog.c:806-836; only KW_DELETE_DEBT_THRESHOLD (921) and KW_ADAPTIVE_ALPHA (925) referenced
  - Replace 30-line enum with two named index constants plus a kwlist-order comment.
  - perf: none
- **bulk_append arg parsing via PyArg_ParseTupleAndKeywords** [platform] ~50 LOC, risk=medium
  - where: py_timelog.c:2235-2294
  - METH_VARARGS|METH_KEYWORDS with "OO|$O:bulk_append" deletes the ~60-line hand-rolled kwnames loop; per-call packing is amortized over multi-thousand-record batches. CAVEAT: test_bulk_append.py:217-219 asserts 'unexpected keyword'/'multiple values' fragments that PyArg words differently - two test regexes must be relaxed.
  - perf: one tuple/dict pack per bulk call; provably off hot path
- **Merge dual mode-switches in pytimelog_make_iter** [one-liner] ~14 LOC, risk=low
  - where: py_timelog.c:3293-3300 and 3307-3326
  - Single switch sets range_t1/range_t2/count_t1/count_t2/count_unbounded; keep the fields distinct (SINCE-unbounded vs RANGE-bounded differ by one record at TS_MAX per half-open invariant).
  - perf: iterator creation only
- **Delete redundant long-double clock overflow pre-check** [does-not-need-to-exist] ~8 LOC, risk=low
  - where: py_timelog.c:410-414 in tl_py_now_ts
  - The long-double bound check is fully subsumed by the exact integer overflow guards at 420-431 (integer division truncation makes them complete for sec*1e9+nsec).
  - perf: none
- **__enter__ reuses start_maintenance body** [one-liner] ~8 LOC, risk=low
  - where: py_timelog.c:3147-3157 duplicates 3094-3107
  - Shared static helper for the lock/tl_maint_start/check sequence.
  - perf: none

### Prior-art leads
- **FASTCALL+kwnames keyword parsing (append/bulk_append)**: CPython Argument Clinic (Tools/clinic, PSF license), _PyArg_UnpackKeywords (private CPython API)
  - fit: AC is a codegen step designed for the CPython tree; adoptable but heavy tooling for 2 methods. Private API disqualified for shipped wheels. append() must stay hand-rolled (hot path, -23.7% measured from FASTCALL fold); bulk_append moot if PyArg swap (S7) lands.
- **Nested Python dict construction (stats)**: Py_BuildValue (CPython C-API)
  - fit: Perfect fit: in-platform, zero deps, internal error cleanup. This is finding S2.
- **Kwarg conversion+range validation (tp_init)**: PyArg O& converter functions (CPython C-API), X-macro table idiom (technique, no dep)
  - fit: O& converters run only when arg provided (natural unset handling); need a {name,kind,dest} descriptor via void* to preserve exact error messages. X-macro version is the lower-risk equivalent and is the primary recommendation (S1).
- **Refcounted context / lifetime pinning**: Concurrency Kit (BSD), liburcu urcu/ref.h (LGPL)
  - fit: Reject-shaped: liburcu fails MIT-compat (LGPL); CK's MSVC coverage is partial; both would wrap ~60 lines of already TSan-validated C11 atomics with the documented acq_rel decrement idiom. No win.
- **Wall-clock auto-timestamp scaling**: C11 timespec_get (already used)
  - fit: Already at the right rung; CPython's _PyTime_* alternatives are private API.

### No-and-no
- **append() hand-rolled vectorcall parsing (1705-1777)**: Hot path: METH_FASTCALL fold measured -23.7% append latency; PyArg alternatives force METH_VARARGS packing per call; _PyArg_UnpackKeywords is private API.
- **Snapshot pin protocol tl_py_acquire/release_snapshot_pinned (621-672)**: TOCTOU-hardened close-vs-pin window with documented release ordering (snapshot before engine_ctx decref, 663-666); already the shared factoring for 6+ call sites.
- **Two-phase close pytimelog_close_no_raise (1453-1571)**: Every branch annotates a specific race: pins sampled under core_lock (1483-1496), ctx detach under the same lock mutation paths use (1502-1510), core_lock deliberately kept alive until tp_dealloc to prevent UAF (1559-1569).
- **tp_traverse trylock (526-538, 1652-1669)**: Parking in traverse during a free-threaded stop-the-world GC deadlocks (holder may be a frozen thread); under-reporting one cycle only over-retains.
- **core_call_strict vs core_call_best_effort duality (556-600)**: Strict must raise on closed while best_effort's TL_ESTATE conflation is required by the busy_policy='flush' EBUSY path (462); merging loses the distinction.
- **Double closed check: CHECK_CLOSED then tl_py_lock_checked (e.g. 1803+1812)**: Unlocked atomic fast-fail plus authoritative locked re-check; removing either regresses perf or reopens the close race.
- **tl_py_buffer_fmt_is_native_i64 (2201-2226)**: No public CPython API validates buffer format strings; tri-state return powers the endianness-specific error message; struct-module round-trip would cost Python calls.
- **Dual ts coercers fast_i64 vs coerce_ts (324-387)**: Documented distinct contracts (facade _coerce_ts parity incl. bool rejection and teaching errors vs PyArg 'L' parity); unifying changes public exception behavior (api-change).
- **kwarg_was_provided instead of NaN sentinel (281-298)**: NaN sentinel would silently treat explicit float('nan') as unset instead of raising ValueError('must be finite') - observable API behavior change for 25 saved lines.
- **GetAttrString('_mostly_ordered_default') in bulk_append (2431-2460)**: Layering smell but a contract-tested behavior (test_bulk_append.py:230 resolution test); removing it is an internal API change between facade and C type.
- **Count precompute stays GIL-attached in make_iter (3328-3336)**: Detaching per iterator creation measured a 461x ingest collapse (GIL handoff starvation); the comment is the receipt.

---

## bindings-views (2021 LOC reviewed)

### Simplifications
- **Delete (or finally test) TimelogIter.view()** [does-not-need-to-exist] ~30 LOC, risk=medium, API-CHANGE
  - where: py_iter.c:456-481,489-490; README.md:164
  - view() has zero tests, zero docs/python-api.md coverage, zero facade/lab/benchmark callers; sole reference is one README bullet. range_t1/t2 fields stay (repr uses them).
  - perf: off hot path entirely
- **Replace custom PyPageSpanObjectsViewIter with CPython PySeqIter fallback** [platform] ~140 LOC, risk=medium, API-CHANGE
  - where: py_span_objects.c:169-279,375,393-411; py_module_state.h:25,65; module.c:90-93; py_compat.h:185-202
  - Removing the Py_tp_iter slot makes iter(view) use PySeqIter over the existing sq_item with identical semantics (IndexError->StopIteration, ValueError propagates); also kills the now-dead TL_PY_OBJ_LOCK2 macros, a module-state slot, a registration row, and a failpoint. Type name of iter(view) changes (test_subinterpreters.py:201 asserts it).
  - perf: swaps a 2-object CS per item for one CS + one extra C dispatch; wash-to-win on FT, object-materialization path not hot
- **Delete unreachable h==NULL and decode-NULL defensive branches** [does-not-need-to-exist] ~40 LOC, risk=low
  - where: py_span.c:360-372; py_span_objects.c:128-129,136-138,150-161,225-234,246-253,309-310,325-328,341-347
  - Core always sets view->h (tl_pagespan_iter.c:457); detach nulls h only together with closed=1 in one CS; handle decode is a cast of an encode of a never-NULL PyObject*. Both error families are unreachable and have zero test coverage.
  - perf: removes a branch from per-item decode paths; strictly >= 0
- **Delete speculative remaining_valid field** [does-not-need-to-exist] ~18 LOC, risk=low
  - where: py_iter.h:96-103; py_iter.c:273,428-439,528-530; py_timelog.c:3289,3357
  - Header admits it exists for a hypothetical future init change; every constructed iterator has it 1 (count failure destroys the object), so the RuntimeError __len__ branch and bare repr branch are unreachable and untested.
- **Drop kind="segment" one-value parameter (lead)** [does-not-need-to-exist] ~25 LOC, risk=medium, API-CHANGE
  - where: py_span_iter.c:98-102; py_timelog.c:3524-3536,3547; python/timelog/__init__.py:635-648; docs/python-api.md:160
  - Validation-only kwarg whose sole job is rejecting everything except its default, threaded through four layers; documented public API so needs a deprecation story - flagged loudly, lead not recommendation.
- **Collapse duplicate closed pre-check between PageSpan.objects() and ObjectsView factory** [one-liner] ~12 LOC, risk=low
  - where: py_span.c:356-372 vs py_span_objects.c:29-42
  - Factory re-validates type+closed for its single caller which just checked closed under the same CS discipline; neither check is safety-load-bearing (all view accessors revalidate under CS), one fail-early check suffices.
- **Test failpoint stubs -> #define NULL** [one-liner] ~10 LOC, risk=low
  - where: py_iter.c:72-82,303,333-334,397-398
  - Non-test builds compile always-0 stub functions passed by pointer per row; defining the names to NULL folds the hook check at compile time by construction.
  - perf: guarantees zero per-row cost instead of relying on IPA constant propagation
- **py_span.c boilerplate compression (redundant getter pre-check, ts-getter macro, shared __enter__)** [already-in-this-codebase] ~40 LOC, risk=low
  - where: py_span.c:454-471,473-508,332-336; py_iter.c:348-352; py_span_iter.c:351-355; py_compat.h idioms section
  - get_timestamps pre-check raises the byte-identical ValueError that getbuffer already raises (own comment concedes it); start/end_ts getters are identical modulo field and mirror the existing TL_PY_DEFINE_CLOSED_GETTER idiom; three verbatim __enter__ bodies collapse to one shared inline.
- **PyPageSpan_FromView defensive checks -> asserts** [does-not-need-to-exist] ~15 LOC, risk=low
  - where: py_span.c:35-54
  - NULL/type checks guard a single internal caller whose inputs are guaranteed by the core iter_next contract; asserts express the contract at zero release cost (keep the StateFromObject lookup).
- **Finish migration to TL_PY_PRESERVE_EXC_* macro** [already-in-this-codebase] ~12 LOC, risk=low
  - where: py_span.c:151-154; py_iter.c:165-180; py_span_iter.c:68-69,83,234-237
  - Four sites hand-roll deprecated-since-3.12 PyErr_Fetch/Restore while py_module_state.h:30-33 already defines the modern PyErr_GetRaisedException wrapper used everywhere else in the binding.

### Prior-art leads
- **Lazy sequence iteration over an indexable view**: CPython PySeqIter (automatic fallback when sq_item present and tp_iter absent)
  - fit: Exact semantic match: getitem already raises IndexError past-end (->StopIteration) and ValueError on closed (propagates). Platform code, FT/TSan story is CPython's. Caveats: iter type name observable (one subinterpreter test asserts it); FT index races become benign-unsequenced, consistent with documented not-thread-safe contract.
- **Zero-copy numeric array exposure with lifetime pinning**: CPython buffer protocol (already adopted)
  - fit: Current exporter IS the platform-idiomatic solution; PyMemoryView_FromMemory lacks exporter pinning and would break the BufferError-on-close contract (CLAUDE.md rule 16). No external C library applies; keep as-is.
- **CPython extension-type boilerplate generation**: CPython Argument Clinic, nanobind/pybind11
  - fit: All fail hard constraints: Clinic unsupported out-of-tree; nanobind/pybind11 are C++ (violates pure C17 + MSVC /WX). Right answer is the codebase's existing local macro idioms (TL_PY_GC_DEALLOC, TL_PY_DEFINE_CLOSED_GETTER) extended per finding F8.
- **Exception-state preservation across cleanup DECREFs**: PyErr_GetRaisedException/SetRaisedException (3.12+, platform)
  - fit: Already wrapped in-codebase as TL_PY_PRESERVE_EXC_BEGIN/END; finding F10 just finishes the migration at four straggler sites.

### No-and-no
- **Triplicated detach-under-CS / release-outside-CS choreography across the three closeable types**: Same shape but different payloads (5 resources vs 2) and release orders; the pattern IS the hard invariant 'no Py_DECREF/hook under any internal lock'. Genericizing needs void*-array or macro gymnastics that obscure TSan/lab-validated code paths - duplication is cheaper than the wrong abstraction.
- **Custom buffer exporter with exports counter (py_span.c:217-304)**: Required to implement cannot-close-while-exported -> BufferError (CLAUDE.md binding rule 16) and the security rule that h[] never gets a numeric buffer; no platform shortcut pins the exporter.
- **err-code-under-CS then raise-outside-CS verbosity**: Direct consequence of the no-Python-C-API-under-internal-locks invariant; table-driving the code->exception map saves ~10 lines and costs greppability.
- **next_batch preallocate-n + closed fast-path (py_iter.c:374-413)**: Fast-path prevents allocating a user-controlled n-slot list on a closed iterator; preallocate+trim beats append loops for the common full batch - this is the documented perf feature amortizing Python->C overhead.
- **Holding the per-object CS across tl_iter_next / tl_pagespan_iter_next**: Deliberate documented carve-out (py_compat.h:141-145) closing the close-vs-next UAF window; 'simplifying' to snapshot-then-call reintroduces the TOCTOU class the v1.3 hostile reviews caught.
- **copy_timestamps vs ObjectsView.copy skeleton similarity**: Different pinned pointers, per-element ops, and error sets in different TUs; a shared helper needs an indirect call in an O(n) loop or a macro - cost exceeds the ~25-line benefit.
- **32-bit overflow guard in getbuffer (py_span.c:238-241)**: Conditionally compiled only where reachable (SIZE_MAX <= UINT32_MAX); 4 lines guarding a real 32-bit wheel target overflow.
- **Longhand PyType_Spec/slots per type + last_ts alias**: CPython convention; registration is already table-driven with a static assert (module.c:73-101); X-macroing specs obscures per-type slot differences for ~0 net LOC. last_ts is a documented public alias costing 4 lines.

---

## build-test-harness (3100 LOC reviewed)

### Simplifications
- **Extract shared binding-test harness header** [already-in-this-codebase] ~750 LOC, risk=low
  - where: bindings/cpython/tests/*.c (8 files)
  - All 8 binding test files duplicate tlpy_set_pythonhome (33 identical lines each), Py init/finalize, TEST/ASSERT/ASSERT_EQ macro sets, counters, and main() epilogue; module-bootstrap helpers duplicated in >=5 files. Extract py_test_harness.h (~150 lines) using the superset macros (test_py_timelog's PyErr_Occurred-checking TEST).
  - perf: test-only, zero engine exposure
- **Collapse 8 CMake test-target stanzas into a function** [minimal-rewrite] ~270 LOC, risk=low
  - where: bindings/cpython/CMakeLists.txt:264-648
  - timelog_add_py_test(NAME SOURCES... DEFS...) helper replaces ~390 lines of copy-pasted add_executable/include/link/compile-options blocks (the 14-line MSVC/else options block repeats 9 times verbatim) with ~110 lines.
  - perf: build config only; CI builds Linux+Windows MSVC every PR
- **Replace run_core_test_groups.py with native CTest per-group tests** [platform] ~220 LOC, risk=medium
  - where: demo/ci/run_core_test_groups.py + CMakeLists.txt:280
  - Register 13 add_test entries in a foreach with ENVIRONMENT TL_TEST_GROUPS=<g> (~10 lines); CTest natively gives per-group pass/fail/timing, -j parallelism (script runs groups serially), and --output-junit. Kills the group-name list duplicated between the script and test_main.c. Workflows' JSON/MD step-summary needs a slim converter or ctest-native output.
  - perf: CI gets faster (parallel groups); no engine impact
- **Dedupe workflows via workflow_call + composite setup action** [platform] ~270 LOC, risk=medium
  - where: .github/workflows/ (compat pr/main pair, setup preambles, tee-to-log blocks)
  - compat pr/main pair differs by only 27 of 257 lines (reusable workflow saves ~100); the checkout/setup-python/pip/configure/build-e2e preamble repeats in >=8 jobs (composite action saves ~100-120); the set+e/tee/PIPESTATUS .log-artifact idiom x12 duplicates Actions native log capture (~80, weakest claim). The 17-file count itself is fine: 1836 LOC, distinct concerns.
  - perf: CI only
- **Replace hand-rolled pytest result protocol** [platform] ~140 LOC, risk=medium
  - where: demo/ci/run_compat_baseline.py:92-189
  - The embedded pytest-plugin-in-a-subprocess + TL-SUMMARY stdout parsing reimplements pytest --junitxml (built-in) or pytest-json-report (MIT). Leg config and markdown writer stay.
  - perf: CI only; summary schema consumed by 3 workflows needs coordinated change
- **Delete byte-identical duplicate filter function** [one-liner] ~30 LOC, risk=low
  - where: core/tests/test_main.c:134-196
  - test_group_enabled and test_name_enabled are byte-identical comma-list matchers (only the parameter name differs); delete one, call the survivor from both sites.
  - perf: none
- **Delete standalone bindings build mode** [does-not-need-to-exist] ~50 LOC, risk=medium
  - where: bindings/cpython/CMakeLists.txt:24-67,189-190,239
  - Library-hunting across 4 hardcoded build dirs for a prebuilt timelog.lib; nothing uses it (scikit-build-core builds from root per pyproject cmake.source-dir='.', all CI configures -S ., no docs). Also removes the option() declarations duplicated against the root CMakeLists.
  - perf: possible historical Windows dev convenience; confirm with maintainer
- **Delete Windows-Clang support blocks** [does-not-need-to-exist] ~35 LOC, risk=medium
  - where: CMakeLists.txt:262-267,364-390
  - Manual CRT lib injection and 27-line clang ASan-DLL PATH discovery exist only for Clang-on-Windows non-MSVC driver; no CI leg, doc, or workflow builds that config (grep-verified), windows-latest uses MSVC.
  - perf: confirm no local Windows-Clang workflow before deleting
- **Table-driven main() dispatch** [minimal-rewrite] ~55 LOC, risk=low
  - where: core/tests/test_main.c:253-357
  - 15 copies of if(test_group_enabled(...)){printf(banner); run_X_tests();} collapse to a static {group,banner,fn} table + loop; gives group-name single source of truth for the CTest migration.
  - perf: none
- **Delete dead harness machinery** [does-not-need-to-exist] ~15 LOC, risk=low
  - where: core/tests/test_harness.h:14,23-24,46-52
  - TEST_MAX_NAME_LEN never used; test_entry_t/TEST_ENTRY registration-table design never instantiated; test_result_t.file/.line written but never read (report prints name+message only; file:line already printed inline at failure).
  - perf: none
- **Delete never-enabled facade-tests CMake option** [does-not-need-to-exist] ~14 LOC, risk=low
  - where: CMakeLists.txt:20-21,350-360
  - TIMELOG_BUILD_PY_FACADE_TESTS defaults OFF, every CI configure passes OFF explicitly, nothing sets ON, and the target is a 10-line wrapper around the pytest command docs already tell users to run directly.
  - perf: none
- **Store only failures in harness results array** [minimal-rewrite] ~10 LOC, risk=low
  - where: core/tests/test_harness.h:29-35 + test_main.c:39,48
  - results[1000] (~544KB BSS) records every pass and fail with unbounded results[count++] (no cap check); Debug suite already at ~497 of 1000 — silent overflow when suites grow. Only the failure recap reads the array; passes need only a counter.
  - perf: removes a latent framework buffer overflow

### Prior-art leads
- **C unit test framework (asserts + registration + runner + filtering)**: sheredom/utest.h (Unlicense, single header, auto-registration via linker sections, GCC/Clang/MSVC, --filter), silentbicycle/greatest (ISC, single header, still manual registration), nemequ/munit (MIT, PRNG/params/timing, manual registration arrays), ThrowTheSwitch/Unity (MIT, but auto-registration needs Ruby scripts — poor fit)
  - fit: utest.h is the only one that fixes the real structural cost (505 manual RUN_TEST lines + drift hazard + helper-assert limitation) but vendors ~1.3k lines and forces a mechanical diff across 17.5k test LOC; must verify MSVC /experimental:c11atomics + section attributes, and TEST_ASSERT_STATUS/tl_strerror becomes a thin custom macro on top. Current harness passes all hard constraints today and registration counts verified drift-free — lead for when the suite outgrows it, not debt now.
- **per-group core test orchestration in CI**: CTest native: set_tests_properties ENVIRONMENT, ctest -j, --output-junit
  - fit: Platform rung, no third-party code; direct replacement for the 298-line serial Python runner, adds group parallelism; JSON/MD step-summary shape consumed by 2 workflows needs a small converter or acceptance of JUnit output.
- **pytest result capture for compat-baseline legs**: pytest --junitxml (built-in), pytest-json-report (MIT, pure Python)
  - fit: Replaces the hand-rolled plugin-in-subprocess + TL-SUMMARY stdout protocol; pytest-json-report emits the same counts/nodeids the script builds by hand; adds one line to requirements-test.txt.
- **duplicated workflow pr/main pairs and setup preambles**: GitHub workflow_call reusable workflows, GitHub composite actions
  - fit: Platform features; compat pair (27-line diff of 257) is the clean win; workflow_call has permissions/secrets sharp edges and reduces grep-ability — apply selectively.
- **embedded-Python bootstrap in binding C tests (PYTHONHOME env dance)**: CPython PyConfig / Py_InitializeFromConfig (config.home, >=3.8)
  - fit: Platform-provided supported API for what tlpy_set_pythonhome does with env vars; fold into the shared harness header extraction rather than keeping 8 copies of the env hack.

### No-and-no
- **Wholesale replacement of the core C test harness with a mature framework**: 538 LOC, 3-compiler -Werror-clean, zero deps, sanitizer-transparent, and the domain assert TEST_ASSERT_STATUS prints tl_strerror on both sides; any swap is a 17.5k-LOC mechanical diff churning the exact ~497-test safety net the project relies on. Fix F1-F3 in place instead.
- **Sanitizer flag plumbing loop in root CMakeLists (100-133)**: The per-build-type loop exists so the FT-TSan CI leg (RelWithDebInfo, sanitizers.yml:224-233) cannot silently produce an uninstrumented build — explicitly commented at lines 114-118; load-bearing for the TSan-clean-on-3.14t constraint.
- **TL_TEST_GROUPS/TL_TEST_FILTER env-var filtering**: ~30 LOC (post-dedup) enabling the group-split CI strategy and targeted local runs; env var beats argv parsing because ctest owns argv.
- **17 separate workflow files as an architecture**: LOC-weighed honestly: 1836 total, median ~104, each with distinct triggers/concurrency/failure-ownership (sanitizers, packaging, codeql, coverage, releases, automation); merging beyond the compat pair and setup preamble trades grep-ability for YAML indirection.
- **check_layer_a_static.py and check_docs_consistency.py**: Bespoke checkers enforcing project-specific invariants (heap-type isolation contract, docs/symbol drift) with no generic tool at equal precision; size proportionate to the job.
- **timelog_copy_python_runtime Windows DLL staging (bindings CMakeLists:114-157)**: Windows CI genuinely runs embedded-Python test executables that need the runtime DLL beside them; the fallback chain handles setup-python layouts. Baroque but exercised.
- **TIMELOG_BUILD_SHARED option**: Never ON in CI but a legitimate ~14-line public build option for a C library incl. export-macro wiring; deletion is API-adjacent for trivial savings. Caveat noted: untested in CI.
- **bench_search_lower_bound target (EXCLUDE_FROM_ALL)**: Supports the v1.3 branchless-search perf work; perf is the product, and the target costs 7 lines and never builds by default.

---

## cross-cutting (3100 LOC reviewed)

### Simplifications
- **Delete ~30 production-dead internal functions** [does-not-need-to-exist] ~500 LOC, risk=low
  - where: tl_recvec.c/h, tl_page.c/h, tl_heap.c/h, tl_intervals.c/h, tl_alloc.c/h, tl_memtable.c/h, tl_memrun.c/h, tl_locks.h, tl_seqlock.h, tl_range.h, tl_window.h, tl_point.h, tl_snapshot.h, tl_memview.h, tl_ooorun.h
  - 13 functions have zero references anywhere (incl. tl__reallocarray, tl_memtable_insert_tombstone_unbounded, tl_lock_is_held, 3 tl_range predicates); ~17 more exist only for tests (recvec search/insert/shrink block, tl_page_upper_bound, tl_heap_build, tl_intervals union/covered_span/contains, tl_memrun_create, tl_memtable_seal adapter, seqlock reader side). Move 3 high-fan-in helpers into the test tree; delete the rest with their tests. Caveat: seqlock reader side is a documented future-lock-free hook - flag to author.
  - perf: Dead code; zero runtime impact. One full CI matrix run to catch #if-guarded callers grep missed.
- **Merge tl_memrun_iter + tl_active_iter into one tl_delta_iter** [minimal-rewrite] ~180 LOC, risk=medium
  - where: core/src/query/tl_memrun_iter.{c,h}, tl_active_iter.{c,h}, tl_plan.h:45-49, tl_merge_iter.c:23-80,144
  - Structs are field-identical modulo unused-after-init back-pointer; next/seek/destroy bodies are token-identical wrappers over tl_submerge. One type with two init functions collapses 4 files to 2 and shrinks kmerge dispatch from 3-way to 2-way (has_variable_watermark becomes a plan-set bool).
  - perf: Hot read path but codegen-identical or marginally better (shorter dispatch chain); fully covered by existing query/merge/OOO tests.
- **Delegate tl_page_lower_bound to tl_ts_lower_bound in tl_search.h** [already-in-this-codebase] ~25 LOC, risk=low
  - where: core/src/storage/tl_page.c:141-176, core/src/internal/tl_search.h
  - tl_page.c re-implements the tl_search.h branchless dual-mode algorithm for int64 arrays. Add TL_INLINE tl_ts_lower_bound beside tl_record_lower_bound and delegate, giving the measured-perf-win TL_LOWER_BOUND_BRANCHLESS_MAX gate a single tuning point.
  - perf: Codegen-identical: page fn is already an extern call; helper is TL_INLINE like the existing record variant. Differential tests test_search_branchless.c + bench keep working unchanged.
- **Use tl__grow_capacity at the two straggler grow sites** [already-in-this-codebase] ~12 LOC, risk=low
  - where: core/src/delta/tl_memtable.c:243-251, core/src/delta/tl_flush.c:250
  - Both hand-roll the overflow-safe doubling that tl_alloc.h:150 tl__grow_capacity provides and 4 other modules already use; memtable site is a verbatim reimplementation.
  - perf: Cold paths (dropped-record collection during flush/seal, not append). Behavior-identical for reachable inputs.

### Prior-art leads
- **Portable threads/mutex/cond shim (tl_sync, 806 LOC)**: tinycthread (zlib), C11 <threads.h>
  - fit: C11 threads dead on MSVC. tinycthread passes license/compiler gates and is vendorable, but lacks tl_mutex_is_held debug tracking, thread naming, ms-granular timedwait; effectively unmaintained; existing shim is TSan-proven on 3.14t. Weak lead - glue eats most of the win.
- **Binary min-heap for k-way merge (tl_heap, 334 LOC)**: klib ksort.h heap functions (MIT), CCAN heap (BSD-MIT)
  - fit: Poor fit: 32-byte entries with (ts, tie_break_key) composite order plus replace_top op the hot merge relies on (tl_merge_iter.c:235); generic heaps cost comparator indirection or pop+push double-sift. Zero-perf-regression rule kills it.
- **Open-addressing live-handle hash (py_handle.c)**: klib khash.h (MIT)
  - fit: License/compiler/allocator gates pass, but the custom table chains resized-out arrays on retired_tables (py_handle.c:69-73,225) so lock-free readers survive rehash under free-threading; khash frees on resize. Poor fit.
- **Lock-free MPSC Treiber stack (py_handle.c retired queue, ~60 LOC)**: Concurrency Kit ck_stack (BSD-2)
  - fit: CK MSVC coverage partial; CK fences are exactly what the project's GCC-TSan notes warn about. Vendoring a dependency for 60 already-portable C11-atomic lines is a net loss.
- **Dynamic arrays (tl_recvec/tl_seqvec)**: klib kvec.h (MIT), stb_ds.h (MIT/public domain)
  - fit: kvec calls libc realloc directly (breaks the tl__* allocator seam, a CLAUDE.md hard rule); stb_ds allocator override is global not per-context; growth logic is already one shared helper. Poor fit.
- **Seq-tagged canonical interval set (tl_intervals, 1122 LOC)**: 
  - fit: No mature C library carries per-interval seq metadata with an amortized-O(1) cursor over canonical half-open sets; domain-specific, earns its keep.
- **Sorting at seal/manifest**: stdlib qsort (already used), klib ks_introsort (MIT) - perf idea only
  - fit: Already at stdlib rung (tl_recvec.c:204, tl_manifest.c:554). Comparator devirtualization via ks_introsort would be a perf experiment, not a simplification.

### No-and-no
- **goto-cleanup pattern (58 sites, 9 label spellings)**: C17 has no defer; single-exit goto is the documented house idiom (CLAUDE.md Cleanup Pattern); label variance is per-function-local and costs zero LOC.
- **Per-type refcount acquire/release wrappers**: The TSan-sensitive memory-ordering core is already centralized in tl_refcount.h (acq_rel chosen because GCC TSan cannot see fences, per header comment); a generator macro saves ~60 LOC but degrades stack traces and grep-ability where the project debugged TSan false positives.
- **K-merge tagged-union if-chain dispatch (tl_merge_iter.c:23-80)**: A vtable would add lines plus an indirect call per record on the hottest read path; 3-way if over an enum is the minimal C encoding and MSVC-warning-managed.
- **tl_submerge vs tl_kmerge structural echo**: Sources differ fundamentally (infallible flat arrays vs fallible iterators with H-16 error latching); unifying requires per-record callback indirection - a perf regression on the merge hot path.
- **Absence of a TL_CHECK propagation macro (173 explicit sites)**: Roughly half the sites need cleanup or status remapping anyway; the style is perfectly uniform; hiding control flow trades ~170 LOC for reviewability the project's culture explicitly values.
- **tl_atomic.h dual C11/MSVC-Interlocked shim (389 LOC)**: MSVC has no reliable C-mode stdatomic under /WX; this IS the platform layer and no candidate library is simpler than the problem.
- **Seqlock writer side, header guards, memcpy loops, tl_count.h variants, py_handle hash growth**: Writer side enforces invariant #6 publication windows; headers already minimal/uniform; the 2 copy loops are strided transposes; count variants differ by seq/watermark visibility semantics; hash growth is load-factor-driven, a different algorithm from tl__grow_capacity.

---

## delta (4089 LOC reviewed)

### Simplifications
- **Delete production-dead two-way merge iterator** [does-not-need-to-exist] ~140 LOC, risk=low
  - where: tl_flush.h:39-116, tl_flush.c:5-66, tl_defs.h:109
  - tl_flush_build k-way merges via tl_heap; tl_merge_iter_* has zero production callers (tests only). Also fix stale comment in query/tl_merge_iter.h:16-17 claiming flush uses it.
  - perf: dead code; zero perf impact
- **Replace 3 hand-rolled growable dropped-record arrays with tl_recvec_t** [already-in-this-codebase] ~90 LOC, risk=medium
  - where: tl_memtable.c:229-313, tl_flush.c:249-269, seal_ex/flush_ooo_head triple-pointer plumbing
  - memtable_collect_drop, memtable_reserve_drops, and flush.c's inline doubling block all reimplement tl_recvec (geometric reserve, push, take-with-tl__free ownership — the exact documented out_dropped contract). Collapses signatures to one tl_recvec_t*.
  - perf: drop collection only runs on tombstone-covered records at seal/flush; off append/query hot paths
- **Kill copy-and-sort drop pre-count (double sort of OOO head)** [minimal-rewrite] ~60 LOC, risk=medium
  - where: tl_memtable.c:344-396 (memtable_count_tomb_drops), call sites :417-437, :897-937
  - Seal sorts the OOO head twice (once to count drops, once to collect); opportunistic gate does the same per chunk when tombstones exist. Replace exact ooo count with head_len upper-bound reserve (still before mutation, preserving failure-atomicity) and a conservative O(H) no-alloc overlap gate; delete the 53-line sorting counter.
  - perf: PERF-POSITIVE: removes one O(H log H) sort + copy per seal and per gated chunk flush; cost is bounded drop-buffer over-allocation only when tombstones exist
- **Retire test-only constructors tl_memrun_create and tl_ooorunset_create** [does-not-need-to-exist] ~70 LOC, risk=low
  - where: tl_memrun.c:94-133 + tl_memrun.h:90-119; tl_ooorun.c:76-127 + tl_ooorun.h:63-66
  - Zero production callers (production uses alloc+init and append); tests already wrap memrun_create in test_memrun_create. ooorunset_create duplicates append's pin loop — deleting it resolves the duplication.
  - perf: cold, test-only code
- **Extract bounds-merge tail shared by five update_bounds_from_* functions** [minimal-rewrite] ~45 LOC, risk=low
  - where: tl_memview.c:21-139
  - Five verbatim copies of the same 10-line min/max/has_data merge block; one bounds_include() helper reduces each function to its source-specific min/max computation.
  - perf: capture-time only; byte-identical behavior
- **Delete six dead inline accessors** [does-not-need-to-exist] ~40 LOC, risk=low
  - where: tl_ooorun.h:96-98; tl_memview.h:207-209, 218-234; tl_memrun.h:214-216, 243-245
  - tl_ooorun_gen, tl_memview_shared_epoch, tl_memview_min_ts/max_ts, tl_memrun_is_empty, tl_memrun_tombs_data have zero uses anywhere including tests.
  - perf: none
- **Collapse copy_intervals + copy_seqs into one dup helper** [minimal-rewrite] ~33 LOC, risk=low
  - where: tl_memview.c:141-195
  - Two byte-identical overflow-check/malloc/memcpy functions (pattern also exists as tl_records_copy in internal/tl_records.h); one generic dup_array covers both.
  - perf: memcpy-bound either way
- **Unify copy_sealed_memruns retry loop with its duplicated fallback body** [minimal-rewrite] ~25 LOC, risk=medium
  - where: tl_memview.c:205-305
  - Fallback duplicates the loop body ~35 lines; loop attempt<=max_retries with alloc_under_lock flag on the final pass keeps the H-09 protocol exactly (test hooks cover both branches).
  - perf: protocol-preserving; same lock hold profile
- **Fold tl_memtable_seal into seal_ex (test-only shim)** [one-liner] ~25 LOC, risk=low
  - where: tl_memtable.c:1059-1062, tl_memtable.h:243-259
  - Production calls only seal_ex (tl_timelog.c:551,607,1138); the plain wrapper serves only ~10 test call sites which can pass NULL,NULL.
  - perf: none
- **Trivia: redundant memset after TL_NEW(calloc), unguarded total_len add vs existing saturating helper, unreachable defensive branches in sealed_index, verbose dec bookkeeping** [one-liner] ~20 LOC, risk=low
  - where: tl_memview.c:473, tl_memview.c:355-356, tl_memtable.h:335-341, tl_memtable.c:506-527
  - Four micro-cleanups; the memview.c:355 fix also upgrades an unguarded addition to the saturating tl_memtable_ooo_total_len helper. H-07 formula itself untouched.
  - perf: none
- **TL_APPEND_HINT_MOSTLY_IN_ORDER is a fully-plumbed no-op knob** [does-not-need-to-exist] ~15 LOC, risk=high, API-CHANGE
  - where: tl_memtable.c:655 ((void)flags), timelog.h:386-387, py_timelog.c:1955/2036/2507
  - The hint is plumbed from Python through the public C API and discarded; fast path is chosen purely by mandatory full sortedness verification. Public API — removal only at a major version; minimum action is documenting it as currently ignored.
  - perf: no runtime effect today

### Prior-art leads
- **Growable typed record array (drop buffers)**: in-repo tl_recvec_t (preferred, rung 2), klib kvec.h (MIT), stb_ds.h (MIT/public-domain)
  - fit: In-repo wins outright: geometric growth, overflow guards, tl__realloc seam, take() matching the documented out_dropped ownership contract. External libs would add a vendored file for a solved problem.
- **Refcounted immutable objects (memrun/ooorun/runset/shared memview)**: Concurrency Kit ck_pr (BSD-2), liburcu urcu/ref.h (LGPL — FAILS license gate)
  - fit: In-house TL_REFCOUNT_ACQUIRE/RELEASE already centralizes the idiom and encodes the GCC-TSan acq_rel-on-decrement workaround (tl_memrun.h:141-153); adoption would re-import the false-positive problem the project engineered around. No adoption.
- **K-way merge min-heap (flush build)**: klib ksort.h heap macros (MIT), CCAN heap (BSD/MIT mix)
  - fit: Heap entries carry (ts, tie_break_key, watermark, handle, iter) for deterministic equal-ts ordering; comparator-pointer heaps add indirect calls in the per-record merge loop, and tl_heap is already shared with the query read path. No adoption.
- **Fixed-capacity ring buffer (sealed queue)**: CCAN ringbuf, ck_ring (BSD-2)
  - fit: Mutex-protected FIFO of a handful of pointers whose index arithmetic is documented invariant H-07; ck_ring is lock-free MPMC — a different concurrency contract and new TSan surface on 3.14t. No adoption.
- **Epoch-validated optimistic capture (H-09)**: ck_sequence seqlock (BSD-2)
  - fit: Protocol is mutex + epoch counter with locked fallback per documented invariant H-09; seqlock restructures publication and saves no lines. No adoption; see S9 for the in-place dedup instead.
- **Co-sorting records with parallel seq array**: qsort_r/qsort_s (platform — GNU/BSD/MSVC signature divergence), klib ksort.h (MIT)
  - fit: qsort_r portability is a minefield under -Werror//WX across GCC/Clang/MSVC; zipping into AoS for ksort would double copies on the seal path. In-house tl_recvec_sort_with_seqs justified; benchmark ksort only if seal sort ever profiles hot.

### No-and-no
- **H-07 subtraction-based ring index (tl_memtable.h:328-348)**: Documented critical invariant #7; the overflow-safe formula is the point. Only two provably unreachable defensive branches are fat.
- **H-09 two-phase memview capture with retry+fallback (tl_memview.c:205-305)**: Always-locked allocation would be ~40 LOC simpler but violates documented invariant #8 (bounded memtable_mu hold under snapshot-heavy reads); non-finding by rule.
- **Full O(n) batch sortedness verification (tl_memtable.c:637-647)**: Header contract mandates full check, no sampling (tl_memtable.h:158-160); a wrong fast path violates sortedness invariant #3 feeding the 4.3x bulk path.
- **Parallel recvec+seqvec (SoA) instead of combined (record,seq) struct**: Seqs are dropped at memrun creation (tl_memtable.c:1001-1004) and flush merges raw tl_record_t arrays into segments; AoS would bloat every downstream memcpy/merge on the hot path by 50%.
- **Reserve-then-push pairing in tl_memtable_insert (tl_memtable.c:582-593)**: Guarantees record and seq arrays cannot diverge if the second allocation fails — preserves the len-equality invariant checked by tl_memtable_validate.
- **Double queue-full check in seal (tl_memtable.c:881-886, 1025-1031)**: Pre-check avoids building a memrun destined for the bin; publish-time re-check is mandatory because flushers pop concurrently under memtable_mu.
- **tl_memrun_alloc/init two-phase (tl_memrun.c:135-148)**: Shell allocated before active arrays are detached keeps ENOMEM on the retryable side of the point of no return (seal failure-atomicity contract).
- **Per-run refcount on tl_ooorun_t in addition to runset refcount**: After tl_ooorunset_append, old and new sets share the same run objects (tl_ooorun.c:157-170) while old sets stay pinned by live memviews/memruns.
- **Debug validators (~330 LOC across memtable/memrun/memview)**: Behind TL_DEBUG, zero release cost, exercised by ASan CI; they are the safety net this audit leans on.
- **Opportunistic-flush no-drop-sink gate decision (tl_memtable.c:431-435 comment)**: Never silently dropping records without a callback sink is correct and must survive S4; only the exact copy+sort counting implementation is fat.

---

## internal-datastructures (2413 LOC reviewed)

### Simplifications
- **Delete 6 production-dead tl_recvec functions** [does-not-need-to-exist] ~190 LOC, risk=low
  - where: core/src/internal/tl_recvec.c:75-102,150-175,181-205,266-336 + header decls
  - tl_recvec_insert, shrink_to_fit, sort(+cmp_record_ts), lower_bound, upper_bound, range_bounds have zero production callers (tests/bench only; tl_recvec_sort has zero callers anywhere). Production search uses tl_record_lower_bound on raw arrays; no upper_bound consumer exists since half-open [t1,t2) uses lower_bound for both ends. Branchless-search coverage survives via test_search_branchless.c legs targeting tl_record_lower_bound/tl_page_*.
  - perf: zero perf impact; none on any executed path
- **Delete tl_heap_build (Floyd heapify)** [does-not-need-to-exist] ~40 LOC, risk=low
  - where: core/src/internal/tl_heap.c:188-217, tl_heap.h:79-87
  - O(n) heapify with tests-only callers; all 4 production merge constructors use reserve+push (K is a handful of sources, and push interleaves with per-source EOF/error handling).
  - perf: zero perf impact
- **Delete 5 dead tl_intervals entry points + fix stale covered_span doc** [does-not-need-to-exist] ~85 LOC, risk=low
  - where: core/src/internal/tl_intervals.c:380-396,576-588,679-702
  - tl_intervals_max_seq and imm_contains have zero callers anywhere; contains, union (mutable wrapper), covered_span are tests-only. covered_span header doc falsely claims compaction delete-debt uses it (replaced by H-18 cursor sweep). Tests rewrite trivially against imm_max_seq/union_imm.
  - perf: zero perf impact
- **Delete 3 zero-caller tl_range.h predicates** [does-not-need-to-exist] ~25 LOC, risk=low
  - where: core/src/internal/tl_range.h:23-30,55-57
  - tl_ts_before_end, tl_ts_at_or_past_end, tl_range_overlap_start have zero callers anywhere (overlap_start is also just TL_MAX). Only tl_range_overlaps and tl_range_is_empty are live.
- **Unreachable defensive branches in intervals coalesce/append -> assert** [does-not-need-to-exist] ~12 LOC, risk=medium
  - where: core/src/internal/tl_intervals.c:112-122,416-418
  - Coalesce's unbounded-prev handling and append's unbounded-prev guard handle states that invariant 5 (unbounded interval always last) plus every internal producer make impossible (split keeps unbounded last, insert walk asserts !end_unbounded at line 245, union appends unbounded only in terminal branch). Replace with TL_ASSERT so debug builds stay loud.
  - perf: removes a branch from coalesce inner loop; neutral-to-positive
- **Fallback: tl_recvec_lower_bound delegates to tl_record_lower_bound** [already-in-this-codebase] ~25 LOC, risk=low
  - where: core/src/internal/tl_recvec.c:266-295 vs tl_search.h:14-43
  - Line-for-line duplicate of the branchless+gated lower_bound in tl_search.h; only relevant if the deletion in S1 is rejected — replace body with one-line delegation to eliminate a divergence hazard.
  - perf: identical codegen after inlining

### Prior-art leads
- **binary min-heap for k-way merge**: klib ksort.h heap macros (MIT), PostgreSQL binaryheap.c (BSD-like), CCAN heap (license varies per module)
  - fit: Poor fit: generic void*+comparator-pointer heaps cost an indirect call per sift comparison on the query-merge hot path; current heap inlines a 2-field compare on a concrete struct and has replace_top. Zero-regression rule makes adoption a net loss.
- **dynamic array (recvec/seqvec)**: klib kvec.h (MIT), stb_ds.h (MIT/public domain), CCAN darray
  - fit: Fails the allocator seam: engine needs per-instance tl_alloc_ctx_t*; kvec/stb_ds route through global malloc/realloc macros. Growth policy already centralized in tl__grow_capacity, so a library saves little; macro containers add MSVC /WX and debuggability friction.
- **coalescing interval map with max-value aggregation (tombstones)**: Boost ICL interval_map (C++ - disqualified), cgranges (MIT, static overlap index only)
  - fit: No mature pure-C library implements canonical half-open coalescing interval sets with per-interval max_seq merge and unbounded ends; C candidates are static query indexes without coalescing insert. Keep hand-rolled.
- **co-sorting parallel arrays (sort_with_seqs)**: qsort_r/qsort_s (non-portable: 3 incompatible signatures glibc/BSD/MSVC), klib ksort.h typed sort (MIT)
  - fit: stdlib variants fail the GCC+Clang+MSVC gate. klib ksort would be a seal-path speedup (inlined comparator vs qsort indirection), an optimization lead rather than a simplification; current pair-array approach is the smallest portable answer.
- **branchless lower_bound**: stdlib bsearch (insufficient: cannot return first->= position)
  - fit: No stdlib/library equivalent; implementation is the standard branchless pattern, a measured shipped perf win, diff-tested against a branchy oracle across the size gate.

### No-and-no
- **hand-rolled typed min-heap**: Query-merge hot path: inlined concrete-type comparator + replace_top (tl_merge_iter.c:235); generic prior art adds an indirect call per sift comparison, violating zero-perf-regression.
- **tl_intervals insert machinery (split+walk+coalesce)**: Evaluated rewriting insert as union-with-singleton to delete ~100 LOC; rejected because the compaction residual builder (tl_compaction.c:899-943) does T ascending inserts — current is O(T) total, union-per-insert is O(T^2) full copies inside compaction.
- **end_unbounded flag instead of sentinel end**: TL_TS_MAX is a legal timestamp; [t1,+inf) must contain it and half-open [t1,TL_TS_MAX) cannot — the flag is the only representation respecting invariant #4.
- **tl_seqvec kept separate from tl_recvec (no generic macro vector)**: Growth/overflow logic already shared via tl_alloc.h helpers; folding ~100 net LOC into a TL_VEC_DEFINE macro costs per-type debuggability and MSVC /WX friction on stable, fully-tested leaf code.
- **SIZE_MAX length guards in push/insert paths**: Load-bearing, not paranoia: without them reserve(len+1) wraps to 0, returns TL_OK, and the write at data[SIZE_MAX] is UB (tl_recvec.c:111, tl_heap.c:141, tl_seqvec.c:77).
- **dual branchless/branchy lower_bound with size gate**: Gate encodes the measured cmov-vs-branch-prediction crossover (TL_LOWER_BOUND_BRANCHLESS_MAX, tl_defs.h:50); single constant, differential tests sweep both sides; a shipped perf win.
- **cursor-based tombstone filtering**: Amortized O(1) per record over sorted scans (tl_intervals.h:226-232), the exact pattern CLAUDE.md mandates over per-record O(log T) probes; multiply used on the read path.
- **tl_records_copy redundant overflow pre-check**: Removing 3 lines would change the returned status TL_EOVERFLOW->TL_ENOMEM (caller-visible); not worth a behavior change.

---

## internal-platform (2825 LOC reviewed)

### Simplifications
- **Delete dead sync-shim surface (thread_set_name, mutex_is_held, thread_self_id, cond_broadcast)** [does-not-need-to-exist] ~130 LOC, risk=low
  - where: tl_sync.c:5-13,86-90,212-264,393-397,518-521,558-588; tl_sync.h:69-72,151-164
  - Four debug/diagnostic functions with zero callers in src AND tests, including a 50-line Windows GetProcAddress/InitOnce thread-naming mechanism nothing invokes; the maint worker never names its thread.
  - perf: all dead or debug-only; zero runtime impact
- **Delete dead atomic ops: ptr family, stores, fence, unused convenience macros** [does-not-need-to-exist] ~120 LOC, risk=low
  - where: tl_atomic.h:46,63-65,76-91,122-133,151-209,255-275,286-322,350-361,372-387
  - tl_atomic_ptr + 5 ptr ops, all store ops, tl_atomic_fence, and inc/dec_u32/dec_u64/store-release macros have zero production callers across 3 backends; the stated tl_atomic_ptr use case (manifest pointer, tl_atomic.h:39) never materialized — manifest is writer_mu-protected.
  - perf: dead code; deleting also removes shim self-tests in test_internal_sync.c
- **Delete unreachable GCC/Clang __atomic fallback backend, replace with #error** [does-not-need-to-exist] ~85 LOC, risk=low
  - where: tl_atomic.h:277-363
  - Third backend reachable only if GCC/Clang in C17 mode defines __STDC_NO_ATOMICS__ — self-described 'unlikely with C17 but defensive'; no supported/CI toolchain compiles it, so it is an untested code shape.
  - perf: unreachable on all supported toolchains
- **Replace MSVC Interlocked backend with C11 stdatomic via /experimental:c11atomics** [platform] ~135 LOC, risk=medium
  - where: tl_atomic.h:137-275 + CMakeLists.txt MSVC flags
  - Windows wheels ALREADY compile the binding with /experimental:c11atomics (bindings/cpython/CMakeLists.txt:210 + 8 more); enabling it for the core deletes the 140-line Interlocked backend and makes MSVC relaxed loads plain movs instead of full lock-cmpxchg RMWs (tl_atomic.h:177-190).
  - perf: strict MSVC perf improvement (loads stop being RMWs); GCC/Clang unchanged; risk is the 'experimental' flag status on standalone core builds (VS2022 17.5+ floor, /WX interaction)
- **Seqlock: delete dead reader half (Tier A); flag write-only seqlock for maintainer decision (Tier B)** [does-not-need-to-exist] ~35 LOC, risk=low
  - where: tl_seqlock.h:86-113 (Tier A); whole file + view_seq field + 7 call sites (Tier B)
  - Production never reads the seqlock counter — tl_seqlock_read/is_even/validate/current are test-only because snapshot capture holds writer_mu (CLAUDE.md invariant 6); the whole seqlock is a documented 'hook for future lock-free optimisations'. Tier A (delete 4 reader helpers) is free; Tier B (~170 LOC) contradicts documented invariant 6/pitfall 2 wording and needs a maintainer call.
  - perf: Tier A zero impact; Tier B would remove 2 atomic RMWs per publication (flush/compaction frequency, off hot path) at high doc/invariant churn cost
- **Slim allocator debug accounting: dead getters, dead peak tracking, misleading total, CAS-loop-to-fetch_sub** [does-not-need-to-exist] ~55 LOC, risk=low
  - where: tl_alloc.c:71-83,95-110,139-154,190-254; tl_alloc.h:194-198
  - tl__alloc_get_total/count/peak have zero callers; peak_allocated feeds only the dead getter via two duplicated CAS-max loops; total_allocated is never decremented on free so the leak warning reports cumulative-bytes-ever as leaked bytes (misleading); tl__free's 10-line CAS underflow loop collapses to fetch_sub + TL_VERIFY like TL_REFCOUNT_RELEASE.
  - perf: all TL_DEBUG-only; release allocation path untouched
- **Delete dead tl__reallocarray and reuse tl__alloc_would_overflow in tl__calloc** [already-in-this-codebase] ~26 LOC, risk=low
  - where: tl_alloc.c:122-126,173-188; tl_alloc.h:98-104,127-129
  - tl__reallocarray has zero callers (growth sites use tl__grow_capacity + tl__realloc directly); tl__calloc hand-rolls the division round-trip overflow check four lines away from the tl__alloc_would_overflow helper the same header exports.
  - perf: identical codegen for the calloc guard; reallocarray is dead
- **Delete dead lock-tracker queries and TL_TRYLOCK** [does-not-need-to-exist] ~40 LOC, risk=low
  - where: tl_locks.h:81-96,109-115,122,126-127
  - tl_lock_is_held, tl_lock_highest_held, and TL_TRYLOCK (both debug and release variants) have zero callers; the tracker core (TL_LOCK/TL_UNLOCK, 43 sites) stays.
  - perf: dead code
- **Delete dead defs/platform macros (ALIGN_UP, IS_ALIGNED, ARRAY_SIZE, PREFETCH, LIKELY, RESTRICT, NOINLINE, CACHE_ALIGNED, UNREACHABLE, LOG_STATIC)** [does-not-need-to-exist] ~40 LOC, risk=medium
  - where: tl_defs.h:141-147; tl_platform.h:41-57(partial),69,156-170; tl_log.h:73-79; tl_seqlock.h:31-33
  - Grep-verified zero users for all of these across src, bindings, and tests (TL_ALIGN_UP survives only in comments); TL_CACHE_LINE_SIZE fallback in tl_seqlock.h duplicates tl_platform.h. Caveat: check the in-flight feat/perf-wins worktree before deleting the hint macros.
  - perf: dead macros; medium risk only because uncommitted perf branches may reference the hint macros

### Prior-art leads
- **portable threads/mutex/condvar shim**: C11 <threads.h>, tinycthread (zlib), pthreads-win32 (LGPL)
  - fit: All fail: Apple SDK has never shipped <threads.h> (macOS wheels are built); glibc needs 2.28+ vs manylinux floor; MSVC needs 17.8+; cnd_timedwait is TIME_UTC-only which regresses the deliberately monotonic condvar waits (tl_sync.c:294-309); pthreads-win32 fails MIT-compat. Hand-rolled shim earns its keep.
- **atomics shim**: MSVC <stdatomic.h> via /experimental:c11atomics, Concurrency Kit ck_pr (BSD-2), portable-snippets psnip/atomic (CC0)
  - fit: MSVC C11 atomics is the strong lead — Windows wheels already require the flag for the binding, so adopting it core-side deletes the whole Interlocked backend and improves MSVC load codegen. ck_pr fails the MSVC gate (gcc/clang asm oriented); psnip is an unmaintained lateral move.
- **overflow-checked int64 arithmetic**: __builtin_{add,sub,mul}_overflow (GCC/Clang), C23 <stdckdint.h>, Windows <intsafe.h>
  - fit: Builtins are single-instruction vs tl_mul_overflow_i64's divisions, but MSVC lacks signed-overflow builtins and stdckdint support there needs verification, so the hand-rolled code cannot be deleted — a builtin fast path adds lines (perf lead, not simplification). intsafe.h is unsigned-only. Call sites are compaction/window frequency, not per-record.
- **seqlock**: liburcu urcu/seqlock (LGPL), ck_sequence (BSD-2), Linux seqcount (GPL)
  - fit: liburcu and Linux fail the license gate; ck fails MSVC. In-tree seqlock is 114 correct LOC — the real question is existence (write-only in production), not implementation.
- **atomic refcount idiom**: ck_ref, folly/Boost intrusive refcount patterns
  - fit: Generic libraries do not preserve the project-specific constraint: acq_rel folded into the RMW because GCC TSan cannot see atomic_thread_fence (tl_refcount.h:8-14, maintainer TSan notes). 41 LOC in-tree beats any adoption.
- **lock-order verification**: Clang Thread Safety Analysis (-Wthread-safety annotations)
  - fit: Compile-time proofs but Clang-only — GCC/MSVC ignore the annotations, so it could complement but not replace the 60-line runtime tracker that must run on all three compilers in Debug CI.
- **C test framework / assert interception**: greatest (ISC), munit (MIT), Unity (MIT)
  - fit: In-tree RUN_TEST harness + pluggable assert hook (tl_platform.h:89-132) is tiny and amortized across ~485 tests; migration is churn with no deletion payoff in this unit.

### No-and-no
- **pthread/Win32 sync shim core (mutex, condvar, thread, monotonic clock)**: No stdlib replacement exists on the supported matrix (no macOS threads.h, glibc 2.28+ gap, MSVC 17.8+ gap) and CLOCK_MONOTONIC condvars are a correctness property threads.h cannot express (tl_sync.c:469-482 documents the wrong-clock failure modes); _beginthreadex over CreateThread is a CRT requirement.
- **TL_REFCOUNT_ACQUIRE CAS loop + acq_rel-in-RMW release**: CAS loop VERIFYs against resurrection-after-zero/overflow before publishing; folding acq_rel into the fetch_sub (no standalone fence) is mandatory for GCC TSan cleanliness on free-threaded 3.14t — 'simplifying' to fetch_add+fence reintroduces documented false positives.
- **TL_ASSERT->TL_ASSUME release semantics with separate TL_VERIFY tier**: Deliberate two-tier contract (tl_platform.h:71-154): internal invariants become optimizer hints in release, OS-primitive results keep always-on aborts (tl_sync.c:355-358); collapsing tiers either loses release perf or makes corrupted-lock states 'unreachable'.
- **debug lock-order tracker core (TL_LOCK/TL_UNLOCK, 43 sites)**: Runtime enforcement of the maint->flush->writer->memtable invariant on every Debug/ASan CI leg in ~55 LOC; no portable compile-time replacement (Clang TSA is Clang-only).
- **logging facility**: log_fn/log_level are public API (timelog.h:296-298); a bounded, level-gated, callback-safe two-stage vsnprintf formatter at 166 LOC is already the floor.
- **MSVC Interlocked-everything design (if the C11-atomics switch is rejected)**: seq_cst-via-Interlocked is the only safe non-C11 choice — the header correctly rejects volatile+_ReadWriteBarrier on ARM64 (tl_atomic.h:144-148); hand-rolling acquire/release Interlocked variants adds code and subtle ARM64 risk.
- **hand-rolled overflow math as the portable default**: MSVC has no signed-overflow builtins and stdckdint is not yet dependable there; implementations are branch-exact, unit-tested, and off the per-record hot path.
- **allocator vtable + inline context**: This IS the custom-allocator seam the adoption constraints require (timelog.h:199-206); inline storage avoids a per-allocation pointer chase.
- **tl__grow_capacity + tl__alloc_would_overflow + sleep/monotonic helpers**: Each has 2-3 real callers and is already the minimal form of its subproblem (overflow-safe doubling, EINTR-resuming nanosleep, monotonic ms clock); library adoption replaces them with dependencies, not deletions.

---

## maint (2423 LOC reviewed)

### Simplifications
- **tl__tombs_union_into duplicates shared tl_tombstones_add_intervals** [already-in-this-codebase] ~20 LOC, risk=low
  - where: core/src/maint/tl_compaction.c:180-201 (call sites :214,:993,:1004)
  - Identical temp-union-swap logic exists as tl_tombstones_add_intervals in internal/tl_tombstone_utils.h:13-63 (7 existing production callers); calling it with (TL_TS_MIN, 0, true) is byte-for-byte equivalent. Delete the local helper.
  - perf: off hot path (compaction); identical work modulo a trivial full-range filter loop
- **Deferred-drop array re-implements tl_recvec_t; tl__grow_array then collapses** [already-in-this-codebase] ~50 LOC, risk=low
  - where: core/src/maint/tl_compaction.c:734-810, tl_compaction.h:137-139
  - dropped_records/len/cap is a dynamic array of tl_record_t — exactly tl_recvec_t, which the SAME function already uses for window_records (:1140,:1218). Swap to recvec; tl__grow_array is then single-caller and its generic void**/zero_new machinery inlines into ~12 lines (zero_new is already unnecessary: ctx_destroy reads only [0,len)).
  - perf: identical amortized growth; off hot path
- **tl_compact_one retry loop: duplicated select+merge and a wasted final merge** [minimal-rewrite] ~15 LOC, risk=low
  - where: core/src/maint/tl_compaction.c:1396-1406 vs :1459-1472
  - Loop bottom re-selects and re-MERGES even after the final EBUSY publish, then discards the result (4 select+merge cycles for 3 publish attempts). Moving select/merge/publish to loop top removes the duplication AND the wasted full k-way merge; metrics semantics preserved. Edge delta: exhaustion always returns TL_EBUSY as the header contract states, instead of occasionally EOF/ENOMEM from the throwaway pass.
  - perf: strict perf WIN: eliminates one full k-way merge per retry-exhaustion episode; covered by cint_one_exhausts_retries
- **Drop the watermarks side-array in merge priming** [minimal-rewrite] ~22 LOC, risk=low
  - where: core/src/maint/tl_compaction.c:1067-1122,:1244
  - watermarks[] is only read while priming the heap; the value is tl_segment_applied_seq(seg), available in the same loops that init each iterator. Prime the heap there and delete the malloc, overflow check, and 3 free sites. Tie-break order unchanged.
  - perf: strict perf win: one fewer malloc/free per compaction
- **One-pass L1 selection (match the L0 style)** [minimal-rewrite] ~11 LOC, risk=low
  - where: core/src/maint/tl_compaction.c:469-498
  - Count-then-fill runs the overlap predicate twice per L1 segment; the sibling L0 path (:564-570) already allocates n upfront. Allocate n_l1 pointers, fill in one pass.
  - perf: neutral-to-better; transient 8 bytes per unselected L1 segment
- **tl__segment_estimate_bytes: two sat-arith helpers replace 45 longhand lines** [minimal-rewrite] ~22 LOC, risk=low
  - where: core/src/maint/tl_compaction.c:503-547
  - Five saturating adds + three saturating muls written out longhand collapse to sat_add/sat_mul_u64 one-liners (reusing tl__alloc_would_overflow for the size_t multiply case). Value only feeds the greedy byte cap, so saturation points are unobservable. C23 stdckdint.h is out (C17+MSVC).
  - perf: off hot path; identical results
- **Delete stale 'Background mode trigger coupling' doc block** [does-not-need-to-exist] ~14 LOC, risk=low
  - where: core/src/maint/tl_compaction.h:182-196
  - Block claims the worker only checks tl_compact_needed when flush work is pending and delete-debt cannot fire on idle wakes; tl_timelog.c:1791-1805 explicitly evaluates it on EVERY wake and documents removing the old gating (v1.3 lab finding). The same header's file comment (:46-53) already has the corrected text.
  - perf: docs only
- **tl_adaptive_wants_resize is dead production code** [does-not-need-to-exist] ~35 LOC, risk=low
  - where: core/src/maint/tl_adaptive.c:395-408, tl_adaptive.h:184-201
  - Zero production callers (repo grep: only test_adaptive_internal.c:629-681). Header claims 'Used by scheduler' — the worker consults tl_compact_needed only. It even takes maint_mu for no-GIL race-freedom on a function production never calls. Delete function, header block, 5 test cases.
  - perf: none (dead)
- **tl_flush_metrics_t.has_records is definitionally record_count>0** [one-liner] ~8 LOC, risk=low
  - where: core/src/maint/tl_adaptive.h:83; tl_adaptive.c:230; tl_timelog.c:1072
  - Sole producer sets it to (record_count > 0); sole consumer checks BOTH (!has_records || record_count == 0). Drop the field. Internal struct, no API impact; touches tl_timelog.c and 5 test initializers.
  - perf: none
- **isfinite + snap_to_quantum branch dedup + unreachable overflow guard** [stdlib] ~15 LOC, risk=low
  - where: core/src/maint/tl_adaptive.c:100,167-199,244,299-301,343
  - isnan(x)||isinf(x) -> !isfinite(x) (file already uses isfinite at :30); hoist the duplicated <=0/NaN/Inf/>=INT64_MAX/llround validation shared by both quantum branches; delete the :194-199 guard whose own comment proves it unreachable ('mathematically qid*q <= wi < INT64_MAX').
  - perf: policy code, off hot path; snap edge cases directly unit-tested
- **Residual tombstones as clip/clip_lower/union of existing primitives** [already-in-this-codebase] ~38 LOC, risk=medium
  - where: core/src/maint/tl_compaction.c:899-943
  - Residual = tombs minus [first_w_start,last_w_end). tl_intervals_clip (preserves max_seq, bounds unbounded — verified in tl_intervals.c) reproduces the before-portion; tl_intervals_clip_lower reproduces the after-portion incl. unbounded preservation; union_imm combines disjoint halves. Needs one guard for first_w_start==TL_TS_MIN. Do only if touching the function anyway.
  - perf: adds one transient tombs copy per compaction (off hot path); leans on cint_residual_* tests
- **FLAG: adaptive subsystem can effectively fire only once (pre-first-L1)** [does-not-need-to-exist] ~0 LOC, risk=high, API-CHANGE
  - where: core/src/maint/tl_adaptive.* (~660 LOC), tl_compaction.c:1383,1437-1439, timelog.h tl_adaptive_config_t, py_timelog.c:856-865
  - window_grid_frozen latches permanently on first L1 publish (never cleared; only other write at open), so EWMA/hysteresis/staleness/failure-backoff act only between warmup and the first record-producing compaction; failure_backoff_* knobs are near-unreachable, and density updates keep running forever feeding a computation that can never act. 10 public C knobs + 10 Python kwargs make removal an API change — flagged for maintainer scope decision, not actionable here. Free micro-win: gate flush-metrics capture on !window_grid_frozen.
  - perf: removal would eliminate per-flush metrics capture + maint_mu EWMA update on adaptive-enabled instances

### Prior-art leads
- **k-way merge min-heap (merge loop over internal tl_heap)**: klib ksort.h heap macros (MIT), CCAN heap module (BSD-MIT), loser-tree merge (textbook)
  - fit: Poor fit: in-repo tl_heap carries engine payload (tie_break_key, watermark, opaque iter), respects tl__malloc seam, and is shared with the query hot path where zero-regression bites; K is small so a loser tree buys nothing measurable. Expect keep.
- **interval-set union/clip/difference (residual tombstones, delete debt)**: Boost ICL (C++ — disqualified), generic C interval-tree libs (node-based, wrong shape), in-repo tl_intervals (rung 2)
  - fit: No pure-C17 MIT library handles a flat canonical interval set with max_seq payload + half-open + unbounded semantics; the real prior art is the repo's own tl_intervals primitives (see S11). Rung 2 beats rung 5.
- **checked/saturating integer arithmetic (segment byte estimate, window spans)**: C23 <stdckdint.h>, portable-snippets psnip_safe (CC0/MIT), GCC/Clang __builtin_*_overflow + MSVC intrinsics
  - fit: stdckdint is C23 and MSVC-late; project is C17 with /WX. Repo already has tl_sub_overflow_i64 and tl__alloc_would_overflow; extend in-repo helpers (two one-liners) rather than vendor.
- **EWMA-driven adaptive sizing control loop**: RocksDB dynamic level sizing (conceptual, Apache-2, C++), classic hysteresis/quantization control patterns
  - fit: No vendorable C library exists; the leverage is scope reduction (S12 flag), not adoption.
- **dynamic array growth (tl__grow_array, dropped records)**: klib kvec.h (MIT), stb_ds (public domain/MIT)
  - fit: In-repo tl_recvec + tl__grow_capacity already cover every use in this unit and respect the allocator seam; rung 2 beats rung 5.

### No-and-no
- **tl__compute_delete_debt cursor sweep (tl_compaction.c:204-332)**: H-18 mandates exactly this O(T+W) cursor structure over the repo's own interval type with max_seq/end_unbounded payloads, TL_MAX_DEBT_WINDOWS cap, and overflow-safe window math; no library does bucketized coverage over a foreign interval type in fewer than these ~60 core lines. Verified against a reference impl in cint_delete_debt_matches_reference.
- **two tombstone sets: tombs vs tombs_clipped (tl_compaction.h:94-107, .c:984-1050)**: Not duplication — one drives residual computation (unclipped, input-only, H-19), the other record filtering (global snapshot view, clipped); the header documents the concrete corruption from conflating them. Collapsing would be a correctness bug.
- **strict publish protocol (tl_compact_publish :1299-1359)**: Every line maps to invariant #6/H-17 or a documented race: off-lock build, pointer-equality base check, seqlock write window, pin-before-unlock for NDEBUG validation (:1338-1343). Already minimal.
- **deferred drop-callback queue firing only after publish (:1177-1188, :1415-1426)**: Binding safety contract: firing during merge lets user code free a payload still visible in the manifest if publish fails/retries (UAF/double-free, per header :129-137 and CLAUDE.md). The queue must exist; only its container changes (S2).
- **tl__l1_overlaps_window_range (:413-437)**: 10 lines whose comment carries the module's key subtlety (window bounds vs record bounds -> L1 non-overlap invariant, with worked example). A generic overlap helper erases documentation value for zero LOC gain.
- **four-phase select/merge/publish API split (tl_compaction.h:148-270)**: Single production caller, but the phase boundaries are load-bearing for the 1,031-line internal test suite (EBUSY injection between merge and publish, residual/watermark inspection). Not over-generalization.
- **greedy selection forward-progress asymmetry (:637-643)**: 'Caps apply only after the first segment' is the liveness guarantee when a single segment alone exceeds a cap; removing the asymmetry deadlocks compaction on oversized segments.
- **NDEBUG validators + adaptive NaN/Inf guards + volatile test failpoint**: Validators are cheap O(n) insurance for invariant #2 (release-mode checks live in the manifest builder per H-12/H-14); adaptive guards each map to the documented 'keep current window' stability rule (tl_adaptive.h:150-154); the failpoint (:20-29) is the simplest possible EBUSY injector.

---

## orchestrator-api (2958 LOC reviewed)

### Simplifications
- **Dead append hint: TL_APPEND_HINT_MOSTLY_IN_ORDER is a no-op by design** [does-not-need-to-exist] ~100 LOC, risk=medium, API-CHANGE
  - where: timelog.h:384-399 -> tl_memtable.c:655 ((void)flags); plumbed from Python mostly_ordered kwarg
  - Core discards flags and verifies sortedness itself (batch_is_sorted); test_delta_internal.c:757 asserts the hint must never be trusted, so it can never do anything. Entire mostly_ordered/mostly_ordered_default plumb in binding+facade feeds this no-op.
  - perf: Zero perf impact; hint is never read. Laziest middle path: document flag as reserved/ignored (0 LOC).
- **Shared write-path epilogue for the four write entrypoints** [minimal-rewrite] ~60 LOC, risk=medium
  - where: tl_timelog.c:634-799 (tl_append/tl_append_batch/tl_delete_range/tl_delete_before)
  - Lock/next_op_seq/insert/seal/unlock/signal/emit-drops/EBUSY-combine repeated 4x (659-673 and 706-720 are identical); a static tl__finish_write(tl, insert_st) collapses them with identical semantics.
  - perf: Static same-TU helper, inlined by GCC/Clang/MSVC; append hot path executes the same instructions. EBUSY contract heavily covered by existing tests.
- **ts-navigation quartet is two functions wearing four coats** [minimal-rewrite] ~55 LOC, risk=low
  - where: tl_timelog.c:1576-1706 (tl_min_ts/tl_max_ts/tl_next_ts/tl_prev_ts)
  - min/next = first-of-iter_since; max/prev = last-of-forward-scan; two static helpers collapse ~130 lines to ~70.
  - perf: Documented diagnostics (timelog.h:516), explicitly off hot path; 18 existing C test call sites.
- **handle_seal_with_backpressure: dead NULL-tolerant out-params + duplicated seal block** [does-not-need-to-exist] ~25 LOC, risk=low
  - where: tl_timelog.c:531-632 (NULL branches 536-539/560-565/616-621; duplicate seal attempt 551-567 vs 605-623)
  - All 4 callers pass non-NULL out-params so the else/free branches are dead; the seal-attempt block appears twice verbatim. Assert-mandatory params + a try_seal helper shrink ~100 lines to ~65.
  - perf: Static function, cold seal path; no hot-path effect.
- **tl_open/init_locks unwind ladders -> house goto-cleanup pattern** [minimal-rewrite] ~27 LOC, risk=low
  - where: tl_timelog.c:218-267 and 282-399
  - init_locks re-enumerates teardown in 5 progressively longer copies; tl_open repeats its teardown 4x. CLAUDE.md's own cleanup pattern (goto) halves it.
  - perf: Open-time cold path.
- **Delete or fold tl_count/tl_count_range (no non-test users)** [does-not-need-to-exist] ~50 LOC, risk=medium, API-CHANGE
  - where: timelog.h:490-494; tl_timelog.c:1526-1563; binding uses tl_snapshot_count_range only
  - Only consumer is test_functional.c. Option A (no api change): fold two near-identical bodies into one static helper (~15 LOC). Option B: delete from public API (~50 LOC, api-change).
  - perf: Off hot path entirely.
- **Delete tl_scan_range visitor API (no non-test users)** [does-not-need-to-exist] ~35 LOC, risk=medium, API-CHANGE
  - where: timelog.h:474-483; tl_timelog.c:1500-1522
  - Thin loop over tl_iter_range that only test_functional.c calls; any C caller writes it in 6 lines. Public-API deletion candidate.
  - perf: No perf relevance.
- **tl_iter_range empty-range special case duplicates plan short-circuit** [already-in-this-codebase] ~16 LOC, risk=low
  - where: tl_timelog.c:1350-1367 vs tl_plan.c:206-209 + tl_timelog.c:1307-1315
  - tl_plan_build already short-circuits t1>=t2 before any allocation and iter_create_internal already returns a done iterator; tl_iter_until proves the path works. Collapse to the same one-line delegation.
  - perf: Empty-range queries are not hot; added cost is one call that memsets and returns. Covered by test_functional.c:150.
- **flush_one_memrun re-inlines tl__emit_drop_callbacks twice** [already-in-this-codebase] ~14 LOC, risk=low
  - where: tl_timelog.c:999-1008 and 1019-1029 vs helper at 466-479
  - Both drop-emission loops are the helper's body verbatim; call it. Failure path must keep free-without-emit (publish contract), which the reshape preserves.
  - perf: Flush path, off hot append/query paths.
- **status_strings NULL-gapped table -> switch** [one-liner] ~10 LOC, risk=low
  - where: tl_timelog.c:65-90
  - 32-slot array with 24 NULL pads plus bounds/NULL checks plus a TL_EINTERNAL special case; an 8-case switch is shorter and cannot drift.
  - perf: tl_strerror is error-path only.
- **Untested TIMELOG_BUILD_SHARED configuration (tl_export.h)** [does-not-need-to-exist] ~30 LOC, risk=medium, API-CHANGE
  - where: tl_export.h:4-18; CMakeLists.txt:15,182-186,205-210; OFF in pyproject.toml:53 and all CI workflows
  - The TL_BUILD_SHARED branch is never compiled anywhere (wheels force false, no CI leg). Either add one CI leg or delete the option + TL_API tokens; deletion is lazier but forfeits DLL-embedder option value.
  - perf: TL_API expands to nothing in all real builds; zero runtime effect either way.
- **Delete TL_WORK_RESHAPE_L0 ('Reserved for future use') and unused TL_APPEND_HINT_MOSTLY_ORDER alias** [does-not-need-to-exist] ~2 LOC, risk=low, API-CHANGE
  - where: tl_timelog.c:1738; timelog.h:387 (alias has zero users repo-wide)
  - Two pure-YAGNI lines: a reserved enum bit nothing references and a public alias nothing (tests, docs, binding, benchmarks) uses.
  - perf: None.

### Prior-art leads
- **Background maintenance worker (thread + condvar + pending flags + exponential backoff), tl_timelog.c:1741-1883**: pthreadpool (BSD-2), Concurrency Kit primitives (BSD-2), liburcu workqueue (LGPL - fails license gate)
  - fit: Poor fit: the value is domain policy (flush-drain with compaction cut-in, heuristic re-check per wake, bools-under-mutex to close lost-wakeup TSan-cleanly), not plumbing; a generic pool provides none of it and adds a dependency where tl_sync already shims platforms. Expected verdict NO.
- **DLL export macro header (tl_export.h)**: CMake GenerateExportHeader (already in build)
  - fit: Would replace 20 hand-written lines with generated file + wheel include-path wiring - more machinery, not less. Moot if the untested shared-build option is deleted instead.
- **Enum-to-string mapping (tl_timelog.c:65-90)**: X-macro idiom (sqlite/CPython style, not a library)
  - fit: For 8 codes a plain switch is lazier than an X-macro table; no library justified.
- **Bounded optimistic-publish retry + exponential backoff (tl_timelog.c:808, 1015-1032, 1730-1731)**: none credible
  - fit: Retried unit is a manifest rebuild (domain logic); backoff is two constants and a clamp. Any dependency is net-negative LOC.

### No-and-no
- **Deferred signalling (request flush/compact only after TL_UNLOCK_WRITER, tl_timelog.c:664-666 etc.)**: Lock order maint_mu->flush_mu->writer_mu->memtable_mu forbids signalling under writer_mu; any 'inline' simplification deadlocks against the worker.
- **flush_publish three-phase pin/build/CAS with memrun pop inside the seqlock window (tl_timelog.c:838-905)**: Implements snapshot-consistency invariant 6: manifest swap and memrun pop must be observed atomically or readers double/zero-count records (comment 886-890). No shorter form preserves it.
- **Plain bools under maint_mu instead of atomic flags (tl_timelog_internal.h:119-127)**: The mutex doubles as the condvar predicate barrier; atomics reintroduce the lost-wakeup race and complicate TSan-cleanliness on 3.14t. Deliberate and documented (tl_timelog.c:1723-1725).
- **Three-state worker machine STOPPED/RUNNING/STOPPING (tl_timelog_internal.h:40-44)**: STOPPING exists to prevent double-join and double-spawn races; a bool re-opens both.
- **EBUSY remapping of seal failures (tl_timelog.c:573-579)**: Not error-swallowing: the write already committed, and surfacing ENOMEM would trigger caller rollback of a committed record, violating the EBUSY-means-accepted contract (binding rule 18).
- **tl_iter_equal + tl_iter_point both existing**: Streaming O(K)-memory vs eager O(M)-memory profiles; both wired through the binding. Fix is a doc sentence, not code deletion.
- **tl_stats skyline-based estimate walk (tl_timelog.c:2062-2118)**: O(pages+tombstones) instead of O(N) is the design point; each component arm uses a distinct short-circuiting counter, so no collapse is available.
- **handle_seal_with_backpressure dropping writer_mu around the wait (tl_timelog.c:585-599)**: Worker needs writer_mu to publish the flush that frees queue space; waiting while holding it livelocks. S-7 trims around this, never through it.
- **tl__next_op_seq UINT64_MAX guard (tl_timelog.c:484-486)**: Technically an impossible-state error path (~585 years at 1G ops/s), but it costs one perfectly-predicted branch; removal buys nothing measurable, so leave it.

---

## query (4791 LOC reviewed)

### Simplifications
- **tl_stats reimplements count; full-extent tl_count.h helpers are the range variants at [TL_TS_MIN,+inf)** [already-in-this-codebase] ~110 LOC, risk=low
  - where: core/src/query/tl_count.h:149-233; core/src/tl_timelog.c:2070-2118
  - tl__visible_records_in_segment/_in_memrun are provably identical to the _range variants called with an unbounded query (intersection with [TL_TS_MIN,+inf) yields the source extent unchanged); their only 3 callers are tl_stats, which itself reimplements tl_snapshot_count_range_internal(TL_TS_MIN,0,true) inline. Have stats call the count API for records_estimate and delete the full-extent pair.
  - perf: one extra range-intersect call per source on the stats path only; append/query hot paths untouched
- **Merge tl_memrun_iter and tl_active_iter into one delta iterator** [minimal-rewrite] ~200 LOC, risk=medium
  - where: core/src/query/tl_memrun_iter.{c,h} + tl_active_iter.{c,h} (471 LOC total)
  - next/seek/destroy bodies are line-identical wrappers over tl_submerge; structs identical except a borrowed pointer that is only NULLed in destroy. One tl_delta_iter_t with two init functions; plan union drops 3 kinds to 2, merge dispatch loses an arm. Deeper optional cut: put tl_submerge_t in the plan union directly (~350 LOC) since plan already prunes what the wrappers re-check.
  - perf: same submerge underneath; one fewer enum arm in hot dispatch — zero or slightly positive; test_delta_internal.c needs 35 mechanical renames
- **tl_point hand-rolls the dynamic record array tl_recvec already provides** [already-in-this-codebase] ~40 LOC, risk=low
  - where: core/src/query/tl_point.c:23-64, tl_point.h:37-42
  - ensure_capacity+add_record duplicate tl_recvec_push/reserve (internal/tl_recvec.h backs 'every contiguous record container in the engine'); tl_point_result_t fields mirror tl_recvec_t exactly. Embed a tl_recvec_t; consumer tl_timelog.c touches 3 sites.
  - perf: identical amortized doubling; point-path speed lives in binary searches, not the buffer
- **Dead-state sweep: write-only fields, dead param, dead branch, dead flag bit** [does-not-need-to-exist] ~30 LOC, risk=low, API-CHANGE
  - where: tl_merge_iter.h:47 (kmerge.alloc); tl_plan.h:87,90-91 (tomb_capacity, segments/memruns_pruned — zero readers repo-wide); tl_iter_build.c head_watermark always 0; tl_point.c:120-123 branch unreachable (caller collect_from_segment:144 already returned when tomb_seq > applied_seq); tl_pagespan_iter.h:119 TL_PAGESPAN_REQUIRE_ZEROCOPY never consumed
  - Seven pieces of state that are written but never read, or provably unreachable. REQUIRE_ZEROCOPY deletion is the only semi-public-API touch (binding-facing enum; binding passes DEFAULT).
  - perf: removes a per-row dead branch from point lookup; otherwise neutral
- **Delete count_sources two-pass in tl_iter_build; over-allocate 2+run_count** [minimal-rewrite] ~24 LOC, risk=low
  - where: core/src/query/tl_iter_build.c:3-24,48-49
  - The exact-count pre-pass only sizes the srcs malloc; build already trims via merge->src_count=idx (line 87). Allocate 2+run_count and delete the function.
  - perf: saves a pass over the runset; wastes at most a few 56-byte slots per iterator lifetime
- **Hoist loop-invariant base_priority; drop impossible i>UINT32_MAX guard** [one-liner] ~8 LOC, risk=low
  - where: core/src/query/tl_plan.c:286-301
  - base_priority depends only on the manifest but is recomputed per sealed memrun; i indexes the small fixed-capacity sealed ring (H-07), never exceeding UINT32_MAX.
  - perf: planning path, negligible either way
- **Inline three single-use tombstone-adder wrappers** [one-liner] ~15 LOC, risk=low
  - where: core/src/query/tl_plan.c:147-169
  - add_segment/memrun/active_tombstones are 6-line single-caller wrappers around tl_tombstones_add_intervals(accum, X_tombs_imm(y), ...).
- **Shared helper for identical L0/L1 loop bodies** [minimal-rewrite] ~25 LOC, risk=low
  - where: core/src/query/tl_snapshot.c:227-264; core/src/query/tl_point.c:325-353
  - Both files duplicate a 10-line loop body verbatim across the L0 and L1 segment lists (only the _get accessor differs); a 5-line per-segment static helper collapses both pairs while keeping the defensive L1 pass.
- **NULL-seqs+watermark support in tl__count_visible_sorted_range absorbs OOO-run inline copy** [already-in-this-codebase] ~25 LOC, risk=low
  - where: core/src/query/tl_count.h:377-413 vs 456-494
  - The OOO-runs branch of tl__count_active_visible_range reimplements the sorted-range counter inline because it lacks NULL-seqs support; the seqs-or-watermark pattern already exists at tl_point.c:84.
  - perf: one predictable per-record branch on the count path (not append/iteration hot paths)
- **Use tl__mallocarray/tl__realloc in ensure_source_capacity** [already-in-this-codebase] ~8 LOC, risk=low
  - where: core/src/query/tl_plan.c:21-57
  - Hand-rolled SIZE_MAX/sizeof overflow guard + malloc/memcpy/free; tl__mallocarray (used in tl_point.c:38) owns the overflow check and tl__realloc exists in the allocator seam.

### Prior-art leads
- **K-way merge iterator with min-heap (tl_merge_iter, tl_submerge)**: CCAN heap (BSD-MIT), PostgreSQL binaryheap (extraction cost), RocksDB MergingIterator (C++ — fails pure-C gate)
  - fit: Poor fit: heap already factored into in-tree tl_heap; merge payload carries watermark + tie_break_key + H-16 error latching; zero-regression rule kills generic-library indirection on the hottest read loop.
- **Dynamic arrays (tl_point result, tl_plan source array)**: klib kvec.h (MIT), stb_ds.h (MIT/Unlicense)
  - fit: Beaten by rung 2: in-tree tl_recvec covers record arrays and respects the tl__malloc allocator seam; stb_ds allocator hooks are global not per-context; plan-source array gain <30 LOC — not worth a vendored file.
- **Atomic refcounted owner with destructor (pagespan owner)**: liburcu urcu/ref.h (LGPL — fails license gate), Concurrency Kit (BSD, primitives only)
  - fit: No adoption: in-tree tl_refcount.h macros are already shared and tuned for the documented GCC-TSan fence limitation (acq_rel decrement); imports would need the same treatment to stay TSan-clean on 3.14t.
- **Interval set / tombstone skyline cursor (consumed here, lives in internal/tl_intervals)**: CCAN interval modules, generic interval-tree libraries
  - fit: No: canonical form (sorted, non-overlapping, non-adjacent, half-open — invariant #5) plus max_seq skyline semantics is bespoke; the forward-only cursor is simpler and faster than any tree for sorted streams.
- **lower_bound binary search**: C stdlib bsearch
  - fit: bsearch lacks lower_bound semantics; in-tree branchless tl_record_lower_bound is a measured v1.3 perf win (point -15%, 3-5x search). Do not touch.

### No-and-no
- **Two-level merge with duplicated heap-seek logic (kmerge over iterators, submerge over raw arrays)**: Deliberate perf structure: inner merge advances raw arrays with zero dispatch (tl_submerge.c:111-122); unifying behind one polymorphic source adds indirection to the hottest read loop — violates zero-regression rule.
- **Snapshot acquisition two-phase sort + epoch-checked memview cache (tl_snapshot.c:96-149)**: Invariants #6/#8: writer_mu serializes publishers+capture; O(N log N) OOO-head sort must run off-lock; cache store revalidates memtable epoch. The apparent redundancy is the design.
- **Pagespan owner freed BEFORE release hook (tl_pagespan_iter.c:135-157)**: Documented allocator-lifetime contract: a binding hook may free the allocator owning the owner struct; 'fixing' the order is a use-after-free.
- **Empty-range pagespan open still creates snapshot+owner (tl_pagespan_iter.c:333-346)**: Pin symmetry with binding pins_enter/release-hook pairing; skipping owner creation leaks the pin.
- **source_next/done/seek if-chain instead of vtable (tl_merge_iter.c:23-84)**: 2-3-arm enum branch beats function-pointer dispatch on the merge hot path and inlines; defensive fallback handled by MSVC pragma.
- **Segment-iter seek monotonicity clamps (tl_segment_iter.c:179-213)**: Load-bearing for kmerge's heap-preserving seek: forward-only sources must never re-yield consumed records after entries with ts >= target are kept in the heap.
- **Filter's tomb_cursor.len==0 fast path (tl_filter.c:30-39)**: 10 LOC skipping a per-record cursor call on the common no-deletes case — hot query iteration.
- **Plan's inline tombstone collection vs reusing tl_snapshot_collect_tombstones**: Single pass over sources during planning; the standalone collector serves count/stats which build no iterators, and the two have subtly different overlap predicates — unification is not behavior-preserving for free.
- **Peek+replace_top instead of pop/push in both merges (tl_merge_iter.c:206-235, tl_submerge.c:108-126)**: ENOMEM safety: a failed push after pop would silently lose a record; documented in-code.
- **Defensive L1 tombstone loops (tl_plan.c:231-234, tl_snapshot.c:247-264, tl_point.c:339-353)**: L1 is tombstone-free by invariant but the loops scan empty interval sets for pennies and keep code correct if the invariant ever changes; each site carries a rationale comment (share the body per S8, keep the defense).
- **tl__range_overlap_half_open hand-rolled intersection (tl_count.h:35-59)**: internal/tl_range.h provides boolean predicates only, no intersection output; 20 honest lines with unbounded-flag handling per the no-sentinel timestamp rule.

---

## storage (3074 LOC reviewed)

### Simplifications
- **Delete V2 row-delete machinery** [does-not-need-to-exist] ~110 LOC, risk=medium
  - where: tl_page.h:14-36,71-74,205-236; tl_page.c:241-255; tl_point.c:111,176; tl_segment_iter.c:22,134,199
  - tl_rowbitset_t, row_del fields, and 32-line tl_page_row_is_deleted are 'never instantiated in V1' (header's own words) yet the merge hot loop calls the check per record; builder hardwires FULLY_LIVE and the validator rejects anything else.
  - perf: Removes one branch per record from merge loop and per page from pruning; shrinks tl_page_t by 16 bytes. Zero-regression, plausibly a small win.
- **Delete dead window helpers** [does-not-need-to-exist] ~55 LOC, risk=low
  - where: tl_window.h:112-163; tl_window.c:116-127
  - tl_window_contains_bounded has zero callers anywhere; tl_window_contains and tl_window_bounds_for_ts are test-only — compaction composes id_for_ts + bounds itself (tl_compaction.c:246,277).
  - perf: Dead code; no runtime effect.
- **Consolidate segment-builder error paths onto segment_destroy + dedupe prefix-count block** [minimal-rewrite] ~45 LOC, risk=medium
  - where: tl_segment.c:161-168,260-291,382-407
  - TL_NEW is calloc-backed and segment_destroy handles every partially-built state, yet five hand-rolled cleanup blocks re-implement it; the 18-line prefix-sum construction is duplicated verbatim between build_l0 and build_l1.
  - perf: Error paths + build-time only; off hot path. Needs new direct ENOMEM injection tests (today covered only indirectly via flush fault injection in test_delta_internal.c).
- **Delete tl_page_upper_bound (no production caller)** [does-not-need-to-exist] ~40 LOC, risk=low
  - where: tl_page.c:177-211; tl_page.h:177-183
  - Only tests/bench call it; the header claim that point queries use it is stale — tl_point.c:106-116 uses lower_bound plus forward scan.
  - perf: Dead code; caveat: it is part of the branchless-search bench harness pair, so deleting removes a benchmarked artifact.
- **Reuse tl_intervals_arr_validate for build_l0 tombstone validation** [already-in-this-codebase] ~22 LOC, risk=low
  - where: tl_segment.c:204-236 vs internal/tl_intervals.c:772-812
  - The 29-line release-mode canonical-form loop in tl_segment_build_l0 duplicates tl_intervals_arr_validate rule-for-rule (only the max_seq<=applied_seq cap differs); the shared validator is merely gated behind #ifdef TL_DEBUG.
  - perf: Flush-build-time O(T) check, off hot path; moving arr_validate out of TL_DEBUG costs nothing in release.
- **Collapse tl_page_builder_t struct** [minimal-rewrite] ~15 LOC, risk=low
  - where: tl_page.h:90-102; tl_page.c:22-30; tl_segment.c:115-118
  - Single production consumer; target_page_bytes field is write-only and builder_build uses only pb->alloc — collapse to tl_page_build(alloc, records, count, out) plus the existing compute_capacity helper.
  - perf: Build path only; identical codegen.
- **Drop redundant zeroing after calloc-backed TL_NEW and dead memset** [one-liner] ~20 LOC, risk=low
  - where: tl_segment.c:247-254,368-376; tl_manifest.c:43-51,497-513; tl_page.c:102
  - TL_NEW is tl__calloc, so explicit field=0/NULL stores are dead; the memset in tl_page_builder_build precedes assignment of all 10 struct fields.
  - perf: Off hot path; partly a style call (explicit init as documentation).
- **Dedupe default_window_size (copies already drifted)** [already-in-this-codebase] ~12 LOC, risk=low
  - where: tl_window.c:7-18 vs tl_timelog.c:97-105
  - tl_timelog.c carries a static byte-for-byte duplicate of tl_window_default_size whose default: case has drifted (1H_S vs 1H_MS); production uses the static, the public one is test-only.
  - perf: Config-time only.
- **Delete write-only cap_l0/cap_l1 manifest fields** [does-not-need-to-exist] ~12 LOC, risk=low
  - where: tl_manifest.h:34,39; tl_manifest.c:45,48,496-513,535-536
  - Both 'diagnostic' capacity fields are stored six times and read nowhere (core, bindings, tests); the comment justifying insert order cites a 'cap_l1 sanity assertion' that does not exist.
  - perf: 8 bytes per manifest; no runtime effect.
- **Delete dead prefix-counts accessor and unreachable NULL fallback** [does-not-need-to-exist] ~14 LOC, risk=low
  - where: tl_segment.h:285-287,300-308
  - tl_segment_page_prefix_counts has zero callers; the NULL-fallback loop in prefix_sum is unreachable because both builders fail the entire build with ENOMEM if the prefix array cannot be allocated.
  - perf: Removes a branch from the range-count precompute path; neutral-to-positive.

### Prior-art leads
- **Typed lower_bound over sorted arrays (5 hand-rolled copies: tl_page.c:141-211, tl_page.c:352-397, tl_manifest.c:87-111)**: C stdlib bsearch (wrong semantics — returns any match), klib ksort.h (no lower_bound primitive), CCAN asearch (bsearch-typed, wrong semantics), local TL_LOWER_BOUND macro (in-codebase dedupe of the 3 branchy copies, ~30 LOC)
  - fit: No mature C library ships lower_bound; the branchless page variant is a measured v1.3 win (point -15.2%) and must stay hand-rolled. Best case is a local macro for the branchy struct-keyed copies. External adoption: expected NO.
- **Growable pointer array (manifest builder add/remove lists tl_manifest.c:199-303; page catalog tl_page.c:291-346)**: klib kvec.h (MIT), stb_ds.h (MIT/Unlicense), internal 20-line tl_ptrvec built on existing tl__grow_capacity
  - fit: kvec hardwires libc realloc — violates tl__realloc seam unless vendored+patched; stb_ds's STBDS_REALLOC override is global-ish, awkward for per-instance tl_alloc_ctx_t. Codebase already owns tl__grow_capacity + overflow guards; even an internal helper is marginal for two sites. Expected NO on external adoption.
- **Intrusive refcounting with destroy-at-zero (tl_segment.c:433-458, tl_manifest.c:63-81)**: liburcu urcu/ref.h (LGPL — fails license), Concurrency Kit ck_pr (BSD-2, primitives only, no refcount object), GLib GRefCount (LGPL — fails)
  - fit: Already deduplicated in-house via TL_REFCOUNT_ACQUIRE/RELEASE, deliberately tuned to fold acquire into the acq_rel RMW because GCC TSan cannot model atomic_thread_fence (documented project constraint). Library adoption re-opens the TSan question for zero LOC win. NO.
- **Overflow-checked signed arithmetic consumed by window math (tl_window.c:35,72,85,100)**: C23 <stdckdint.h> ckd_*, GCC/Clang __builtin_*_overflow, hand-rolled MSVC fallback (required for C17+/WX)
  - fit: Lives in internal/tl_math.h outside this unit; recorded so the internal-unit auditor verifies builtins are used where available. MSVC C17 keeps a manual fallback necessary regardless.

### No-and-no
- **Single-allocation SoA page layout with overflow-checked alignment math (tl_page.c:61-124)**: One-free destruction, cache-adjacent metadata, and hardening against caller-supplied counts; two allocations or a flexible array member would regress flush/compaction alloc traffic or cannot host two typed arrays.
- **Branchless binary search + size gate with duplicated branchy fallback (tl_page.c:151-198)**: Measured v1.3 product win (point -15.2%, search 3-5x); perf is the product and the fallback is required above the gate where cmov's unconditional dependent loads lose.
- **Release-mode invariant checks: L1 window containment, manifest non-overlap after sort, cross-page sortedness (tl_segment.c:134-141,419-423; tl_manifest.c:560-575)**: Mandated by H-12/H-13/H-14 in CLAUDE.md; they run at publication frequency, not per record, and removing them is a non-finding by rule.
- **O(n^2) validate_removals/validate_adds pointer scans (tl_manifest.c:331-412)**: H-10/H-11 duplicate/level validation over tens of segments once per publish; a hash set is more code and a dependency for a non-problem.
- **COW manifest builder as an architecture (tl_manifest.c:113-600)**: Mutate-under-lock 'simplification' violates immutability-after-publication and the seqlock publication protocol; the builder is the mechanism behind H-17 strict publish.
- **Window math: signed floor division and overflow-saturating bounds with unbounded-trailing-window encoding (tl_window.h:45-58, tl_window.c:49-110)**: C has no signed floor division; negative timestamps and INT64 edges are exhaustively tested (test_storage_internal.c:89-245) and the unbounded encoding is load-bearing for L1 non-overlap.
- **Page catalog metadata duplication / fence pointers (tl_page.h:264-270)**: Binary search touches one contiguous meta array instead of chasing a pointer per probe; removing the cache regresses query pruning. (The flags member alone dies with the V2-machinery deletion.)
- **Segment triple bounds: record_*, tomb_*, overall min/max (tl_segment.h:63-72)**: All consumed — overall by manifest pruning (tl_manifest.c:582-589), record bounds by count/plan (tl_count.h:157, tl_plan.c:247), tomb bounds by snapshot tombstone collection (tl_snapshot.c:232); collapsing them would 'silently lose deletes' per the builder's own comment (tl_segment.c:299-300).

---


TOTALS: 112 simplification findings, ~6871 LOC saved estimate (pre-verification)
