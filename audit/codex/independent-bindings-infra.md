**Executive Summary**

This is not mostly “reinvented wheels.” The CPython binding is hand-rolled because the project’s own contract requires free-threaded/subinterpreter safety, attached thread-state discipline, no Python execution under internal locks, preserved exception state across DECREF, and buffer-export lifetime rules: [CLAUDE.md](/home/vldvhk/Documents/timelog/CLAUDE.md:368), [CLAUDE.md](/home/vldvhk/Documents/timelog/CLAUDE.md:395), [CLAUDE.md](/home/vldvhk/Documents/timelog/CLAUDE.md:411), [CLAUDE.md](/home/vldvhk/Documents/timelog/CLAUDE.md:451).

Good simplification targets exist, but they are mostly cold-path or build-only: CMake test boilerplate, `py_timelog.c` argument-wrapper repetition, config-validation repetition, one duplicated error-format helper, and shallow heap-type boilerplate. I would not replace the handle lifetime machinery, PageSpan buffer protocol, module-state initialization, or hot append/bulk append parsers with third-party libraries under the stated constraints.

**Findings**

1. **YES SIMPLER: binding CMake test targets are copy-paste machinery. NO library prior art needed.**

Evidence: the extension source list already exists once at [bindings/cpython/CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:163), then near-identical embedded-test source/include/link/compile blocks repeat for `test_py_timelog`, `test_py_iter`, `test_py_span`, `test_py_maint_b5`, `test_py_errors`, and `test_py_module_exec`: [bindings/cpython/CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:305), [bindings/cpython/CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:357), [bindings/cpython/CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:410), [bindings/cpython/CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:462), [bindings/cpython/CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:514), [bindings/cpython/CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:601). Test registration is also manually enumerated at [bindings/cpython/CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:655).

Recommendation: introduce a CMake function for embedded binding tests, with parameters for test source, extra compile definitions, and whether `PYTHONPATH` is needed. Use target-scoped warning helpers instead of global add/remove warning policy: root adds global warning flags at [CMakeLists.txt](/home/vldvhk/Documents/timelog/CMakeLists.txt:48) and [CMakeLists.txt](/home/vldvhk/Documents/timelog/CMakeLists.txt:82), then the binding subdir globally disables Werror at [bindings/cpython/CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:69).

LOC estimate: save 120-170 net CMake LOC after ~50-70 LOC of helper glue. Risk: low-medium; build-system risk only, zero runtime perf impact.

2. **YES SIMPLER: `PyTimelog_init` config parsing is table/macro bait. NO external prior art.**

Evidence: a keyword enum and kwlist are manually kept in lockstep at [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:806) and [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:838), then the parse format must match both at [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:901). Adaptive and compaction dict keys/conflicts are bespoke at [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:943) and [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:1030). Numeric validations repeat the same sentinel/range/cast/store pattern from [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:1116), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:1252), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:1288), and [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:1338).

Recommendation: use local macros or small descriptor helpers for `size_t`, `uint32_t`, timestamp, and bounded double options. Do not use a generic config library; preserving exact Python exceptions and sentinels is the hard part.

LOC estimate: save 100-150 net LOC. Risk: medium because exact error strings and “dict conflicts flat kwarg” behavior must be regression-tested. Perf: init-only, no hot-path effect.

3. **YES SIMPLER: repeated timestamp method wrappers in `py_timelog.c`. NO useful library prior art.**

Evidence: `next_ts` and `prev_ts` are structurally identical except function/name: [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:2973), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:3013). `since`, `until`, `equal`, and `point` repeat one-argument FASTCALL parsing, `tl_py_fast_i64`, `tl_py_validate_ts`, and `pytimelog_make_iter`: [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:3399), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:3424), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:3460), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:3486). Two-argument range validation repeats the same shape in `range` and `delete_range`: [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:3368), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:2593).

Recommendation: use static helpers that take method name, arity, iterator mode/core function, and timestamp labels. Keep METH_FASTCALL. Do not switch to tuple/dict parsing; that risks allocation and error-message changes.

LOC estimate: save 80-120 net LOC. Risk: low-medium, mostly exact TypeError text. Perf: no regression if helpers stay static and FASTCALL stays.

4. **YES SIMPLER: duplicate formatted error raising. NO library prior art.**

Evidence: `TlPy_RaiseFromStateFmt` and `TlPy_RaiseFromObjectFmt` duplicate the same 512-byte buffer, `vsnprintf`, empty-message fallback, and `PyErr_SetString` path: [bindings/cpython/src/py_errors.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_errors.c:137), [bindings/cpython/src/py_errors.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_errors.c:175).

Recommendation: one internal `tlpy_raise_fmt_va(st, status, format, va_list)` helper.

LOC estimate: save 18-25 net LOC. Risk: low. Perf: irrelevant.

5. **LIMITED YES SIMPLER: shallow span/iterator boilerplate. NO deep extraction, NO library prior art.**

Evidence: `enter` methods are identical in `PageSpan`, `TimelogIter`, and `PageSpanIter`: [bindings/cpython/src/py_span.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span.c:332), [bindings/cpython/src/py_iter.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_iter.c:348), [bindings/cpython/src/py_span_iter.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span_iter.c:351). Existing helpers already centralize GC dealloc and closed getters at [bindings/cpython/include/timelogpy/py_compat.h](/home/vldvhk/Documents/timelog/bindings/cpython/include/timelogpy/py_compat.h:217) and [bindings/cpython/include/timelogpy/py_compat.h](/home/vldvhk/Documents/timelog/bindings/cpython/include/timelogpy/py_compat.h:232).

Do not extract the detach/release core into a generic object manager: `PageSpan` has buffer-export blocking and owner/timelog release at [bindings/cpython/src/py_span.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span.c:111), `TimelogIter` releases iter/snapshot/pins/engine/handle/owner in a strict order at [bindings/cpython/src/py_iter.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_iter.c:147), and `PageSpanIter` delegates pin release through a core owner hook at [bindings/cpython/src/py_span_iter.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span_iter.c:55).

LOC estimate: save 30-50 net LOC with `TL_PY_DEFINE_ENTER` and maybe shared flags macros. Risk: medium if macro indirection hides lifetime ownership. Perf: none.

6. **TEST HARNESS: YES prior art exists; NO zero-regression replacement unless you accept migration churn.**

Evidence: the harness is a small framework: fixed result array at [core/tests/test_harness.h](/home/vldvhk/Documents/timelog/core/tests/test_harness.h:14), result struct at [core/tests/test_harness.h](/home/vldvhk/Documents/timelog/core/tests/test_harness.h:21), assertion macros at [core/tests/test_harness.h](/home/vldvhk/Documents/timelog/core/tests/test_harness.h:58), runner at [core/tests/test_main.c](/home/vldvhk/Documents/timelog/core/tests/test_main.c:22), failure recording at [core/tests/test_main.c](/home/vldvhk/Documents/timelog/core/tests/test_main.c:47), env filters at [core/tests/test_main.c](/home/vldvhk/Documents/timelog/core/tests/test_main.c:134) and [core/tests/test_main.c](/home/vldvhk/Documents/timelog/core/tests/test_main.c:166), and manual suite dispatch at [core/tests/test_main.c](/home/vldvhk/Documents/timelog/core/tests/test_main.c:253). It also has unchecked `g_test_ctx.count++` paths at [core/tests/test_main.c](/home/vldvhk/Documents/timelog/core/tests/test_main.c:39) and [core/tests/test_main.c](/home/vldvhk/Documents/timelog/core/tests/test_main.c:48).

Prior art: `greatest` is closest: one-header C test framework, no dynamic allocation, permissive ISC, and intended to build cleanly with warning flags; see its README summary. ([github.com](https://github.com/silentbicycle/greatest)) Unity is MIT licensed. ([github.com](https://github.com/ThrowTheSwitch/Unity/blob/master/LICENSE.txt)) µnit is MIT-licensed, no-dependency, and has a fuller CLI. ([github.com](https://github.com/nemequ/munit))

But a zero-regression replacement must preserve `TL_TEST_GROUPS`, `TL_TEST_FILTER`, void-return tests, exact CTest behavior, and current macro names or touch every core test file outside this audit scope. With adapter glue, net savings are probably 0-150 LOC if fetched externally, and negative if vendored in-tree. Risk: high. I would not do this just to delete 538 local LOC.

**NO-And-NO Section**

- **Handle lifetime subsystem: NO simpler, NO replacement.** This is not “just a hash table.” The live table has atomic entry publication rules for lock-free GC traversal at [bindings/cpython/src/py_handle.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_handle.c:48), old tables are retired until teardown at [bindings/cpython/src/py_handle.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_handle.c:68), the retired queue is a Treiber stack with explicit C11/TSan memory-order rationale at [bindings/cpython/src/py_handle.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_handle.c:237), and `tp_traverse` must not lock or allocate at [bindings/cpython/src/py_handle.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_handle.c:1005). `uthash`/`khash` solve ordinary hash tables, not this CPython GC/DECREF/pin problem. Concurrency Kit is prior art for lock-free structures, but its license file includes extra component licenses and it does not erase the CPython ownership glue. ([raw.githubusercontent.com](https://raw.githubusercontent.com/concurrencykit/ck/master/LICENSE))

- **PageSpan buffer protocol: NO simpler, NO replacement.** `getbuffer` must atomically check closed/export state, reject writable buffers, expose only timestamps, and never leak encoded `PyObject*` handles: [bindings/cpython/src/py_span.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span.c:217), [bindings/cpython/src/py_span.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span.c:246), [bindings/cpython/src/py_span.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span.c:272). This is CPython buffer API work, not a third-party container problem.

- **Hot append/bulk append parsers: NO simpler via prior art.** `append` preserves facade-compatible signatures and `TL_EBUSY` commit semantics at [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:1693), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:1827). `bulk_append` needs FASTCALL parsing, buffer-format validation, native-endian/alignment checks, min-ts floor, and all-or-nothing batch semantics: [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:2229), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:2362), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:2462), [bindings/cpython/src/py_timelog.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_timelog.c:2521). Argument Clinic is not a pure C17 vendorable library and would risk error/perf drift.

- **Module-state initialization: NO simpler, NO library replacement.** The type registry is already the correct local abstraction: creation order table at [bindings/cpython/src/module.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/module.c:57), traversal loop at [bindings/cpython/src/module.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/module.c:117), rollback-aware exports at [bindings/cpython/src/module.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/module.c:349), and free-threaded module slots at [bindings/cpython/src/module.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/module.c:484). This is CPython multi-phase init boilerplate, not a reusable C library problem.

- **Iterator/PageSpan release ordering: NO deep abstraction.** Each type releases different resources in different orders: `TimelogIter` at [bindings/cpython/src/py_iter.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_iter.c:147), `PageSpan` at [bindings/cpython/src/py_span.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span.c:144), `PageSpanIter` at [bindings/cpython/src/py_span_iter.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span_iter.c:225), and objects view is intentionally lazy/simple at [bindings/cpython/src/py_span_objects.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span_objects.c:106). A generic destructor framework would hide the invariants and save little.

**Ranked Shortlist**

1. Factor `bindings/cpython/CMakeLists.txt` embedded-test target boilerplate. Net save: ~120-170 LOC. Risk: low-medium.
2. Extract `py_timelog.c` one/two-argument timestamp wrappers and next/prev navigation helper. Net save: ~80-120 LOC. Risk: low-medium.
3. Macro/table-drive `PyTimelog_init` numeric option validation. Net save: ~100-150 LOC. Risk: medium.
4. Add `va_list` formatted-error helper in `py_errors.c`. Net save: ~20 LOC. Risk: low.
5. Add shallow CPython heap-type helper macros for identical `enter`/flags/possibly close wrappers. Net save: ~30-50 LOC. Risk: medium.
6. Consider `greatest` only if you are willing to migrate the core test runner semantics deliberately. It is valid prior art, but not a zero-regression quick deletion.

No files were modified. I did not run tests; this was a read-only source audit.


