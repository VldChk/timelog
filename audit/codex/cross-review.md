**Cross-Examination Verdict**

I read `CLAUDE.md` and the full draft. I would not approve the draft as written: the core simplification direction is mostly real, but several “zero-regression” and additive-total claims are overstated.

| Finding | Verdict | Evidence |
|---|---:|---|
| C5 memtable double sort | **MODIFIED** | Real issue, but narrower than “one O(H log H) sort per seal.” The duplicate sort only appears for unsorted OOO heads when tombstone-drop pre-counting runs: pre-count at [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:899), second sort in flush at [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:448). |
| C4 compaction retry/selection | **CONFIRMED** | Watermarks side array is transient setup-only at [tl_compaction.c](/home/vldvhk/Documents/timelog/core/src/maint/tl_compaction.c:1072); L1 overlap selection is two-pass at [tl_compaction.c](/home/vldvhk/Documents/timelog/core/src/maint/tl_compaction.c:469); final failed publish can still rebuild/merge before loop exit at [tl_compaction.c](/home/vldvhk/Documents/timelog/core/src/maint/tl_compaction.c:1455). Perf-positive, but mostly maintenance/race-path. |
| B3 tombstone union helper | **CONFIRMED** | `tl__tombs_union_into` is a temp+union+replace wrapper at [tl_compaction.c](/home/vldvhk/Documents/timelog/core/src/maint/tl_compaction.c:179). Existing shared helper already unions intervals into caller accumulator using its allocator at [tl_tombstone_utils.h](/home/vldvhk/Documents/timelog/core/src/internal/tl_tombstone_utils.h:13). |
| B5 full-count/range-count collapse | **MODIFIED** | Count equivalence is real: `tl_count()` already calls the range path with full extent at [tl_timelog.c](/home/vldvhk/Documents/timelog/core/src/tl_timelog.c:1546). But `tl_stats()` still needs page counts, tombstone counts, min/max, and component iteration at [tl_timelog.c](/home/vldvhk/Documents/timelog/core/src/tl_timelog.c:2049). Do not claim the whole stats loop disappears. |
| A3 row-delete reserves | **CONFIRMED** | V2-only metadata is present in the page shape at [tl_page.h](/home/vldvhk/Documents/timelog/core/src/storage/tl_page.h:7), builder always emits fully-live pages at [tl_page.c](/home/vldvhk/Documents/timelog/core/src/storage/tl_page.c:114), validator rejects row-delete pages at [tl_page.c](/home/vldvhk/Documents/timelog/core/src/storage/tl_page.c:247). |
| C1 active/memrun iterator merge | **CONFIRMED** | Structs are field-identical except source pointer type: [tl_memrun_iter.h](/home/vldvhk/Documents/timelog/core/src/query/tl_memrun_iter.h:23), [tl_active_iter.h](/home/vldvhk/Documents/timelog/core/src/query/tl_active_iter.h:23). Implementations are near copies after init: [tl_memrun_iter.c](/home/vldvhk/Documents/timelog/core/src/query/tl_memrun_iter.c:81), [tl_active_iter.c](/home/vldvhk/Documents/timelog/core/src/query/tl_active_iter.c:72). |
| C9 custom PySeqIter adoption | **MODIFIED / BLOCK** | LOC deletion is plausible, but not zero-regression. The custom iterator has observable type/module-state behavior at [py_span_objects.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span_objects.c:169) and explicit two-object locking in `next` at [py_span_objects.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_span_objects.c:195). Tests assert the type name at [test_subinterpreters.py](/home/vldvhk/Documents/timelog/python/tests/test_subinterpreters.py:194). |
| A7 binding “dead code” | **MODIFIED / BLOCK** | Some micro-dead state exists, e.g. drop-node `ts` is set at [py_handle.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_handle.c:697) and appears unused. But reload rollback is documented public behavior at [docs/python-api.md](/home/vldvhk/Documents/timelog/docs/python-api.md:31), `TimelogIter.view()` is public at [py_iter.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_iter.c:456), and `remaining_valid` drives length/repr behavior at [py_iter.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_iter.c:426). |
| D1 C11 atomics on MSVC | **MODIFIED** | Current core deliberately bypasses `stdatomic` on MSVC at [tl_atomic.h](/home/vldvhk/Documents/timelog/core/src/internal/tl_atomic.h:17). The CPython extension already passes `/experimental:c11atomics` at [bindings CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:204), but the core target does not at [CMakeLists.txt](/home/vldvhk/Documents/timelog/CMakeLists.txt:41). Needs MSVC CI proof before “zero-regression.” |
| E1 shared binding test harness | **CONFIRMED** | The eight C binding tests duplicate Python home/init/finalize/assert harnesses, e.g. [test_py_errors.c](/home/vldvhk/Documents/timelog/bindings/cpython/tests/test_py_errors.c:17), [test_py_handle.c](/home/vldvhk/Documents/timelog/bindings/cpython/tests/test_py_handle.c:25), [test_py_module_exec.c](/home/vldvhk/Documents/timelog/bindings/cpython/tests/test_py_module_exec.c:16). |
| E2 CMake test-target helper | **CONFIRMED** | Binding test target stanzas are copy-pasted: examples at [bindings CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:264), [bindings CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:305), [bindings CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:410). |
| D2 CTest-native core groups | **CONFIRMED** | The Python script is a custom scheduler/report wrapper over CTest/subprocess at [run_core_test_groups.py](/home/vldvhk/Documents/timelog/demo/ci/run_core_test_groups.py:109). Group filtering already exists in C at [test_main.c](/home/vldvhk/Documents/timelog/core/tests/test_main.c:253). |
| D3 pytest JSON/JUnit switch | **MODIFIED / PARTLY REFUTED** | The draft references a custom summary protocol, but the actual script parses `COMPAT_BASELINE_*` lines at [run_compat_baseline.py](/home/vldvhk/Documents/timelog/demo/ci/run_compat_baseline.py:102). `pytest-json-report` is not in test deps at [pyproject.toml](/home/vldvhk/Documents/timelog/pyproject.toml:29), so using it contradicts “zero external dependencies.” Built-in `--junitxml` is the safer rung. |
| C7 `PyErr_FormatV` | **CONFIRMED** | Two helpers duplicate fixed 512-byte `vsnprintf` buffers at [py_errors.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_errors.c:137) and [py_errors.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/py_errors.c:175). CPython’s formatting API would remove truncation-prone code. |

**Headline Verdict**

“Zero library adoption” is defensible for production/core code. I did not find a clearly superior third-party C library that passes the stated constraints and improves the hot path without allocator/concurrency risk.

Section F is incomplete and partly sloppy. Unity is not simply “Ruby codegen”; the core is C and the Ruby runner is optional. `pytest-json-report` appearing in D3 would itself be a new dependency unless replaced with built-in JUnit XML. TLSF is also under-discussed: it is a plausible C allocator library, but adopting it would replace allocator internals rather than simplify the current `tl__malloc` seam, so I would not call it a missed good adoption.

**Missed Opportunities**

1. Export/type-name lists are triplicated. `managed_export_names` at [module.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/module.c:40), export descriptors at [module.c](/home/vldvhk/Documents/timelog/bindings/cpython/src/module.c:351), and test copies at [test_py_module_exec.c](/home/vldvhk/Documents/timelog/bindings/cpython/tests/test_py_module_exec.c:16) could be one descriptor source.

2. Binding compile-option boilerplate is repeated beyond just test stanzas. `_timelog` has MSVC/Unix warning options at [bindings CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:203), then each test repeats variants, e.g. [bindings CMakeLists.txt](/home/vldvhk/Documents/timelog/bindings/cpython/CMakeLists.txt:287).

**Double-Counting Audit**

The 4.4-5.2K headline is not honest as an additive, verified zero-regression total.

A7 and C9 overlap on `PageSpanObjectsViewIter`, module-state type storage, and tests. Count one path, not both.

D2 and E3 overlap around core-test grouping/filter/report infrastructure; once CTest owns grouping, some table-dispatch savings shrink.

C1’s optional “direct plan union” deeper cut overlaps C10 query micro-cleanups and should not be included alongside C10 without a line-level deletion plan.

A7 test deletions and E1 harness extraction touch the same binding test files. Harness boilerplate can be counted; removing behavioral reload/iterator tests cannot be counted as zero-regression.

B5 is overstated: range/full count helper unification is valid, but `tl_stats()` still needs separate stats work, so its projected LOC should be downgraded.

**Final Table**

| Action | Findings |
|---|---|
| **BLOCK** | A7 major binding deletions; C9 PySeqIter replacement; D1 as an unconditional platform rung; D3 if it means adding `pytest-json-report`; C5 if claimed as universal seal-path perf gain. |
| **DOWNGRADE** | B5 stats deletion scope; C4 perf framing; D2/E3 combined savings; C1 optional deeper plan-union savings; headline 4.4-5.2K additive total. |
| **ENDORSE** | A3 row-delete reserve removal; B3 tombstone union helper reuse; C1 base active/memrun iterator merge; C4 selected compaction cleanups; C5 narrow double-sort fix; C7 `PyErr_FormatV`; E1 shared binding test harness; E2 CMake test-target helper. |

No tests were run; this was a source-level hostile review under the read-only sandbox.  

