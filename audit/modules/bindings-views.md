# Ponytail Simplification Audit — Unit: bindings-views

Auditor stance: lazy senior dev ("the best code is code never written"), but every line of the
four assigned files was read in full, plus the supporting headers (`py_compat.h`,
`py_module_state.h`, `py_iter.h`, `py_span.h`, `py_span_iter.h`, `py_span_objects.h`,
`py_handle.h`) and the relevant caller/registration sites (`py_timelog.c` make_iter +
page_spans, `module.c` type table, core `tl_pagespan_iter.h/.c` view contract).

Files reviewed (2,021 LOC of unit code):

| File | LOC | Type(s) |
|---|---|---|
| `bindings/cpython/src/py_span.c` | 596 | PyPageSpan (buffer protocol) |
| `bindings/cpython/src/py_iter.c` | 577 | PyTimelogIter |
| `bindings/cpython/src/py_span_iter.c` | 425 | PyPageSpanIter |
| `bindings/cpython/src/py_span_objects.c` | 423 | PyPageSpanObjectsView + PyPageSpanObjectsViewIter |

## Executive Summary

This unit is in noticeably better shape than the "four near-identical CPython types" framing
suggests: the codebase has ALREADY extracted the worst boilerplate (`TL_PY_GC_DEALLOC`,
`TL_PY_DEFINE_CLOSED_GETTER`, `TL_PY_DEFINE_CHECK`, table-driven type registration in
`module.c`), and the remaining per-type duplication (detach-under-CS / release-outside-CS
choreography) is load-bearing free-threading discipline that should NOT be genericized.

What remains is a crop of genuinely dead or speculative code:

1. **`TimelogIter.view()` is compiled, shipped, advertised in README — and has ZERO tests, zero
   docs/python-api.md coverage, zero facade/lab/benchmark callers.** Deletion candidate (or
   test-it-or-lose-it). ~30 LOC. **api-change**.
2. **The entire custom `PyPageSpanObjectsViewIter` heap type duplicates CPython's built-in
   `PySeqIter` fallback.** Removing the `Py_tp_iter` slot makes `iter(view)` use the platform
   sequence iterator with identical semantics (IndexError→StopIteration, ValueError propagates).
   ~140 LOC including module-state/registration/failpoint plumbing and the now-single-use
   `TL_PY_OBJ_LOCK2` macros. **api-change** (observable type name).
3. A family of **unreachable defensive branches** (`h == NULL` "future-proofing", decode-NULL
   "invalid handle", `remaining_valid`) — none reachable by construction, none tested. ~55 LOC.
4. Small compressions: redundant pre-checks that duplicate checks one call deeper, deprecated
   `PyErr_Fetch/Restore` where the codebase's own modern macro exists, test-hook stubs that can
   be `#define`'d to NULL, and a start/end-ts getter pair that mirrors the existing
   closed-getter macro pattern. ~85 LOC.

Total honest potential: **~300 LOC (~15% of the unit)**, most of it low-risk. No external
library adoption is warranted anywhere in this unit — the only prior-art wins are *platform*
(CPython itself) and *already-in-this-codebase* rungs.

---

## Per-File Walkthrough

### py_iter.c — PyTimelogIter (577 LOC)

- **Lines 33–82 (test failpoints)**: `TL_PY_ITER_TEST_HOOKS` gated; production `#else` compiles
  two always-return-0 stubs whose addresses are passed as function pointers into
  `pytimelogiter_step`. See Finding F7.
- **Lines 96–200 (detach/release/cleanup)**: exemplary collect-under-lock / execute-outside-lock
  split. Verbose but each line is doing invariant work (see NO-and-NO N1).
- **Lines 244–327 (`pytimelogiter_step`)**: single shared step used by both `__next__` and
  `next_batch` — good existing de-duplication. Holds CS across `tl_iter_next` per the
  documented py_compat.h carve-out (py_compat.h:141–145).
- **Lines 361–420 (`next_batch`)**: preallocate-n + trim strategy; the closed fast-path at
  379–387 earns its keep *because* of the preallocation (avoids allocating an n-slot list on a
  closed iterator). NO-and-NO N5.
- **Lines 426–448 (`__len__`)**: `remaining_valid` branch — see Finding F4.
- **Lines 456–481 (`view()`)**: see Finding F1.
- **Lines 508–539 (`repr`)**: fine; the `!remaining_valid` branch at 528–530 is unreachable
  (F4).

### py_span.c — PyPageSpan (596 LOC)

- **Lines 32–87 (`PyPageSpan_FromView`)**: defensive NULL/type checks for a single internal
  caller — see Finding F9.
- **Lines 111–166 (detach/release/cleanup)**: the atomic "check exports + mark closed + detach"
  CS is the heart of the close-vs-getbuffer race fix; correct and irreducible (N1).
- **Lines 217–304 (buffer protocol)**: the platform-idiomatic exporter. The
  `#if SIZE_MAX <= UINT32_MAX` guard (238–241) is real on 32-bit; keep (N4). The exports
  counter is what implements the documented "cannot close while exported → BufferError"
  contract (CLAUDE.md binding rule 16) — a custom exporter type is the only way to get this;
  `PyMemoryView_FromMemory` provides no lifetime pinning (N2).
- **Lines 352–375 (`objects()`)**: pre-checks closed + h, then calls
  `PyPageSpanObjectsView_Create` which re-checks closed under the same CS discipline — see
  Finding F6; `h_missing` branch is unreachable — see F3.
- **Lines 377–435 (`copy_timestamps`)**: pin-owner-then-copy; structurally similar to
  `PyPageSpanObjectsView_copy` but element materialization differs — extraction rejected (N8).
- **Lines 454–471 (`get_timestamps`)**: the closed pre-check is fully redundant — see F8a.
- **Lines 473–513 (start/end/last_ts getters)**: two identical getters modulo field — see F8b.

### py_span_iter.c — PyPageSpanIter (425 LOC)

- **Lines 44–84 (release-hook context)**: the armed-flag pattern implements H-15 (symmetric
  arm/fire); earns its keep.
- **Lines 93–197 (`PyPageSpanIter_Create`)**: the `kind` parameter accepts exactly one value —
  see Finding F5. The lock-ordered acquisition of handle_ctx/engine_ctx/pin under `core_lock`
  is TOCTOU-hardened per the review history; do not touch.
- **Lines 208–254, 285–338**: same detach/release choreography as py_iter.c but with a
  2-field payload vs 5-field — a generic extraction would need out-param arrays or macro
  gymnastics (N1).
- **Line 235 (`PyErr_Fetch`)**: deprecated idiom, codebase already owns the modern macro — F10.

### py_span_objects.c — PyPageSpanObjectsView + Iter (423 LOC)

- **Lines 23–53 (`Create`)**: re-checks type + closed for a single internal caller (F6).
- **Lines 106–163 (`sq_item`)**: correct decode-under-CS pattern. err=2 (`h==NULL`) and err=4
  (decode NULL) are unreachable — F3.
- **Lines 169–279 (custom iterator type)**: ~110 LOC re-implementing what CPython's `PySeqIter`
  fallback provides for free once `sq_item` exists — Finding F2. This is also the ONLY user of
  `TL_PY_OBJ_LOCK2` in the entire binding (verified by grep), so py_compat.h:185–196+201–202
  become dead with it.
- **Lines 285–353 (`copy`)**: fine (N8); err=2 branch unreachable (F3).

---

## Findings (Simplifications)

### F1. `TimelogIter.view()` — untested, unreferenced, undocumented-in-API-ref public method
**Rung: 1 (does-not-need-to-exist)** · **api-change** · risk: medium · est. −30 LOC

- `py_iter.c:456-481` — `PyTimelogIter_view` builds a `PageSpanIter` for the iterator's
  normalized range; `py_iter.c:489-490` registers it.
- Evidence of deadness:
  - `grep -rn '\.view(' docs/ python/ bindings/cpython/tests/` → **zero** hits (only README).
  - Zero hits in `python/tests/`, zero in the C binding tests, zero in the local `lab/`
    harness (`harness.py`/`generators.py`/`oracle.py`), zero in `docs/python-api.md`.
  - Sole reference anywhere: `README.md:164` ("iterator helpers: `len(it)`, `next_batch(n)`,
    and `it.view()`").
- The `range_t1/range_t2` fields (`py_iter.h:85-86`, "for view() support") must STAY — `repr`
  uses them (`py_iter.c:521-523`), so only the method body + table row + the
  `timelogpy/py_span_iter.h` include (`py_iter.c:15`) go.
- **Loud flag**: it is README-advertised, so this is a public-API removal. The lazy-senior
  alternative if the feature is wanted: keep it and add the missing test — an untested public
  method that bridges two resource-lifetime domains (iter snapshot → new pagespan snapshot) is
  the worst of both worlds.
- Test safety net: none today (that is the finding).

### F2. Replace custom `PyPageSpanObjectsViewIter` with CPython's `PySeqIter` fallback
**Rung: 4 (platform)** · **api-change** (type name only) · risk: medium · est. −140 LOC

- `py_span_objects.c:169-279` defines a full heap type (struct, dealloc, traverse, clear,
  `objectsviewiter_next`, `PyPageSpanObjectsView_iter` factory) whose behavior is: walk
  `sq_item(view, 0..len-1)`, stop at end, propagate errors.
- CPython already does exactly this: if a type has `sq_item` and **no** `tp_iter`,
  `PyObject_GetIter` wraps it in `PySeqIter`, which calls `__getitem__(0), (1), …` and converts
  `IndexError` → `StopIteration`. `PyPageSpanObjectsView_getitem` already raises `IndexError`
  on out-of-range (`py_span_objects.c:154-156`) and `ValueError` on closed (147-149) — the
  observable iteration semantics are **identical** (closed-mid-iteration still raises
  ValueError; exhaustion still stops cleanly).
- What gets deleted:
  - `py_span_objects.c:169-279` iterator machinery (~110 LOC) and slots/spec at 393-411
    (~19 LOC), factory `TlPy_CreatePageSpanObjectsViewIterType` (418-421);
  - `Py_tp_iter` slot at 375 (removing it is what enables the fallback);
  - `py_module_state.h:25` state field, `:65` failpoint enum entry;
  - `module.c:90-93` table row + `_Static_assert` count 6→5 (module.c:100-101);
  - `py_compat.h:185-196,201-202` — `TL_PY_OBJ_LOCK2/UNLOCK2` become dead (this is their only
    user, verified).
- Perf note: perf is the product, so measured honestly — the custom `next` takes a **2-object
  critical section** (`py_span_objects.c:220`) per item; the PySeqIter path takes ONE critical
  section (inside `sq_item`) plus one extra C dispatch (`PySeqIter_Next → sq_item`). Under
  free-threaded builds one fewer CS acquisition may actually win; under GIL builds it is a
  wash. Either way this is the object-materialization path (already paying per-item
  PyObject/refcount costs), not the append/scan/merge hot path.
- Concurrency note: `PySeqIter`'s `it_index` is CPython-managed; under FT misuse two threads
  could observe duplicate/skipped indices, but `sq_item` revalidates bounds + closed under the
  span's CS, so **memory safety is preserved** — which matches the documented contract
  ("A PageSpanObjectsView instance is NOT thread-safe", py_span_objects.h:13-15). Must stay
  TSan-clean: PySeqIter is CPython's own code, exercised by the FT test suite.
- **Flags**: `python/tests/test_subinterpreters.py:201` asserts
  `type(objects_iter).__name__ == "PageSpanObjectsViewIter"` and `__module__ ==
  "timelog._timelog"` — that check (an interpreter-isolation probe) would need rewording;
  PySeqIter is a static CPython type shared across interpreters, which is CPython's problem,
  not a Layer-A violation (the static checker polices *our* types). `test_py_module_exec.c`
  references at :485-496, :667, :788, :906-907 need updating. The iter type is NOT exported as
  a module attribute (test asserts `module_attr_absent(module, "PageSpanObjectsViewIter")`,
  test_py_module_exec.c:496), so the public-API blast radius is just `type(iter(view))`
  identity.

### F3. Unreachable defensive branches: `h == NULL` and decode-NULL in the span/objects family
**Rung: 1 (does-not-need-to-exist)** · risk: low-medium · est. −40 LOC

- `h == NULL` can never be observed with `closed == 0`:
  - Core always fills it: `core/src/query/tl_pagespan_iter.c:457`
    (`out_view->h = &page->h[row_start];`) — no NULL path exists; the header comment
    "May be NULL if handles are unavailable (future-proofing)" (py_span.h:89) admits this is
    speculative.
  - On close, `pagespan_detach_locked` sets `h = NULL` **and** `closed = 1` in the same CS
    (py_span.c:125-130), and every site checks `closed` first under the same CS.
  - Dead sites: `py_span.c:360-372` (`h_missing` in `objects()`), `py_span_objects.c:128-129`
    + 150-153 (getitem err=2), `:225-227` + 246-249 (iternext err=2), `:309-310` + 325-328
    (copy err=2).
- decode-NULL ("invalid handle in span") is likewise unreachable: `tl_py_handle_decode` is a
  pure cast (py_handle.h:76-78) that returns NULL only for handle==0, and handles enter the
  engine exclusively via `tl_py_handle_encode(obj)` with `obj` a real argument object
  ("must not be NULL", py_handle.h:63). Dead sites: `py_span_objects.c:136-138` + 157-161
  (getitem err=4), `:232-234` + 250-253 (iternext err=3), `:341-347` (copy).
- Zero test coverage: `grep -rn "handles not available\|invalid handle in span"` over both test
  trees → no hits. These branches have never executed.
- Honest counterpoint: the messages are user-facing and the checks are off any hot loop except
  the per-item decode paths (where they cost one predictable branch). If the maintainer wants
  to keep a guard, a single `assert(span->h != NULL)` preserves debug-build detection at zero
  release cost. Does not violate any documented invariant.

### F4. `remaining_valid` — speculative field guarding an impossible state
**Rung: 1 (does-not-need-to-exist)** · risk: low · est. −18 LOC

- `py_iter.h:96-103` says the quiet part out loud: "Kept explicit so `__len__` can fail
  deterministically **if initialization logic changes in the future**."
- Every successfully constructed iterator has it set to 1: `py_timelog.c:3288-3289` initializes
  0, and the only return path that yields the object sets it at `py_timelog.c:3357`; the count
  failure path destroys the object (`py_timelog.c:3343-3356`). After close,
  `pytimelogiter_detach_locked` zeroes `remaining_count` (py_iter.c:133) but leaves
  `remaining_valid == 1`, so `len(closed_iter) == 0` — the valid path.
- Dead consumers: `py_iter.c:435-439` (`RuntimeError: iterator remaining length is
  unavailable` — zero test hits) and `py_iter.c:528-530` (`<TimelogIter>` repr branch).
- Also touches `pytimelogiter_step`'s decrement guard (`py_iter.c:273`), which simplifies to
  `if (self->remaining_count > 0)`.

### F5. `kind="segment"` parameter — one-value enum threaded through four layers
**Rung: 1 (does-not-need-to-exist)** · **api-change** · risk: medium · est. −25 LOC (lead only)

- The only accepted value is `"segment"`: `py_span_iter.c:98-102` (`strcmp` + error),
  `py_timelog.c:3511` docstring "currently supported value", facade
  `python/timelog/__init__.py:635` (`views(self, t1=None, t2=None, *, kind="segment")`),
  `docs/python-api.md:160`.
- Classic speculative flexibility: a validation-only parameter whose sole job is rejecting
  everything except its default. If a second span source ever ships, re-adding a kwarg is a
  backward-compatible change — carrying it now buys nothing.
- **Loud flag**: documented public Python API (`views()`/`page_spans()` signature). Removal
  needs a deprecation story; that's why this is a lead, not a recommendation. The C-internal
  `PyPageSpanIter_Create(..., const char* kind)` parameter could be dropped independently of
  the Python surface (callers all pass "segment": py_iter.c:478, py_timelog.c:3547, 30+ test
  sites) but then the Python kwarg validation moves into py_timelog.c — a wash unless the
  Python kwarg goes too.

### F6. `PyPageSpanObjectsView_Create` re-validates its single caller
**Rung: 6 (one-liner)** · risk: low · est. −12 LOC

- The factory (`py_span_objects.c:29-42`) type-checks (`TlPyPageSpan_Check`) and re-checks
  `closed` under CS; its ONLY caller is `PyPageSpan_objects` (`py_span.c:374`), which already
  checked `closed` (+ the unreachable `h`) three lines earlier under the same CS discipline
  (py_span.c:358-372).
- Neither check is load-bearing for safety — every accessor on the view re-validates under CS
  (`getitem`, `length`, `copy`, iternext), and a close can slip in between the two checks
  today anyway. One fail-early check suffices; keep the factory's (it needs `mod_st` for the
  type lookup regardless) and delete the pre-check block in `objects()`, or vice versa.
- Well covered by existing tests (objects()-on-closed-span behavior is asserted in
  test_py_span.c and python tests).

### F7. Test failpoint stubs → `#define … NULL`
**Rung: 6 (one-liner)** · risk: low · est. −10 LOC

- `py_iter.c:72-82`: the non-test build defines two static always-0 functions whose addresses
  flow through the `test_fail_hook` function pointer in `pytimelogiter_step`
  (py_iter.c:303). GCC/Clang almost certainly constant-propagate this (static, two call
  sites), but `#define tl_py_iter_test_should_fail_iternext NULL` (and `_next_batch`) in the
  `#else` folds `test_fail_hook != NULL && …` at compile time **by construction** — simpler
  and guaranteed-zero-cost on the row-iteration path.

### F8. Boilerplate compression inside py_span.c
**Rung: 6 (one-liner) / 2 (already-in-this-codebase pattern)** · risk: low · est. −40 LOC

- **F8a**: `PyPageSpan_get_timestamps` (py_span.c:454-471) pre-checks `closed` and raises
  `ValueError("PageSpan is closed")` — but `PyMemoryView_FromObject` → `pagespan_getbuffer`
  raises the **byte-identical** exception (py_span.c:276-278); the code's own comment
  (468-469) concedes getbuffer "re-takes the CS and re-checks closed atomically." The getter
  collapses to `return PyMemoryView_FromObject((PyObject*)self);`. −10 LOC, zero behavior
  change, covered by existing closed-span tests.
- **F8b**: `PyPageSpan_get_start_ts` / `get_end_ts` (py_span.c:473-508) are identical modulo
  the field. The codebase already established the macro-getter idiom with
  `TL_PY_DEFINE_CLOSED_GETTER` (py_compat.h:232-241); a sibling
  `TL_PY_DEFINE_SPAN_TS_GETTER(Fn, field)` turns 36 lines into ~14. −20 LOC.
- **F8c**: three verbatim `__enter__` bodies (`return Py_NewRef(self)`: py_span.c:332-336,
  py_iter.c:348-352, py_span_iter.c:351-355). One shared
  `static inline PyObject* tl_py_enter(PyObject* self, PyObject* noargs)` in py_compat.h's
  "Shared object idioms" section replaces all three. −12 LOC. (`__exit__`/`close` bodies
  differ per type — PageSpan's close raises BufferError — so only `__enter__` is truly
  shareable; don't force the rest.)

### F9. `PyPageSpan_FromView` defensive checks for its single internal caller
**Rung: 1 (does-not-need-to-exist)** · risk: low · est. −15 LOC

- py_span.c:35-54: NULL-checks `view`, `view->owner`, `timelog`, plus a full
  `TlPy_StateFromObject` + `TlPyTimelog_Check` type check. The one caller
  (`py_span_iter.c:330`) passes a view freshly filled by `tl_pagespan_iter_next` (owner
  guaranteed by core contract, tl_pagespan_iter.h:169) and a timelog captured from a live
  PageSpanIter. The RuntimeError paths are unreachable; asserts express the contract at zero
  release cost. Keep `TlPy_StateFromObject` (needed for the type lookup); drop the rest.
- Runs once per span (~4K records), so the cycle cost was never the issue — the 20 lines of
  noise were.

### F10. Deprecated `PyErr_Fetch/Restore` where the codebase already has the modern macro
**Rung: 2 (already-in-this-codebase)** · risk: low · est. −12 LOC

- `py_module_state.h:30-33` defines `TL_PY_PRESERVE_EXC_BEGIN/END` on
  `PyErr_GetRaisedException/SetRaisedException` (noting "the modern raised-exception API is
  always available"), used by py_errors.c:93, module.c:141/186/332, py_timelog.c:1542.
- Four sites in this unit still hand-roll the 3-variable `PyErr_Fetch`/`PyErr_Restore` idiom
  (deprecated since 3.12): py_span.c:151-154, py_iter.c:165-180, py_span_iter.c:68-69+83,
  py_span_iter.c:234-237. Pure consistency/deprecation cleanup on cold cleanup paths.

---

## Prior-Art Leads (with honest fit notes)

1. **Lazy sequence iteration → CPython `PySeqIter` (platform, rung 4).** See F2. Fit:
   exact-semantics replacement (the type already raises IndexError past-the-end); MIT-question
   moot (it's the platform); TSan/FT story is CPython's own. Caveats: iterator type identity is
   observable (one subinterpreter test asserts the name); FT index races become
   benign-but-unsequenced instead of CS-serialized — consistent with the documented
   "NOT thread-safe" contract.
2. **Zero-copy array exposure → CPython buffer protocol (platform).** Already adopted — the
   PageSpan exporter is the idiomatic implementation. Alternatives
   (`PyMemoryView_FromMemory`) provide no exporter pinning and would break the
   BufferError-on-close contract (CLAUDE.md binding rule 16). No external library (stb/klib et
   al.) has anything to offer here; this sub-problem is CPython-specific. **Verdict lead: keep.**
3. **CPython extension-type boilerplate generators** (CPython Argument Clinic; nanobind/pybind11).
   Poor fit on hard constraints: Clinic is a CPython-internal tool not supported for
   out-of-tree stable use; nanobind/pybind11 are C++ (violates pure-C17 + MSVC /WX
   constraint). The right tool is what the codebase already does: small local macros
   (`TL_PY_GC_DEALLOC`, `TL_PY_DEFINE_CLOSED_GETTER`) plus longhand slots. **Verdict lead: no
   adoptable library; extend the local idioms (F8) instead.**
4. **Exception-state preservation → `PyErr_GetRaisedException` (platform, 3.12+).** Already
   wrapped in-codebase as `TL_PY_PRESERVE_EXC_*`; F10 is just finishing the migration.

---

## NO and NO (earns its keep — grounded)

- **N1. Triplicated detach-under-CS / release-outside-CS choreography** (py_iter.c:109-200,
  py_span.c:111-166, py_span_iter.c:208-254). Same *shape*, different payloads (5 resources vs
  owner+timelog vs iter+timelog) and different release orders (iter/snapshot before
  pins_exit/DECREF, py_iter.c:154-157). This pattern IS the hard invariant "no Py_DECREF,
  weakref callback… while ANY internal lock is held" (CLAUDE.md, Binding rules). A generic
  extraction needs void*-arrays or macro gymnastics that would obscure exactly the code paths
  the hostile concurrency reviews and the lab/TSan matrix have validated. Duplication here is
  cheaper than the wrong abstraction.
- **N2. Custom buffer exporter with an `exports` counter** (py_span.c:217-304). Required to
  implement "cannot close span while buffers are exported → BufferError" (py_span.c:320-323;
  CLAUDE.md pitfall 16). No platform shortcut exists: memoryview-from-pointer APIs don't pin,
  and the SECURITY comment (py_span.c:245-251) explains why `h[]` must never get a numeric
  buffer. Every line is doing contract work.
- **N3. The err-code-under-CS → raise-outside-CS pattern** (py_span.c:229-287,
  py_span_objects.c:122-162, 217-258). Verbose, yes — but it is the direct consequence of "no
  Python C-API that can fail/run Python under an internal lock". Table-driving the
  code→exception mapping would save ~10 lines and cost greppability of every message. Keep.
- **N4. 32-bit overflow guard in getbuffer** (py_span.c:238-241). Conditionally compiled only
  where reachable (`SIZE_MAX <= UINT32_MAX`); 4 lines; real. Keep.
- **N5. `next_batch` preallocation + closed fast-path** (py_iter.c:379-413). The fast-path
  looks redundant against `pytimelogiter_step`'s closed handling, but it prevents allocating an
  n-slot list (user-controlled n) for a closed iterator. The preallocate+trim strategy beats
  append-loops for the common full-batch case — this is the documented perf feature
  (BENCHMARK_REPORT.md: "next_batch() amortizes Python→C call overhead"). Keep.
- **N6. Longhand PyType_Spec/slots per type** (all four files). CPython convention; the
  registration side is already table-driven (module.c:73-95 + static assert). An X-macro over
  type specs would obscure per-type differences (buffer slots, sq_item, iternext) for ~0 net
  LOC. Keep.
- **N7. `TL_PY_OBJ_LOCK2` in objectsviewiter_next** (py_span_objects.c:220-241). While the
  custom iterator exists, the 2-object CS is the correct way to make index-advance atomic with
  span-state reads without lock-order issues. It only becomes deletable *via* F2.
- **N8. `copy_timestamps` vs `ObjectsView.copy` skeleton similarity** (py_span.c:377-435,
  py_span_objects.c:285-353). Same pin-owner/copy-loop shape, but different pinned pointers
  (ts vs h), different per-element ops (PyLong_FromLongLong vs decode+NewRef), different error
  sets, in different TUs. A shared helper needs a per-element callback (indirect call in an
  O(n) loop) or a macro. Cost exceeds benefit. Keep.
- **N9. Holding the per-object CS across `tl_iter_next` / `tl_pagespan_iter_next`**
  (py_iter.c:261-283, py_span_iter.c:300-314). Deliberate, documented carve-out
  (py_compat.h:141-145) closing the close-vs-next UAF window; do not "simplify" into
  snapshot-pointer-then-call — that reintroduces the exact TOCTOU class the v1.3 reviews
  caught.
- **N10. `PyPageSpan_get_last_ts` alias for `end_ts`** (py_span.c:510-513). 4 lines buying a
  documented public alias (docs list both). Keep.

---

## Test-Coverage Notes

- Well-covered (safe to refactor against): span close/exports/BufferError, objects() on closed
  span, iteration semantics, module init failpoints (test_py_span.c ~40 scenarios,
  test_py_iter.c incl. failpoint suites, test_py_module_exec.c, python/tests/*).
- **Zero coverage today** (all deletion candidates, or need tests if kept):
  `TimelogIter.view()` (F1), `h==NULL` paths (F3), decode-NULL paths (F3),
  `remaining_valid==0` paths (F4).
- F2 requires touching test_py_module_exec.c (state-slot assertions) and
  test_subinterpreters.py:201 (type-name probe).
