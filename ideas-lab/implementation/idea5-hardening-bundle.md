# Idea 5 — Cheap hardening / docs bundle (DETAILED PLAN)

## Goal
Lock in five already-justified safety/precision properties so they can't silently regress, and sharpen the
positioning docs. **Mostly preventive: comments + regression tests + a small docs edit.** Almost no behavior
change (the engine already has the right behavior for 4 of 5; we add guards/tests that catch a future
regression). Verified current state below.

## The five sub-items + current state (verified)
1. **Do NOT wire `tp_vectorcall` on the heap types.** *State:* `PyTimelog_slots` / `PyPageSpan_slots`
   (py_timelog.c:3213, py_span.c:550) contain no `Py_tp_call` or vectorcall slot — instances are not
   callable. The idea-2 METH_FASTCALL work is per-*method* vectorcall (correct), not type-level.
   *Risk it guards:* a future "optimization" wiring `tp_vectorcall`/`tp_call` on a heap type (vectorcall
   offset + heap-type lifetime hazards, and Timelog/PageSpan are not callable objects). *Deliverable:*
   a guard comment at both slot tables + a regression test asserting instances are not callable.
2. **Never export encoded `h[]` handles as numeric zero-copy.** *State:* `pagespan_getbuffer`
   (py_span.c:217) sets `view->buf = ts` only (int64 timestamps); `h[]` (encoded `PyObject*`) is used solely
   to *decode objects* (`PageSpanObjectsView` returns real Python objects, never raw handles). *Risk it
   guards:* exposing `h[]` as a numeric buffer would leak/forge raw pointers (UAF / pointer disclosure).
   *Deliverable:* a guard comment at getbuffer + a regression test that the only buffer is int64 `ts`, its
   byte length is `len*8`, and there is no path yielding `h[]` as numeric data (objects view yields objects).
3. **PEP 688 facade Buffer annotation/test.** *State:* PageSpan is a C type with `bf_getbuffer`; CPython
   ≥3.12 (we require ≥3.12) recognizes it as a virtual subclass of `collections.abc.Buffer` via the PEP 688
   subclasshook — but there is no test pinning it and no annotation note. *Deliverable:* a test asserting
   `isinstance(span, collections.abc.Buffer)` and that `memoryview(span)` works; a one-line note in the
   PageSpan facade docstring that it satisfies the PEP 688 buffer protocol (int64 timestamps).
4. **Free-threaded "GIL stayed disabled" import check.** *State:* ALREADY implemented — packaging-pr.yml
   step "Verify Py_mod_gil declaration honored" imports the installed wheel and asserts
   `sys._is_gil_enabled() is False` before+after import (cp314t); test_free_threading.py does the dev-build
   equivalent (lines 32-60). *Deliverable:* VERIFY only (re-run test_free_threading on 3.14t). If the wheel
   matrix includes cp313t without the GIL gate, extend the gate to it (check `packaging-pr.yml` matrix); else
   no code. Do not add redundant checks.
5. **Positioning precision.** *State:* what-is-timelog.md / README do not over-claim ("fastest"/"outperform"
   absent), but the positive wedge is understated. *Deliverable:* sharpen what-is-timelog.md (and the README
   one-liner if needed) to state the precise differentiators — **O(1) out-of-order append + snapshot-safe
   concurrent reads over live Python objects** — and add an explicit "not positioned as the fastest static
   range-query index" note so the precise claim is durable.

## Files
- `bindings/cpython/src/py_timelog.c` (~3213) and `bindings/cpython/src/py_span.c` (~550): guard comment at
  the slot tables (item 1). `py_span.c` getbuffer (~217): guard comment (item 2).
- `python/timelog/__init__.py`: one-line PEP 688 note in the PageSpan docstring (item 3).
- `python/tests/test_hardening.py` (NEW): items 1, 2, 3 regression tests (+ a local FT-import sanity that
  no-ops off free-threaded builds, reusing the conftest gil-probe pattern — item 4 dev-level).
- `docs/what-is-timelog.md` (+ maybe `README.md`): positioning sharpening (item 5).
- *(maybe)* `.github/workflows/packaging-pr.yml`: extend the GIL gate to cp313t **iff** that tag is in the
  wheel matrix and currently ungated (item 4).

## Tests (the regression net)
`python/tests/test_hardening.py`:
- `test_timelog_not_callable` / `test_pagespan_not_callable`: `assert not callable(instance)` (item 1).
- `test_pagespan_buffer_is_int64_ts_only`: `mv = memoryview(span); assert mv.format in ("q","l"); assert
  mv.itemsize == 8; assert mv.nbytes == len(span)*8` and the values equal the timestamps (item 2).
- `test_no_numeric_handle_export`: the objects view yields Python objects (not ints/handles); there is no
  public attribute/method returning `h[]` as a buffer/memoryview (item 2).
- `test_pagespan_is_pep688_buffer`: `isinstance(span, collections.abc.Buffer)` and `memoryview(span)` works
  (item 3).
- `test_import_keeps_gil_disabled`: on a free-threaded host (else skip), re-import timelog and assert
  `sys._is_gil_enabled()` stays False (item 4 dev-level mirror of the wheel CI check).

## Risk surface (for hostile plan review)
1. **`callable()` is a sufficient probe for "no tp_vectorcall"?** tp_vectorcall requires tp_call to be set;
   with neither set, `callable()` is False. A reviewer should confirm this is a faithful guard (or propose a
   stronger probe, e.g. checking `Py_TPFLAGS_HAVE_VECTORCALL` is clear).
2. **Buffer format char portability** — int64 may surface as `'q'` or `'l'` depending on platform/typestr;
   the test must accept both (or assert itemsize==8 instead of an exact format char).
3. **PEP 688 subclasshook reality** — confirm `collections.abc.Buffer` exists on 3.12+ and that a C type
   with only `bf_getbuffer` (no Python `__buffer__`) is actually recognized; if NOT auto-recognized, the
   deliverable becomes an explicit `Buffer.register(PageSpan)` (decide which).
4. **h[] disclosure completeness** — is `ts` truly the ONLY buffer-exporting surface? Are there other C types
   (PageSpanObjectsView/Iter) with a `bf_getbuffer`? The test/guard must cover every buffer exporter, not
   just PageSpan.
5. **Over-narrowing the positioning** — the sharpened wedge must stay accurate (it IS good at range scans;
   the point is it's not *positioned* as the fastest static range index, not that it's slow). Don't introduce
   a new inaccurate claim.
6. **Item 4 redundancy** — adding a dev-level FT import test must not duplicate test_free_threading.py to the
   point of noise; justify it as the per-suite local guard or fold into the existing test.
7. **No behavior regression** — items 1,2,4 add only comments/tests; item 3 adds a docstring line + test;
   item 5 is docs. Core/ctest/pytest counts: core/ctest unchanged, pytest grows by the new tests only.

## Gate
- 483 core · 9/9 ctest · (169 + new) pytest green on 3.13.
- ASan binding suite green (comments don't change codegen, but rebuild + run to be safe).
- 3.14t: test_hardening + test_free_threading green (item 4 verification).
- check_docs_consistency.py + check_layer_a_static.py + `git diff --check` green (item 5 docs).
- Every new test asserts a property that currently HOLDS (they pass on first run = they pin real behavior).

## Done = green
All five properties pinned by passing tests / sharpened docs, full gate green. Commit
`test+docs: lock in hardening guards (vectorcall, h[] non-export, PEP 688, FT-GIL) + sharpen positioning`.

---
## v2 — CORRECTIONS after 2 hostile plan reviews (both empirically verified against the staged .so)

- **Item 1 (MAJOR): `callable()` is insufficient.** `PyCallable_Check` reads only `tp_call`; a half-wired
  `tp_vectorcall_offset` without `tp_call` would pass `callable()==False`. **Load-bearing probe = the
  `Py_TPFLAGS_HAVE_VECTORCALL` (1<<11) bit must be clear** on the C types; keep `not callable()` as a
  secondary check. Test the **raw C types** (`timelog._timelog.{Timelog,TimelogIter,PageSpan,PageSpanIter,
  PageSpanObjectsView}`), since `Timelog` is `BASETYPE` (a Python subclass adding `__call__` is the user's
  choice, not a binding regression). Guard comment states the invariant is "binding wires no tp_call/
  vectorcall," not "no subclass is callable."
- **Item 2 (MINOR): assert read-only + concrete negative.** Add `memoryview(span).readonly is True` and
  `pytest.raises((TypeError, BufferError))` on a write. Replace the prose "no h[] export" with a STRUCTURAL
  assertion: `{T for T in public_types if issubclass(T, collections.abc.Buffer)} == {PageSpan}` — so any
  future type that grows a buffer slot trips the test. (Verified: `Py_bf_getbuffer` exists in exactly one
  slot table, py_span.c:562; objects view decodes to real PyObjects, never the uint64 handle.)
- **Item 3 (MAJOR): relocate the PEP 688 note.** PageSpan is a C re-export; its docstring is the C
  `Py_tp_doc` (py_span.c:551), NOT a Python docstring in `__init__.py`. Add the note there (rebuild).
  Drop the `Buffer.register` fallback — `isinstance(span, collections.abc.Buffer)` is already True on ≥3.12
  via the subclasshook (empirically confirmed). Keep the isinstance + `memoryview(span)` test.
- **Item 4 (MINOR): no cp313t gap (confirmed) → verify only; delete the in-process mirror test.** cp313t is
  intentionally not built (pyproject.toml: "3.13t intentionally omitted"); the only FT wheel (cp314t) is
  fully gated by packaging-pr.yml's "Verify Py_mod_gil declaration honored" step. A re-`import timelog` in
  the SAME process is a tautology (module init is cached). So DROP `test_import_keeps_gil_disabled`; the
  real guard is the existing subprocess `test_free_threading.py::test_import_does_not_enable_gil` — just run
  it on 3.14t. **Known gap (record, not fix):** the Py_mod_gil declaration is verified on the wheel path but
  NOT the sdist build path (only `twine check` runs there). Low risk (the declaration lives in module.c
  source, identical in both builds); note it, leave a CI sdist-import-GIL check as future work.
- **Item 4 format (MINOR): assert `format == "q"`** exactly (PAGESPAN_TS_FORMAT is hardcoded "q"); the
  `in ("q","l")` branch is dead and weakens the guard.
- **Item 5 (MINOR): "not *positioned as* the fastest static range-query index"** — phrase about positioning,
  not slowness (range scans are strong: README B4 ≈ 18M rec/s). No superlatives exist to remove anywhere
  (verified what-is-timelog.md / README / docs/index.md / performance.md); this is pure under-statement.
- **No dropped sub-item** (both reviewers confirmed all 5 map to deliverables).

### Net implementation set
Comments: py_timelog.c + py_span.c slot tables (item 1), py_span.c getbuffer (item 2), py_span.c `Py_tp_doc`
PEP 688 note (item 3). Tests: NEW `python/tests/test_hardening.py` with the HAVE_VECTORCALL flag check +
callable secondary (1), the read-only/format/structural-buffer assertions (2), the PEP 688 isinstance (3) —
NO in-process GIL mirror (4). Docs: what-is-timelog.md wedge sharpening (5). Rebuild (Py_tp_doc changed).
