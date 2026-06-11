# exp01 — METH_FASTCALL for `append` (idea N1/T1.1, my discovery N28)

**Hypothesis:** Converting the `append(ts, obj)` hot method from `METH_VARARGS`+`PyArg_ParseTuple`
to `METH_FASTCALL` eliminates the per-call args-tuple allocation and shaves measurable ns/call.

**Change:** `bindings/cpython/src/py_timelog.c` — `PyTimelog_append` signature →
`(PyTimelog*, PyObject *const *args, Py_ssize_t nargs)`, manual `nargs`/`PyLong_AsLongLong` parse,
method-table flag `METH_VARARGS`→`METH_FASTCALL` with the `(PyCFunction)(void(*)(void))` cast.
**13 insertions, 5 deletions** (`append-fastcall.patch`). Engine logic byte-for-byte unchanged.

## Measurement (Release, Python 3.13, pinned core, median of 5)

| Op | Baseline (VARARGS) | exp01 (FASTCALL) | Δ |
|----|--------------------|------------------|---|
| `append(ts,obj)` raw C | 125.8 ns | **95.0 ns** | **−30.8 ns / −24.5%** |
| `point(ts)` raw C *(control, unchanged)* | 372.7 ns | 362.3 ns | ~noise |
| `append(obj,ts=)` facade end-to-end | 307.1 ns | 266.8 ns | −40.3 ns / −13% |

The unchanged `point` control staying flat confirms the delta is the append calling convention,
not measurement drift.

## Cross-check vs literature (research strand 1)
- Stinner (CPython): `struct.pack("i",1)` 119→76.8 ns (1.56×, −42 ns) purely from FASTCALL.
- PyTorch #49476: ~15 ns/call saved. rogerbinns: up to 7× for kwargs-heavy methods.
- Predicted range for a 2-positional method: **15–45 ns saved**. **Measured 30.8 ns — dead-center.**

## Correctness
- Error-path smoke: arity (0/1/3 args) → `TypeError`; non-int ts → `TypeError`; huge ts → `OverflowError`. All correct.
- Full facade suite: **98 passed, 16 skipped** — identical to baseline. Zero regressions.
- Free-threading safety (research-confirmed): the FASTCALL `args[]` are borrowed and only read during
  the call; `append` already `Py_INCREF`s `obj` before storing the handle → safe on 3.14t and subinterpreters.

## Verdict: 🟩 LOW-HANGING FRUIT
~6 effective LOC for a 24.5% raw-append speedup, zero risk, zero regressions, stable-ABI since 3.7.
**Generalizes** to 9 more positional-only methods (range/since/until/point/equal/next_ts/prev_ts/
delete_range/delete_before) — expected *largest relative* win on the 1-int methods where parse cost
dominates. Next step (N28): fold the facade's 3 signatures into `METH_FASTCALL|METH_KEYWORDS` in C and
delete the Python override — the facade wrapper measured **~181 ns**, larger than the entire C call, so
end-to-end `append` could go 307→~110 ns (~2.8×).

**Productionization gate before merge:** rebuild under ASan/UBSan + 3.14t functional + the lab differential
suite (per the project's zero-regression matrix); apply the same pattern to the other 9 methods in one PR.
