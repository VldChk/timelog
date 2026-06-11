# Idea 2 — METH_FASTCALL across all positional query/delete methods (DETAILED PLAN)

## Goal
Convert the 9 positional `METH_VARARGS`+`PyArg_ParseTuple` methods to `METH_FASTCALL` (no args-tuple
allocation, no tuple parse), measured −15…−24% per call on the binding boundary. `append` is **excluded**
(handled by idea 3's facade-fold with keywords). Zero behavior change except the (intended) absence of an
allocated args tuple.

## Methods in scope (all pure-positional, no keywords)
| Method | args | def line | parse |
|--------|------|----------|-------|
| `point` | 1×int64 | 2681 | `"L"` |
| `since` | 1×int64 | 2609 | `"L"` |
| `until` | 1×int64 | 2629 | `"L"` |
| `equal` | 1×int64 | 2660 | `"L"` |
| `next_ts` | 1×int64 | (fwd 48) | `"L"` |
| `prev_ts` | 1×int64 | (fwd 49) | `"L"` |
| `delete_before` | 1×int64 | 1917 | `"L"` |
| `range` | 2×int64 | 2584 | `"LL"` |
| `delete_range` | 2×int64 | 1881 | `"LL"` |

## Transform
Signature `(PyTimelog* self, PyObject* args)` → `(PyTimelog* self, PyObject *const *args, Py_ssize_t nargs)`.
Centralize int64 extraction in ONE helper so the `"L"`-equivalence rule lives in one place:
```c
/* Match PyArg_ParseTuple "L": accept int and __index__-able objects, reject float/str.
 * PyLong_AsLongLong already: rejects float (TypeError), accepts exact int, and on
 * non-int calls __index__ via the number protocol. Returns -1 with exc set on error. */
static int tl_py_fast_i64(PyObject* o, long long* out) {
    long long v = PyLong_AsLongLong(o);
    if (v == -1 && PyErr_Occurred()) return -1;
    *out = v;
    return 0;
}
```
Per method (1-arg example):
```c
if (nargs != 1) { PyErr_Format(PyExc_TypeError, "<name>() takes exactly 1 argument (%zd given)", nargs); return NULL; }
long long ts_ll; if (tl_py_fast_i64(args[0], &ts_ll) < 0) return NULL;
/* ... unchanged: tl_py_validate_ts(ts_ll, ...) + engine call ... */
```
Method table: each `METH_VARARGS` → `METH_FASTCALL`, cast `(PyCFunction)(void(*)(void))`. Update the two
forward declarations (next_ts/prev_ts) to the FASTCALL signature.

## Correctness / parity argument
- The body after parsing is **unchanged** (same `tl_py_validate_ts`, same engine call, same return).
- The only externally-visible deltas: (a) no per-call args tuple is built (the win), (b) arity/type errors
  now come from my explicit checks + `PyLong_AsLongLong` instead of `PyArg_ParseTuple`. The error *type*
  is identical (`TypeError`); the *message* text differs slightly.
- FT/subinterp: `args[]` are borrowed and only read during the call; none of these methods store an arg.
  No new state. Safe on 3.14t and subinterpreters (same contract validated for append in exp01).
- The Python **facade** wraps these (coerces ts via `_coerce_ts`) and calls `super().range(t1,t2)` etc.
  positionally — unaffected by the C calling convention.

## Risks & mitigations
1. **Error-message/text dependency** — if any test asserts the exact `PyArg_ParseTuple` message text, it
   breaks. Mitigation: grep tests for message assertions; keep messages close to CPython's wording; the
   facade tests assert `TypeError` *type*, not text (verify).
2. **`"L"` vs `PyLong_AsLongLong` edge cases** — float (both reject), `__index__` objects (both accept via
   number protocol), huge int (both `OverflowError`). Mitigation: a behavioral-parity test that drives each
   method on the **raw C type** with: valid int, float (→TypeError), non-numeric (→TypeError), wrong arity
   (→TypeError), `2**63` overflow (→OverflowError), and a `__index__` object — comparing raw-C-type behavior
   conceptually to the documented `"L"` contract. (Recorded in the test, see below.)
3. **`equal`/`point` returning iterators** — converting the entry doesn't change the returned object; verify.

## Test (regression catcher)
Extend `python/tests/` with `test_fastcall_methods.py`: for each of the 9 methods, on BOTH the facade and
the raw `timelog._timelog.Timelog`, assert: correct results vs a small known dataset; `TypeError` on wrong
arity and on non-int/float/string arg; `OverflowError` on `2**63`; and that an `__index__` object is
accepted identically to its int value. Plus the existing 98 pytest + 480 core (the C methods are exercised
by facade tests). Perf: re-run the per-call microbench (point/next_ts) to confirm the −15% win, no regression.

## Done = green
483 core · 9/9 ctest · 98 pytest + new fastcall test · ASan/UBSan clean · per-call microbench shows the win.
Commit `feat(bindings): METH_FASTCALL for positional query/delete methods`.

---
## v2 — REVISED after 2 hostile plan reviews (both empirical). No happy-path/parity blocker
(`PyLong_AsLongLong` ≡ `"L"` verified byte-identical incl. message text on 3.12+, since both are
`__index__`-based since 3.10). But two real BLOCKERS + test gaps to fix:

### B-1 (CRITICAL) — preserve each method's `CHECK_CLOSED`-vs-parse ORDER; do NOT add/move it
Two existing orderings must be kept exactly:
- **Iterator methods** `point, equal, range, since, until`: **parse FIRST**; `CHECK_CLOSED` lives *inside*
  `pytimelog_make_iter`. On a closed log + bad arg the **arg error wins**. → My edits must NOT add a
  top-level `CHECK_CLOSED` to these.
- **`delete_range, delete_before, next_ts, prev_ts`**: `CHECK_CLOSED` is **first**, before parse. On a
  closed log + bad arg, **"closed" wins**. → Keep it first.
Implementation rule: **edit only the signature + the parse block in place; leave `CHECK_CLOSED` exactly
where it is.** Add a test for the closed×bad-arg cross-product to lock this contract.

### B-2 — normalize arity with `PyVectorcall_NARGS`
`Py_ssize_t n = PyVectorcall_NARGS(nargs); if (n != 1) {…}` (canonical; strips a possible
`PY_VECTORCALL_ARGUMENTS_OFFSET` bit). `args` is then indexable `[0,n)`; never touch `args[-1]`.

### Helper rationale fix + floor
`PyLong_AsLongLong` is `__index__`-based since CPython 3.10; `"L"` likewise. requires-python ≥3.12 clears
this comfortably. No `PyNumber_Index` needed (verified a no-op). Drop the "messages match CPython" claim —
keep clear `<name>()`-prefixed messages; no test pins the text.

### Test additions (the gates that catch the above)
- **closed×bad-arg ordering** per method class (B-1 contract).
- **keyword rejection**: `point(t=5)` etc. → `TypeError` (now enforced by the interpreter, not the body).
- **bool asymmetry** (DO NOT get this wrong): raw `timelog._timelog.Timelog` **accepts** `True→1`; the
  **facade rejects** bool (`_coerce_ts`). Test must assert each layer's actual behavior.
- **FT concurrency** (`python/tests`, marked `freethreading`): N threads hammering the 9 converted methods
  — especially `delete_range`/`delete_before` interleaved with `append` — under 3.14t; assert no crash/leak.
- **`__index__`/float/str/overflow parity** on the raw C type.
