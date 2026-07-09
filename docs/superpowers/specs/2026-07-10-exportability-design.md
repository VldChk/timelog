# Exportability: `to_numpy()` and `to_dict()` — Design

Date: 2026-07-10 · Branch: `feat/exportability` (off `audit/ponytail-simplification`)
Status: council-reviewed design (4 advisors: 3× Claude + Codex CLI; split decision
resolved by measurement).

## Goal

Two export APIs on `Timelog`:

1. `to_numpy(t1=None, t2=None, *, dtype=None)` — export `(ts, number)` records
   as a pair of numpy arrays.
2. `to_dict(t1=None, t2=None)` — export records as `{ts: obj}`.

Hard constraints: absolute simplicity (ponytail), flawless perf and stability,
numpy stays an optional dependency (the C binding remains numpy-free).

## Decision: pure facade, zero C changes

Both methods live in `python/timelog/__init__.py` and compose existing,
already-audited primitives:

- `_slice_to_iter(self, slice(t1, t2))` — bound handling (`None` = open end),
  timestamp coercion, snapshot-isolated single-use `TimelogIter`.
- `len(it)` — EXACT precomputed visible-row count for the iterator's snapshot
  (tombstone-aware, computed via `tl_snapshot_count_range` at creation).
- `dict(pairs)` / `np.fromiter(pairs, structured_dtype, count=n)` — C-loop
  consumption of the iterator.

A C fill-into-buffer fast path (mirror of `bulk_append`) was evaluated and
rejected on measurement: `np.fromiter` with exact `count` runs at ~74 ns/record
(71 ms / 1M records; raw iteration floor is 38 ns/record), so the C path could
at best save ~40 ms on a 1M-row one-shot export while adding ~150 lines of
critical-section C. The public signatures are implementation-agnostic; the C
path remains a drop-in upgrade if a real workload ever measures export as a
bottleneck.

## API contract

### `to_numpy(t1=None, t2=None, *, dtype=None) -> (timestamps, values)`

- Returns a tuple of two fresh, contiguous, C-owned 1-D arrays:
  `timestamps` is `int64`; `values` is `float64` unless `dtype` overrides it
  (any numpy dtype-like; conversion and conversion errors are numpy's,
  as if by `float(x)` for the default). Mirrors `bulk_append(timestamps,
  objects)` — round-trip symmetric.
- Bounds behave exactly like `log[t1:t2]` slicing: `None` = open end,
  reversed bounds yield empty arrays (sequence semantics), half-open `[t1, t2)`.
- Empty range → `(np.empty(0, int64), np.empty(0, dtype))`, never None/raise.
- Duplicate timestamps: all records are exported (it is a multimap).
- `bool` values convert to 1.0/0.0 (they are payloads; the key-side bool
  rejection in `_coerce_ts` applies to timestamps only).
- Default `float64` loses integer precision above 2^53 — documented; users
  with big-int payloads pass `dtype=np.int64`.
- Non-convertible value → numpy's `TypeError`/`ValueError`, re-raised with the
  failing row index (derived from the exact count minus `len(it)` remaining —
  no per-record wrapper, hot path untouched). The iterator is closed in
  `finally`, so no snapshot pin leaks and `close()` works immediately after.
- numpy imported lazily inside the method; absence raises the stock
  `ModuleNotFoundError` (the method is named `to_numpy` — no wrapper needed).
  `to_dict` never touches numpy.
- Closed log → existing `TimelogError` from the query path (zero new code).
- Snapshot isolation: the export sees exactly the records visible when the
  method was called; concurrent writes don't tear it.

### `to_dict(t1=None, t2=None) -> dict[int, object]`

- `dict(pairs)` over the same slice iterator, closed in `finally`.
- Duplicate timestamps: **last wins = newest append**. Verified twice:
  empirically (memtable-only and across flushed levels) and in code
  (`tl_heap.c` pops lower `tie_break_key` first; `tl_plan.c` assigns newer
  sources higher keys, so equal-ts records yield oldest→newest).
  `core/src/query/tl_merge_iter.h` currently disclaims equal-ts yield order as
  non-public; this design promotes that single line to a documented guarantee
  ("equal-ts yield order is oldest→newest") since `to_dict` now depends on it.
- Values are arbitrary Python objects, returned as-is (no copies, new refs).

## What was deliberately skipped (and when to add it)

- **C fill fast path (approach B)** — add behind the identical signature only
  if a real workload measures export as a bottleneck. (~2x at best.)
- **Iterator-level `to_numpy`/`to_dict`** — users holding an iterator can
  already `dict(it)` / `np.fromiter(it, ...)`; two spellings is surface bloat.
- **`to_pandas`** — `pd.Series(vals, index=ts)` is the user's one-liner;
  say so in the docstring and stop.
- **Values-as-lists dict mode / raise-on-duplicate** — value-type instability
  on a data property / hostile to legal multimap use.
- **Structured-array return** — strided field views, second-class interop.
- **Per-record ts error context** — requires a wrapping generator that kills
  the fromiter fast path; row index (free) is enough.

## Implementation plan

1. `python/timelog/__init__.py`: add `to_numpy` (~20 lines incl. docstring)
   and `to_dict` (~10 lines) in a new "Export" section after `views()`.
   Implementation sketch:

   ```python
   def to_dict(self, t1=None, t2=None):
       it = _slice_to_iter(self, slice(t1, t2))
       try:
           return dict(it)
       finally:
           it.close()

   def to_numpy(self, t1=None, t2=None, *, dtype=None):
       import numpy as np
       value_dtype = np.dtype(np.float64 if dtype is None else dtype)
       it = _slice_to_iter(self, slice(t1, t2))
       try:
           n = len(it)
           try:
               arr = np.fromiter(
                   it, dtype=np.dtype([("ts", np.int64), ("value", value_dtype)]),
                   count=n)
           except (TypeError, ValueError) as exc:
               row = n - len(it) - 1   # rows consumed before the failure
               raise type(exc)(
                   f"to_numpy() could not convert the value at row {row}: {exc}"
               ) from exc
           return arr["ts"].copy(), arr["value"].copy()
       finally:
           it.close()
   ```

2. `core/src/query/tl_merge_iter.h`: flip the tie-order disclaimer comment to
   the documented oldest→newest guarantee (comment-only change).
3. `docs/python-api.md`: new "Export API" section (methods, contracts:
   last-wins=newest, float64/2^53 note, bounds-as-slice, optional numpy).
4. `python/tests/test_export.py`: one pytest file covering: basic both
   methods; None/one-sided/reversed/empty bounds; duplicate-ts (last-wins
   newest, cross-flush; to_numpy keeps all); tombstone filtering after
   delete; value types (int/float/bool/numpy scalars); dtype=int64 exact
   round-trip incl. >2^53; non-numeric raises with row index and iterator
   is released (close() succeeds right after); NaN/inf; TL_TS_MIN/TL_TS_MAX
   timestamps; closed log raises; snapshot isolation vs concurrent append;
   numpy-absent ImportError (via `sys.modules["numpy"] = None` monkeypatch);
   1M-record smoke with throughput printout.
5. Validation: full pytest 3.13 + 3.14t, C tests untouched (comment-only C
   change) but ASan ctest run anyway, docs checker
   (`demo/ci/check_docs_consistency.py`), lint. Perf: rerun the 1M benchmark
   and record numbers in the PR body.

## Requirements traceability

| Owner requirement | Where satisfied |
|---|---|
| numpy export of (ts, number) | `to_numpy`, measured 74 ns/rec @ 1M |
| dict export {ts: obj} | `to_dict`, 57-63 ms @ 1M |
| numpy optional | lazy import; binding untouched |
| absolute simplicity | ~30 facade lines, 0 new C code, 0 new deps |
| flawless stability | composes only already-audited primitives; no new lock surface; pins released via finally |
| flawless perf | 74 ns/rec export ≈ 13.5M rec/s; C drop-in documented if ever needed |
