# Exportability: `to_numpy()` and `to_dict()` — Design

Date: 2026-07-10 · Branch: `feat/exportability` (off `audit/ponytail-simplification`)
Status: v2 — revised after hostile review (4 reviewers: 3× Claude + Codex CLI;
1 BLOCKER + 4 MAJOR confirmed and folded in below).

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
- `len(it)` — EXACT precomputed visible-row count for the iterator's snapshot.
  Hostile review attacked and confirmed exactness against unflushed memtable,
  OOO runs, tombstones, TL_TS_MIN/MAX, and concurrent writers
  (`tl_snapshot_count_range_internal` counts all components against the same
  tombstone skyline as the query filter; cross-validated by
  `func_count_cross_validate*` C tests). `Timelog.close()` raises while the
  iterator's pin is held, so the count cannot be invalidated mid-export.
- `itertools.islice` + `np.fromiter(..., count=k)` / `dict.update(pairs)` —
  bounded C-loop consumption of the iterator, **chunked**.

A C fill-into-buffer fast path (mirror of `bulk_append`) was evaluated and
rejected on measurement: fromiter costs ~74 ns/record best-case vs a 38 ns raw
iteration floor, and on OOO-ingested data the floor itself rises to
92–116 ns/record (heap-scattered payloads, many-L0 fan-in) — no C path
recovers that. Savings stay bounded ~2× on a one-shot export; not worth ~150
lines of critical-section C. The public signatures are implementation-agnostic;
the C path remains a drop-in upgrade if a real workload measures export as a
bottleneck.

### Chunked consumption (hostile-review fix, stability)

A monolithic `np.fromiter(it, count=n)` / `dict(it)` is a single
uninterruptible C call: it monopolizes the GIL for the whole export (measured
72 ms stall at 1M rows; ~4 s at 50M) — the same failure class as the
documented 461× ingest collapse in `pytimelog_make_iter`. Both methods
therefore consume the iterator in chunks of 65,536 records (~5 ms of work,
matching the GIL switch interval; eval-loop switch points run between chunks).
Measured: identical throughput (75.1 vs 74.5 ns/rec), max thread-scheduling
gap 5.3 ms vs 72 ms, transient memory 16 B/rec vs 32 B/rec. On free-threaded
builds the chunking is simply harmless.

## API contract

### `to_numpy(t1=None, t2=None, *, dtype=None) -> (timestamps, values)`

- Returns a tuple of two fresh, contiguous, C-owned 1-D arrays: `timestamps`
  is `int64`; `values` is `float64` unless `dtype` overrides it. Shape-
  compatible with `bulk_append(timestamps, objects)` (values come back as
  converted numbers, not the original objects).
- `dtype` must be a **scalar numeric dtype** (`np.dtype(dtype).kind` in
  `"iuf"`), else `TypeError`. This forecloses silent data mangling found in
  review: `dtype=str` → every value becomes `''`; `'U2'` → truncation;
  subarray dtypes → 2-D return. Conversion semantics within numeric dtypes are
  numpy's (e.g. `dtype=np.int64` floors floats) — documented, not re-validated.
- Bounds behave exactly like `log[t1:t2]` slicing: `None` = open end,
  reversed bounds yield empty arrays, half-open `[t1, t2)`. Consequence
  (review-confirmed, needs one docs line): a record AT `TL_TS_MAX` is included
  only via `t2=None`; no bounded `t2` can include it.
- Empty range → `(np.empty(0, int64), np.empty(0, dtype))`.
- Duplicate timestamps: all records are exported (multimap).
- Value conversion follows numpy: `bool` → 1.0/0.0, `None` → NaN under float
  dtypes (the ecosystem's missing-value convention; `np.float64(None)` is
  `nan`) and TypeError under integer dtypes. Default `float64` loses integer
  precision above 2^53 — documented; big-int users pass `dtype=np.int64`.
- Non-convertible value → the original exception propagates **unmodified in
  type and args**, with a row-index note attached via `exc.add_note(...)`
  (never `type(exc)(msg)` — crashes on subclasses with non-trivial
  constructors, e.g. `UnicodeDecodeError`). The note is attached only when
  `row = n - len(it) - 1 >= 0` and the iterator is still open (skips
  pre-consumption errors and "iterator too short" mislabeling). Catch net:
  `(TypeError, ValueError, OverflowError)` — `float(10**400)` raises
  OverflowError. `np.dtype(...)` construction happens OUTSIDE the try.
- The iterator is closed in `finally`; no snapshot pin outlives the call.
  During the call the export holds a reader pin, so a concurrent `close()`
  raises `TimelogError` until the export finishes (one docs sentence).
- numpy imported lazily inside the method; absence raises the stock
  `ImportError`. `to_dict` never touches numpy.
- Closed log → existing `TimelogError` from the query path.
- Snapshot isolation: the export sees exactly the records visible at call time.

### `to_dict(t1=None, t2=None) -> dict[int, object]`

- Chunked `d.update(islice(it, CHUNK))` loop over the same slice iterator
  (`while len(it):`), closed in `finally`. Values returned as-is (new refs).
- Duplicate timestamps collapse to ONE value: the last in iteration order.
  **Which record wins is unspecified** — deterministic for a given storage
  state, but NOT append order in general. Hostile review disproved the
  original newest-wins guarantee twice: (a) the OOO head sorts equal-ts
  records by `(ts, handle, seq)` — handle is a pointer, so OOO duplicates
  order by allocation address (`tl_recvec.c` `cmp_recseq_pair`); (b) the
  compaction merge primes L0 (newer) sources before L1 (older), physically
  re-baking equal-ts records newest-first, so the winner can CHANGE when a
  background compaction tick runs. Docs must say: needing a specific winner →
  avoid duplicate timestamps or use `point(ts)` and choose explicitly.
  `tl_merge_iter.h`'s tie-order disclaimer stays exactly as-is (v1 of this
  spec wanted to promote it to a guarantee — that would document a falsehood).
- Only failure modes: `MemoryError`, or `TimelogError` from the engine
  (review-confirmed: keys are C-built ints, items are C-built 2-tuples).

## Measured performance (restated as ranges — review finding)

| Scenario (1M records) | per-record |
|---|---|
| in-order, float payloads, 3.13 | ~74 ns |
| int payloads → float64 | ~98 ns |
| mixed float/int/bool | ~95 ns |
| 30% OOO ingest history (165 L0 segs) | 132–152 ns |
| same, after full compaction | ~110 ns |
| 3.14t free-threaded, in-order floats | ~89 ns |
| `to_dict`, in-order | 57–63 ns |

Raw iteration floor spans 29–116 ns/rec with data layout; GC pressure measured
nil. These are export-API numbers, not a regression gate.

## What was deliberately skipped (and when to add it)

- **C fill fast path** — only if a real workload measures export as a
  bottleneck (bounded ~2× and shrinking on OOO layouts).
- **Iterator-level `to_numpy`/`to_dict`**, **`to_pandas`**, **values-as-lists
  dict mode**, **structured-array return** — as v1, all cut.
- **Per-record ts error context** — wrapper generator kills the fast path;
  row index via `len(it)` arithmetic is free and review-verified exact.
- **Newest-wins duplicate guarantee** — requires C-core comparator + compaction
  ordering changes with their own hostile review; out of scope.

## Implementation plan

1. `python/timelog/__init__.py` — new "Export" section after `views()`:

   ```python
   _EXPORT_CHUNK = 65536   # ~5ms of fromiter work: bounds GIL monopolization

   def to_dict(self, t1=None, t2=None):
       it = _slice_to_iter(self, slice(t1, t2))
       try:
           d = {}
           while len(it):
               d.update(_islice(it, _EXPORT_CHUNK))
           return d
       finally:
           it.close()

   def to_numpy(self, t1=None, t2=None, *, dtype=None):
       import numpy as np
       value_dtype = np.dtype(np.float64 if dtype is None else dtype)
       if value_dtype.kind not in "iuf":
           raise TypeError(...)
       pair_dtype = np.dtype([("ts", np.int64), ("value", value_dtype)])
       it = _slice_to_iter(self, slice(t1, t2))
       try:
           n = len(it)
           ts = np.empty(n, np.int64)
           values = np.empty(n, value_dtype)
           pos = 0
           try:
               while pos < n:
                   k = min(_EXPORT_CHUNK, n - pos)
                   chunk = np.fromiter(_islice(it, k), dtype=pair_dtype, count=k)
                   ts[pos:pos + k] = chunk["ts"]
                   values[pos:pos + k] = chunk["value"]
                   pos += k
           except (TypeError, ValueError, OverflowError) as exc:
               row = n - len(it) - 1
               if row >= 0 and not it.closed:
                   exc.add_note(f"to_numpy(): raised while converting the "
                                f"value at row {row} of {n}")
               raise
           return ts, values
       finally:
           it.close()
   ```

2. `docs/python-api.md`: new "Export API" section (contracts above, incl.
   unspecified duplicate winner, TS_MAX-only-via-`t2=None`, 2^53 note,
   reader-pin duration, numpy optional).
3. `demo/ci/check_docs_consistency.py`: add `"to_dict", "to_numpy"` to
   `REQUIRED_PY_METHODS` so the documented surface is guarded.
4. `python/tests/test_export.py` (tests first — TDD):
   - to_dict: basic; one-sided/None/reversed/empty bounds; values arbitrary
     objects; closed log; tombstone filtering after delete; duplicate-ts:
     in-order memtable case (currently newest — asserted as "one of the
     appended values, exactly one key"), OOO duplicates (contract: one of
     them, deterministic per state), duplicates across flush + L1 re-bake via
     `maint_step()` loop (NOT bare `compact()` — review found it can no-op on
     many-L0 layouts; assert `stats()` L0/L1 actually changed).
   - to_numpy: basic int/float/bool payloads; dtype=int64 exact round-trip
     incl. >2^53; dtype guard rejects str/object/subarray/complex/datetime;
     empty + reversed bounds; TL_TS_MIN record; TL_TS_MAX record included via
     t2=None and excluded via t2=TL_TS_MAX; duplicates all exported;
     tombstone filtering; conversion failure at row 0 / mid / last row:
     original exception type + args preserved, note text has the right index,
     `__cause__` untouched, and `log.close()` succeeds right after (pin
     released); OverflowError path gets the note; non-pair-breaking values
     (None, str) raise; snapshot isolation vs concurrent append; chunk
     boundary correctness (n exactly at, one under, one over _EXPORT_CHUNK —
     use a shrunk chunk constant via monkeypatch to keep the test fast);
     numpy-blocked → ImportError (`sys.modules["numpy"] = None`), and to_dict
     still works with numpy blocked.
   - 1M-record smoke marked `@pytest.mark.stress`.
5. Validation: full pytest 3.13 + 3.14t (+ subinterp/freethreading legs),
   ASan ctest (no C changes, but run anyway), docs checker, lint, perf rerun
   of the benchmark table.

## Requirements traceability

| Owner requirement | Where satisfied |
|---|---|
| numpy export of (ts, number) | `to_numpy`, 74–152 ns/rec measured across layouts |
| dict export {ts: obj} | `to_dict`, 57–63 ns/rec |
| numpy optional | lazy import; binding untouched |
| absolute simplicity | ~45 facade lines, 0 new C code, 0 new deps |
| flawless stability | audited primitives only; pins released via finally; GIL stall bounded to ~5 ms by chunking; no new lock surface |
| flawless perf | chunking measured free (75.1 vs 74.5 ns/rec); C drop-in documented if ever needed |
