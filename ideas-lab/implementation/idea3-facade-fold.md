# Idea 3 — Fold facade `append` into C (DETAILED PLAN)

## Goal
Move the facade `append` override's logic into the C `append` method as `METH_FASTCALL|METH_KEYWORDS`,
eliminating the Python wrapper + its second Python→C transition. Measured potential 3.46× on the auto-ts
`append(obj)` path (exp06). **Zero behavior change** vs the current facade across all 3 signatures.

## Current facade override (the exact contract to preserve)
```python
def append(self, obj_or_ts, obj_or_none=_SENTINEL, *, ts=None):
    if obj_or_none is _SENTINEL:          # 1 positional
        obj = obj_or_ts
        ts = _now_ts(self.time_unit) if ts is None else _coerce_ts(ts)   # append(obj) | append(obj, ts=X)
    else:                                  # 2 positional
        ts = _coerce_ts(obj_or_ts); obj = obj_or_none                    # append(ts, obj) legacy
    self._check_min_ts(ts)                 # ValueError if ts < self._min_ts
    super().append(ts, obj)
```
- `_coerce_ts(x)`: `__index__`-coerce; **reject bool** → `TypeError("timestamp must be int (bool not allowed)")`;
  `OverflowError` if outside int64.
- `_now_ts(u)`: `time.time_ns() // {s:1e9, ms:1e6, us:1e3, ns:1}[u]`.
- `_check_min_ts(ts)`: `ValueError(f"timestamp {ts} is below min_ts boundary ({self._min_ts})")` if guarded.

## Design (narrow blast radius — do NOT touch extend's logic)
1. **C state gains `min_ts`**: add `int64_t min_ts; int has_min_ts;` to `PyTimelog`. A new
   `_set_min_ts(value_or_None)` C method (or reuse construction) lets the facade push it. The facade
   `__init__`/`reopen` already compute `min_ts_val`; they additionally call `self._set_min_ts(min_ts_val)`
   and **keep `self._min_ts` as a mirror** (so `extend`/`_coerce_and_guard`/slicing are UNCHANGED).
2. **C `append`** becomes `METH_FASTCALL|METH_KEYWORDS`, dispatching the 3 signatures:
   - `nargs==1, no kw` → `obj=args[0]`, `ts = clock_gettime(CLOCK_REALTIME)` scaled by `self->time_unit`.
   - `nargs==1, kw {"ts"}` → `obj=args[0]`, `ts = coerce(args[1])`.
   - `nargs==2, no kw` → `ts = coerce(args[0])`, `obj=args[1]`.
   - else → `TypeError` (mirror Python arity/kw errors).
   Then: if `has_min_ts && ts < min_ts` → `ValueError(...)`; INCREF obj; `tl_append`; existing
   `TL_EBUSY`/live-note/retired-drain path (byte-identical to today's C append body).
3. **Delete the facade `append` override** (and `_now_ts` becomes C-internal; keep the Python `_now_ts`
   only if still referenced — verify).
4. A C **`coerce_ts` helper** matching `_coerce_ts` EXACTLY: reject `PyBool_Check` →
   `TypeError("timestamp must be int (bool not allowed)")`; else `PyNumber_Index` then `PyLong_AsLongLong`
   (so `__index__` works and float/str raise); `OverflowError` on range. (This is STRICTER than idea-2's
   `tl_py_fast_i64` because append's ts rejects bool — they are deliberately different.)

## Auto-timestamp in C (must equal `_now_ts`)
`time.time_ns()` ≡ `clock_gettime(CLOCK_REALTIME)` → `sec*1e9 + nsec`. Divide by the unit divisor from
`self->time_unit` (TL_TIME_S/MS/US/NS → 1e9/1e6/1e3/1). Use integer floor division to match `//`.

## Risk surface (for hostile review)
1. **bool rejection** — `append(ts=True, obj)` and `append(True, obj)` must raise TypeError (facade
   `test_facade.py` pins `match="bool"`). The C coerce MUST reject bool; idea-2's helper does NOT — keep
   them separate.
2. **min_ts state sync** — `extend` and slicing still use `self._min_ts`; the C `min_ts` must be set
   wherever `self._min_ts` is (init + reopen). If they diverge, append vs extend disagree. Mirror, don't move.
3. **time_unit auto-ts parity** — integer floor-division must match `_now_ts`; monotonic-ish wall clock;
   `CLOCK_REALTIME` (not MONOTONIC) to match `time.time_ns()`.
4. **signature disambiguation** — every current call shape must map identically, incl. `append(obj, ts=X)`,
   `append()` (too few → TypeError), `append(a,b,c)` (too many → TypeError), `append(ts=X)` (no obj → TypeError),
   `append(obj, ts=X, foo=Y)` (unknown kw → TypeError).
5. **FT / borrowed args** — obj (args[0/1]) is INCREF'd before storage (as today); kwnames handling under
   FASTCALL|KEYWORDS (values are in args[nargs..]); no retained args pointer.
6. **the override removal** — the facade subclass `append` disappears; `super().append` callers inside the
   facade (extend? no — extend uses super().extend) — verify nothing else calls `self.append` expecting the
   Python wrapper. Auto-ts now happens in C, so any test mocking `_now_ts` or `time.time_ns` may break — check.
7. **`_mostly_ordered_default`** — append never used it (only extend); confirm no interaction.

## Test (regression catcher) — extend `test_fastcall_methods.py` / `test_facade.py`
All 3 signatures (results); bool rejected on both `append(True,o)` and `append(o,ts=True)`; auto-ts produces
a valid ms wall-clock ts and is monotonic-ish; `append(o, ts=X)` and `append(ts,o)` parity; min_ts guard
raises ValueError below boundary on append AND still on extend (sync); arity/unknown-kw → TypeError;
overflow → OverflowError; FT concurrency (append interleaved). Plus the existing 148 pytest (the facade
append tests are the strongest guard) and the C suite.

## Done = green
483 core · 9/9 ctest · 148+ pytest (all facade append tests) · ASan/UBSan binding · auto-ts microbench
shows ~3× on `append(obj)`. Commit `feat(bindings): fold facade append (3 signatures + auto-ts) into C`.

---
## v2 — DECISION after 2 hostile plan reviews (both recommended against the naive full fold)
Full fold (to capture the real 3.46×; the narrow `append2` shim recovers only ~10%), but with every
blocker fixed:
- **BLOCKER-1 (tests-first):** ✅ DONE — `test_append_contract.py` (19 tests) characterizes the current
  facade and passes; it is the regression net the fold must keep green.
- **BLOCKER-2 (name collision):** C field named `min_ts_floor` (NOT `min_ts`; that public method returns
  the engine's smallest ts — unrelated).
- **Single source of truth for the floor:** C owns `min_ts_floor`; the facade `_min_ts` becomes a
  read-only **property** reading from C, so `_check_min_ts`/`extend`/`__setitem__`/slicing readers are
  UNCHANGED (narrow blast radius). `__init__`/`reopen` call `_set_min_ts_floor`. Reset in `PyTimelog_init`
  so reopen can't leak a stale floor.
- **OverflowError message parity:** the C coerce does its own range check + `PyErr_Format` matching
  `_coerce_ts`'s exact text; ValueError floor message matches `_check_min_ts` exactly.
- **Auto-ts:** portable `timespec_get(TIME_UTC)` (Windows-safe) → integer `1000000000LL` arithmetic →
  `// divisor[self->time_unit]` (matches `time.time_ns()//div`; wall clock is non-negative so floor==trunc).
- **__setitem__ double-coerce:** `__setitem__` still calls `super().append(ts,obj)` → the 2-positional C
  path re-coerces an already-int (cheap) and re-checks the floor (now single-source, can't diverge). Accept.

### Implementation order (each step independently green)
- **Step A:** C `min_ts_floor` state + `_set_min_ts_floor`/`_min_ts_floor` + facade `_min_ts` property;
  append override UNCHANGED. Gate: 19 + 148 pytest green (pure state migration, behavior identical).
- **Step B:** C `append` FASTCALL|KEYWORDS fold (3 sigs + coerce + auto-ts + floor check) + delete the
  facade override. Gate: 19 + 148 pytest, ASan binding, auto-ts microbench ~3×.
