# exp06 — Fold the facade `append` into C (idea N28 ★, my measured discovery)

**Hypothesis:** the Python facade `append` override costs more than the C call it wraps. exp01 *measured*
the wrapper at ~181 ns (keyword-ts path). Doing the auto-timestamp + insert entirely in C should reclaim it.

**Why the facade is slow:** `timelog.Timelog.append(obj)` is a Python method that (1) dispatches through
the subclass, (2) checks a sentinel + branches on signature, (3) calls `_now_ts()` → **`time.time_ns()`
(a full Python→C transition)** + a division, (4) runs `_check_min_ts`, then (5) calls
`super().append(ts, obj)` — **a second Python→C transition**. Two boundary crossings + Python logic per
append.

**Change (MVP, `append-now-and-fastcall.patch`):** add a C `append_now(obj)` method (`METH_O`, no args
tuple) that reads the wall clock via `clock_gettime(CLOCK_REALTIME)` and inserts in **one** C call.
(MVP assumes `ms` time_unit; a production version reads the configured unit and folds all 3 signatures
into `METH_FASTCALL|METH_KEYWORDS`, deleting the Python override.)

## Measurement (Release, 3.13, pinned core, same build)

| Path | ns/append |
|------|-----------|
| facade `append(obj)` — Python wrapper + 2 C transitions | 372.5 |
| C `append_now(obj)` — auto-ts folded into one C call | **107.8** |
| **Δ** | **3.46× faster, −265 ns/append** |

Bigger than the exp01 estimate (~2.8×) because the auto-timestamp path pays for an *extra* `time.time_ns()`
C transition that folding removes outright.

## Correctness
- 1000 `append_now(object())` → 1000 queryable records, valid monotonic ms wall-clock timestamps.
- `append_now` is purely additive → full facade suite **98 passed, 16 skipped** (unchanged).

## Verdict: 🟩 LOW-HANGING FRUIT (biggest end-to-end win in the lab)
The hottest user-facing path — `append(obj)` with auto-timestamp — is **3.46× faster** when folded into C.
This is the single largest measured end-to-end improvement found. The MVP proves both the magnitude and
the achievability.

**Productionization:** implement `append`/`append_now` as `METH_FASTCALL|METH_KEYWORDS` covering all three
signatures (`append(ts,obj)`, `append(obj)`, `append(obj, ts=…)`), read the configured `time_unit` from
the engine (not hard-coded `ms`), fold the `_check_min_ts` guard into C, and delete the Python override.
Validate under ASan/TSan + 3.14t + the differential suite. Stacks with exp01's FASTCALL conversion.
