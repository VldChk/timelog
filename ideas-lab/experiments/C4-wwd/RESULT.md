# C4-wwd — Whole-window drop (built, gated, independently reviewed + re-verified)

**Implementation (+135 LOC, `prototype.patch`):** new `tl__l1_window_fully_deleted()` tests whether a
selected L1 segment's entire window is covered by a single canonical clipped tombstone whose
`max_seq > seg->applied_seq` (the seq test mirrors the per-record merge filter, so permanently-live
survivors are never dropped). Fully-covered segments are flagged in a `ctx->dropped_l1[]` bitmap,
excluded from the k-way merge, still removed from the manifest by the existing publish loop, and
flat-scanned by `tl__drop_whole_window()` to fire `on_drop_handle` (scan skipped entirely when
`on_drop_handle == NULL` ⇒ true O(1) drop).

## Agent measurement (pure-C, on_drop_handle = NULL)
TTL/retention, whole windows covered by one tombstone in a single pass: **267× / 275× / 67×** compaction-CPU
speedup (10.15 ms → 0.04 ms, etc.); query results byte-identical; merge pops 1 record vs ~1M baseline.

## Independent verification (my own, in `tl-wt-wwd`)
- **Built clean; `./build-rel/test_timelog` = 480 passed, 0 failed** in the local verification run. This
  tree preserves the summary, harnesses, and patch, not the raw command transcript.
- Agent's handle-leak gate (weakref payloads, delete every other window): baseline ≡ variant — dropped
  payloads released (0 leaked), survivors kept (0 premature drops). Confirmed correct handle cleanup.

## ⚠️ Review finding — false-negative in the coverage test (the agent's gates missed it)
`tl__l1_window_fully_deleted` iterates clipped tombstones sorted by start and `return false`s at the
**first** interval with `start ≤ window_start` that doesn't reach `window_end`. With **multiple disjoint
tombstones**, the window-covering interval can be a *later* one — e.g. deletes `[0,5)` **and**
`[100,200)`, window `[150,160)`: the code tests `[0,5)`, bails, and **never checks `[100,200)`** which
actually covers the window. Consequence: **correct output (never a wrong drop), but it fails to drop
windows it could** whenever the covering tombstone isn't the first `start ≤ window_start` interval.
- This is a **missed-optimization, not a safety bug** — which is why the 480-test + handle-leak gates
  (single-tombstone TTL cases) passed.
- It **partly explains the agent's own "wash in the realistic case"** finding: multi-`delete_range`
  workloads silently skip the drop.
- **Fix (small):** in the non-covering branch, only `return false` when the interval actually contains
  `window_start` (`iv->end > window_start`); otherwise `continue` to the next interval.

## Honest impact scope (agent + my review)
- The big win (67–275×) is **pure-C, single-tombstone, whole-window TTL retention** only.
- In the **CPython binding `on_drop_handle` is always non-NULL**, so the mandatory flat-scan of dropped
  records caps the gain → a wash from Python.
- In the **default streaming path** (incremental/bounded compaction, many small passes) the full-coverage
  condition is rarely met per pass *and* the false-negative compounds it → a wash (±2%).

## Verdict: 🟦 cool-but-costly / workload-specific (downgraded from the agent's "low-hanging")
Correct, leak-free, free (no regression), and a large win for the **pure-C TTL/retention** use case — but
a wash for the CPython binding and the default streaming path, *and* the coverage test needs the
false-negative fix to reach its full potential. Worth shipping **only** if a pure-C, TTL-heavy embedding
is a target; with the fix it would help multi-delete retention too. Not the unconditional win the notes implied.
