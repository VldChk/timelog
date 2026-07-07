# Ponytail Audit — Unit: maint

Auditor stance: lazy senior dev. Read every line of all four files (2,423 LOC total),
plus the supporting infrastructure needed to verify each claim
(`tl_tombstone_utils.h`, `tl_recvec.h`, `tl_intervals.h/.c`, `tl_alloc.h`, `tl_heap.h`,
`tl_segment.h`, `tl_window.h`, `tl_timelog.c` worker/flush paths,
`test_compaction_internal.c`, `test_adaptive_internal.c`, public `timelog.h`,
`py_timelog.c` config plumbing).

Files reviewed in full:

| File | LOC |
|---|---|
| `core/src/maint/tl_compaction.c` | 1,483 |
| `core/src/maint/tl_compaction.h` | 280 |
| `core/src/maint/tl_adaptive.c` | 408 |
| `core/src/maint/tl_adaptive.h` | 252 |

## Executive Summary

The compaction core is disciplined: the four-phase select/merge/publish split, the
two-tombstone-set design, deferred drop callbacks, and the strict publish protocol all
earn their keep against documented invariants (L1 non-overlap, seqlock publication,
half-open intervals, H-17/H-18/H-19). No invariant-violating "simplification" is
proposed.

What I did find:

1. **Two rung-2 duplications**: `tl__tombs_union_into` re-implements the shared
   `tl_tombstones_add_intervals` helper, and the deferred-drop array re-implements
   `tl_recvec_t` — which is *already used eleven lines away in the same function*.
   Killing the second one also collapses the over-general `tl__grow_array`.
2. **One wasted k-way merge per retry-exhaustion episode**: `tl_compact_one`'s loop
   shape performs a full select+merge *after* the final EBUSY publish and throws the
   result away. Restructuring the loop removes both the code duplication and the
   wasted work — a simplification that is also a perf win.
3. **Dead code and stale docs**: `tl_adaptive_wants_resize` has zero production
   callers; a 14-line doc block in `tl_compaction.h` describes trigger behavior the
   code explicitly no longer has; `tl_intervals_covered_span` (cross-unit) claims to
   be "the delete-debt metric" and is called by nothing but tests.
4. **A strategic flag, not a finding**: the entire adaptive subsystem (~660 impl LOC,
   ~1,238 test LOC, 10 public C knobs, 10 Python kwargs) can only take effect before
   the first L1 segment exists, because `window_grid_frozen` latches permanently at
   first L1 publish. It is public API, so this is an api-change deprecation question
   for the maintainer, not a deletion I can recommend inside this audit's constraints.

Honest total for the actionable items: **~250 LOC** net deletion at low risk, plus one
medium-risk 38-line rewrite, with no hot-path perf cost anywhere (two items are strict
perf improvements: one fewer malloc per compaction, one fewer full merge per
retry-exhaustion).

---

## Per-File Walkthrough

### tl_compaction.h (280 lines)

Lines 1–64: module doc. Accurate except one block (see S7). Lines 79–146: context
struct — every field is used; the twin tombstone sets (`tombs` at :108 vs
`tombs_clipped` at :109) are documented with *why using the wrong one breaks
correctness* (:94–107). That is exactly the kind of comment that earns its bytes.
Lines 148–270: phase API. Four functions + ctx lifecycle, consumed by one production
caller (`tl_compact_one`) and by `test_compaction_internal.c` (1,031 lines, 18 test
cases incl. EBUSY injection, retry exhaustion, residual preservation, watermark
respect). The split is what makes deterministic phase testing possible — keep.
Lines 182–196: **stale doc block, see S7**.

### tl_compaction.c (1,483 lines)

- :20–29 test failpoint (`tl_test_force_ebusy_count`) — minimal, keep.
- :35–122 ctx init/destroy — straight resource cleanup, destroy is safe on partial
  init as documented at header :164–167. Keep.
- :128–173 NDEBUG validators (L0 generation order, L1 non-overlap adjacent-pair scan)
  — cheap, guard invariant #2. Keep.
- :180–201 `tl__tombs_union_into` — **duplicate of shared helper, see S1**.
- :204–332 `tl__compute_delete_debt` — cursor sweep, O(T+W), `TL_MAX_DEBT_WINDOWS`
  cap (tl_defs.h:34), unbounded short-circuit at :233–237. H-18 compliant.
  **NO-and-NO** (see below).
- :349–388 `tl_compact_needed` — pins manifest under writer_mu (UAF note :350–355),
  correct sequential (not nested) lock use. Micro-nit: maint_mu is taken at :368–370
  to read `effective_window_size` even when only the L0-count trigger at :372 will
  decide; moving it inside the `delete_debt_threshold > 0` branch saves one mutex
  round-trip per worker wake. Not worth a line-count entry; noted here only.
- :413–437 `tl__l1_overlaps_window_range` — 10 lines guarding the exact
  window-bounds-not-record-bounds subtlety of invariant #2, with a worked example in
  the comment. **NO-and-NO**.
- :451–501 `tl__compact_select_l1` — two-pass count-then-allocate. **See S5**.
- :503–547 `tl__segment_estimate_bytes` — 45 lines of longhand saturating
  arithmetic. **See S6**.
- :553–678 greedy L0 selection — three caps (inputs/windows/bytes), forward-progress
  guarantee at :637–643 ("caps apply only after at least one segment"). Sound. Keep.
- :684–723 `tl_compact_select` — pins snapshot + manifest, takes generation under
  writer_mu per lock order. Metrics counters are public API (`timelog.h:688–691`),
  can't trim. Keep.
- :734–810 `tl__grow_array` + `tl__ensure_output_capacity` + `tl__push_dropped_record`
  — **over-general once dropped_records becomes a recvec, see S2**.
- :827–869 `tl__flush_window_records` — thin, correct, unbounded-window note at
  :822–825. Keep.
- :884–972 `tl__build_residual_tombstones` — H-19. Hand-rolled interval difference.
  **See S11** for an expression in existing primitives.
- :978–1247 `tl_compact_merge` — two tombstone sets built (:987–1050), watermark
  validation against `applied_seq` (:1008–1012, :1046–1050), direct segment-iterator
  k-way merge via `tl_heap`, cursor-based filtering (:1173–1188), window-jump
  partitioning that keeps work O(records) not O(window span) (:1190–1216, comment
  explains why). Architecture is right. The `watermarks` side-array is removable —
  **see S4**.
- :1250–1293 manifest builder application — linear, validation lives in the builder
  (H-10/H-11). Keep.
- :1299–1359 `tl_compact_publish` — build off-lock, pointer-equality base check under
  writer_mu (:1323), seqlock-bracketed swap (:1331–1336), pin-before-unlock for the
  NDEBUG validation (:1338–1343 — subtle and necessary). Strict protocol per H-17.
  **NO-and-NO**.
- :1365–1483 `tl_compact_one` — adaptive candidate compute/commit discipline
  (compute before, commit only after successful publish, :1369–1374) is correct.
  Loop shape duplicates select+merge and wastes a final merge — **see S3**.

### tl_adaptive.h (252 lines)

Config validation, state struct, flush metrics, and six exported functions. The
`TL_ADAPTIVE_INTERNAL_TEST` block (:210–250) exposes five helpers for the 1,238-line
unit-test file — legitimate. `has_records` field (:83) — **see S9**.
`tl_adaptive_wants_resize` (:184–201) — **dead, see S8**.

### tl_adaptive.c (408 lines)

Well-guarded floating-point policy code; no allocation in the loop as advertised (:5).
Findings: `isnan||isinf` vs the `isfinite` already used at :30 (**S10**), duplicated
validation between the two branches of `tl__adaptive_snap_to_quantum` (:167–189) and
a provably unreachable overflow guard (:194–199, the comment itself concedes
"mathematically qid * q <= wi < INT64_MAX") — folded into **S10**.
`tl_adaptive_wants_resize` (:395–408) — **S8**.

---

## Findings (the Ladder)

### S1 — `tl__tombs_union_into` duplicates `tl_tombstones_add_intervals` [rung: already-in-this-codebase]

- **Where**: `tl_compaction.c:180–201`; call sites :214, :993, :1004.
- **Evidence**: The shared helper `tl_tombstones_add_intervals(accum, tombs, t1, t2,
  t2_unbounded)` in `core/src/internal/tl_tombstone_utils.h:13–63` performs the
  identical temp-union-swap (`tl_intervals_union_imm` → destroy accum → `*accum =
  merged`, utils :52–61 vs compaction :187–200). Called with `t1 = TL_TS_MIN,
  t2_unbounded = true`, its range filter selects every interval (`first = 0, last =
  len-1`), making it exactly `tl__tombs_union_into`. The shared helper already has 7
  production call sites (`tl_snapshot.c:204,219,239,259`, `tl_plan.c:152,160,168`).
- **Change**: delete the local helper; replace 3 calls with
  `tl_tombstones_add_intervals(accum, seg_tombs, TL_TS_MIN, 0, true)`.
- **LOC saved**: ~20. **Risk**: low. **Perf**: identical modulo one trivially
  predictable range-filter loop over intervals already being unioned; all call sites
  are compaction-path (off hot path).
- **Tests**: covered by `cint_merge_with_tombstones`, `cint_delete_debt_matches_reference`.

### S2 — Deferred-drop array re-implements `tl_recvec_t`; `tl__grow_array` then over-general [rung: already-in-this-codebase]

- **Where**: fields `dropped_records/dropped_len/dropped_cap`
  (`tl_compaction.h:137–139`), `tl__push_dropped_record` (`tl_compaction.c:790–810`),
  `tl__grow_array` (:734–770), `tl__ensure_output_capacity` (:776–784), destroy
  plumbing (:116–121), callback loop (:1421–1425).
- **Evidence**: `tl_recvec_t` (`internal/tl_recvec.h`) is a dynamic array of exactly
  `tl_record_t` "(ts, handle) pairs" with amortised O(1) push — and `tl_compact_merge`
  *already uses one* for `window_records` at `tl_compaction.c:1140–1141, :1218`. The
  dropped-record queue is the same shape: `dropped_records[dropped_len].ts/.handle`
  (:805–806).
- **Change**: `tl_recvec_t dropped;` in the ctx; `tl_recvec_push(&ctx->dropped, ts,
  handle)`; `tl_recvec_data/len` in the callback loop; `tl_recvec_destroy` in
  ctx_destroy. That leaves `tl__grow_array` with a single caller (output_l1), so its
  generic `void**`/`elem_size`/`zero_new` machinery collapses into ~12 direct lines in
  `tl__ensure_output_capacity` using the shared `tl__grow_capacity` +
  `tl__alloc_would_overflow` (`tl_alloc.h:127,150`). Note the `zero_new` flag is
  already unnecessary: ctx_destroy only reads `output_l1[0 .. len)` (:99–103).
- **LOC saved**: ~50 net. **Risk**: low. **Perf**: identical amortised growth; off hot
  path. **Tests**: drop-callback behavior covered by compaction tests + Python handle
  lifecycle tests.

### S3 — `tl_compact_one` retry loop: duplicated select+merge AND a wasted final merge [rung: minimal-rewrite]

- **Where**: `tl_compaction.c:1396–1406` (pre-loop select+merge) vs :1459–1472
  (loop-bottom re-select+re-merge); loop at :1412–1473.
- **Evidence**: loop body order is publish → (return unless EBUSY) → destroy/init →
  select → merge → increment. On the final attempt (`attempt == max_retries-1`),
  publish returns EBUSY and the loop bottom **still runs a full select + k-way
  merge**, whose result is immediately discarded by the post-loop
  `tl_compact_ctx_destroy(&ctx)` at :1476. With `TL_COMPACT_MAX_RETRIES = 3`
  (`tl_timelog.c:808`), an exhaustion episode does 4 select+merge cycles for 3
  publish attempts.
- **Change**: move ctx_init/select/merge to loop top; publish at loop bottom; success
  handling unchanged; EBUSY metrics (`compaction_publish_ebusy` every miss,
  `compaction_retries` only when another attempt follows, :1454–1457) preserved
  verbatim.
- **Behavioral delta (declare honestly)**: today, if the *throwaway* select/merge
  after the last publish fails or EOFs (e.g. a concurrent compaction emptied L0), the
  function returns that status (EOF/ENOMEM) instead of TL_EBUSY and skips
  `tl_adaptive_record_failure`. The restructure always returns TL_EBUSY on exhaustion
  — which is what the header contract says (`tl_compaction.h:266` "TL_EBUSY if all
  retries exhausted"). Arguably a bug fix.
- **LOC saved**: ~15. **Risk**: low. **Perf**: strictly better (one full merge
  eliminated per exhaustion). **Tests**: `cint_one_exhausts_retries` (EBUSY
  injection), `cint_publish_ebusy_on_manifest_change` cover this loop directly.

### S4 — `watermarks` side-array in merge is unnecessary [rung: minimal-rewrite]

- **Where**: `tl_compaction.c:1067–1076` (alloc + overflow check), :1083, :1089
  (fills), :1104–1122 (separate priming loop reads `watermarks[i]`), :1098–1099,
  :1117–1118, :1244 (frees).
- **Evidence**: the watermark is just `tl_segment_applied_seq(seg)`
  (`tl_segment.h:277`, trivial inline), available in the same loops that already init
  each iterator (:1080–1091). Refills reuse `min_entry.watermark` (:1159), so the
  array is only read at priming.
- **Change**: prime the heap inside the two iterator-init loops (init iter → next →
  push entry with `.watermark = tl_segment_applied_seq(seg)`, `.tie_break_key =
  (uint32_t)iter_idx`). Tie-break order (L0s then L1s by index) unchanged. Heap
  init/reserve moves before the loops.
- **LOC saved**: ~22, plus one malloc/free per compaction removed. **Risk**: low.
  **Perf**: strictly better (fewer allocations). **Tests**:
  `cint_compaction_respects_input_watermarks`, `cint_merge_basic`,
  `cint_merge_multi_window`.

### S5 — Two-pass L1 selection → one pass [rung: minimal-rewrite]

- **Where**: `tl_compaction.c:469–498` (count pass :470–476, alloc, fill pass
  :492–498; `tl__l1_overlaps_window_range` evaluated twice per segment).
- **Evidence**: the sibling L0 selection at :564–570 already allocates `n_l0` pointers
  upfront regardless of how many get picked. Doing the same for L1 (`n_l1` pointers,
  8 bytes each, transient, freed in ctx_destroy which tolerates `len <=` allocation)
  makes it one pass.
- **LOC saved**: ~11. **Risk**: low. **Perf**: neutral-to-better (one overlap test per
  segment instead of two); transient over-allocation is bytes-per-L1-segment.
- **Tests**: `cint_select_selects_all_l0`, `cint_residual_tombstones_preserved_under_window_cap`.

### S6 — `tl__segment_estimate_bytes`: longhand saturating arithmetic [rung: minimal-rewrite]

- **Where**: `tl_compaction.c:503–547`.
- **Evidence**: 45 lines that are five saturating adds and three saturating
  multiplies written out longhand ("`if (est > SIZE_MAX - page_meta_bytes) return
  SIZE_MAX;`" repeated with varying operands). Two 1–2 line local helpers —
  `sat_add(size_t,size_t)` and `sat_mul_u64(uint64_t,size_t)` (the u64 input matters:
  `record_count` is `uint64_t`, `tl_segment.h:75`) — express the same function in
  ~15 lines. `tl__alloc_would_overflow` (`tl_alloc.h:127`) already provides the
  multiply-overflow predicate for the size_t case. (C23 `<stdckdint.h>` would be the
  stdlib answer, but the project is C17 + MSVC `/WX`, so local helpers win.)
- **LOC saved**: ~22. **Risk**: low — the value only feeds the greedy byte cap
  (`target_bytes` at :627–635); exact saturation points are unobservable.
- **Tests**: indirectly via selection cap tests; a saturation unit test would be new.

### S7 — Stale/false "Background mode trigger coupling" doc block [rung: does-not-need-to-exist]

- **Where**: `tl_compaction.h:182–196`.
- **Evidence**: the block states "The background worker only calls this function on
  wakes that already have flush work pending" and "delete-debt compaction will NOT
  fire on pure idle wakes". The worker code says the opposite and says *why the old
  behavior was removed*: `tl_timelog.c:1791–1805` — "Evaluate the compaction
  heuristic on EVERY wake-up… Previously this was gated on pending flush work, which
  let user-flushed L0 grow unboundedly and left delete_debt_threshold inert on idle
  instances (v1.3 usability lab findings)." The same header's own file-level comment
  (`tl_compaction.h:46–53`) already carries the corrected description, so the
  function-level block is both wrong and redundant.
- **LOC saved**: ~14 (docs). **Risk**: zero.

### S8 — `tl_adaptive_wants_resize` is dead production code [rung: does-not-need-to-exist]

- **Where**: `tl_adaptive.c:395–408`, header `tl_adaptive.h:184–201`.
- **Evidence**: repo-wide grep of `core/` + `bindings/`: the only callers are
  `core/tests/test_adaptive_internal.c:629–681` (5 assertions). The header claims
  "Used by scheduler to decide if compaction should run" — no scheduler code
  references it (`tl_timelog.c` worker consults `tl_compact_needed` only,
  :1801–1813). The function even takes `maint_mu` "so the no-GIL build has no
  production C data races" (`tl_adaptive.c:390–393`) — synchronization engineering
  for a function production never calls.
- **Change**: delete function, header block, and the 5 test cases (or keep it only if
  a scheduler integration is genuinely planned — in which case fix the doc).
- **LOC saved**: ~35 impl/header + ~60 test. **Risk**: low (test-only surface).

### S9 — `tl_flush_metrics_t.has_records` is definitionally redundant [rung: one-liner]

- **Where**: field `tl_adaptive.h:83` ("`has_records; /* record_count > 0 */`" — the
  comment admits it); sole producer `tl_timelog.c:1072`
  (`metrics.has_records = (metrics.record_count > 0)`); sole consumer
  `tl_adaptive.c:230` checks **both**: `!metrics->has_records ||
  metrics->record_count == 0`.
- **Change**: drop the field; check `record_count == 0`. Touches `tl_timelog.c`
  (outside this unit) and 5 designated initializers in `test_adaptive_internal.c`.
- **LOC saved**: ~8 net. **Risk**: low. Internal struct — no API change.

### S10 — `!isfinite`, snap_to_quantum branch dedup, unreachable guard [rung: stdlib]

- **Where**: `tl_adaptive.c:100, 168–169, 177, 244, 299–301, 343` use
  `isnan(x) || isinf(x)` while :30 already uses `isfinite` — same header, same file.
  `tl__adaptive_snap_to_quantum` duplicates the full
  `<=0 / NaN / Inf / >=INT64_MAX / llround / wi<=0` validation in both the
  no-quantum branch (:167–174) and the quantum branch (:177–189); hoisting it above
  the quantum test makes the no-quantum case `return (tl_ts_t)wi;`. The overflow
  guard at :194–199 is unreachable by its own comment ("mathematically
  qid * q <= wi < INT64_MAX") — `wi` is already bounded by the hoisted check, so no
  "corrupted density" can reach it.
- **LOC saved**: ~15 across the file. **Risk**: low. **Tests**:
  `test_adaptive_internal.c` exercises snap-to-quantum edge cases directly
  (quantum 0, odd/even quanta, INT64 edges).

### S11 — Residual tombstones are an interval-set difference already expressible in `tl_intervals` primitives [rung: already-in-this-codebase, medium risk]

- **Where**: `tl_compaction.c:899–943` (the per-interval loop inside
  `tl__build_residual_tombstones`).
- **Evidence**: residual = `ctx->tombs` minus `[first_w_start, last_w_end)`. The
  intervals module already provides both halves: `tl_intervals_clip(iv, TL_TS_MIN,
  first_w_start)` reproduces the "before" portion including the
  unbounded-becomes-bounded rule (clip impl `tl_intervals.c` truncates unbounded to
  `t2` and preserves `max_seq`, verified in source), and
  `tl_intervals_clip_lower(iv, last_w_end)` reproduces the "after" portion including
  unbounded preservation and `res_start = max(start, last_w_end)`
  (`tl_intervals.h:163–177`), matching the careful widening-avoidance comment at
  :918–924. Combine with `tl_intervals_union_imm` on two clipped copies (copy =
  union with empty imm). Guards needed: skip "before" when
  `first_w_start == TL_TS_MIN` (clip precondition `t1 < t2`), skip "after" when last
  window unbounded (current code already does, :917). The two clipped sets are
  disjoint by construction so union max_seq semantics never engage.
- **LOC saved**: ~38 (89 → ~50 with error handling). **Cost**: one extra transient
  copy of the tombs set per compaction (off hot path; tombs is typically small).
- **Risk**: medium — unbounded/max_seq edges are subtle even if the primitives check
  out; must lean on `cint_residual_tombstones_unbounded` and
  `cint_residual_tombstones_preserved_under_window_cap`, plus intervals unit tests.
  Only do this if touching the function anyway.

### S12 — FLAG (api-change): the adaptive subsystem can effectively fire only once [rung: does-not-need-to-exist candidate — NOT actionable without deprecation]

- **Evidence chain**:
  - Candidate computation is gated on `!tl->window_grid_frozen`
    (`tl_compaction.c:1383`).
  - `window_grid_frozen` latches `true` on the first compaction that publishes any
    L1 output (:1437–1439) and is **never cleared** (only other write is at open,
    `tl_timelog.c:375`; grep confirms).
  - Therefore EWMA smoothing, staleness detection, hysteresis, quantum snapping, and
    failure backoff all operate only in the interval between `warmup_flushes` and
    the first record-producing compaction. In particular
    `failure_backoff_threshold/pct` require repeated publish-retry exhaustion
    *before any L1 exists* — a near-unreachable regime.
  - Density updates keep running forever regardless (`tl_timelog.c:1068–1108` gates
    on `target_records > 0` only), feeding a computation that can never act once
    frozen — per-flush wasted work (bounded, small) plus permanent conceptual load.
  - Cost side: ~660 LOC impl/header, 1,238 LOC tests, 10 knobs in public
    `tl_adaptive_config_t` (`timelog.h`), 10 mirrored kwargs in the CPython binding
    (`py_timelog.c:856–865`), a docs page, and validation code.
- **Why not a finding**: `tl_adaptive_config_t` is public C API and the kwargs are
  public Python API — hard constraint says flag loudly, don't cut. Also the grid
  freeze itself is invariant C-10; the *design* is coherent, it's the
  cost/benefit that is questionable.
- **Recommendation to maintainer**: decide whether "one-shot pre-L1 window sizing" is
  the intended product scope. If yes, say so in `adaptive-segmentation.md` and
  consider trimming the knobs that cannot matter (failure backoff, staleness) at the
  next major version. If no, the feature needs unfreeze machinery — a much bigger
  discussion. Either way, gate the flush-metrics capture on `!window_grid_frozen`
  as a free micro-win (one condition, but requires maint_mu read discipline).

### Cross-unit observation — `tl_intervals_covered_span` is dead and its doc lies

- `tl_intervals.h` (accessor section) documents it as "used as the compaction
  policy's delete-debt metric". It is not: the metric is `tl__compute_delete_debt`
  (`tl_compaction.c:204`), and repo-wide the only callers are
  `test_internal_data_structures.c:996,1012`. Belongs to the `internal` unit's
  ledger, recorded here because the stale doc points at this unit.

---

## NO-and-NO (earns its keep)

1. **`tl__compute_delete_debt` cursor sweep** (`tl_compaction.c:204–332`): hand-rolled
   but justified. It computes *max per-window coverage ratio* over a canonical
   interval set with `max_seq`/`end_unbounded` payloads, half-open semantics, a
   `TL_MAX_DEBT_WINDOWS` cap, and overflow-safe window-ID math — H-18 requires
   exactly the O(T+W) cursor structure written here (:288–322). No C library
   implements "bucketized coverage over your own interval type" with less glue than
   these 60 core lines. Verified against a reference implementation in
   `cint_delete_debt_matches_reference`.
2. **Two tombstone sets** (`tombs` vs `tombs_clipped`, header :94–107, merge
   :984–1050): looks like duplication, is not — one drives residual computation
   (unclipped, input-only, H-19), the other record filtering (global snapshot view,
   clipped). The header documents the failure mode of conflating them. Collapsing
   them would be a correctness bug, not a simplification.
3. **Strict publish protocol** (`tl_compact_publish`, :1299–1359): build off-lock,
   pointer-equality base check, seqlock write window, pin-before-unlock for debug
   validation. Every line maps to invariant #6/H-17 or to a documented race
   (:1338–1343). Already minimal.
4. **Deferred drop queue semantics** (fire only after publish; header :129–137,
   merge :1177–1188, one :1420–1426): required by the binding safety contract —
   firing during merge lets user code free a payload still visible in the manifest
   on a failed/retried publish (UAF/double-free). The queue must exist; S2 only
   changes its container.
5. **`tl__l1_overlaps_window_range`** (:413–437): 10 lines whose comment carries the
   single most important selection subtlety in the module (window bounds vs record
   bounds → L1 non-overlap). Generic interval-overlap helpers would erase the
   documentation value for zero LOC gain.
6. **Four-phase select/merge/publish API** (header :148–270): one production caller,
   but the phase boundaries are load-bearing for the 1,031-line internal test suite
   (EBUSY injection between merge and publish, residual inspection, watermark
   checks). Not single-caller over-generalization.
7. **Debug validators** (:128–173): NDEBUG-only, O(n) adjacent-pair scans guarding
   invariants #2 and merge tie-break preconditions. Cheap insurance; release-mode
   equivalents (H-12/H-14) live in the manifest builder as designed.
8. **Greedy selection forward-progress rule** (:637–643): the "caps apply only after
   the first segment" asymmetry looks removable but is the liveness guarantee when a
   single segment exceeds a cap on its own. Keep.
9. **Adaptive NaN/Inf/overflow guards in the policy loop** (`tl_adaptive.c`
   throughout): off hot path, each guard maps to a "keep current window" stability
   rule the header documents (:150–154 "Resetting to a fixed base causes the control
   loop to oscillate"). Beyond S10's tidying, the defensive shape is correct for
   floating-point control code.
10. **`volatile int tl_test_force_ebusy_count`** (:20–29): simplest possible
    failpoint; the volatile rationale is documented. Keep.

## Prior-Art Leads (for later verification, honest fit notes)

1. **K-way merge / min-heap** (merge loop :1093–1222 over `internal/tl_heap`): known
   territory — klib `ksort.h` heap macros (MIT), CCAN `heap` (BSD-MIT), or a loser
   tree for fewer comparisons. Fit: poor. The in-repo heap carries engine-specific
   payload (`tie_break_key`, `watermark`, opaque iter — `tl_heap.h:27–33`), already
   respects the allocator seam, and is shared with the query hot path where the
   zero-regression rule bites; K is small (≤ max_compaction_inputs), so a loser tree
   buys nothing measurable. Verdict expectation: keep in-repo.
2. **Interval set difference/union** (residuals :884–972): interval containers exist
   (Boost ICL — C++, out; various interval-tree C libs — wrong shape, usually
   node-based trees with their own allocators, no `max_seq` payload). The real prior
   art is in-repo `tl_intervals` (S11). Verdict expectation: rung 2 beats rung 5.
3. **Checked/saturating arithmetic** (S6; also `tl_sub_overflow_i64` usage
   throughout): C23 `<stdckdint.h>` is the stdlib answer but the project is C17 with
   MSVC `/WX`; portable-snippets `psnip_safe` (CC0/MIT) vendors cleanly but is ~1
   header for what two local inline functions do. Fit: adopt-nothing, extend the
   in-repo helpers.
4. **EWMA-driven sizing control loop** (`tl_adaptive.c`): conceptual prior art is
   database auto-tuning (RocksDB dynamic level sizing) and classic
   hysteresis/quantization control patterns — no vendorable C library exists;
   the leverage here is scope reduction (S12), not adoption.
5. **Dynamic array growth** (S2): klib `kvec.h` (MIT) is the canonical external
   answer, but in-repo `tl_recvec` + `tl__grow_capacity` already cover every use in
   this unit. Rung 2 beats rung 5.

## Suggested Order of Attack

Zero-risk docs/dead-code first (S7, S8, S9, S10), then the mechanical rung-2 swaps
(S1, S2, S5, S6), then the loop restructures with test scrutiny (S3, S4), S11 only
opportunistically, S12 to the maintainer as a scope decision.
