# Idea 4 — Document/tune `max_delta_segments` as the tiering↔leveling dial (DETAILED PLAN)

## Goal
**Documentation only.** Turn `max_delta_segments` from a bare, undocumented knob into a clearly
explained tiering↔leveling dial, backed by the measured trade-curve, so users can tune it for their
workload and avoid the "never compacts" misconfiguration trap. **No code/behavior change. Default stays 8.**

## Why docs-only (scope discipline)
The audit's confirmed 🟩 action is *documentation/config guidance now*; the runtime OOO-overlap-adaptive
trigger (C4-roi) is an explicit separate prototype, **out of scope**. Changing the default (e.g. 8→16)
is a behavior change that would require broad re-validation and is NOT what the evidence supports as a
universal win (the matrix shows higher is better *only* for mild workloads; adversarial OOO wants it low).
So: keep default 8, document the curve + when to deviate.

## What the knob actually is (verified in code)
- `tl_config_t.max_delta_segments` (`core/include/timelog/timelog.h:268`), default `TL_DEFAULT_MAX_DELTA_SEGMENTS`
  = 8 (`core/src/tl_timelog.c:121,201`).
- Trigger site: `core/src/maint/tl_compaction.c:372` — `if (tl_manifest_l0_count(m) >= cfg.max_delta_segments)`
  compaction is requested. So it bounds **L0 segment count** (read fan-in) before compaction fires.
- Low value = eager **leveling** (compact often: low read-amp, high write-amp + compaction CPU).
  High value = lazy **tiering** (let L0 pile up: low write-amp/CPU, higher read-amp; risk of never compacting).
- Strategy context (exp04 research): Timelog = literature-convergent hybrid (RocksDB 1-leveling × Cassandra
  TWCS); this is the single STCS↔LCS dial. No new algorithm is worth adopting.

## The measured evidence to cite (saved, real)
From `ideas-lab/experiments/exp04-compaction/` (KNOB_MATRIX.md + RESULT.md):

**Knob matrix** (subprocess-isolated, 3 paired seeds → median, N=400k, `knob_matrix_baseline.json`):
| trigger | write-amp (seg re-merge proxy) | compaction CPU | point p50 |
|---|---|---|---|
| 2  | 75.0 | 57.9 ms | ~700 ns |
| 8 (default) | 18.7 | 24.9 ms | ~690 ns |
| 32 | 2.68 | 5.6 ms | ~750 ns |
→ **WA swings 28×**, **compaction CPU ~10×**, **read p50 nearly flat** (in-order/mild-OOO segments have
disjoint time ranges that fence-prune well).

**Adversarial full-overlap OOO** (RESULT.md Exp4/5, 16 L0 each spanning the whole domain, 3-repeat):
| trigger | compactions | point p50 | space |
|---|---|---|---|
| 8 (default) | 2 | 601 ns | 49 pages |
| 32 / never | 0 | **3166 ns** | 64 pages |
→ When compaction fires, OOO reads are **5.3× faster** and use **31% less space**. trigger≥32 with only
16 L0 **silently never compacts** — the misconfiguration trap.

**In-order read-amp vs L0 depth** (Exp1): 1→581ns, 8→591ns, 32→691ns (1.19×), 128→982ns (1.69×) — gentle.
**Space-amp** is governed by *deletes* (delete_storm SA≈1.67 at every trigger), **not** this dial.

Honest caveats to include: numbers are 400k-record, 3-seed medians; WA is a segment-count proxy (not bytes);
in-memory write-amp is cheap (no disk/fsync/wear), which is *why* the default is conservative.

## Files to edit (all docs/comments; no logic)
1. **`core/include/timelog/timelog.h`** (~line 268) — expand the inline `max_delta_segments` comment from
   "`0 => default (8). L0 segment bound.`" to a few lines: what it bounds, the tiering↔leveling direction,
   the never-compacts trap, "tune don't guess — see docs/configuration.md". (Source of truth; keep terse.)
2. **`python/timelog/__init__.py`** (~line 150) — expand the kwarg docstring line similarly (1–3 lines,
   facade-user-facing; point to docs/configuration.md).
3. **`docs/configuration.md`** — replace the bare `- max_delta_segments` bullet with a proper subsection:
   the dial explanation, the trade table (28× WA / 10× CPU / flat read), the adversarial-OOO 5.3× caveat,
   the never-compacts trap, the "deletes use a different lever" note, and concrete guidance (default / lower /
   higher). Link to the compaction internals doc + performance methodology.
4. **`docs/internals/components/compaction-and-maintenance.md`** — add a "Tuning the tiering↔leveling dial"
   subsection (the internals home for the curve + the RUM rationale for why default is conservative).
5. *(Maybe)* **`docs/performance.md`** — one-line pointer to the trade curve if it fits; skip if it bloats.

## Guidance text (the actionable core — must be accurate, hedged correctly)
- **Default (8)** — balanced; the conservative knee for adversarial OOO (≈600 ns reads at ~26% less
  rewriting than trigger=2). Right choice when the workload is unknown or mixed.
- **Lower (2–4)** — eager leveling. Only if you must minimize read latency under *heavy out-of-order
  overlap* and can afford ~3–10× more compaction CPU and write-amp. Usually unnecessary (default already
  gives ~600 ns OOO reads).
- **Higher (16–32)** — lazy tiering. For write-heavy, in-order / mildly-OOO workloads whose reads
  fence-prune well: cuts compaction CPU ~3–4× and write-amp up to ~28× at ~no read cost. **Keep it below
  your steady-state L0 count or compaction never fires** (never-compacts trap → unbounded read-amp).
- **Not a space/delete lever** — space-amp is driven by tombstones; use `delete_debt_threshold` and
  `delete_before`/TTL, not this knob.

## Risk surface (for hostile plan review)
1. **Accuracy** — every cited number must match the saved JSON/RESULT (no rounding that misleads; label the
   WA proxy as a proxy). Reviewers should diff claims against `knob_matrix_baseline.json` / RESULT.md.
2. **Over-claiming** — must NOT imply "raise it for a free win"; the 5.3× OOO caveat + never-compacts trap
   are mandatory hedges. The flat-read result is workload-specific (in-order/mild-OOO), not universal.
3. **Default-change temptation** — explicitly do NOT change the default; if a reviewer argues for it, that's
   a separate, out-of-scope decision needing 2–5M-record re-validation.
4. **Docs-gate** — `check_docs_consistency.py` requires all markdown links resolve; any new link
   (compaction-and-maintenance.md, performance.md, PERFORMANCE_METHODOLOGY.md) must be a real relative path.
5. **Header/facade drift** — the C comment, the facade docstring, and configuration.md must agree (no
   divergent default or direction). Single trade-curve, three pointers to it.
6. **No behavior/test impact** — zero code change ⇒ core/ctest/pytest counts must be byte-identical to the
   pre-idea-4 gate; the only new gate is docs-consistency + layer-A static (both must stay green).

## Test / gate (docs change)
- `python3 demo/ci/check_docs_consistency.py` → pass (links resolve).
- `python3 demo/ci/check_layer_a_static.py` → pass.
- `git diff --check` → no whitespace errors.
- Full suite unchanged: 483 core · 9/9 ctest · 169 pytest (no code touched).
- Manual: numbers cross-checked against `exp04-compaction/*.json` + RESULT.md/KNOB_MATRIX.md.

## Done = green
Docs build/links clean, static gates green, suite counts unchanged, every cited figure traceable to a saved
artifact. Commit `docs(config): document max_delta_segments as the tiering<->leveling dial`.

---
## v2 — CORRECTIONS after 2 hostile plan reviews (both found real defects; all verified vs code+JSON)

### Accuracy fixes (reviewer 1, verified against raw JSON `exp04_3.13.json`/`exp04_confirm.json`)
- **A. "31% less space" is WRONG → use ~23%.** 49 vs 64 pages = (64−49)/64 = **23.4%** less. (The 31% inverts it:
  64 is 30.6% *more* than 49.) RESULT.md inherited the same error — do not propagate it.
- **B. Drop the exact in-order depth-1/8 ns.** Raw JSON exp1 = 571/601/691/982; RESULT.md's 581/591 are a
  noisier single-shot. Publish only the **shape**: read-amp grows gently with L0 depth, **≈1.2× at 32
  segments, ≈1.7× at 128** (true under both artifacts). No absolute depth-1 ns.
- **C. ratio basis** follows B (≈1.2×/≈1.7×, not the disputed 1.19×).
- **D. Label the matrix trade table "(steady workload, N=400k)"** — those p50s (721/691/752) are the steady
  rows; read stays flat across steady/ooo/delete_storm (~650–762 ns) but the table is steady.
- **E. Label the adversarial-OOO block "N=200k"** (compaction_bench/confirm ran N=200_000); reserve "N=400k"
  for the knob matrix. Exp1 read-amp curve was N=262k — just say "≈260k" or omit N for that shape line.
- **F. Use "~600 ns" not "601"** for the default-trigger OOO read (confirm median is 602; 601 is trigger=2).
- Keep the safe headline figures (all verified): **WA 28× (75.0→2.68), CPU ~10× (57.9→5.6 ms), read flat,
  5.3× OOO (~600→~3170 ns), 12.5% in-order page reclaim, SA≈1.67 delete-driven, default=8, `>=` trigger**.
- Do NOT cite the 483/9/169 suite counts as evidence figures (they're the gate, not a trade number).

### Claim-correctness fixes (reviewer 2, verified against `tl_compaction.c`)
- **BLOCKER-1 — "never compacts" is FALSE as a blanket claim.** `tl_compact_needed` (tl_compaction.c:349-388)
  has TWO trigger arms: L0-count `>=` max_delta_segments (372) **and** delete-debt `>=` delete_debt_threshold
  (377-383); plus explicit `compact()` runs `tl_compact_one()` regardless of the knob. **Reframe:** raising
  the knob above the L0 count a workload accumulates stops the *automatic L0-count trigger*; compaction can
  still fire via `delete_debt_threshold` or an explicit `compact()`. The genuine trap = **delete-free
  workload + sole reliance on the auto L0 trigger + never calling compact()** → L0 (and read-amp) grow
  unbounded (the exp04 OOO `max_delta_segments=32` vs 16-L0 case: 0 compactions, 5.3× slower reads).
- **BLOCKER-2 — the "higher = lazy tiering, cheaper CPU" numbers assume UNBOUNDED `compaction.max_inputs`.**
  The drain is capped per compaction at `max_inputs` (tl_compaction.c:586). If `max_inputs`/`max_windows` are
  set, a high trigger yields more frequent, smaller compactions, partially negating the savings. **Scope the
  claim** to "with default unbounded max_inputs" and cross-reference.
- **MAJOR-3 — tiering↔leveling is an ANALOGY, not a mode switch.** The knob does not change the L0→L1
  algorithm or L1's leveling discipline (always non-overlapping windows); it only controls how *eagerly the
  overlapping L0 tier is collapsed*. Phrase as analogy; don't imply "leveling mode."
- **MAJOR-4 — "higher = near-free" must lead with the precondition + drift warning.** Free only for workloads
  that stay in-order/mild-OOO and whose segments **fence-prune** (window_size-dependent). Workload drift
  toward time-overlap silently triggers the 5.3× read cliff (no error). The recommendation is in *segment
  count*; byte/latency impact scales with `memtable_max_bytes` (segment size) and `window_size` (pruning).
- **MAJOR-5 — "write-amp is cheap" must not read as "free."** Add the real in-memory costs: transient
  old+new merge RAM spike (C4-gran: the `max_compaction_windows` cap does not fully bound it), CPython
  per-survivor handle traversal/refcount churn on every re-merge, cache pressure. The **Lower (2-4)** bullet
  must warn it *thrashes*: trigger=2 = **75× WA / 57.9 ms CPU** (not the vague "~3-10×").
- **MINOR-6 — default 8 is "safe under current (limited) evidence," not "proven optimal."** State the bar to
  change it: subprocess-isolated, ≥5 paired-seed, **2–5M-record** runs showing 16 dominates 8 without
  regressing the adversarial-OOO read cliff. Keep the change OUT of scope.
- **MINOR-7 — reconcile the trap with the delete lever:** if `delete_debt_threshold>0`, delete-driven
  compaction still drains the L0 backlog, so a high trigger is *not* the never-compacts trap there.
- **Cross-references (configuration.md MUST link):** `compaction.max_inputs`/`max_windows` (drain cap),
  `delete_debt_threshold` (2nd trigger + delete lever), `window_size` (fence-pruning), `memtable_max_bytes`
  (segment size), `maintenance="disabled"` (manual: user must call flush/compact/maint_step; maint_step
  re-evaluates the trigger each call).

### Net effect on the deliverable
Same docs-only scope, default still 8, but the prose is rewritten to: (1) name all three compaction triggers
and scope the trap precisely; (2) scope every "higher is cheaper" claim to unbounded-max_inputs +
in-order/fence-pruning; (3) present tiering↔leveling as an analogy; (4) state honest in-memory costs and the
trigger=2 thrash numbers; (5) cite only JSON-verified figures with correct N labels and the 23% space fix;
(6) cross-link the five interacting knobs. This is the version to implement.
