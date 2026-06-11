# exp04 — Compaction strategy: measured + researched (theme T4)

The biggest theme in the notes, and the one the first lab pass shamefully skipped. This time it's
**measured** (5 sub-experiments from Python) **and** grounded in the modern LSM literature (2 completed
research strands, with one failed strand recorded in `_data/compaction-study.json`).

## The question answered first: what *is* Timelog's compaction strategy?

`maint_step()` drives it (NOT `compact()`, which is async and merely *requests* work). Probing the
L0→L1 transition shows: Timelog implements **one** policy — **tiered overlapping L0 → leveled,
time-windowed non-overlapping L1**. Each time window collapses to exactly one L1 segment. Research
confirms this is structurally **RocksDB "1-leveling" (tier-L0 + level-above) crossed with Cassandra
TWCS** — i.e. Timelog *already independently arrived at the hybrid the literature converged on*. The
STCS↔LCS (tiering↔leveling) axis is the single knob **`max_delta_segments`** (the L0 trigger).

## Measurements (Release, 3.13, pinned core; full run `exp04_3.13.json`, confirmation `exp04_confirm.json`)

### Exp1 — Read amplification vs L0 depth (clean depth control; point = purest signal)
| L0 segments | point p50 | vs depth-1 | range p50 | pages |
|---|---|---|---|---|
| 1 | 581 ns | 1.00× | 2655 | 65 |
| 8 | 591 ns | 1.02× | 3526 | 72 |
| 32 | 691 ns | 1.19× | 4539 | 96 |
| 128 | 982 ns | **1.69×** | 4629 | 128 |
| compacted→1×L1 | 581 ns | 1.00× | — | 65 |

→ Read latency grows monotonically with merge fan-in; compacting back to one L1 segment **restores
depth-1 speed**. Read-amp is real but gentle for *in-order* data (disjoint segment ranges prune well).

### Exp4/5 — OOO ingest: the 5.3× finding (confirmed, 3 paired-seed repeats)
With **out-of-order** ingest, the same 16 L0 segments each span the whole time domain → every query
must merge all 16:

| `max_delta_segments` | compactions | segments re-merged (WA) | point p50 | space |
|---|---|---|---|---|
| 2 | 8 | 23 | 601 ns | 49 pages |
| **8 (default)** | 2 | **17** | **601 ns** | 49 pages |
| 32 | 0 | 0 | **3166 ns** | 64 pages |
| never compact | 0 | 0 | 3166 ns | 64 pages |

→ **When compaction fires, OOO reads are 5.3× faster and use 31% less space.** A too-high trigger
(≥32 with only 16 L0) **silently never compacts** — a latent misconfiguration trap. The corrected
write-amp proxy (`select_l0_inputs+select_l1_inputs`, segments re-merged) shows **trigger=8 is a good
conservative knee for this adversarial OOO case**: same ~600 ns reads as trigger=2 but 26% less rewriting
(17 vs 23 segments). trigger=2 wastes write-amp; trigger=32 wastes 5.3× read latency. The broader C4 knob
matrix shows 16/32 can be better for mild workloads, so this is evidence for workload-adaptive policy
rather than a universal default proof.

### Exp3 — Space: compaction reclaims **12.5%** of pages by merging overlapping L0.

## Research verdict: is there a better strategy to adopt? (the "4 strategies + new popular one")

The "new popular strategy" you remember = **Lazy Leveling / Dostoevsky** (Dayan & Idreos, SIGMOD'18) —
tier everywhere except the largest level. **But every modern strategy's benefit is denominated in *disk*
write-amplification** (flash wear / I/O bandwidth), and via the **RUM conjecture** Timelog sits at a
*different corner*: its Update cost is in-memory memcpy with no fsync/wear (nearly free), and its scarce
resource is **RAM (M)**, not write-amp (U). So:

| Strategy | Verdict for Timelog | Why |
|---|---|---|
| **Lazy Leveling / Dostoevsky** | 🟥 inapplicable | optimizes disk WA Timelog doesn't have; L1 is time-windows not a size cascade — no L2..Ln to lazily tier |
| **RocksDB Universal** | 🟥 reject | space-amp *doubles* during compaction — actively harmful when RAM is scarce |
| **Monkey (Bloom alloc)** | 🟥 inapplicable | optimizes point-key *existence*; Timelog is a time-range index (fence pointers, no Bloom) |
| **k-LSM** | 🟥 false lead | it's a concurrent priority queue, not a compaction policy |
| **STCS / LCS classics** | ⬛ already spanned | L0=bounded-tier (STCS idea), L1=non-overlap (LCS idea) — both already present |
| **TWCS** | 🟩 closest analog | Timelog's L1 *is* TWCS structurally; source of the best untapped idea ↓ |
| **Spooky / ScyllaDB ICS** | 🟦 only as a larger design | *granularity*, not tiering: bound the RAM transient; C4-gran shows the existing cap is not enough |

## The two genuinely transferable ideas (vs adopting a whole new algorithm)

1. **🟦 Whole-window drop for TTL/delete (TWCS idea, workload-specific) — VERIFIED UNIMPLEMENTED (`confirm.py`/probe):**
   because L1 windows are non-overlapping in *time*, a delete/tombstone that fully covers a window can drop
   that entire L1 segment as an **O(1) manifest edit** instead of a merge. **Measured today it does not:**
   (a) a pure delete (no new L0) reclaims *nothing* — fully-tombstoned windows stay resident (6 L1 / 6
   pages unchanged after deleting 3 of 6 windows), filtered only at read time; (b) when a later compaction
   engages, it **merges/rewrites** the fully-covered windows (`select_l1_inputs += 5`, pages 6→4) instead
   of dropping them. Natural fit for retention/TTL — the dominant delete shape for a time index — so this
   wasted merge work is real. Later C4-wwd prototype/review showed the pure-C TTL case is large but the CPython
   binding path needs flat `on_drop_handle` cleanup and a multi-`delete_range` false-negative fix before this is
   production-simple. The seam is `tl__compact_select_l1` (skip + drop fully-tombstoned windows instead of selecting them).
2. **🟦 True granular / sub-window compaction (Spooky/ICS idea, larger design):** today a wide L0 timestamp
   spread can rewrite *all* window-overlapping L1 segments in one pass, transiently holding old+new copies
   — a Full-Merge RAM spike. C4-gran shows the existing `max_compaction_windows` cap is not sufficient:
   it slightly reduces the largest transient but repeatedly re-merges L1 and costs much more CPU. A real
   fix needs new sub-window slicing or another policy that avoids repeatedly touching the same L1 windows.

## Verdict: ⬛→🟩 No new *algorithm* is worth adopting — the strategy is already right
Timelog's compaction is the literature-convergent hybrid; the modern "new popular" strategies all optimize
a resource (disk WA) Timelog doesn't pay. **The real wins are tuning + two surgical additions:**
1. 🟩 Tune/document `max_delta_segments` as the tiering↔leveling dial (measured **5.3×** read impact on
   adversarial OOO; trigger=8 is conservative there; warn about the too-high-trigger "never compacts" trap).
2. 🟦 Whole-window drop for TTL/delete (O(1) reclaim in pure-C TTL; workload-specific in CPython).
3. 🟦 True sub-window granular compaction to bound the RAM transient; not solved by the existing cap.
4. 🟥 Explicitly reject Universal / Monkey / structural lazy-leveling / k-LSM (record the rationale).

## Honest methodology caveats
Single-process (not subprocess-per-cell), in-order Exp1/2 are single-shot (the OOO headline *is* 3-repeat
confirmed); WA is a segment-count proxy (`select_*_inputs`), not bytes; workloads are 200–400k records
(the review recommends ≥2–5M for steady-state write-amp). Effects reported (5.3×, 1.7×, 12.5%) are large
relative to observed variance, but a production decision should use the review's full protocol
(subprocess isolation, ≥5 paired-seed repeats, 2–5M records, `thread_time_ns` compaction CPU).
