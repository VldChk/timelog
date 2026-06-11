# Timelog Creativity Lab — Final Report

*An open-minded scientific sweep of the `.ideas/` heap: deduplicate → theme → exhaust → research →
**build & measure** → seed. Evidence before assertions. Historical phase-one report; see
`AUDIT_REPORT.md` for the current final classification.*

**Date:** 2026-06-04 · **Branch:** `timelog-experiments` @ `e7e7efb` (1.2.0 baseline) · **Env:** Linux, GCC 13,
pyenv CPython 3.13.12 + 3.14.3 + 3.14.3t (free-threaded).

> **Superseded note:** this is the phase-one creativity-lab report. The later serious audit added C2/C3/C4/C5/C6/C7
> prototypes and corrected several classifications. Use `AUDIT_REPORT.md` as the current final seed.

---

## TL;DR — the headline

From 37 messy notes I distilled a deduplicated, family-level idea space, layered current PEP/CPython research
on top (adding an entire **search-algorithmics** seam the notes missed), then **actually built and measured
six experiments in isolated worktrees** — including the biggest theme (compaction) and two ideas the
measurements *killed*. The phase-one measured production candidates:

| Experiment | Change | Measured result | Tests |
|------------|--------|-----------------|-------|
| **exp01/01b — `METH_FASTCALL`** | flip representative hot methods off `METH_VARARGS` (~6 LOC each) | append **−23.7%**, point **−15.8%**, next_ts **−14.6%** | 98 facade + 480 core ✅ |
| **exp02 — branchless `lower_bound`** | one inline fn, ~7 LOC, no layout change | isolated search **3–5×**, point **−15.2%** end-to-end | 480 core ✅ |
| exp03 — competitive positioning | no core change | **~11×** vs `bisect.insort` (OOO append); SortedList raises reader exceptions on 3.14t, Timelog 0 errors | — |
| **exp04 — compaction strategy** | measure + research the largest theme | OOO read-amp **5.3×** without compaction (3-repeat confirmed); whole-window-drop **verified unimplemented**; modern strategies (Lazy Leveling/Universal/Monkey) **rejected** for an in-memory engine | 480 core ✅ |
| **exp06 — fold facade `append` into C ★** | C `append_now` (auto-ts in one call) | facade `append(obj)` 372.5 → **107.8 ns = 3.46×** (−265 ns); biggest end-to-end win | 98 facade ✅ |
| exp05 — loser-tree k-way merge | tournament tree vs binary heap | **🟥 net-negative** (0.85–0.92× at K≥16): heap's `replace_top` short-circuits; saved a big refactor | — |

The phase-one binding/search wins are **independent and stack**. Later audit work keeps FASTCALL and
branchless search as true low-hanging PRs, but classifies facade-fold as a high-ROI production rewrite
that must preserve the Python facade contract exactly.

---

## 1. What was processed (Phases 0–1)

- **37 files** → md5 dedup → **34 unique** (3 exact-dup pairs: 7≡19, 12≡23, 13≡25).
- 12-agent fan-out digested them into **176 atomic ideas** (`00-raw-catalog.md`, `_data/raw-digests.json`).
- Relevance, judged against Timelog's *real* architecture (in-memory, C17 core + hand-written CPython
  C-API, no I/O): **23 core · 8 tangential · 3 irrelevant**.
- **Dropped as irrelevant:** Merkle anti-entropy (distributed), readinto/mmap (disk/socket I/O),
  io_uring+eBPF (syscall offload) — none transfer to an in-memory extension.

## 2. The idea space (Phases 2–3 — `01-themes.md`)

176 atoms → **8 deduped, mutually-exclusive themes**, each with a family-level complete idea list:
T1 calling-convention/vectorcall · T2 batch/bulk APIs · T3 zero-copy/Arrow/NumPy · T4 compaction
strategy & scheduling · T5 tombstones/deletes · T6 subinterpreters/free-threading/HPy · T7 memory &
allocator · T8 CI/benchmark/profiling. A **ground-truth correction** threaded through all of them:
*the notes assume vectorcall is already shipped — it is not* (verified: every hot method is `METH_VARARGS`).

## 3. What research added — and removed (Phase 4 — `02-ideation.md`)

5 web-enabled strands → **40 cited findings, 30 new ideas, 25 corrections** (`_data/research.json`).

- **Added a whole new theme — T9 in-memory search/merge algorithmics** (branchless/Eytzinger/SIMD/
  loser-tree/prefetch) that the LSM-policy-heavy notes never touched — and which is where an *in-memory*
  index actually lives or dies.
- **New interop ideas** the notes lacked: Arrow **PyCapsule** dunders, **DLPack** (reaches torch/jax),
  PEP 688 buffer annotation.
- **Pruned ~⅓ of the notes as dead ends for Timelog specifically:** HPy migration (already achieved
  without it), pyo3/abi3 packaging (abi3 is *incompatible* with free-threading until 3.15 — PEP 803),
  exporting `h[]` as Arrow (unsafe — encoded pointers), PEP 757 for handles (wrong scope). *Pruning bad
  ideas is as valuable as adding good ones.*
- Corrected stale facts: CLAUDE.md's "~4KB page" is actually **64 KiB**; free-threading is now
  **officially supported** (PEP 779), not aspirational.

## 4. Experiments built & measured (Phases 6–7 — `experiments/`)

Binding-path measurements: Release, pinned core, median of 5, re-validated in a single back-to-back session
(`_bench/clean_3way_3.13.json`) to eliminate cross-build drift. Standalone C microbenchmarks use their
own harness protocol (for example best-of-5/7 inner loops) as documented in each `bench_*.c`.

### exp01 / exp01b — `METH_FASTCALL` on the hot methods  🟩
`METH_VARARGS`+`PyArg_ParseTuple` → `METH_FASTCALL` removes the per-call args-tuple allocation. Applied
to `append`, `point`, `next_ts`, `prev_ts`. **append −23.7%, point −15.8%, next_ts −14.6%.** Error paths
(arity, non-int, overflow) correct; 98 facade + 480 core tests green; FT-safe (args borrowed, only read
during call; `append` INCREFs before storing). Matches published precedent (Stinner: 1.56× on `struct.pack`).

### exp02 — Branchless `lower_bound`  🟩
The branchy binary search in `tl_search.h` (the most-used search) → branchless cmov form (arithmetic
offset). **3–5× on the isolated search for page-sized arrays; −15.2% on the `point` path end-to-end;
480/480 core tests pass.** The microbench also *reproduced the research's nuance*: at 1M rows branchless
*loses* (branchy speculation hides DRAM latency) — but Timelog's pages cap at ~4096 records, in the
winning regime. The experiment told us *why*, not just *whether*.

### exp03 — Competitive positioning  ⬛→🟩
Deliberately adversarial to my own hypothesis (it caught three ways my first framing was unfair). Honest
outcome: Timelog is **not** the fastest single-thread static range index (numpy/bisect win that), but it
**is** the clear winner on its real wedge — **O(1) out-of-order append (~11× vs `bisect.insort` at 200k)**
and **snapshot-isolated, never-torn, non-blocking concurrent reads over arbitrary Python objects under
free-threading**, where `SortedList` raises exceptions and Timelog completes the most reads with zero errors.

### exp04 — Compaction strategy: measure + research the biggest theme  ⬛→🟩
The largest theme in the notes (and the one the first pass skipped). `maint_step()` (not async `compact()`)
drives compaction; probing the L0→L1 transition shows Timelog implements **tiered-L0 + leveled
time-windowed-L1** — structurally **RocksDB 1-leveling × Cassandra TWCS**, i.e. *the hybrid the literature
converged on*. Measured: read-amp grows 1.0→1.7× with L0 depth; **OOO ingest → 5.3× read penalty unless
compaction fires** (3-repeat confirmed); compaction reclaims 12.5% space; `max_delta_segments` is the
tiering↔leveling dial. Trigger=8 is a conservative knee in the adversarial OOO run; broader mild-workload
sweeps show 16/32 can reduce compaction CPU with little read cost, so adaptive policy is the real follow-up.
Research verdict on the "new popular strategy": it's **Lazy Leveling / Dostoevsky** — but it (and Universal,
Monkey, k-LSM) is **inapplicable**: every modern strategy optimizes *disk* write-amp, and via the **RUM
conjecture** Timelog sits at a different corner (in-memory U is free; RAM-M is scarce). The two genuinely
transferable ideas — both verified/researched, not yet built: **(1) whole-window drop** for TTL/delete
(measured unimplemented — compaction *merges* fully-tombstoned windows instead of O(1)-dropping them),
**(2) true sub-window granular compaction** to bound the RAM transient; the existing cap alone is insufficient.

### Key measurement discipline lessons
- *Re-measure competing variants in one session* — per-build deltas were inflated ~2–3 pts by drift.
- *A benchmark that flatters you teaches nothing* — in-order inserts hid bisect's O(n); the GIL hid the
  concurrency story; both had to be fixed for the result to be trustworthy.
- *Verify every "Timelog already does X" claim against the tree* — agents hallucinated `METH_FASTCALL`.

## 5. Seeding / classification (Phase 8 — `03-classification.md`)

- 🟩 **Worth productionizing (measured):** fold facade `append` into C (3.46×, exp06; production must preserve all facade
  semantics), FASTCALL (exp01), branchless search (exp02), and `max_delta_segments` documentation (exp04);
  plus PEP 688 annotation, FT
  GIL-assert wheel test, positioning docs, don't-export-h[].
- 🟦 **Cool-but-costly:** Arrow/DLPack export, whole-window-drop/delete reclaim, true sub-window granular compaction
  (the one modern-LSM idea that fits an in-memory engine), SIMD intra-page search.
- 🟥 **BS/not-for-us (incl. measured kills):** loser-tree merge (exp05, net-negative), SoA catalog (~1.0×),
  Lazy Leveling/Universal/Monkey/k-LSM (exp04, inapplicable in RAM); Merkle, mmap/socket I/O, io_uring/eBPF,
  HPy, pyo3, plain abi3, PEP 757 for handles.
- ⬛ **Inconclusive / partly-realized:** T2 batch APIs (`extend` 1.51× but typed-buffer bulk has headroom),
  interpolation search, FT correctness audits, compaction-ROI prototypes.

## 6. Recommended backlog (ranked by measured ROI)

1. 🟩 **Fold facade `append` auto-timestamp into C** — measured **3.46× / −265 ns** (exp06), biggest single win;
   high ROI but not a trivial patch.
2. 🟩 **FASTCALL positional hot methods** — proven −15…−24% on representative methods (exp01/01b); all 10 need conversion+measurement before an all-method claim.
3. 🟩 **Branchless `lower_bound`** (+ page/recvec) — proven −15% point, 3–5× search (exp02), ~20 LOC.
4. 🟦 **Whole-window drop / delete reclaim** — later serious audit found this is workload-specific in CPython and
   needs false-negative fixes plus delete-driven L1-reclaim design.
5. 🟩 **Document/tune `max_delta_segments`** as the tiering↔leveling dial — 5.3× adversarial-OOO read impact (exp04);
   adaptive runtime policy is separate work.
6. 🟦 **Arrow C Data + DLPack export on PageSpan** — later C3 prior runs reported zero-copy, but current artifacts are patch-only; still feature work because release/lifetime contracts matter.
7. 🟦 **True sub-window granular compaction** — possible RAM-transient fix, but C4-gran shows the current cap is not enough.

*Wins #1–#3 are independent and stack. **Killed by measurement** (saved real work): loser-tree merge
(exp05, net-negative), SoA catalog split (~1.0× at realistic sizes), and the modern compaction algorithms
(Lazy Leveling / Universal / Monkey — inapplicable in RAM).*

## 7. Honest limitations

- exp01/02 are **lab MVPs**, not merge-ready: productionize under ASan/UBSan/TSan + 3.14t + the project's
  differential/property suite (per the zero-regression matrix) before a PR.
- The **compaction-strategy** theme (T4) is now measured *and* researched (exp04), but the runs are
  200–400k records single-process; a production decision wants ≥2–5M records, subprocess-per-cell
  isolation, and ≥5 paired-seed repeats (the OOO 5.3× headline *is* 3-repeat confirmed). The two surgical
  wins it surfaced (whole-window-drop, true granular compaction) are verified/researched, but granular needs a new design beyond the existing cap.
- exp03's concurrency story would be sharper with competitor libs installed in 3.14t and a throughput-vs-
  cores scaling plot (readers × cores).
- SIMD remains research-seeded; loser-tree was measured net-negative; Arrow/DLPack were later built and measured in the serious audit.

## 8. Lab artifact map

```
ideas-lab/
├── README.md                  phase tracker / index
├── 00-raw-catalog.md          per-doc digest + dedup + relevance (Phase 1)
├── 01-themes.md               deduped exhaustive idea registry, 8 themes (Phases 2-3)
├── 02-ideation.md             research: 30 new ideas + 25 corrections (Phase 4)
├── 03-classification.md       seeding: 🟩/🟦/🟥/⬛ with evidence (Phase 8)
├── REPORT.md                  this file (Phase 7)
├── _data/                     raw-digests.json, research.json (provenance)
└── experiments/
    ├── _bench/                microbench.py, baseline + clean_3way_3.13.json
    ├── exp01-fastcall-append/ RESULT.md + patches (worktree exp/fastcall-append)
    ├── exp02-branchless-search/ RESULT.md + bench_lower_bound.c (worktree exp/branchless-search)
    ├── exp03-competitive/     RESULT.md + competitive_bench.py (3.13 + 3.14t concurrency)
    ├── exp04-compaction/      RESULT.md + compaction_bench.py + confirm.py (read/write/space + OOO 5.3×)
    ├── exp05-loser-tree/      RESULT.md + bench_kmerge.c (heap vs tournament tree — killed)
    └── exp06-facade-fold/     RESULT.md + patch (append_now, 3.46× — biggest win)
```
Reproduce the binding/search experiments from the saved patches; the worktrees `timelog-wt-fastcall`
(`exp/fastcall-append`) and `timelog-wt-search` (`exp/branchless-search`) hold the live builds.

---

*Open mind, open heart — and a profiler. The two cheapest changes in this report (~80 LOC combined) are
also two of the largest measured wins. The biggest single end-to-end prize (the ~181 ns facade wrapper)
was invisible until measurement exposed it. That is the whole point of a lab.*
