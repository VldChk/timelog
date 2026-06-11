# Phase 5 & 8 — Seeding / Classification

Every surviving idea family and decision-significant atom, seeded with a verdict and **evidence** (measured where possible).
This is not a machine-verifiable one-to-one classification of all 176 raw atoms because the raw digest did not
preserve `raw_atom -> canonical_id`. Verdicts:
🟩 worth productionizing next · 🟦 cool-but-costly · 🟥 BS / not-for-us · ⬛ inconclusive (needs > MVP).

The phase-one experiments (exp01/01b/02/03/04/05/06) plus the later serious-audit prototypes
(`C2-*`, `C3-*`, `C4-*`, `C5-*`, `C6-*`, `C7-*`) anchor the high-confidence verdicts. The remaining
items are seeded from research evidence + code grounding.

---

## 🟩 Worth productionizing next — measured win or cheap hardening with clear scope

| Idea | Evidence | Notes |
|------|----------|-------|
| **N1/T1.1 FASTCALL hot positional methods** | **MEASURED on representative methods** (exp01/01b): append −23.7%, point −15.8%, next_ts −14.6%; saved patch covers append/point/next_ts/prev_ts, with 98 facade + 480 core tests green | True low-hanging binding win. Production task is still to convert and benchmark all 10 listed methods, not to assume the remaining six have identical deltas. Stable-ABI since 3.7, FT-safe. |
| **N17/T9 Branchless `lower_bound`** | **MEASURED** (exp02): 3–5× isolated search, point −15.2% end-to-end, 480/480 tests; ~7 LOC | True low-hanging search win. Extend to `tl_page_*`/`tl_recvec_*`. Stacks with FASTCALL (independent code). |
| **N28 ★ Fold facade `append` auto-timestamp into C** | **MEASURED** (exp06): C `append_now` = 107.8 ns vs facade 372.5 ns = **3.46× / −265 ns** — biggest end-to-end win in the lab; 98 facade tests green | High-ROI next PR, but not a trivial patch. MVP built (METH_O, `clock_gettime`). Productionize as real C/facade API work: `METH_FASTCALL\|METH_KEYWORDS` over all 3 append signatures, configured `time_unit`, `_coerce_ts` parity, `_mostly_ordered_default`, and the facade's `min_ts` guard, then delete the Python override. |
| **T2.1/T2.3 typed-buffer `bulk_append(int64_buffer, objects)`** | **MEASURED in prior lab run, but current artifact is patch-only** (C2-bulk): reported 9–10× vs per-append, 2.4× vs `extend`; no raw transcript/JSON is saved in this tree | Strict fast path, not an `extend()` substitute. Before PR, rerun and save bench/test logs. Production fix required: reject or byteswap non-native-endian `int64` buffers before direct-casting, preserve rollback semantics, and use `PyMem_Malloc` for scratch. |
| N3 Don't wire `tp_vectorcall` on the type | research: heap-type / static-type fragility | A decision + code comment; prevents a trap. |
| N8 Never export `h[]` zero-copy | research: handles are encoded `PyObject*` | A safety boundary; corrects doc_24. |
| N10 PEP 688 `collections.abc.Buffer` annotation | research: zero C work (slot already satisfies it) | Facade annotation + 1 test. |
| N11 Gating FT "GIL-disabled" wheel test | research: silent GIL re-enable risk | Move assertion into cibuildwheel cp314t override. |
| N25 Positioning: concurrent-safety + O(1) OOO append | **MEASURED** (exp03): ~11× vs `bisect.insort` OOO @200k; SortedList raises on 3.14t, Timelog 0 errors | Docs/marketing; precise wedge, not overclaim. |
| **N-T4 Document/tune `max_delta_segments`** as the tiering↔leveling dial | **MEASURED** (exp04/C4-knobs): adversarial OOO shows 5.3× read impact when compaction never fires; broader mild workloads show 16/32 can cut compaction CPU with little read cost | Docs + config guidance now; runtime OOO-overlap-adaptive policy is separate subsystem work. |
| T8.21 pytest under `PYTHONMALLOC=debug` | research/doc_35 | Cheap CI safety net. |
| T1.8 exception-safe hot-wrapper discipline | source/doc_35 + existing C-extension risk profile | Cheap hardening checklist: tiny wrappers, early errors, and explicit DECREF audits before optimizing hot paths. |
| T7.16 process-isolated memory phases | source/doc_8 + current lab methodology | Use subprocess-per-cell for memory-sensitive experiments and document worker-restart deployment guidance where RSS return-to-OS matters. |

## 🟦 Cool-but-costly — genuine upside, needs real refactor / new subsystem

| Idea | Why valuable | Cost / risk |
|------|--------------|-------------|
| N5/N6 Arrow C Data Interface export (`__arrow_c_array__`/`__arrow_c_stream__`) | **Prior lab reported** pyarrow/polars zero-copy with pointer identity, but current artifact is patch-only (C3-arrow) | Medium feature, not a trivial patch: timestamp column only, shared export-pin helper, explicit release-callback/thread-state contract, and saved sanitizer/bench logs before PR. |
| N7 DLPack export (`__dlpack__`) | **Prior lab reported** `np.from_dlpack(span)` zero-copy read-only, but current artifact is patch-only (C3-dlpack) | Medium feature: versioned struct + owner-pin deleter, owning-interpreter cleanup constraints, and saved sanitizer/bench logs before PR. |
| N9 Centralize pin-and-release across buffer/Arrow/DLPack | One lifetime contract vs 3 UAF surfaces | Refactor of `py_span.c` owner. Medium. |
| T3.13 Arrow/Velox interop guardrails | Prevent fragile local-only integrations from becoming ABI/support burdens | Add schema/version pinning, bounded fan-out/backpressure, metrics, and support-window docs as part of any Arrow/Velox export feature. |
| N13 Atomic `exports` counter + FT race test | Hardens close-while-exported under 3.14t | Medium; needs FT stress harness. |
| N19 SIMD intra-page final-block scan | Amortize last search levels across a cache line | Runtime CPU dispatch + NEON portability. Medium-high. |
| N22 Batched/vectorized multi-point search API | SIMD throughput (up to ~70× AVX2) across many queries | New API + binding plumbing; only bulk-query users benefit. High. |
| **N-T4 True sub-window granular compaction (Spooky/ICS-inspired)** | would bound the **RAM transient** during wide-OOO compaction, which is the real scarce resource per RUM | High. C4-gran shows the existing `max_compaction_windows` cap is not enough: it trades a small transient reduction for repeated L1 re-merges and ~10x CPU in the spot sweep. Needs new slicing/design, not a config flip. |
| T4 compaction subsystems (ROI gate T4.8, adaptive modes T4.12, EWMA+CUSUM CompactDetector T4.15-21) | Smarter maintenance *decisions* | Now **partly tested** (exp04): the *structure* is already optimal; these are decision-policy refinements on top. Audit overlap with existing adaptive-segmentation first. High. |
| **N-T4 Whole-window drop for TTL/delete** (TWCS idea) | **MEASURED** (C4-wwd): 67–275× pure-C TTL compaction CPU in best case; leak-clean and 480-gated | Workload-specific: wash in CPython/default streaming path due to mandatory `on_drop_handle` flat scan; fix the multi-`delete_range` false-negative first. |
| **Delete-driven L1 reclaim** | **MEASURED GAP** (C5-canon): retention-shaped 50% delete reclaims 0 space under the lab protocol; independent spot-check shows other threshold/window shapes can reclaim | Design + coverage work, not a config flip. The gap is default-disabled/workload-sensitive L1 reclaim, not absence of any reclaim path. |
| **Read-side batching** (`range_read_into`, `scan_many`, `hash_pages`) | Raw docs T2.2/T2.4/T2.5 propose it; C2 measured only ingest | Needs separate API design and measurement. Potentially useful for analytics users, but not proven by `bulk_append`. |

## 🟥 BS / not-for-us — wrong stack, no transfer, or actively unsafe

| Idea | Why dropped |
|------|-------------|
| doc_2 Merkle anti-entropy | Distributed replica sync; Timelog is single-process. |
| doc_22 readinto/mmap/socket zero-copy | Disk/network I/O framing is out of scope; its generic `memoryview`/`frombuffer` material is treated as duplicate of the in-memory buffer ideas in T3/T8, not as a distinct rejected atom. |
| doc_33 io_uring + eBPF compaction offload | Cuts *syscalls* in disk-LSM; Timelog is pure-memory. |
| HPy migration (docs 4/7/20/21) | **Moot** — subinterpreter + FT already achieved without HPy (PyMutex/critical sections/Treiber/seqlock). |
| pyo3 / maturin CI matrix (doc_10/20) | Wrong stack — hand-written C-API, not Rust. |
| Plain **abi3** single-wheel (doc_7/19) | **Incompatible with free-threading until 3.15** (PEP 803 abi3t). Can't serve Timelog's FT users today. |
| PEP 757 for handle int-conversion | Scoped to arbitrary-precision bignums; handles are pointers anyway. |
| T1.3 `PyObject_Vectorcall` in C-core loops | Timelog's drop path is callback-free (Treiber stack) — little/no call site to optimize. |
| Arrow Flight / networked external consumers | Network/service transport is out of scope for an in-memory embedded extension; keep only in-process Arrow C Data export ideas. |
| **Lazy Leveling / Dostoevsky** (the "new popular" LSM strategy) | **exp04-researched:** optimizes *disk* write-amp Timelog doesn't have; L1 is time-windows not a size cascade — no L2..Ln to lazily tier. RUM corner shift. |
| **RocksDB Universal compaction** | **exp04:** space-amp *doubles* during compaction — actively harmful when RAM is the scarce resource. Explicitly reject. |
| **Monkey (Bloom-filter allocation)** | **exp04:** optimizes point-key *existence*; Timelog is a time-range index (fence pointers, no Bloom, no existence test). |
| **k-LSM** | **exp04:** it's a concurrent priority queue, not a compaction policy — a naming false-lead. |
| **N20 Loser/tournament-tree k-way merge** | **MEASURED net-negative (exp05):** binary heap with `replace_top` already wins (0.85–0.92× at K≥16) because `sift_down` short-circuits on same-source replacement. Would be a large, risky refactor for a *loss*. |
| **N18 SoA catalog split** | **MEASURED negligible** (microbench): 1.00–1.05× at realistic catalog sizes (16–1024 pages, already cache-resident); only 1.53× at 4096+ pages = 16M-record segments. The "4× fewer cache lines" is geometrically true but doesn't translate to speed. Not worth the refactor. |

## ⬛ Inconclusive — promising but needs more than an MVP to decide

| Idea | What's needed |
|------|---------------|
| N21 Prefetch on merge page-advance | Research-plausible but unmeasured. Needs a standalone page-advance/k-way merge microbench and an end-to-end OOO read workload before production classification. |
| N23 Interpolation-seeded search | Benchmark on real ts distributions; risky on OOO/clustered worst case. |
| N14 abi3t-in-3.15 migration | Forward-looking; document the checklist now, execute when 3.15 is the floor. |
| N15 PEP 779 single-thread budget CI gate | Needs cp314t-vs-cp314 CI infra. |
| N12 / N16 FT critical-section + borrowed-ref audits | Correctness audits — valuable, but review-not-measure; route through the project's hostile-review process. |
| T6.8-T6.11 subinterpreter isolation/finalizer/opaque-transfer tests | Mostly already covered by the Layer A/B test suite, but the raw idea includes create/destroy stress counts and opaque-transfer probes that should be checklist-mapped before closing. |
| T8.17-T8.19 compaction validation/LLD/select-L0 extraction | Good engineering hygiene from doc_9; not tested as an idea-lab perf win. Keep as CI/refactor backlog, not a measured optimization. |
| T4 ROI gate / CompactDetector / adaptive modes | First audit existing maint/ subsystem for overlap, then prototype + measure on the 3 workloads (T8.10). |
| T7/T8 operational harness atoms not individually ranked above | Several are valuable engineering hygiene but not measured feature wins. Keep as CI/profiling backlog, not performance claims, until each has a specific gate or experiment. |
| "Is Timelog the fastest?" (exp03) | Loses single-thread static range to numpy/bisect; wins OOO append + concurrent safety. Verdict is *workload-dependent*, not absolute. |

---

## Top backlog (ranked by measured ROI)

1. **🟩 Fold facade `append` auto-timestamp into C** — measured **3.46× / −265 ns** end-to-end (exp06), the biggest single win; productionize carefully over all 3 signatures + configured time_unit + `_coerce_ts`/`_mostly_ordered_default` + `min_ts`.
2. **🟩 `bulk_append` typed-buffer ingest** — prior run reported 9–10× vs per-append and 2.4× vs `extend`; rerun/save logs and fix native-endian validation before PR.
3. **🟩 FASTCALL positional hot methods** — measured −15 to −24% on representative methods (exp01/01b); convert and benchmark all 10 before claiming all-method deltas.
4. **🟩 Branchless `lower_bound`** (+ page/recvec variants) — measured −15% point, 3–5× search (exp02), ~20 LOC.
5. **🟦 Arrow C Data + DLPack export on PageSpan** — prior runs reported zero-copy; current tree is patch-only, so rerun/save logs before feature work.
6. **🟦 Delete-driven L1 reclaim** — measured gap: pure deletes retain L1 space until new writes trigger compaction; design needed.
7. **🟦 Whole-window drop for TTL/delete** — buildable after false-negative fix; large pure-C TTL win but not an unconditional CPython/default-path win.
8. **🟩 Document/tune `max_delta_segments`** as the tiering↔leveling dial — measured 5.3× adversarial-OOO read impact and 28× WA swing; adaptive runtime policy is 🟦 subsystem work.

> Wins #1, #2, #3 are **independent and stack** (facade-fold removes the wrapper; FASTCALL removes the
> call-boundary tuple; branchless speeds the in-page search). Ship as one binding+search PR and re-measure.

**Killed by measurement (saved real work):** loser-tree k-way merge (exp05, net-negative at relevant K),
SoA catalog split (microbench, ~1.0× at realistic sizes), and the modern compaction algorithms
(Lazy Leveling / Universal / Monkey / k-LSM — exp04, inapplicable to an in-memory engine).
