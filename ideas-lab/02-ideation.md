# Phase 4 — Ideation on Top (my own + web/PEP research)

5 web-enabled research strands → **40 cited findings, 30 new ideas, 25 corrections** (full provenance in
`_data/research.json`). This layer extends the notes with current (2024–2026) PEP/CPython reality and adds
an entire idea space the notes never touched — **in-memory search/merge algorithmics** — plus my own
measured discovery from the exp01 baseline.

Count note: "30 new ideas" is the raw research-agent count in `_data/research.json`; the canonical
registry below dedupes and merges that material into 28 `N*` entries.

---

## 4.1 Corrections — where the 2-month-old notes are stale or wrong

These matter because several notes' recommendations are built on false premises. All verified against the
tree or primary sources.

| # | Correction | Evidence |
|---|------------|----------|
| C1 | The notes' "binding backend" axis (pyo3 / hpy-hybrid / vectorcall) is fictional. Timelog is a **hand-written CPython C-API** extension; "vectorcall" is just a flag on existing C methods, not a backend. | grep: no pyo3/Cython/HPy |
| C2 | **vectorcall is NOT shipped** (docs 20/29 assume it is). Zero `METH_FASTCALL` in the tree — all hot methods `METH_VARARGS`. A real opportunity. | verified in `py_timelog.c` |
| C3 | doc_36's "register via `tp_vectorcall_offset` (for types)" is the **wrong mechanism** here. Correct lever = `METH_FASTCALL` on the `PyMethodDef`. `tp_vectorcall` is only for making *instances callable*. | PEP 590, c-api/call |
| C4 | "Convert to multiphase init (PEP 489)" is listed as future work (doc_7/19) but is **already done** (`module.c`: `Py_mod_exec`, `Py_mod_multiple_interpreters=PER_INTERPRETER_GIL_SUPPORTED`, `Py_mod_gil=NOT_USED`). | `module.c` |
| C5 | "Target **abi3** to widen install base" (doc_7/19) is **wrong for Timelog now**: PEP 803 shows plain abi3 is *incompatible* with free-threading until the separate `abi3t` variant in 3.15. A single abi3 wheel can't serve FT users. | PEP 803, PEP 793 |
| C6 | Free-threading is **officially supported (PEP 779, Phase II, 3.14)** — not "aspirational/when available." Drop experimental hedging; Timelog already ships cp314t. | PEP 779 |
| C7 | doc_24's "export ts[] **and h[]** as Arrow columns" is **wrong for h[]**: handles encode `PyObject*` pointers, not numeric data — must stay opaque behind `objects()`/`tl_py_handle_decode`. | Arrow CDI spec |
| C8 | PEP 757 does **not** speed the handle path (scoped to arbitrary-precision bignums). For fixed uint64 the new APIs are `PyLong_From/AsUInt64` (3.14), and even those don't apply since handles are pointers. | PEP 757 |
| C9 | CLAUDE.md's "**~4KB page**" is stale — actual default is **64 KiB** (`TL_DEFAULT_TARGET_PAGE_BYTES`, ~4096 records, ~32 KiB `ts[]`). This is what makes search micro-opts (branchless/SIMD/prefetch) relevant, not negligible. | verified `tl_defs.h:27` |
| C10 | doc_33 (io_uring + eBPF compaction offload) is inapplicable — Timelog is strictly in-memory, no syscalls. | ground truth |
| C11 | HPy is **not needed and not adopted**; subinterpreter isolation + FT were already achieved without it (PyMutex / critical sections / Treiber stack / seqlock). The HPy-centric migration plans (docs 4/7/20/21) are moot. | `module.c`, CLAUDE.md |
| C12 | cibuildwheel 3.0 builds **cp314t by default** (no enable flag); only cp313t needs `CIBW_ENABLE`. The notes' conditional framing is outdated. | cibuildwheel 3.0 |

## 4.2 New ideas (beyond the notes)

Effort/confidence are the researchers' honest ratings, adjusted by my grounding. **★ = my own discovery**
or a materially sharpened version. IDs continue into the seeding/classification (Phase 5).

### Calling convention (extends T1)
| ID | Idea | Effort | Conf |
|----|------|:------:|:----:|
| N1 | Convert all **10 positional-only** `METH_VARARGS` methods to `METH_FASTCALL` (append ✓ done in exp01; +range/since/until/point/equal/next_ts/prev_ts/delete_range/delete_before). | low | high |
| N2 | FASTCALL microbench on **3.13 *and* 3.14t**, asserting the temp-tuple elimination via `sys.getallocatedblocks()` delta (not just ns/call). | med | high |
| N3 | **Do not** wire `tp_vectorcall_offset` on the Timelog/PageSpan types (static `IMMUTABLETYPE`; heap types never inherit vectorcall). Document the rationale in-code. | low | high |
| N4 | Defer kwargs methods (`extend`, `page_spans`) to `METH_FASTCALL\|METH_KEYWORDS` only once public `PyArg_ParseArray()` (CPython PR #144283, Jan 2026) ships in a targetable release. | med | med |
| **N28 ★** | **Fold the facade's 3 append signatures into a `METH_FASTCALL\|METH_KEYWORDS` C method** (auto-timestamp via `clock_gettime` in C) and delete the Python override. *Measured:* the wrapper costs **~181 ns** (facade 307 vs raw-C 126) — bigger than the entire C call. Potential end-to-end append ~307→~110 ns (**~2.8×** predicted). *→ exp06 BUILT & measured: 372.5→107.8 ns = **3.46×**.* | med | high |

### Zero-copy / interop (extends T3)
| ID | Idea | Effort | Conf |
|----|------|:------:|:----:|
| N5 | `__arrow_c_array__` on PageSpan exporting `ts[]` as non-null int64 Arrow column (vendored **nanoarrow**); owner-pin in `private_data`, dropped in release callback. Reaches PyArrow≥15 / Polars≥1.3 zero-copy. | med | high |
| N6 | `__arrow_c_stream__` on a span-iterator — **fresh snapshot per call** (the DuckDB #17084 one-shot-stream rule), one RecordBatch per page across L0/L1. | high | high |
| N7 | `__dlpack__`/`__dlpack_device__` on PageSpan (READ_ONLY flag, kDLCPU, int64) — reaches **torch/jax/cupy** which can't speak PEP 3118. Genuine gap in the notes. | med | med |
| N8 | **Never** vend `h[]` zero-copy (encoded pointers) — keep payloads opaque. Safety boundary. | low | high |
| N9 | Centralize the pin-and-release logic so `bf_getbuffer` + `__arrow_c_array__` + `__dlpack__` all route one core helper (one lifetime contract, one critical section). | med | med |
| N10 | Annotate facade PageSpan returns with `collections.abc.Buffer` (PEP 688, zero C work) + version-gated interop tests. | low | high |

### Free-threading / packaging (extends T6/T8)
| ID | Idea | Effort | Conf |
|----|------|:------:|:----:|
| N11 | **Gating** "import-and-assert-GIL-disabled" wheel test inside the cibuildwheel cp314t override (a silently GIL-re-enabled wheel must fail the build). | low | high |
| N12 | Audit every `Py_BEGIN_CRITICAL_SECTION` (L4) region for *blocking while held* — FT docs: a critical section is **suspended** (lock dropped) if the thread blocks. Add a debug assert. | med | med |
| N13 | Make PageSpan's `exports` counter atomic + an FT stress test racing `getbuffer`/`releasebuffer` vs `close()` on 3.14t. | med | med |
| N14 | Don't pursue plain abi3; record the **abi3t-in-3.15 migration checklist** (static→heap types, `PyModExport`, opaque PyObject). | low | high |
| N15 | A **PEP 779 single-thread budget** CI gate: cp314t ≤15% slower than cp314 on Timelog's own append/range microbench. | med | med |
| N16 | Audit borrowed-ref patterns (prefer `*_GetItemRef`) in `extend()`/`append()` fast paths under FT. | med | med |

### In-memory search & merge — **the novel frontier** (new theme T9; notes never touched it)
| ID | Idea | Effort | Conf |
|----|------|:------:|:----:|
| **N17** | **Branchless cmov `lower_bound`** for `tl_record_lower_bound` (+ `tl_page_lower/upper_bound`, `tl_recvec_*`). No layout change, no invariant impact. Measured precedent ~1.8–2× on the search itself. | low | high |
| N18 | **SoA catalog split**: dense `max_ts[]` separate from `tl_page_meta_t[]` → ~4× fewer cache lines in catalog navigation (currently 32 B/entry = 2 keys/line; dense int64 = 8/line). | med | med |
| N19 | **Hybrid intra-page search**: branchless binary search down to a ~16–32 window, then AVX2/AVX-512 (GCC/Clang vector ext + runtime dispatch) linear scan of the final block. | med | med |
| N20 | **Loser/tournament tree** for `tl_merge_iter`/`tl_submerge` k-way merge — ~halves comparisons (log k vs 2·log k). Honest expectation single-digit-%→~1.5× (already uses flat-array `replace_top`), *not* Grafana's 5–12×. | high | med |
| N21 | **Software prefetch** on segment/page advance in k-way merge — the page walk is sequential/predictable, a textbook prefetch pattern. | low | med |
| N22 | **Batched/vectorized multi-point search** API (SIMD across many queries) — pairs with a FASTCALL bulk API; gain only for bulk-query users. | high | low |
| N23 | Interpolation-**seeded** binary search for near-uniform in-order pages (one probe → bounded branchless search), guarded against OOO/clustered worst case. | med | low |

### Positioning & benchmarking (extends T8)
| ID | Idea | Effort | Conf |
|----|------|:------:|:----:|
| **N24** | **Competitive benchmark**: Timelog vs `bisect.insort`, `sortedcontainers.SortedList`, `numpy searchsorted`, `pandas DatetimeIndex` across (a) append throughput, (b) range p50/p99, (c) **concurrent N-writer/M-reader correctness+throughput on 3.14t**. | med | high |
| N25 | Lead positioning on **concurrent-mutation safety** (numpy/pandas/SortedList are unsafe under FT — cited) + **O(1) append vs bisect O(n)**. Not "they don't run on FT" (false — wheels exist); the precise wedge is *safe concurrent mutation*. | low | high |
| N26 | Borrow **TSBS query shapes** (lastpoint, groupby-orderby-limit) as benchmark vocabulary; don't claim to beat QuestDB on rows/s — wrong quadrant (server SQL vs embedded per-op latency). | low | med |
| N27 | Roaring-bitmap design as a reference for the **tombstone interval set** (`core/src/internal/intervals`) — internal opt, not a positioning rival. | med | low |

`★ Insight ─────────────────────────────────────`
**The research's biggest contribution is what it *removed* from the idea space.** Roughly a third of the
original notes (HPy migration, pyo3/abi3 packaging, io_uring compaction, exporting h[] as Arrow) are
**dead ends** for Timelog specifically — wrong stack, already-done, or actively unsafe. Pruning these is as
valuable as the additions: it stops the lab from "exploring" work that can't pay off. The genuinely new,
high-value space is **search/merge algorithmics (T9)** — which the LSM-policy-heavy notes completely missed,
and which is where an *in-memory* index actually lives or dies.
`─────────────────────────────────────────────────`
