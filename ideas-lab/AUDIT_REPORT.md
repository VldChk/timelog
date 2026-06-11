# Timelog Serious Audit — Final Seeded Report

*A real audit, not a cherry-pick: every large theme got either a prototype **built in an isolated,
reversible worktree**, a direct measurement study, or an explicit code audit — then seeded by evidence.
Built C prototypes were gated on the 480-core + 98-pytest suites where applicable. Where the answer was
"already done" or "doesn't help," that is reported as honestly as the wins.*

**Baseline:** `e7e7efb` (never modified). **Method & isolation contract:** `AUDIT.md`. **Per-prototype
detail:** `FLEET_RESULTS.md` + `experiments/<id>/`. **Reusable infra built:** `harness/compaction_lab.py`,
`run_matrix.py`, `mem_probe.py`, `delete_lab.py`.

---

## 1. The shape of the result

17 experiments/verifications, including saved C patches, strict-buildable C/Python harnesses, measurement studies,
2 measurement-killed ideas, and several "already-implemented" verifications. Some prior-run claims (notably C2/C3)
are preserved as patch-only provenance and require rerun transcripts before production PRs. Two compaction follow-ups
remain seeded design work rather than built prototypes. The
single most important meta-finding:

> **The 2-month notes materially overestimated what's missing.** A large share of the proposed
> "improvements" are *already implemented and correct* in Timelog. The genuinely new value is concentrated
> in the **binding/interop surface**, and the one real *gap* the audit surfaced is **delete-driven space reclaim**.

## 2. Final summary — confirmed actions and current boundaries

`feat/perf-wins` contains production-worthy work. The current dirty tree has
also had the latest compatibility/docs findings fixed and revalidated. Fresh
current-tree proof covers regular CPython 3.13, ASan/UBSan, a release 3.14t
`PYTHON_GIL=0` full Python suite, docs/static guards, JSON artifact validity,
same-harness perf A/B for the changed Python-call hot paths, the opt-in
branchless benchmark, native/core TSan, and a supplemental oracle correctness
run that includes non-context-manager usage. The final pass also found and fixed
a free-threaded build-system bug: CMake was not defining `Py_GIL_DISABLED=1` for
binding objects compiled against a free-threaded interpreter, so CPython object
critical sections could compile out. Larger lab runs on this same dirty tree
are now split: 3.13 remains preserved June 9 evidence, while release 3.14t
`PYTHON_GIL=0` was rerun after the build fix and passed.

### 🟩 Worth productionizing — measured wins (current tree built; 3.13 full Python + CTest, ASan/UBSan, 3.14t GIL-off full Python + CTest, focused free-threaded TSan)

- **Fold the facade `append` path into C** — still the hottest user-facing win.
  Fresh pinned same-harness A/B vs clean `e7e7efb` shows
  `append(obj)` **4.39×** faster, `append(ts, obj)` **3.39×** faster, and
  `append(obj, ts=...)` **3.33×** faster (raw medians preserved in
  `ideas-lab/verification/perf_ab_extended_summary_2026-06-09.md`). Current
  production shape is confirmed:
  the real `append` API is `METH_FASTCALL|METH_KEYWORDS`, supports all three
  signatures, preserves configured `time_unit`, auto timestamps,
  `mostly_ordered`, and the C-owned `min_ts` floor, and removes the Python
  override. The text signature now keeps legacy keyword binding working
  (`obj_or_ts`, `obj_or_none=None`), and lifecycle races are documented as
  externally serialized rather than implied safe.

- **`METH_FASTCALL` on the 9 positional query/delete methods** —
  `range`, `since`, `until`, `equal`, `point`, `next_ts`, `prev_ts`,
  `delete_range`, and `delete_before`. Fresh pinned same-harness A/B shows all
  changed raw call surfaces faster: `point` **1.36×**, `equal` **1.28×**,
  `next_ts` **1.31×**, `prev_ts` **1.15×**, `range` **1.26×**, `since`
  **1.27×**, `until` **1.23×**, `delete_before` **1.36×**, and
  `delete_range` **1.36×** (same preserved A/B artifact). Review found the
  borrowed-argument/refcount shape
  sound: borrowed `args[]` are consumed inside the call, and values that outlive
  the call are promoted before storage. Fresh focused 3.13, full regular,
  ASan/UBSan, and 3.14t GIL-off full-suite gates passed.

- **Size-gated branchless lower/upper bound** — keep the implementation, with a
  bounded performance claim. Correctness coverage reaches all five changed seams
  and covers exact matches, misses, duplicates, extremes (`TL_TS_MIN` /
  `TL_TS_MAX`), and branchless↔branchy boundaries. The direct five-seam
  benchmark now runs `tl_record_lower_bound`, `tl_recvec_lower_bound`,
  `tl_recvec_upper_bound`, `tl_page_lower_bound`, and `tl_page_upper_bound`.
  This run showed **1.93-4.98×** speedups at the gated sizes across all seams and
  exited successfully with no correctness mismatches. It did print **1 advisory
  fallback timing warning** on one recvec size above the gate, so do not claim
  large-size fallback is warning-free across every seam without a cleaner A/B
  benchmark. Raw output is preserved in
  `ideas-lab/verification/branchless_five_seam_benchmark_2026-06-10.txt`.

- **Document/ship `max_delta_segments` as the tiering/leveling dial** — the
  guidance is ready to carry forward. The recorded matrix supports a large
  write-amplification / compaction-CPU tradeoff and an adversarial overlap read
  penalty; the default `8` remains conservative. The docs artifact now includes
  replay commands, seeds, source-tree provenance, and raw JSON for the matrix and
  adversarial confirmation. `compact()` wording now correctly says it requests
  compaction; background maintenance or `maint_step()` performs the work.

- **Hardening/docs bundle** — ship with the performance work. Confirmed guardrails:
  no heap-type `tp_vectorcall`, no numeric export of encoded `h[]` handles,
  PEP 688-visible buffer behavior, free-threaded import sanity, uniform
  `PageSpanObjectsView` invalidation after parent span close, and positioning
  that says Timelog's wedge is amortized memtable-layer out-of-order append plus
  snapshot-safe reads over Python objects. The docs checker now strips comments
  and `#if 0`, validates active `TL_API` declarations, checks facade AST methods,
  and guards the public binding method table. The free-threaded CMake path now
  propagates `Py_GIL_DISABLED=1` into every CPython binding/test target, and the
  critical-section wrapper includes TSan annotations so uninstrumented libpython
  critical sections remain visible to race-detector runs.

### 🟨 Current proof boundary — do not overclaim

- **Confirmed gates on the exact dirty tree:** regular CPython 3.13 release
  build; full Python suite (**183 passed / 16 skipped**); regular CTest
  (**9/9**); docs consistency self-check; Layer-A static scan; JSON validity for
  checked-in benchmark artifacts; linked docs benchmark artifacts are now
  visible as added files after a narrow `.gitignore` whitelist; `git diff --check`;
  ASan/UBSan build; ASan/UBSan CTest (**9/9**); ASan/UBSan full Python
  (**183 passed / 16 skipped**); 3.14t release rebuild with generated flags
  showing `-DPy_GIL_DISABLED=1` for `_timelog`; 3.14t `PYTHON_GIL=0` full
  Python suite (**198 passed / 1 skipped**); 3.14t CTest (**9/9**);
  fresh release 3.14t GIL-off lab rerun (**112/112, 2867 cases**, 54.9s wall);
  clean-baseline pinned perf A/B for changed
  Python-call hot paths; and the opt-in branchless-search benchmark target.
  Larger oracle-backed lab evidence is preserved under
  `ideas-lab/verification/`: 3.13 lab from June 9 (**112/112, 2858 cases**) and
  a fresh post-`Py_GIL_DISABLED` release 3.14t GIL-off rerun from June 10
  (**112/112, 2867 cases**, artifact
  `lab_3.14t_tl_feat_release_after_pygil_fix_2026-06-10.md`). Additional
  reviewer-requested spot checks passed after restoring release extension artifacts:
  storage group branchless
  coverage (**1/1**, preserved in
  `ideas-lab/verification/storage_branchless_group_2026-06-10.md`),
  append/FASTCALL contract slice (**77 passed**),
  direct five-seam branchless benchmark (exit 0, no correctness mismatches,
  **1 advisory timing warning**), and a 266,240-record
  non-context-manager facade integration check over
  `append`/`point`/`range`/`views()`. Release extension artifacts were restored
  after sanitizer runs and verified not to link ASan/UBSan/TSan. The recovered
  naked-unlocked-context lint also passed against its 17-site baseline (output in
  `ideas-lab/verification/naked_unlocked_ctx_lint_2026-06-10.txt`). A
  supplemental current-tree oracle check also passed:
  `demo/correctness_ci.py --profile pr` with a 30-second override, seed `12345`,
  synthetic 5% OOO source, **380 ops**, **723 checks**, **558,713 inserts**,
  **59,425 deletes**, and **0 issues**. Focused free-threaded TSan evidence also
  passed under Clang 19 with narrow CPython-runtime suppressions:
  `test_free_threading.py`, `test_freethreaded_stress.py`, and the FASTCALL
  concurrency test produced **9 passed** and no TSan report files. The valid
  artifact is
  `ideas-lab/verification/clang19_tsan_freethreaded_repo_suppressions_valid_2026-06-10.txt`;
  it records that the staged package extension matched the TSan-built `.so`.

- **TSan boundary:** there are now two separate TSan facts. First, the native/core
  RelWithDebInfo TSan build is correctly instrumented: generated flags show
  `-fsanitize=thread` on core, `_timelog`, and `test_py_handle`; direct
  `test_py_handle` passed (**13/13**) under TSan with no report files; and the
  core `timelog_tests` CTest suite passed under TSan with no report files.
  Second, free-threaded Python TSan is locally usable only with Clang 19's runtime
  and narrow CPython-runtime suppressions. Unsuppressed Python+TSan first reports
  CPython BRC/dict internals even without Timelog. After adding only those
  runtime suppressions, and after adding Timelog TSan annotations for CPython
  critical-section wrappers, the focused free-threaded Timelog Python suite
  passed (**9 passed**) with no TSan report files; the saved artifact verifies
  the staged extension hash matched the TSan-built `.so`. Workflow-equivalent
  GCC libtsan still aborts Python startup before tests with
  `FATAL: ThreadSanitizer: unexpected memory mapping ...`.

- **Lifecycle/reopen support is intentionally not race-safe.** The public
  contract is now explicit: `close()` / `reopen()` / `configure()` must be
  externally serialized against all other users of the same instance. Do not
  claim concurrent lifecycle/reopen is supported unless the floor/config
  application moves fully into the C reopen path before `closed=0`.

- **CodeRabbit CLI review was not run.** The CLI is not installed in this
  environment (`coderabbit --version` returned `NOT_INSTALLED`), so this pass is
  local review plus prior independent reviewer reports, not an external
  CodeRabbit result.

### 🟦 Worth considering — real upside, but validate before production PR

- **`bulk_append(int64_buffer, objects)` typed-buffer ingest** — prior C2 evidence
  reported **9-10× vs per-append** and **2.4× vs `extend`**, and review found the
  refcount, rollback, and `TL_EBUSY` shape directionally sound. The current saved
  artifact is still patch-only, so this is not final-green. Before PR: rerun and
  save raw benchmark/test logs, reject or byteswap non-native-endian `int64`
  buffers, test native/non-native NumPy arrays, and swap raw `malloc` to
  `PyMem_Malloc`.

- **Arrow C Data export (`__arrow_c_array__`) on `PageSpan`** — useful and likely
  worth building, but current evidence is patch-only provenance. Production shape:
  timestamp column only, pyarrow/polars consumer checks with pointer identity,
  ASan/UBSan coverage, shared PageSpan export-pin helper, no `h[]` export, and an
  explicit owning-interpreter/thread-state release-callback contract.

- **DLPack export (`__dlpack__`) on `PageSpan`** — useful for NumPy/Torch/JAX/CuPy
  consumers that do not speak PEP 3118. Current evidence is patch-only
  provenance, so production needs saved consumer checks, read-only enforcement,
  sanitizer evidence, and the same export-pin/owning-interpreter discipline as
  Arrow.

- **Close the delete-reclaim gap** — the one genuine reliability/efficiency gap
  found by the audit. C5 measured a retention-shaped workload where deleting
  **50%** of data reclaimed **0 space**: `space_amp` stayed at **2.103×**,
  tombstones accumulated, and no compaction fired. This is design work, not a
  config flip: add a delete-driven L1 reclaim path with coverage for
  default-disabled and workload-sensitive cases.

- **Whole-window-drop for TTL/delete** — built as a +135 LOC prototype and
  reported **67-275×** pure-C TTL compaction-CPU in the best case. It is not a
  general binding win because CPython `on_drop_handle` forces a flat scan, and
  review found a false-negative around multi-`delete_range` windows. Only pursue
  for pure-C or TTL-heavy embeddings after fixing that coverage bug.

- **mimalloc for memory-sensitive deployments** — C7 measured peak RSS
  **−12.7% / −11.2%** and post-close fragmentation **−36.7%**; later checks
  narrowed this to peak/fragmentation rather than universal steady-state RSS.
  About **87%** of RSS is native C-core, so allocator choice can matter. Cost is
  packaging/linking policy.

### 🟥 Checked and rejected — do not pursue

- **Loser/tournament-tree k-way merge** — measured net-negative
  (**0.85-0.92×** at relevant K). Timelog's heap `replace_top` already
  short-circuits same-source replacement. Large refactor, measured loss.

- **SoA page catalog split** — measured roughly **1.0×** at realistic catalog
  sizes because the catalog is already cache-resident. It only helps at extreme
  16M+-record segment scales, not enough to justify the refactor.

- **Granular compaction via the existing cap** — `max_compaction_windows` does
  not meaningfully bound wide-OOO transient RAM. C4-gran preserved query
  correctness but changed one merge into many maintenance steps and roughly
  **10×** drain CPU. A real fix needs new sub-window slicing/design, not a knob
  flip.

- **Modern disk-LSM strategies** — Lazy Leveling/Dostoevsky, Universal, Monkey,
  and k-LSM optimize disk write-amp or existence-query filters Timelog does not
  have. Universal's temporary space-amp doubling is actively harmful in RAM.
  Timelog already has the literature-convergent shape for this domain:
  tiered-L0 plus leveled time-windowed L1.

- **HPy / pyo3 / plain abi3 migration** — wrong stack or wrong timing. Timelog is
  hand-written C-API, and plain abi3 is incompatible with free-threaded wheels
  until Python 3.15's abi3t path. Layer A/B already achieved subinterpreter and
  free-threaded support without HPy.

- **Merkle anti-entropy, io_uring/eBPF, mmap/socket zero-copy** — distributed,
  disk, or network I/O concepts with no direct transfer to an in-memory embedded
  engine. Their useful generic buffer lessons are already represented by the
  in-memory buffer/interop work above.

### ✅ Already implemented and verified — leave alone

- **Atomic/free-threaded PageSpan export protection** — already protected by the
  per-object critical section; C6 stress reported 287k reads, 0 crashes.
- **Iterator critical-section shape** — the critical section wraps lock-free
  `tl_iter_next`, so there is no block-while-held footgun in the audited path.
- **Multiphase init / per-interpreter state / free-threaded module declaration** —
  already implemented in `module.c` without HPy.
- **Compaction architecture choice** — already tiered-L0 plus leveled
  time-windowed L1; the remaining work is policy and delete reclaim, not replacing
  the whole compaction strategy.

## 3. Honest limitations
- The five 🟩 productionization items now live together on `feat/perf-wins`; do not read the older isolated
  experiment patches as the production source of truth. The branch remains the thing to review, test, and PR.
- C2/C3 (`bulk_append`, Arrow, DLPack) still preserve patch-only provenance without raw rerun logs; productionize
  them only after fresh consumer/benchmark evidence, sanitizer coverage, and explicit export-lifetime review.
- Compaction/memory studies are 200k-5M records; a production tuning decision wants the larger end plus more
  seeds. WWD still needs its false-negative fix for multi-delete workloads.
- The delete-reclaim gap (C5) needs a design and coverage for default-disabled/workload-sensitive L1 reclaim
  before it is a buildable fix. The allocator result is a packaging decision, not a Timelog core patch.

---
*Reversibility: every prototype lives on a throwaway branch off `e7e7efb`; `git worktree remove` + patches
in `experiments/<id>/` mean Timelog itself was never at risk. The wins are real and measured; the dead-ends
were killed by measurement, not opinion; the gaps are named with the evidence that found them.*
