# Ideas Lab Verification

Date: 2026-06-07

This file verifies the lab against `.ideas/goal.md`. It is intentionally an audit
artifact, not another pitch document: it records evidence, corrections made during
review, and limits of the evidence.

## Requirement Checklist

| Goal requirement | Current evidence | Verdict |
|---|---|---|
| Read original ideas one by one | The audit re-read all 37 `.ideas/doc_*.md` files in batches and compared them to `00-raw-catalog.md`, `01-themes.md`, and the final reports. | Verified by manual review; see caveat below on per-atom machine mapping. |
| Exact de-duplication | Fresh md5 check: 37 docs, 34 unique hashes, exact duplicate groups `doc_7/doc_19`, `doc_12/doc_23`, `doc_13/doc_25`. `00-raw-catalog.md` lists the same groups. | Verified. |
| Irrelevant filtering | `raw-digests.json` classifies 23 core, 8 tangential, 3 irrelevant. The irrelevant docs are `doc_2` Merkle replica repair, `doc_22` file/socket/mmap I/O, and `doc_33` io_uring/eBPF disk-LSM offload. `doc_22`'s I/O framing is out of scope; its generic `memoryview`/`frombuffer` material is treated as a duplicate of the in-memory buffer work already represented by other docs. | Verified. |
| Group remaining ideas by themes | `01-themes.md` groups the surviving idea families into T1-T8 and each non-dropped source doc is referenced at least once. Fresh source-reference check found no missing non-dropped canonical docs and no references to dropped/duplicate docs. A hostile source audit then added missing family atoms from docs 8/31/35. | Verified at source-document/family level; not atom-level machine proof. |
| Lists are exclusive and contain everything | `01-themes.md` is now explicit that it is the canonical deduped family registry, not a machine-verifiable `raw_atom -> canonical_id` map. Cross-theme ideas are assigned by implementation locus. | Verified only at source-document/family level. Atom-level completion remains unproven without a raw-atom mapping. |
| Think beyond source docs with current research | `02-ideation.md` records 5 research strands, 40 cited findings, 30 raw research ideas, and 25 corrections. It now clarifies that 30 raw research ideas were deduped into 28 canonical `N*` entries. | Verified. |
| Explore ideas with labs/prototypes/measurements | `experiments/` contains patches, harnesses, results, and JSON/CSV artifacts for binding, search, compaction, competitive, memory, and free-threading/export checks. C2/C3 currently preserve patch-only provenance rather than raw measurement transcripts. `FLEET_RESULTS.md` now distinguishes that weaker evidence. | Partially verified; C2/C3 need rerun logs before production claims are fully proven. |
| Inspect all lab code/prototypes/measurements | Reviewed Python harnesses, C microbenches, prototype patches, and result JSON/CSV summaries. Fixed harness issues that could hide failures: broad append exception swallowing, matrix seed-failure masking, `mem_probe` child/A-B status masking, weak delete baseline, generic-drain cap masking, C4-gran count-only fingerprints, and strict-C build portability in the C4-wwd benches. | Verified after fixes. |
| Confirm low-hanging / high-effort / pointless classifications | `03-classification.md` now has corrected buckets: measured low-hanging candidates, patch-only rerun candidates, medium feature/refactor candidates, measured/researched rejects, and inconclusive items. `N21` prefetch was downgraded from green to inconclusive; SoA catalog moved to measured-red; FASTCALL/C2/C3 confidence was downgraded to match saved artifacts. | Partially verified; remaining proof gap is raw rerun evidence for C2/C3 and all-10 FASTCALL. |
| Clean final report and lab artifacts | `README.md`, `AUDIT_REPORT.md`, `FLEET_RESULTS.md`, `03-classification.md`, and per-experiment `RESULT.md` files now agree that C2/C3 are patch-only in the current tree and must be rerun before production PRs. | Verified for consistency; not a full completion proof. |

## Corrections Made During Verification

- Fixed stale GIL/free-threading wording in root docs, binding comments, and the LLD. Explicit user
  `close()` may detach the active thread state around core close; finalizer/dealloc cleanup keeps the
  thread state attached.
- Extended `demo/ci/check_layer_a_static.py` to scan root Markdown, user-facing docs, and the
  `ideas-lab` Markdown deliverable for stale blanket process-lock support claims.
- Narrowed lab hot-loop exception handling to `TimelogBusyError`, whose contract means the write was
  committed. Other exceptions now fail or are counted instead of silently improving timings.
- Made `run_matrix.py` fail a cell if any expected seed fails instead of computing medians over only
  successful seeds.
- Made `mem_probe.py` fail if its worker process exits non-zero, and made allocator A/B runs exit non-zero
  when a configured allocator child fails or produces unparsable output. Unavailable optional allocators remain
  explicit skips.
- Made generic compaction/delete harness drains raise if their quiescence cap is hit, so capped runs cannot
  publish stable-state metrics.
- Forced `delete_lab.py` to call `compact()` and verify a clean L1 baseline before measuring delete debt.
- Strengthened C4-gran fingerprints to include `(timestamp, handle)` data. The multiset hash matches
  across caps; ordered hashes differ because duplicate-timestamp tie order is unspecified by the core API.
- Fixed C4-wwd C benchmark portability under strict C11 by declaring the POSIX clock feature level and
  including the required standard headers.
- Added previously under-accounted source atoms:
  - doc_8 process-isolated memory phases (`T7.16`);
  - doc_31 Arrow/Velox schema/backpressure/observability guardrails (`T3.13`);
  - doc_35 exception-safe hot-wrapper discipline (`T1.8`).
- Corrected report overclaims:
  - compaction research had 2 completed strands, not 3;
  - not every large theme had a built prototype; some had measurement studies or code audits;
  - C7 mimalloc evidence supports peak/fragmentation RSS wins, not a universal steady-state win;
  - raw research had 30 ideas, deduped to 28 canonical `N*` entries;
  - doc_33 had no negative idea atom in `raw-digests.json`.
  - C2/C3 current artifacts are patch-only and lack raw bench/test transcripts;
  - FASTCALL was measured on representative methods, not all 10 production methods.

## Classification Verdict

### Low-hanging / productionizable next

- `METH_FASTCALL` for positional hot methods: measured call-boundary win, small patch surface.
- Branchless `lower_bound`: measured search/point win, low implementation risk if applied carefully.
- Fold facade auto-timestamp append into C: largest measured hot-path win, but productionization must
  preserve all facade semantics and configured `time_unit`.
- Typed-buffer `bulk_append`: prior run reported a large ingest win, but the current tree is patch-only;
  production requires rerun logs, native-endian validation or byteswap, and `PyMem_Malloc` scratch allocation.
- Cheap hardening/docs: no `tp_vectorcall` trap, never export `h[]`, PEP 688 annotation, GIL-disabled
  wheel check, positioning docs, `max_delta_segments` documentation.

### Real upside, major or conditional work

- Arrow C Data / DLPack exports: prior runs reported zero-copy, but the current tree is patch-only;
  release-callback / owner-interpreter cleanup must be designed as feature work, not pasted from the lab patch.
- Delete-driven L1 reclaim: genuine measured gap, needs design and coverage.
- Whole-window drop: safe/winning in pure-C TTL cases, but CPython `on_drop_handle` flat scan and a
  known multi-delete false-negative make it conditional.
- True sub-window granular compaction: the current cap is not enough; a real fix needs new design.
- SIMD/batched read-side APIs and central export-pin helper: plausible but nontrivial.
- mimalloc: optional deployment/packaging knob for peak/fragmentation-sensitive users.

### Pointless / rejected / not for Timelog

- Loser/tournament merge and SoA catalog: killed by measurement.
- Lazy Leveling, Universal, Monkey, k-LSM: disk-LSM optimizations do not transfer to Timelog's RAM-first
  RUM corner.
- HPy/pyo3/plain abi3: wrong stack or no longer needed for the achieved free-threaded/subinterpreter
  support.
- Merkle anti-entropy, mmap/socket/readinto, io_uring/eBPF: distributed/disk/network concepts with no
  direct transfer to the in-memory extension.

## Verification Commands

Representative commands used in the final audit:

```bash
python - <<'PY'
# count docs, md5 duplicates, raw digest counts, source-theme coverage
PY
python demo/ci/check_layer_a_static.py
python demo/ci/check_docs_consistency.py
git diff --check
python -m py_compile ideas-lab/harness/*.py ideas-lab/experiments/*/*.py ideas-lab/experiments/_bench/*.py
gcc -std=c11 -Wall -Wextra -Werror -O2 -Icore/include -Icore/src ideas-lab/experiments/exp02-branchless-search/bench_lower_bound.c -o /tmp/bench_lower_bound_check
gcc -std=c11 -Wall -Wextra -Werror -O2 ideas-lab/experiments/exp05-loser-tree/bench_kmerge.c -o /tmp/bench_kmerge_check
gcc -std=c11 -Wall -Wextra -Werror -O2 ideas-lab/experiments/_probes/soa_catalog_microbench.c -o /tmp/soa_catalog_microbench_check
gcc -std=c11 -Wall -Wextra -Werror -O2 -Icore/include ideas-lab/experiments/C4-gran/peak_rss_c.c build-rel/libtimelog.a -lpthread -lm -o /tmp/peak_rss_c_check
gcc -std=c11 -Wall -Wextra -Werror -O2 -Icore/include ideas-lab/experiments/C4-wwd/bench_wwd.c build-rel/libtimelog.a -lpthread -lm -o /tmp/bench_wwd_check
gcc -std=c11 -Wall -Wextra -Werror -O2 -Icore/include ideas-lab/experiments/C4-wwd/bench_wwd_bestcase.c build-rel/libtimelog.a -lpthread -lm -o /tmp/bench_wwd_bestcase_check
PYTHONPATH=python pytest -q python/tests
ctest --test-dir build-rel --output-on-failure
PYTHONPATH=python PYTHON_GIL=0 PYENV_VERSION=3.14.3t pyenv exec pytest -q python/tests --tb=short
```

## Remaining Caveats

- The lab did not preserve a machine-checkable `raw_atom -> canonical_theme_id` map. The current registry
  is verified at source-document/family level and by manual review, not by a strict atom-level JSON map.
- The source `.ideas/doc_*.md` corpus is gitignored and local-only. This deliverable preserves digests,
  summaries, and classification evidence, but an external reviewer cannot independently re-read the original
  source documents from the tracked tree unless that corpus is provided separately.
- C2-bulk, C3-arrow, and C3-dlpack preserve prototype patches and prior-run claims, but not raw measurement
  transcripts or full gate logs in the current tree. They remain high-value rerun candidates, not fully
  proven production-ready changes.
- FASTCALL is measured on representative hot methods. The remaining positional methods still need conversion,
  direct benchmarks, and gate logs before the "all 10" claim is complete.
- C2/C3 patches are lab prototypes. They apply cleanly, but are not merge-ready without the production
  fixes documented in `03-classification.md` and per-experiment reports.
- `C4-gran/prototype.patch` is intentionally a note, not a code patch. `C7-mem/prototype.patch` describes
  a file now present in the lab tree, so it is a baseline patch artifact rather than something to apply
  on top of the current lab directory.
- `ideas-lab/harness/libmimalloc.so` is ignored and local. `mem_probe.py` no longer searches the repo-local
  directory by default for `LD_PRELOAD`; reruns must use system allocator libraries or explicitly opt in via
  `TIMELOG_MEM_PROBE_PRELOAD_DIRS`.
