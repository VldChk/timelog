# Master Findings Ledger — convergence matrix

Sources: CX = Codex independent audits (audit/codex/*.md), CL = Claude 12-unit fleet
(audit/modules/*.md), LF = landscape facts (audit/prior-art/landscape-facts.md).
Panel = hostile verification verdict (Phase 4). LOC = net estimate incl. glue.

## A. Simplification candidates (Codex-sourced; Claude convergence TBD)

| ID | Claim | Where | LOC | Risk | CX | CL | Panel |
|----|-------|-------|-----|------|----|----|-------|
| S-01 | Remove/flag speculative V2 page-delete plumbing (costs live read-path branches) | tl_page.h:11,21; tl_page.c:117,247; tl_segment_iter.c:22,134; tl_point.c:111; tl_pagespan_iter.c:437 | 80–110 | med | ✓ | ? | — |
| S-02 | One allocator-aware grow/reserve helper for ~10 duplicated grow loops | tl_recvec.c:52; tl_seqvec.c:47; tl_heap.c:110; tl_intervals.c:10; tl_page.c:291; tl_manifest.c:199; tl_plan.c:20–57; tl_point.c:22–50; tl_memtable.c:229–313; tl_flush.c:249–269 | 140–230 | low-med | ✓✓ | ? | — |
| S-03 | Dedup lower/upper-bound kernels (macro/static-inline, keep branchless gate) | tl_search.h:14; tl_recvec.c:266,297; tl_page.c:141,177 | 50–80 | med (bench) | ✓ | ? | — |
| S-04 | Prune dead/test-only internal APIs (tl__reallocarray, tl_thread_self_id, tl_recvec_insert, recvec shrink_to_fit, tl_heap_build) | tl_alloc.h:104; tl_sync.h:152; test_internal_data_structures.c:243,381,1281 | 180–260 | low-med | ✓ | ? | — |
| S-05 | Manifest builder: pointer-vec helper replaces 4 parallel add/remove list impls | tl_manifest.h:106; tl_manifest.c:138–290 | 50–75 | low | ✓ | ? | — |
| S-06 | DELETE dead two-way merge iterator in flush layer (production-dead) | tl_flush.h:39–116; tl_flush.c:9–66 | 100–130 | low | ✓ | ? | — |
| S-07 | Collapse full-count helpers into range-count with full bounds | tl_count.h:149–233 vs 243–349 | 55–80 | low | ✓ | ? | — |
| S-08 | Flush paths reuse existing tl__emit_drop_callbacks helper | tl_timelog.c:997–1029 dup of 466–479 | 18–24 | low | ✓ | ? | — |
| S-09 | Share active/memrun iterator next/seek bodies (keep two init adapters) | tl_active_iter.c:72–124 ≈ tl_memrun_iter.c:81–135 | 40–70 | med | ✓ | ? | — |
| S-10 | Demote test-only constructors (tl_memrun_create, tl_ooorunset_create, tl_memtable_seal) | tl_memrun.c:94–133; tl_ooorun.c:76–127; tl_memtable.c:1059–1061 | 30–60 | low-med | ✓ | ? | — |
| S-11 | Remove dead adaptive surface (tl_adaptive_wants_resize, TL_WORK_RESHAPE_L0) | tl_adaptive.h:185; tl_adaptive.c:395–408; tl_timelog.c:1733–1739 | 20–35 | low | ✓ | ? | — |
| S-12 | CMake function for 6 copy-pasted embedded-test targets; target-scoped warnings | bindings/CMakeLists.txt:305–655; root CMakeLists.txt:48,82 | 120–170 | low-med | ✓ | ? | — |
| S-13 | Table/macro-drive PyTimelog_init config validation (keep exact errors) | py_timelog.c:806–1338 | 100–150 | med | ✓ | ? | — |
| S-14 | Helper-factor repeated FASTCALL timestamp method wrappers | py_timelog.c:2973,3013,3399–3486,3368,2593 | 80–120 | low-med | ✓ | ? | — |
| S-15 | va_list-based shared raise helper in py_errors.c | py_errors.c:137,175 | 18–25 | low | ✓ | ? | — |
| S-16 | Shallow TL_PY_DEFINE_ENTER / flags macros across span/iter types | py_span.c:332; py_iter.c:348; py_span_iter.c:351 | 30–50 | med | ✓ | ? | — |

Codex total if all adopted: ~1100–1600 net LOC removed, zero library additions.

## B. Prior-art adoption candidates

| ID | Sub-problem | Candidate | CX verdict | CL | LF facts | Panel |
|----|-------------|-----------|------------|----|----------|-------|
| P-01 | Dynamic arrays | klib kvec / stb_ds / utarray | REJECT (allocator seam, status codes, callback shape) | ? | ? | — |
| P-02 | Min-heap | klib / CCAN heap | REJECT (tie-break+watermark payload, hot path) | ? | ? | — |
| P-03 | Lock-free structures/seqlock | Concurrency Kit, liburcu | REJECT (platform assumptions, mixed licenses, wheel fit) | ? | ? | — |
| P-04 | Hash table (live handles) | khash/uthash | REJECT (lock-free GC traversal contract is the hard part) | ? | ? | — |
| P-05 | C test framework | greatest / Unity / µnit | VALID prior art; NOT zero-regression (migration churn, env-filter semantics); net ≤0 if vendored | ? | ? | — |
| P-06 | Interval set | interval trees / cgranges | REJECT (seq-aware skyline semantics ≠ generic intervals) | ? | ? | — |
| P-07 | CPython binding boilerplate helper lib (pure C) | (none known) | n/a — verify LF | ? | ? | — |

## C. Codex NO-AND-NO (machinery that earns its keep — grounded)

tombstone interval skyline; window/range math; page/segment/manifest semantics; logging;
records copy helper; sync/atomic/seqlock/refcount platform layer; OOO mini-LSM memtable;
memview capture + sealed-ring publication; compaction select/merge/publish; k-merge heap
(as-is); point-lookup fast path; handle lifetime subsystem (Treiber stack + live table);
PageSpan buffer protocol; hot append/bulk_append parsers; module multi-phase init;
per-type release ordering.

## D. Observations (out of zero-regression scope)

- Public speculative knobs (batch-append flags ignored by impl; reserved pagespan flags)
  — API-change territory, major-version only (timelog.h:383–399; tl_memtable.c:651–655).
- Test harness swap to `greatest` is real prior art but negative-value at current scale.
