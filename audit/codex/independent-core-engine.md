# Timelog C Core Simplicity / Prior-Art Audit

## Executive Summary

No external C library earns a recommendation for hot-path replacement. The core data structures are tightly coupled to Timelog invariants: immutable publication, seq/tie ordering, custom allocator/status returns, tombstone skyline semantics, and seqlock publication windows.

There are still worthwhile simplifications:

1. Delete the dead delta two-way merge iterator: ~100-130 net LOC saved, no runtime risk.
2. Collapse duplicated count helpers: ~55-80 LOC saved, low risk.
3. Reuse existing drop-callback helper in flush paths: ~18-24 LOC saved, low risk.
4. Factor active/memrun iterator bodies carefully: ~40-70 LOC saved, medium risk.
5. Unify local dynamic-array grow loops with repo-local helpers, not stb/klib: ~50-90 LOC saved, medium risk.
6. Remove/demote test-only constructors and dead adaptive/work-item API: ~50-95 net LOC saved, low risk.

## Findings

### 1. Dead delta two-way merge iterator

**SIMPLER: YES.** `tl_merge_iter_t` in the delta flush layer is production-dead. It is declared at [tl_flush.h](/home/vldvhk/Documents/timelog/core/src/delta/tl_flush.h:39):39-116 and implemented at [tl_flush.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_flush.c:9):9-66, but real flush construction uses a heap k-way path at [tl_flush.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_flush.c:134):134-221 and [tl_flush.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_flush.c:230):230-291.

**PRIOR ART: YES, but irrelevant.** Two-way sorted merge is textbook; no mature library should be vendored to replace dead code.

**LOC:** save ~120-140 core LOC, add 0-20 test helper LOC if tests still want it; net ~100-130.  
**Risk:** low. No hot path can regress if callers are absent.

### 2. Duplicated visible-count helpers

**SIMPLER: YES.** Full-segment/full-memrun count helpers duplicate range helpers: full versions live at [tl_count.h](/home/vldvhk/Documents/timelog/core/src/query/tl_count.h:149):149-233, range versions at [tl_count.h](/home/vldvhk/Documents/timelog/core/src/query/tl_count.h:243):243-349. Stats call the full helpers at [tl_timelog.c](/home/vldvhk/Documents/timelog/core/src/tl_timelog.c:2084):2084-2116; snapshot counting calls range helpers at [tl_snapshot.c](/home/vldvhk/Documents/timelog/core/src/query/tl_snapshot.c:311):311-325.

**PRIOR ART: NO.** This is not a generic count problem; it depends on Timelog visibility watermarks and half-open timestamp ranges documented in [CLAUDE.md](/home/vldvhk/Documents/timelog/CLAUDE.md:120):120-133.

**LOC:** save ~55-80 LOC by making full-count wrappers call the range implementation with full bounds or by sharing one inline worker.  
**Risk:** low if kept inline and benchmarked; arithmetic path is the same.

### 3. Duplicate drop-callback loops

**SIMPLER: YES.** There is already a helper at [tl_timelog.c](/home/vldvhk/Documents/timelog/core/src/tl_timelog.c:466):466-479. `flush_one_memrun` duplicates that loop at [tl_timelog.c](/home/vldvhk/Documents/timelog/core/src/tl_timelog.c:997):997-1008 and [tl_timelog.c](/home/vldvhk/Documents/timelog/core/src/tl_timelog.c:1018):1018-1029. The seal path already uses the helper at [tl_timelog.c](/home/vldvhk/Documents/timelog/core/src/tl_timelog.c:1138):1138-1155.

**PRIOR ART: NO.** This is project callback/lifetime glue.

**LOC:** save ~18-24 LOC.  
**Risk:** low; preserve the existing rule that callbacks happen after publish/discard, not under the writer lock.

### 4. Active and memrun iterators are near-duplicates

**SIMPLER: YES, cautiously.** The structs are almost the same at [tl_active_iter.h](/home/vldvhk/Documents/timelog/core/src/query/tl_active_iter.h:23):23-36 and [tl_memrun_iter.h](/home/vldvhk/Documents/timelog/core/src/query/tl_memrun_iter.h:23):23-36. Their `next`/`seek` bodies are duplicated at [tl_active_iter.c](/home/vldvhk/Documents/timelog/core/src/query/tl_active_iter.c:72):72-124 and [tl_memrun_iter.c](/home/vldvhk/Documents/timelog/core/src/query/tl_memrun_iter.c:81):81-135. Both initialize the same `tl_submerge` engine through [tl_iter_build.c](/home/vldvhk/Documents/timelog/core/src/query/tl_iter_build.c:26):26-96.

**PRIOR ART: NO.** The generic problem is k-way merge, but the actual semantics include run/head tie ids and visibility watermarks from [tl_iter_build.c](/home/vldvhk/Documents/timelog/core/src/query/tl_iter_build.c:58):58-88.

**LOC:** save ~40-70 LOC by keeping two init adapters and sharing the iterator body.  
**Risk:** medium. Active has sorted-head assertions at [tl_active_iter.c](/home/vldvhk/Documents/timelog/core/src/query/tl_active_iter.c:19):19-20; memrun has applied-seq watermarks at [tl_memrun_iter.c](/home/vldvhk/Documents/timelog/core/src/query/tl_memrun_iter.c:42):42-55.

### 5. Repeated dynamic-array growth

**SIMPLER: YES, repo-local.** Manual growth appears in plan sources at [tl_plan.c](/home/vldvhk/Documents/timelog/core/src/query/tl_plan.c:20):20-57, point results at [tl_point.c](/home/vldvhk/Documents/timelog/core/src/query/tl_point.c:22):22-50, memtable arrays at [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:229):229-313, and dropped flush records at [tl_flush.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_flush.c:249):249-269. The repo already has allocator growth primitives at [tl_alloc.h](/home/vldvhk/Documents/timelog/core/src/internal/tl_alloc.h:127):127-163.

**PRIOR ART: YES, but do not vendor.** `klib`/`stb_ds`-style vectors solve the generic shape, but Timelog needs `tl__malloc`/`tl__realloc`, status-code errors, overflow handling, and MSVC `-WX` compatibility from [timelog.h](/home/vldvhk/Documents/timelog/core/include/timelog/timelog.h:191):191-206 and [tl_timelog.c](/home/vldvhk/Documents/timelog/core/src/tl_timelog.c:179):179-183.

**LOC:** save ~50-90 net with an internal `tl__ensure_array_capacity` helper.  
**Risk:** medium because current call sites differ on zeroing and `TL_ENOMEM` vs `TL_EOVERFLOW`.

### 6. Test-only constructors and wrappers

**SIMPLER: YES.** `tl_memrun_create` wraps allocation/init at [tl_memrun.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memrun.c:94):94-133, while production uses lower-level allocation/init at [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:891):891 and [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:1006):1006. `tl_ooorunset_create` at [tl_ooorun.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_ooorun.c:76):76-127 is similarly bypassed by production append logic at [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:547):547. `tl_memtable_seal` is a trivial wrapper at [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:1059):1059-1061.

**PRIOR ART: NO.** These are local convenience APIs.

**LOC:** save ~90-120 core LOC, likely add ~40-70 test LOC; net ~30-60.  
**Risk:** low to medium; mostly test churn.

### 7. Dead adaptive/work-item surface

**SIMPLER: YES.** `tl_adaptive_wants_resize` is declared at [tl_adaptive.h](/home/vldvhk/Documents/timelog/core/src/maint/tl_adaptive.h:185):185-201 and implemented at [tl_adaptive.c](/home/vldvhk/Documents/timelog/core/src/maint/tl_adaptive.c:395):395-408, while production compaction computes candidates directly at [tl_compaction.c](/home/vldvhk/Documents/timelog/core/src/maint/tl_compaction.c:1369):1369-1389. `TL_WORK_RESHAPE_L0` is a reserved unused enum value at [tl_timelog.c](/home/vldvhk/Documents/timelog/core/src/tl_timelog.c:1733):1733-1739.

**PRIOR ART: NO.** Adaptive reshaping policy is project-specific.

**LOC:** save ~20-35 LOC plus one enum entry.  
**Risk:** low unless this is intentionally kept as internal API for future tests.

### 8. Public speculative knobs

**SIMPLER: NO under zero API regression.** Batch append flags are public at [timelog.h](/home/vldvhk/Documents/timelog/core/include/timelog/timelog.h:383):383-399, but ignored at [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:651):651-655 because sortedness must still be verified at [tl_memtable.h](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.h:152):152-160 and [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:671):671-679. Pagespan flags are partly reserved at [tl_pagespan_iter.h](/home/vldvhk/Documents/timelog/core/src/query/tl_pagespan_iter.h:105):105-120, while current open rejects unsupported modes at [tl_pagespan_iter.c](/home/vldvhk/Documents/timelog/core/src/query/tl_pagespan_iter.c:316):316-325 and returns direct page pointers at [tl_pagespan_iter.c](/home/vldvhk/Documents/timelog/core/src/query/tl_pagespan_iter.c:432):432-464.

**PRIOR ART: NO.** This is API surface, not machinery.

**LOC:** major-version cleanup only.  
**Risk:** high for compatibility; do not touch in a zero-regression pass.

## Explicit NO-And-NO Section

### OOO mini-LSM / memtable machinery

**SIMPLER: NO. PRIOR ART: NO.** The design is explicitly an appendable sorted active run plus OOO head/runset with query-time submerge and generation ordering at [CLAUDE.md](/home/vldvhk/Documents/timelog/CLAUDE.md:89):89-95. Implementation complexity in OOO flush at [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:398):398-566 and seal at [tl_memtable.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.c:857):857-1062 buys hot append behavior and immutable publication. Generic LSM libraries do not fit pure C17, in-memory-only, custom allocator, CPython TSan-clean constraints.

### Memview snapshot/cache and sealed-ring publication

**SIMPLER: NO. PRIOR ART: NO.** Snapshot consistency and lock ordering are documented at [CLAUDE.md](/home/vldvhk/Documents/timelog/CLAUDE.md:135):135-168. The snapshot path pins/captures under `writer_mu` at [tl_snapshot.c](/home/vldvhk/Documents/timelog/core/src/query/tl_snapshot.c:71):71-164, and sealed ring indices are overflow-safe at [tl_memtable.h](/home/vldvhk/Documents/timelog/core/src/delta/tl_memtable.h:328):328-348. This is core concurrency correctness, not replaceable glue.

### Tombstone interval skyline

**SIMPLER: NO. PRIOR ART: NO.** Half-open and canonical tombstone invariants are documented at [CLAUDE.md](/home/vldvhk/Documents/timelog/CLAUDE.md:120):120-133. The interval set is seq-aware at [tl_intervals.h](/home/vldvhk/Documents/timelog/core/src/internal/tl_intervals.h:8):8-22 with cursor lookup at [tl_intervals.h](/home/vldvhk/Documents/timelog/core/src/internal/tl_intervals.h:226):226-260. Compaction even needs two tombstone sets with distinct semantics at [tl_compaction.h](/home/vldvhk/Documents/timelog/core/src/maint/tl_compaction.h:94):94-110.

### Compaction selection/merge/publish

**SIMPLER: NO. PRIOR ART: NO.** L1 non-overlap and window-bound compaction are invariants at [CLAUDE.md](/home/vldvhk/Documents/timelog/CLAUDE.md:104):104-113. Selection caps and forward progress are encoded at [tl_compaction.c](/home/vldvhk/Documents/timelog/core/src/maint/tl_compaction.c:553):553-678; merge/publish are at [tl_compaction.c](/home/vldvhk/Documents/timelog/core/src/maint/tl_compaction.c:978):978-1247 and [tl_compaction.c](/home/vldvhk/Documents/timelog/core/src/maint/tl_compaction.c:1299):1299-1359. Mature LSM engines exist, but not as a small MIT-compatible C17 in-memory component fitting these invariants.

### Query k-merge heap

**SIMPLER: NO for library replacement. PRIOR ART: YES, but reject.** The heap carries Timelog-specific tie-break, watermark, iterator, and handle fields at [tl_heap.h](/home/vldvhk/Documents/timelog/core/src/internal/tl_heap.h:21):21-33, with replace-top support at [tl_heap.c](/home/vldvhk/Documents/timelog/core/src/internal/tl_heap.c:219):219-225. It is used in flush, submerge, query k-merge, and compaction at [tl_flush.c](/home/vldvhk/Documents/timelog/core/src/delta/tl_flush.c:199):199-221, [tl_submerge.c](/home/vldvhk/Documents/timelog/core/src/query/tl_submerge.c:57):57-82, [tl_merge_iter.c](/home/vldvhk/Documents/timelog/core/src/query/tl_merge_iter.c:153):153-162, and [tl_compaction.c](/home/vldvhk/Documents/timelog/core/src/maint/tl_compaction.c:1093):1093-1115. `klib`/CCAN-style heaps are prior art, but replacing this would add adapter risk on a hot path.

### Point lookup fast path

**SIMPLER: NO. PRIOR ART: NO.** Point lookup has a dedicated path at [tl_point.c](/home/vldvhk/Documents/timelog/core/src/query/tl_point.c:362):362-432 and a separate public iterator path at [tl_timelog.c](/home/vldvhk/Documents/timelog/core/src/tl_timelog.c:1402):1402-1435. Folding it into the range iterator would simplify code but regress point-query latency.

## Ranked Shortlist

1. Delete delta `tl_merge_iter_t`: highest confidence, no production behavior.
2. Replace duplicated count helpers with one shared inline implementation.
3. Replace duplicate flush drop-callback loops with `tl__emit_drop_callbacks`.
4. Factor active/memrun iterator bodies after adding focused iterator parity tests.
5. Add one internal dynamic-array capacity helper; do not vendor `stb_ds`/`klib`.
6. Demote test-only constructors and dead adaptive/work-item APIs.

Recommended external library adoption: **none**. The only plausible prior-art targets are vectors and heaps, and both lose to small repo-local helpers under the stated allocator, warning, TSan, wheel-vendoring, and zero hot-path regression constraints.

No files were modified.


