# AGENT Context: timelog Repository

## Repository Identity And Build System
- The project is a C project named `timelog`, version `1.0.0`, compiled as C17. (`CMakeLists.txt:2`, `CMakeLists.txt:8`)
- The root README defines timelog as a native C library for Python time-series operations. (`README.md:2`)
- Build options include native CPU tuning and shared-library toggle. (`CMakeLists.txt:13`, `CMakeLists.txt:15`)
- Default build type is `Release` if not explicitly set. (`CMakeLists.txt:17`, `CMakeLists.txt:19`)
- GCC/Clang builds enable `-Wall -Wextra -Wpedantic -Werror` and hidden symbol visibility. (`CMakeLists.txt:47`, `CMakeLists.txt:49`, `CMakeLists.txt:51`)
- POSIX builds define `_POSIX_C_SOURCE=200809L`. (`CMakeLists.txt:54`, `CMakeLists.txt:56`)
- Core sources are explicitly organized by phase (`internal`, `storage`, `delta`, `query`, `maint`, `adaptive`) in `TIMELOG_SOURCES`. (`CMakeLists.txt:75`, `CMakeLists.txt:89`, `CMakeLists.txt:94`, `CMakeLists.txt:100`, `CMakeLists.txt:112`, `CMakeLists.txt:114`)
- The main library target is `timelog`, with public headers from `core/include` and private internal include paths for source submodules. (`CMakeLists.txt:123`, `CMakeLists.txt:126`, `CMakeLists.txt:127`, `CMakeLists.txt:131`)
- Core and test binaries compile with `TL_TEST_HOOKS`; tests also compile with `TL_ADAPTIVE_INTERNAL_TEST`. (`CMakeLists.txt:136`, `CMakeLists.txt:200`, `CMakeLists.txt:203`)
- A C test executable `test_timelog` is built and registered as `timelog_tests`. (`CMakeLists.txt:181`, `CMakeLists.txt:210`)
- Test source inventory covers internal, functional, invariants, concurrency/stress, pagespan, and adaptive tests. (`CMakeLists.txt:161`, `CMakeLists.txt:167`, `CMakeLists.txt:171`, `CMakeLists.txt:173`, `CMakeLists.txt:176`, `CMakeLists.txt:178`)
- A demo target `adaptive_segmentation_demo` links against `timelog`. (`CMakeLists.txt:216`, `CMakeLists.txt:217`)

## Public API Contract (core/include/timelog/timelog.h)
- The public API defines timelog as an in-memory, time-indexed multimap with LSM-style OOO ingestion. (`core/include/timelog/timelog.h:8`, `core/include/timelog/timelog.h:11`)
- Reads are snapshot-isolated; writes require external single-writer coordination. (`core/include/timelog/timelog.h:17`, `core/include/timelog/timelog.h:45`, `core/include/timelog/timelog.h:46`, `core/include/timelog/timelog.h:49`)
- Time ranges are half-open `[t1, t2)` across APIs. (`core/include/timelog/timelog.h:22`, `core/include/timelog/timelog.h:450`)
- Status semantics explicitly distinguish write `TL_EBUSY` (data accepted; do not retry) from true write failures like `TL_ENOMEM`/`TL_EOVERFLOW` (no insert). (`core/include/timelog/timelog.h:118`, `core/include/timelog/timelog.h:124`, `core/include/timelog/timelog.h:130`, `core/include/timelog/timelog.h:143`)
- `tl_open()` documents background maintenance auto-start in `TL_MAINT_BACKGROUND` mode and manual maintenance in disabled mode. (`core/include/timelog/timelog.h:340`, `core/include/timelog/timelog.h:343`, `core/include/timelog/timelog.h:349`)
- `tl_close()` documents that unflushed data is dropped unless `tl_flush()` is called first. (`core/include/timelog/timelog.h:357`, `core/include/timelog/timelog.h:360`)
- The write API includes append, batch append, delete-range, delete-before, flush, and compact request. (`core/include/timelog/timelog.h:411`, `core/include/timelog/timelog.h:413`, `core/include/timelog/timelog.h:417`, `core/include/timelog/timelog.h:420`, `core/include/timelog/timelog.h:432`, `core/include/timelog/timelog.h:435`)
- Snapshot and iterator APIs are explicit (`tl_snapshot_acquire/release`, range/since/until/equal/point iteration). (`core/include/timelog/timelog.h:441`, `core/include/timelog/timelog.h:444`, `core/include/timelog/timelog.h:451`, `core/include/timelog/timelog.h:455`, `core/include/timelog/timelog.h:459`, `core/include/timelog/timelog.h:466`, `core/include/timelog/timelog.h:475`)
- Stats expose storage, memtable, and cumulative operational counters (including compaction retries and publish EBUSY counts). (`core/include/timelog/timelog.h:648`, `core/include/timelog/timelog.h:663`, `core/include/timelog/timelog.h:669`, `core/include/timelog/timelog.h:670`)
- Adaptive config is part of the public config (`tl_config_t.adaptive`) with target, bounds, hysteresis/backoff controls. (`core/include/timelog/timelog.h:273`, `core/include/timelog/timelog.h:312`)

## Internal Orchestrator Model (`tl_timelog_t`)
- `tl_timelog` is the single authoritative internal instance type. (`core/src/internal/tl_timelog_internal.h:7`, `core/src/internal/tl_timelog_internal.h:56`)
- Lock order is explicitly `maint_mu -> flush_mu -> writer_mu -> memtable_mu`. (`core/src/internal/tl_timelog_internal.h:85`)
- `tl_timelog` stores `op_seq`, manifest pointer, memtable, worker state, adaptive state, and cumulative atomics. (`core/src/internal/tl_timelog_internal.h:163`, `core/src/internal/tl_timelog_internal.h:166`, `core/src/internal/tl_timelog_internal.h:178`, `core/src/internal/tl_timelog_internal.h:127`, `core/src/internal/tl_timelog_internal.h:140`, `core/src/internal/tl_timelog_internal.h:188`)
- The window-grid freeze flag is part of core state and is intended to become permanent once L1 exists. (`core/src/internal/tl_timelog_internal.h:143`, `core/src/internal/tl_timelog_internal.h:156`)

## Lifecycle Implementation
- `tl_open()` copies config, normalizes, initializes locks/memtable/manifest/counters, sets `op_seq=0`, and may auto-start maintenance worker in background mode. (`core/src/tl_timelog.c:417`, `core/src/tl_timelog.c:426`, `core/src/tl_timelog.c:437`, `core/src/tl_timelog.c:448`, `core/src/tl_timelog.c:451`, `core/src/tl_timelog.c:489`, `core/src/tl_timelog.c:508`)
- `window_grid_frozen` is initialized from whether manifest already has L1 segments. (`core/src/tl_timelog.c:502`)
- `tl_close()` stops worker first, then marks closed, releases manifest/cache, destroys memtable and locks, then frees instance memory. (`core/src/tl_timelog.c:544`, `core/src/tl_timelog.c:560`, `core/src/tl_timelog.c:580`, `core/src/tl_timelog.c:586`, `core/src/tl_timelog.c:592`, `core/src/tl_timelog.c:595`, `core/src/tl_timelog.c:604`)

## Write Path And Memtable Model
- Every append/delete path increments `op_seq` under writer lock before writing into memtable. (`core/src/tl_timelog.c:733`, `core/src/tl_timelog.c:736`, `core/src/tl_timelog.c:781`, `core/src/tl_timelog.c:838`, `core/src/tl_timelog.c:873`)
- Deferred signaling is enforced: seal/write under `writer_mu`, then maintenance signal after unlock. (`core/src/tl_timelog.c:620`, `core/src/tl_timelog.c:748`, `core/src/tl_timelog.c:850`)
- Backpressure/write acceptance behavior is encoded in `handle_seal_with_backpressure`, returning `TL_EBUSY` when insert succeeded but sealing/queue conditions failed. (`core/src/tl_timelog.c:629`, `core/src/tl_timelog.c:657`, `core/src/tl_timelog.c:667`, `core/src/tl_timelog.c:711`)
- Memtable active state includes record vectors plus parallel sequence vectors for both in-order run and OOO head. (`core/src/delta/tl_memtable.h:36`, `core/src/delta/tl_memtable.h:37`, `core/src/delta/tl_memtable.h:38`, `core/src/delta/tl_memtable.h:39`)
- Memtable tombstones are stored as coalesced interval fragments in `active_tombs`. (`core/src/delta/tl_memtable.h:40`)
- Sealed queue is a fixed-capacity ring preallocated at init; queue metadata includes head/len/cap/epoch. (`core/src/delta/tl_memtable.h:26`, `core/src/delta/tl_memtable.h:58`, `core/src/delta/tl_memtable.h:59`, `core/src/delta/tl_memtable.h:61`, `core/src/delta/tl_memtable.h:67`)
- Ring index mapping is overflow-safe and subtraction-based. (`core/src/delta/tl_memtable.h:320`, `core/src/delta/tl_memtable.h:337`, `core/src/delta/tl_memtable.h:341`)
- Insert routing is timestamp-based: in-order to `active_run`, OOO to `ooo_head`, both storing per-record `seq`. (`core/src/delta/tl_memtable.c:379`, `core/src/delta/tl_memtable.c:397`, `core/src/delta/tl_memtable.c:401`, `core/src/delta/tl_memtable.c:416`)
- Batch insert explicitly enforces all-or-nothing semantics via pre-reserve in both fast and slow paths. (`core/src/delta/tl_memtable.c:491`, `core/src/delta/tl_memtable.c:526`, `core/src/delta/tl_memtable.c:545`, `core/src/delta/tl_memtable.c:558`)
- Tombstone insertion uses `tl_intervals_insert` with `seq` and adjusts epoch/bytes only when insertion happened. (`core/src/delta/tl_memtable.c:608`, `core/src/delta/tl_memtable.c:610`, `core/src/delta/tl_memtable.c:614`)
- Seal applies tombstones to active records using `tomb_seq > run_seq` predicate before building memrun; memrun gets `applied_seq`. (`core/src/delta/tl_memtable.c:776`, `core/src/delta/tl_memtable.c:777`, `core/src/delta/tl_memtable.c:791`, `core/src/delta/tl_memtable.c:795`)

## Immutable Delta Objects
- `tl_memrun_t` carries tombstones, bounds, refcount, and `applied_seq` watermark. (`core/src/delta/tl_memrun.h:56`, `core/src/delta/tl_memrun.h:62`, `core/src/delta/tl_memrun.h:68`, `core/src/delta/tl_memrun.h:74`)
- Memrun initialization stores `applied_seq` and starts `refcnt=1`. (`core/src/delta/tl_memrun.c:89`, `core/src/delta/tl_memrun.c:95`)
- `tl_ooorun_t` is immutable sorted records with `applied_seq` and generation `gen`. (`core/src/delta/tl_ooorun.h:19`, `core/src/delta/tl_ooorun.h:25`, `core/src/delta/tl_ooorun.h:27`)
- OOO run creation sets both `applied_seq` and `gen`. (`core/src/delta/tl_ooorun.c:38`, `core/src/delta/tl_ooorun.c:39`)

## Tombstone Interval Engine
- Tombstones are represented as half-open intervals carrying `max_seq` per fragment. (`core/src/internal/tl_intervals.h:10`, `core/src/internal/tl_intervals.h:30`, `core/src/internal/tl_intervals.h:40`)
- Mutable insert splits/merges and applies max-seq semantics (`it->max_seq = max(old, seq)`) before coalescing. (`core/src/internal/tl_intervals.c:216`, `core/src/internal/tl_intervals.c:220`, `core/src/internal/tl_intervals.c:250`, `core/src/internal/tl_intervals.c:273`)
- Cursor lookup returns `max_seq` at timestamp in forward-scan form. (`core/src/internal/tl_intervals.c:671`, `core/src/internal/tl_intervals.c:691`, `core/src/internal/tl_intervals.c:692`)

## Flush Path
- Flush builder context includes output `applied_seq` and tomb fragments for filtering. (`core/src/delta/tl_flush.h:32`, `core/src/delta/tl_flush.h:33`)
- Flush merge is K-way over run + OOO runs; each input carries a watermark (`mr->applied_seq` or `run->applied_seq`). (`core/src/delta/tl_flush.c:150`, `core/src/delta/tl_flush.c:169`, `core/src/delta/tl_flush.c:189`, `core/src/delta/tl_flush.c:204`)
- During flush filtering, record is kept only when `tomb_seq <= watermark`. (`core/src/delta/tl_flush.c:255`, `core/src/delta/tl_flush.c:257`)
- L0 segment output is built with `ctx->applied_seq` as segment watermark. (`core/src/delta/tl_flush.c:321`, `core/src/delta/tl_flush.c:333`)
- Flush publish follows base-capture, off-lock manifest build, under-lock validation, and seqlock swap. (`core/src/tl_timelog.c:945`, `core/src/tl_timelog.c:952`, `core/src/tl_timelog.c:973`, `core/src/tl_timelog.c:976`, `core/src/tl_timelog.c:988`, `core/src/tl_timelog.c:990`)
- Memrun pop from sealed queue occurs inside the same seqlock publication section to avoid snapshot double-visibility of source and output. (`core/src/tl_timelog.c:992`, `core/src/tl_timelog.c:996`, `core/src/tl_timelog.c:999`)
- `tl_flush()` loops sealing and flushing until both active and sealed data are drained. (`core/src/tl_timelog.c:1280`, `core/src/tl_timelog.c:1285`, `core/src/tl_timelog.c:1304`, `core/src/tl_timelog.c:1313`)

## Snapshot And Query Pipeline
- Snapshot object stores manifest ref, shared memview ref, captured `op_seq`, and cached bounds. (`core/src/query/tl_snapshot.h:47`, `core/src/query/tl_snapshot.h:52`, `core/src/query/tl_snapshot.h:57`, `core/src/query/tl_snapshot.h:62`)
- Snapshot implementation currently relies on `writer_mu` serialization and explicitly states no seqlock retry loop in acquisition logic. (`core/src/query/tl_snapshot.c:89`, `core/src/query/tl_snapshot.c:92`)
- Acquisition captures manifest and memview under writer lock, captures `op_seq`, then sorts OOO head off-lock for fresh captures and updates epoch cache when still valid. (`core/src/query/tl_snapshot.c:100`, `core/src/query/tl_snapshot.c:109`, `core/src/query/tl_snapshot.c:123`, `core/src/query/tl_snapshot.c:127`, `core/src/query/tl_snapshot.c:139`, `core/src/query/tl_snapshot.c:145`)
- Snapshot tombstone collection unions active memview, sealed memrun, and L0 tombstones (with defensive L1 tomb inclusion). (`core/src/query/tl_snapshot.c:213`, `core/src/query/tl_snapshot.c:221`, `core/src/query/tl_snapshot.c:236`, `core/src/query/tl_snapshot.c:256`)
- Query planning builds source list from L1/L0/memruns/active and assigns source watermarks from segment/memrun `applied_seq` (active uses variable per-record seq via active iterator). (`core/src/query/tl_plan.c:75`, `core/src/query/tl_plan.c:102`, `core/src/query/tl_plan.c:135`)
- Plan collects tombstones and clips them to query range before handoff. (`core/src/query/tl_plan.c:349`, `core/src/query/tl_plan.c:356`, `core/src/query/tl_plan.c:360`)
- K-merge iterator keeps per-entry watermark, tracks skip metadata (`max_watermark`, `has_variable_watermark`), and exposes watermark in `next()`. (`core/src/query/tl_merge_iter.h:52`, `core/src/query/tl_merge_iter.h:53`, `core/src/query/tl_merge_iter.c:168`, `core/src/query/tl_merge_iter.c:173`, `core/src/query/tl_merge_iter.c:263`)
- K-merge seek preserves prefetched heap entries `>= target` and only reseeks entries `< target`. (`core/src/query/tl_merge_iter.c:343`, `core/src/query/tl_merge_iter.c:348`, `core/src/query/tl_merge_iter.c:359`, `core/src/query/tl_merge_iter.c:372`)
- Filter iterator applies tombstone sequencing rule `drop if tomb_seq > watermark` and can skip-ahead by using tomb cursor + kmerge seek. (`core/src/query/tl_filter.c:49`, `core/src/query/tl_filter.c:53`, `core/src/query/tl_filter.c:54`, `core/src/query/tl_filter.c:55`, `core/src/query/tl_filter.c:62`)
- Point lookup computes `max_tomb_seq_at(ts)` across snapshot sources and applies the same watermark rule in segment/memrun/active collectors. (`core/src/query/tl_point.c:311`, `core/src/query/tl_point.c:349`, `core/src/query/tl_point.c:397`, `core/src/query/tl_point.c:154`, `core/src/query/tl_point.c:228`, `core/src/query/tl_point.c:90`)

## Memview Capture And Cache
- Memview capture copies active run/head/tombs, pins OOO runset and sealed memruns, then computes bounds from records and tombstones. (`core/src/delta/tl_memview.c:404`, `core/src/delta/tl_memview.c:417`, `core/src/delta/tl_memview.c:438`, `core/src/delta/tl_memview.c:432`, `core/src/delta/tl_memview.c:449`, `core/src/delta/tl_memview.c:458`, `core/src/delta/tl_memview.c:464`)
- Sealed queue copy uses two-phase metadata snapshot + revalidation with bounded retries and lock-held fallback. (`core/src/delta/tl_memview.c:273`, `core/src/delta/tl_memview.c:280`, `core/src/delta/tl_memview.c:305`, `core/src/delta/tl_memview.c:312`, `core/src/delta/tl_memview.c:336`, `core/src/delta/tl_memview.c:343`)
- Shared memview wrapper stores epoch and atomic refcount for cache reuse. (`core/src/delta/tl_memview.h:81`, `core/src/delta/tl_memview.h:82`, `core/src/delta/tl_memview.c:587`, `core/src/delta/tl_memview.c:588`, `core/src/delta/tl_memview.c:605`, `core/src/delta/tl_memview.c:614`)

## Storage Layer
- `tl_page_t` is immutable SoA (`ts[]` + `h[]`) with sorted timestamp invariant and metadata bounds. (`core/src/storage/tl_page.h:45`, `core/src/storage/tl_page.h:54`, `core/src/storage/tl_page.h:58`, `core/src/storage/tl_page.h:62`, `core/src/storage/tl_page.h:72`)
- Page-level `lower_bound`/`upper_bound` are binary searches over sorted `ts`. (`core/src/storage/tl_page.c:182`, `core/src/storage/tl_page.c:189`, `core/src/storage/tl_page.c:209`, `core/src/storage/tl_page.c:216`)
- Page catalog search uses binary search over monotonic `max_ts` or `min_ts`. (`core/src/storage/tl_page.c:434`, `core/src/storage/tl_page.c:441`, `core/src/storage/tl_page.c:461`, `core/src/storage/tl_page.c:467`)
- Segment model separates L0 (overlap + tombstones) and L1 (non-overlap + no tombstones) and carries `applied_seq`. (`core/src/storage/tl_segment.h:14`, `core/src/storage/tl_segment.h:15`, `core/src/storage/tl_segment.h:55`, `core/src/storage/tl_segment.h:86`)
- L0 build permits records and/or tombstones and stores `applied_seq`. (`core/src/storage/tl_segment.c:210`, `core/src/storage/tl_segment.c:211`, `core/src/storage/tl_segment.c:247`)
- L1 build requires records, sets `tombstones=NULL`, stores window bounds and `applied_seq`, and enforces H-12 window-bound validation in release mode. (`core/src/storage/tl_segment.c:350`, `core/src/storage/tl_segment.c:351`, `core/src/storage/tl_segment.c:364`, `core/src/storage/tl_segment.c:368`, `core/src/storage/tl_segment.c:396`)
- Manifest is immutable copy-on-write publication root with L1 sorted/non-overlap invariants. (`core/src/storage/tl_manifest.h:12`, `core/src/storage/tl_manifest.h:13`, `core/src/storage/tl_manifest.h:16`, `core/src/storage/tl_manifest.h:17`)
- Manifest builder acquires segment refs into new arrays, sorts L1 by window start, validates non-overlap (H-14), and computes cached bounds. (`core/src/storage/tl_manifest.c:549`, `core/src/storage/tl_manifest.c:567`, `core/src/storage/tl_manifest.c:579`, `core/src/storage/tl_manifest.c:582`, `core/src/storage/tl_manifest.c:592`, `core/src/storage/tl_manifest.c:599`, `core/src/storage/tl_manifest.c:615`)
- `tl_window` uses mathematical floor division for window ID and overflow-safe bound computation with unbounded-end handling at `TL_TS_MAX`. (`core/src/storage/tl_window.h:13`, `core/src/storage/tl_window.h:20`, `core/src/storage/tl_window.c:50`, `core/src/storage/tl_window.c:66`, `core/src/storage/tl_window.c:136`, `core/src/storage/tl_window.c:143`)

## Compaction And Background Maintenance
- Compaction context pins selected L0/L1 inputs, a base manifest, a snapshot, effective tomb maps, outputs, and deferred dropped records. (`core/src/maint/tl_compaction.h:69`, `core/src/maint/tl_compaction.h:71`, `core/src/maint/tl_compaction.h:75`, `core/src/maint/tl_compaction.h:76`, `core/src/maint/tl_compaction.h:80`, `core/src/maint/tl_compaction.h:81`, `core/src/maint/tl_compaction.h:84`, `core/src/maint/tl_compaction.h:88`, `core/src/maint/tl_compaction.h:113`)
- Compaction-needed trigger checks include L0 count threshold and optional delete-debt threshold. (`core/src/maint/tl_compaction.c:418`, `core/src/maint/tl_compaction.c:424`, `core/src/maint/tl_compaction.c:427`)
- L1 selection is explicitly window-overlap based (not record-bound overlap). (`core/src/maint/tl_compaction.c:448`, `core/src/maint/tl_compaction.c:499`, `core/src/maint/tl_compaction.c:536`)
- Selection captures snapshot and uses `tl_snapshot_seq()` as compaction output watermark (`ctx->applied_seq`). (`core/src/maint/tl_compaction.c:729`, `core/src/maint/tl_compaction.c:735`)
- Merge phase builds union tomb sets, builds clipped tomb set from snapshot tombstones, and runs K-way merge with per-input watermarks and tomb filtering (`tomb_seq > watermark` means drop). (`core/src/maint/tl_compaction.c:1012`, `core/src/maint/tl_compaction.c:1050`, `core/src/maint/tl_compaction.c:1092`, `core/src/maint/tl_compaction.c:1103`, `core/src/maint/tl_compaction.c:1148`, `core/src/maint/tl_compaction.c:1196`)
- Deferred dropped records are collected during merge and callback firing is deferred until publish success. (`core/src/maint/tl_compaction.c:1197`, `core/src/maint/tl_compaction.c:1205`, `core/src/maint/tl_compaction.c:1551`, `core/src/maint/tl_compaction.c:1562`)
- Compaction outputs L1 segments with `ctx->applied_seq`, plus optional residual tombstone-only L0 segment also carrying `ctx->applied_seq`. (`core/src/maint/tl_compaction.c:882`, `core/src/maint/tl_compaction.c:974`, `core/src/maint/tl_compaction.c:980`)
- Publish is strict: if current manifest differs from base, returns `TL_EBUSY` and caller retries. (`core/src/maint/tl_compaction.c:1381`, `core/src/maint/tl_compaction.c:1391`, `core/src/maint/tl_compaction.c:1395`)
- Compaction publish swap uses seqlock around manifest pointer update. (`core/src/maint/tl_compaction.c:1399`, `core/src/maint/tl_compaction.c:1403`, `core/src/maint/tl_compaction.c:1405`)
- `tl_compact_one()` performs bounded retry loop and increments `compaction_publish_ebusy` and `compaction_retries` counters on conflicts. (`core/src/maint/tl_compaction.c:1546`, `core/src/maint/tl_compaction.c:1606`, `core/src/maint/tl_compaction.c:1608`)
- After successful publish with L1 outputs, compaction freezes window grid and commits adaptive success updates under `maint_mu`. (`core/src/maint/tl_compaction.c:1584`, `core/src/maint/tl_compaction.c:1588`, `core/src/maint/tl_compaction.c:1593`, `core/src/maint/tl_compaction.c:1594`)
- Background maintenance worker runs a flag-based loop under `maint_mu`, drains flush work first, and executes compaction with transient-error backoff and retry flag restoration. (`core/src/tl_timelog.c:1901`, `core/src/tl_timelog.c:1922`, `core/src/tl_timelog.c:1937`, `core/src/tl_timelog.c:1944`, `core/src/tl_timelog.c:1992`, `core/src/tl_timelog.c:2006`, `core/src/tl_timelog.c:2058`, `core/src/tl_timelog.c:2082`)

## Adaptive Segmentation
- Adaptive logic is feature-gated by `target_records`; zero means disabled. (`core/src/maint/tl_adaptive.h:12`, `core/src/maint/tl_adaptive.c:27`)
- Candidate computation is conservative: fallback returns current window when preconditions are not met (warmup, invalid EWMA, etc.). (`core/src/maint/tl_adaptive.h:160`, `core/src/maint/tl_adaptive.c:304`, `core/src/maint/tl_adaptive.c:309`, `core/src/maint/tl_adaptive.c:319`, `core/src/maint/tl_adaptive.c:322`)
- Candidate pipeline computes `target_records / ewma_density`, applies failure backoff, guardrails, hysteresis, and quantum snapping. (`core/src/maint/tl_adaptive.c:339`, `core/src/maint/tl_adaptive.c:346`, `core/src/maint/tl_adaptive.c:353`, `core/src/maint/tl_adaptive.c:363`, `core/src/maint/tl_adaptive.c:369`)
- Resize desire is blocked when `window_grid_frozen` is true. (`core/src/maint/tl_adaptive.c:434`)

## Stats And Validation
- `tl_stats()` aggregates segment/page/record counts from manifest plus memview, includes tombstone totals across active/sealed/L0, and reads cumulative counters from parent `tl_timelog`. (`core/src/tl_timelog.c:2382`, `core/src/tl_timelog.c:2397`, `core/src/tl_timelog.c:2416`, `core/src/tl_timelog.c:2455`, `core/src/tl_timelog.c:2465`, `core/src/tl_timelog.c:2494`)
- Adaptive stats are read under `maint_mu` when adaptive is enabled. (`core/src/tl_timelog.c:2514`, `core/src/tl_timelog.c:2515`, `core/src/tl_timelog.c:2520`)
- `tl_validate()` is a debug-only deep validator and returns `TL_OK` no-op in release builds. (`core/src/tl_timelog.c:2533`, `core/src/tl_timelog.c:2540`)

## CPython Binding Architecture
- CPython extension `_timelog` is built from `py_handle`, `py_errors`, `py_timelog`, iterator/span modules, and module init code. (`bindings/cpython/CMakeLists.txt:122`, `bindings/cpython/CMakeLists.txt:125`, `bindings/cpython/CMakeLists.txt:128`, `bindings/cpython/CMakeLists.txt:133`, `bindings/cpython/CMakeLists.txt:137`)
- Binding test suite is enabled by default via `TIMELOG_BUILD_PY_TESTS` and registered as CTest tests (`py_handle`, `py_timelog`, `py_iter`, `py_span`, `py_maint_b5`, `py_errors`). (`bindings/cpython/CMakeLists.txt:177`, `bindings/cpython/CMakeLists.txt:496`, `bindings/cpython/CMakeLists.txt:501`, `bindings/cpython/CMakeLists.txt:506`, `bindings/cpython/CMakeLists.txt:511`, `bindings/cpython/CMakeLists.txt:516`, `bindings/cpython/CMakeLists.txt:521`)
- Handle encoding is pointer-cast based with compile-time size assertion and round-trip encode/decode helpers. (`bindings/cpython/include/timelogpy/py_handle.h:49`, `bindings/cpython/include/timelogpy/py_handle.h:55`, `bindings/cpython/include/timelogpy/py_handle.h:64`, `bindings/cpython/include/timelogpy/py_handle.h:74`)
- Python on-drop callback contract is explicitly no-GIL/no-Python-API on maintenance thread. (`bindings/cpython/include/timelogpy/py_handle.h:16`, `bindings/cpython/include/timelogpy/py_handle.h:219`, `bindings/cpython/include/timelogpy/py_handle.h:221`)
- The binding explicitly requires the CPython GIL and is marked unsupported on free-threaded/no-GIL builds. (`bindings/cpython/include/timelogpy/py_timelog.h:20`, `bindings/cpython/include/timelogpy/py_timelog.h:21`)

## `CLAUDE.md` Intent Vs Current Code
- `CLAUDE.md` documents in-memory/no-disk architecture. (`CLAUDE.md:3`, `CLAUDE.md:4`)
- Public API and implementation align with in-memory design (`timelog` multimap and all in-memory structures). (`core/include/timelog/timelog.h:8`, `core/src/internal/tl_timelog_internal.h:163`, `core/src/storage/tl_manifest.h:12`)
- `CLAUDE.md` documents lock order `maint_mu -> flush_mu -> writer_mu -> memtable.mu`, matching internal headers. (`CLAUDE.md:184`, `core/src/internal/tl_timelog_internal.h:85`, `core/src/delta/tl_memtable.h:24`)
- `CLAUDE.md` describes snapshot seqlock retry protocol, but current snapshot acquisition code states writer-mutex capture without seqlock retry. (`CLAUDE.md:131`, `CLAUDE.md:135`, `core/src/query/tl_snapshot.c:89`, `core/src/query/tl_snapshot.c:92`)

## Tombstone Watermark Model Alignment
- Canonical model doc: `docs/internals/components/tombstone-watermark-model.md`.
- The design goal is two-tier sequencing: mutable per-record seq + immutable per-source applied watermark.
- Current implementation has global `op_seq` in timelog and increments it for inserts/deletes. (`core/src/internal/tl_timelog_internal.h:166`, `core/src/tl_timelog.c:736`, `core/src/tl_timelog.c:838`)
- Current mutable layers store per-record seqs in active run and OOO head sequence vectors. (`core/src/delta/tl_memtable.h:37`, `core/src/delta/tl_memtable.h:39`)
- Current immutable sources carry applied watermark in memrun and segment. (`core/src/delta/tl_memrun.h:74`, `core/src/storage/tl_segment.h:86`)
- Read/filter rule in code is `drop if tomb_seq > watermark`, matching the documented model. (`core/src/query/tl_filter.c:51`, `core/src/query/tl_filter.c:54`)
- Point lookup also uses max tomb seq at timestamp and compares against per-source watermarks/seqs. (`core/src/query/tl_point.c:311`, `core/src/query/tl_point.c:154`, `core/src/query/tl_point.c:228`, `core/src/query/tl_point.c:90`)
- The current implementation realizes piecewise-max tomb fragments through `tl_intervals` (`max_seq` intervals + cursor). (`core/src/internal/tl_intervals.h:30`, `core/src/internal/tl_intervals.h:40`, `core/src/internal/tl_intervals.c:250`, `core/src/internal/tl_intervals.c:671`)

## Practical Mental Model (Code-Verified)
- Writes mutate memtable state (`active_run`/`ooo_head`/`active_tombs`) under writer serialization with monotonic `op_seq`. (`core/src/delta/tl_memtable.h:36`, `core/src/delta/tl_memtable.h:38`, `core/src/delta/tl_memtable.h:40`, `core/src/tl_timelog.c:733`, `core/src/tl_timelog.c:736`)
- Sealing creates immutable memruns (with applied watermark), enqueueing to fixed sealed ring for flush. (`core/src/delta/tl_memtable.c:791`, `core/src/delta/tl_memtable.c:795`, `core/src/delta/tl_memtable.c:819`, `core/src/delta/tl_memtable.h:58`)
- Flush converts memruns into L0 segments and atomically swaps manifest + pops memrun under seqlock publication. (`core/src/delta/tl_flush.c:328`, `core/src/tl_timelog.c:988`, `core/src/tl_timelog.c:996`, `core/src/tl_timelog.c:999`)
- Compaction rewrites L0(+overlapping L1) into new L1 windows with strict publish validation/retries, then retires dropped records via deferred callback path. (`core/src/maint/tl_compaction.c:513`, `core/src/maint/tl_compaction.c:1350`, `core/src/maint/tl_compaction.c:1391`, `core/src/maint/tl_compaction.c:1546`, `core/src/maint/tl_compaction.c:1561`)
- Reads acquire snapshot (`manifest + memview + op_seq`), build source plan, k-merge by timestamp, and apply tombstone watermark filtering. (`core/src/query/tl_snapshot.h:47`, `core/src/query/tl_snapshot.h:52`, `core/src/query/tl_snapshot.h:57`, `core/src/query/tl_plan.c:191`, `core/src/query/tl_merge_iter.c:222`, `core/src/query/tl_filter.c:53`, `core/src/query/tl_filter.c:54`)
