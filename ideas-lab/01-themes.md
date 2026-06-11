# Phase 2–3 — Theme Registry (deduped, exclusive, family-level complete)

176 raw atoms → **8 themes**, deduped to canonical idea families. Each idea has a stable ID, source docs
`[n]`, and a grounded note. IDs are referenced by the experiments (Phase 6) and the final seeding.
This registry is source-document/family complete, but the raw digest did not preserve a machine-checkable
`raw_atom -> canonical_id` map; it must not be treated as atom-level proof.

> ⚠️ **Ground-truth correction** carried into every theme: contrary to what docs 20/29 assume,
> Timelog does **not** currently use vectorcall/`METH_FASTCALL` anywhere. Verified directly:
> all hot methods (`append`, `range`, `since`, `until`, `point`, `equal`, `next_ts`, `prev_ts`,
> `delete_range`, `delete_before`) are `METH_VARARGS` + `PyArg_ParseTuple`. The buffer protocol
> *is* already used (PageSpan `bf_getbuffer`); the retired-handle path *is* lock-free (no Python
> callback on drop). These facts reshape relevance below.

---

## T1 — Calling convention: vectorcall / METH_FASTCALL  ·  src 1,18,36,37,29,20,21
- **T1.1** Convert hot `METH_VARARGS` methods to `METH_FASTCALL` — kill the per-call args-tuple build + `PyArg_ParseTuple`. Hottest target: `append(ts,obj)`. [1,18,20,21,29,36]
- **T1.2** Implement `tp_vectorcall_offset` (+`Py_TPFLAGS_HAVE_VECTORCALL`) on hot callable *types* (iterator `__next__`, result objects). [18,36]
- **T1.3** Use `PyObject_Vectorcall` instead of `PyObject_Call` where the C core invokes Python callables in tight loops. *(Low applicability: Timelog's drop path is callback-free; verify before pursuing.)* [1,18,29]
- **T1.4** Build a vectorcall-vs-varargs microbench (sweep nargs 0/1/2/4/8/16, ≥100k iters, pinned core) to quantify ns/call & break-even. [1,18,36]
- **T1.5** Profile first — measure Python→C boundary cost for `append`/`range` before refactor; convert only where call overhead is a real fraction. [18,36,29]
- **T1.6** Apply narrowly: hot iterators & batch ops; skip cold management calls (`compact`/`snapshot`/`close`). [36]
- **T1.7** *(rationale)* Frame vectorcall as the call-boundary expression of Timelog's existing zero-copy/lock-free philosophy. [36]
- **T1.8** Keep hot C wrappers tiny and exception-safe: early error returns, immediate DECREF on every owned temporary, and explicit refcount audits before optimizing. [35]

## T2 — Batch / bulk Python↔C APIs  ·  src 13,26,29,16,31,32
- **T2.1** `bulk_append(timestamps, handles)` — parse a sequence/buffer once in C, insert without per-item boxing. [26,13,29]
- **T2.2** `range_read_into(t1,t2,out_buf)` — fill a caller-provided writable memoryview in place (zero alloc). [26]
- **T2.3** Return typed buffers (`array('q')`/memoryview) instead of lists of Python ints for bulk results. [26,13]
- **T2.4** `scan_many(pagespan, ranges, out_idx)` — batched range scan over contiguous buffers. [13]
- **T2.5** `hash_pages(pagespan, out_u64)` — batched page hashing (integrity / bloom seeding). [13]
- **T2.6** Release the GIL around the *whole* native batch loop, not per item. [13,26,29]
- **T2.7** Validate bounds/alignment/size once per batch, not per item. [13]
- **T2.8** Batch-size heuristic `B ≈ ceil(call_overhead / per_elem_cost)`; `batch_size` kwarg; default 64–128; sweep {8,16,32,64,128}. [13,26,16,29]
- **T2.9** Keep per-item APIs as thin shims over `_many` variants. [13]
- **T2.10** Batched errors: collect failure indices/bitmap, raise once. [26]
- **T2.11** Fixed endianness/format (`<q`/`<Q`) in bulk API; enforce in tests. [26]
- **T2.12** Ship an A/B microbench template in docs for users to find their own break-even. [26,16]
- **T2.13** Compute FFI break-even `N_break = t_overhead / t_saved_per_element`. [16]
- **T2.14** Minimum-batch-size guard/warning for pathological tiny queries below the throughput knee. [31,32]

## T3 — Zero-copy / buffer protocol / Arrow & NumPy interop  ·  src 24,31,16,27,32,35,37,8
- **T3.1** Export sealed pages as `ArrowArray` via the Arrow C Data Interface (**timestamp column only**; `h[]` handles are encoded `PyObject*` pointers and must not be exposed as numeric data), with release callbacks. [24]
- **T3.2** In-process `ArrowArrayStream` over L0/L1 windows for streaming batches; Arrow Flight/server/network transport is out of scope for the in-memory embedding. [24,31]
- **T3.3** Keep PageSpan/Arrow exports PEP 3118-compliant for `numpy.frombuffer` zero-copy. [24,35]
- **T3.4** Document the export lifetime contract (release exactly once; pinned by snapshot/seqlock). [24,31]
- **T3.5** Use nanoarrow helpers for ArrowSchema/ArrowArray init to cut FFI boilerplate. [24]
- **T3.6** Dual read APIs: in-proc C callback (fused analytics) + in-process streaming Arrow for local consumers. Networked Arrow Flight remains filtered as I/O infrastructure, not a Timelog core idea. [31]
- **T3.7** Pointer-identity validation that PageSpan exports truly alias internal buffers. [16,27,32]
- **T3.8** Attach `xxhash64` side-checksum to prove zero-copy + integrity cheaply. [16]
- **T3.9** Read-only/writable-rejection tests: assert PageSpan timestamp exports are immutable and reject writable buffer requests while still proving pointer stability. [27]
- **T3.10** Debug asserts: pages pinned until release; catch double-free / premature reuse / access-after-release. [27,24]
- **T3.11** Prefer `PyObject_GetBuffer` over per-element conversions for bulk ts/handle arrays (e.g. bulk append from numpy). [35,8,37]
- **T3.12** Zero-copy Arrow Int64/Timestamp adapters over SoA `ts[]` only for Velox/Polars consumers; payload handles stay behind `objects()`. [31]
- **T3.13** Interop guardrails for Arrow/Velox-style exports: schema/version pinning, bounded fan-out/backpressure, metrics, and explicit ABI/support-window documentation. [31]

## T4 — Compaction strategy & scheduling  ·  src 12,6,15,17,30,11,34
- **T4.1** Time-aware leveled hybrid: recent/hot windows leveled & narrow; cold windows aged to read-optimized last level / TWCS whole-drop. [12]
- **T4.2** Keep recent window small to bound L0 fan-in (hot query touches ≤1–2 runs); level hot windows aggressively. [12,6]
- **T4.3** Size-tiered within a window during heavy ingest; consolidate to leveled when the window cools. [12]
- **T4.4** Align L1 window boundaries to retention horizon → whole-window TTL drop with zero compaction. [12]
- **T4.5** Scope delete-driven micro-merges to windows in the delete span only. [12]
- **T4.6** Periodically re-index/coalesce tombstones per window, then reshape/TTL reclaim. [12]
- **T4.7** Bias compactor to keep last N windows extra-clean for `[now-Δ, now)` reads (recency-priority queue). [12]
- **T4.8** Per-compaction **ROI gate**: meter cost (bytes_in+out, cpu_sec) + estimate Δp95 benefit; run only if ROI > τ. [15]
- **T4.9** Benefit model: N→1 merge ≈ (N-1)·cost_per_run_lookup over a horizon; refine from a rolling outcome log. [15]
- **T4.10** Per-task metrics struct feeding ROI + telemetry histograms (taken/skipped_low_roi/skipped_stall). [15]
- **T4.11** Conservative τ default (ROI>1.0); lower only on SLO violation. [15]
- **T4.12** Adaptive mode switch — conservative (throttle, larger targets, delay merges) vs aggressive (more threads, size-aligned, tiered). [17]
- **T4.13** Signals: p99 vs 5-min EMA (>1.15× → conservative); WA proxy vs 15-min (>1.07× & latency stable → aggressive); L0 backlog (>~32 → emergency). [17]
- **T4.14** Hysteresis/dwell: ≥5–10 min/mode, token-bucket ≤6 switches/day, revert after 10–15 min quiet. [17]
- **T4.15** EWMA tail-growth on `log(tail_len)` (α≈0.15) for sustained-expansion detection. [30]
- **T4.16** Per-key write-skew via normalized HHI over a 2048-key sliding window. [30]
- **T4.17** CUSUM on `log(tail_len)` with drift k + dual thresholds (h_start/h_stop) + min-compact duration. [30]
- **T4.18** Couple skew into CUSUM via `boost = 1 + 0.35·ew_skew`. [30]
- **T4.19** Backward-anchored compaction windows capped at `max_windows` (=4). [30]
- **T4.20** Wire `CompactDetector.step(tail_len,key,now)` into the append path/timer (O(1) EWMAs + O(window) HHI). [30]
- **T4.21** `DetectorConfig` for tuning (α, k, h, min_compact, cooldown, max_windows, window) without code changes. [30]
- **T4.22** Factorial sweep `memtable_size{16,32,64,128 MiB} × tombstone_canon{off,on}` on delete-storm + mixed(80/15/5). [11]
- **T4.23** Memtable sizing rules: upsize when flush-count high/WA>3×/P50 jittery & L0 span bounded; downsize when P99 reads −>20% or reshape thrashes. [11]
- **T4.24** Secondary sweep `TW_window{5,10,20m} × level_multiplier{4,8}` only if read-amp/retention edge cases persist. [11]
- **T4.25** Bottleneck decision matrix: read tails→recent-window leveling; ingest→per-window STCS; retention→TWCS; delete storms→canon + micro-merge. [12,11]

## T5 — Tombstones / deletes  ·  src 11,12,37  *(canon mechanics live in T4.5/T4.6)*
- **T5.1** Measure **reclaim lag** (tombstone-create → data-absent post-compaction) + residual tombstone count per level. [11]
- **T5.2** Objective rules to enable tombstone canonicalization (e.g. P99 range −≥15% AND compaction CPU ≤+20%; or reclaim lag −30% w/ ≤+10% space). [11]
- **T5.3** Correctness sanity checks: reinsertion after overlapping tombstones; snapshot-consistent reads under continuous compaction; reshape stability. [11]
- **T5.4** `delete_range` marks all affected entries in one C loop (no per-tombstone Python re-entry). [37]

## T6 — Subinterpreters / free-threading / HPy  ·  src 4,5,7,21,28,20
- **T6.1** Inventory every process-global/static mutable (manifests, error sentinels, type caches, stats, tombstone registry, retired stack) with lifetime + sharing intent → `globals.md`. [7,21,4]
- **T6.2** Move module state into a per-interpreter module-state struct via multiphase init. [7,21]
- **T6.3** Convert any static singleton types to heap types (`PyType_FromSpec`) stored in module state. [7]
- **T6.4** Use `Py_tss_t`/C11 TSS for thread-local scratch instead of hidden static thread-locals. [7]
- **T6.5** C11 `_Atomic` on owned C structs (stats relaxed; manifest release/acquire); honest GIL boundaries. [7]
- **T6.6** *(strategic)* Port to HPy handles so refcount leaks become compile-time errors + enable Universal/PyPy wheels. [7,21]
- **T6.7** *(staged)* Enable HPy hybrid build in CMake; port one hot method (`range`) first to validate toolchain. [21,7]
- **T6.8** Subinterpreter pytest suite: isolation smoke, capsule/opaque cross-interp refusal, GC/finalizer isolation, create/destroy stress (300+). [5,7,21]
- **T6.9** Timelog-specific subinterp assertions: seqlock interpreter-local; PageSpan export fails cleanly cross-interp; per-interpreter worker. [5]
- **T6.10** Never share raw Timelog capsules/opaque handle pointers across interpreters; reject on cross-interp import. [4,5]
- **T6.11** Validate finalizers/refcounts safe under interpreter switching (retired stack, manifests). [4]
- **T6.12** HPy Universal + `HPY_DEBUG=1` CI jobs to catch handle misuse & prove forward-compat. [5,20]
- **T6.13** HPy-vs-C-API decision gates (CPython-ABI p50 ≤5%/p95 ≤10%; Universal ≤12%/≤20%) before adopting. [28]

## T7 — Memory & allocator behavior  ·  src 3,8,14
- **T7.1** Two-process memory probe (monitor+worker) sampling RSS + tracemalloc → CSV ~4 Hz. [14]
- **T7.2** Slope analysis to split Python leaks (tracemalloc↑ & RSS↑) from native fragmentation (tracemalloc flat, RSS↑). [14]
- **T7.3** CI gates on leak-slope thresholds. [14]
- **T7.4** Detect allocator step-jumps (≥3 jumps >8 MiB) → correlate with sealing/compaction batch sizes. [14]
- **T7.5** Capture top-K tracemalloc frames per sample for a hotspot CSV column. [14]
- **T7.6** Allocator A/B via `LD_PRELOAD` (jemalloc/mimalloc) or `PYTHONMALLOC` to isolate fragmentation. [14,3,8]
- **T7.7** jemalloc tuning (dirty_decay_ms, background_thread, tcache_max) to curb RSS creep. [14]
- **T7.8** `MALLOC_ARENA_MAX=2–4` to limit glibc per-thread arena bloat (esp. free-threading). [14,3]
- **T7.9** Phase workloads so arenas empty between phases; don't mix long-lived + varied short-lived churn. [8]
- **T7.10** Prefer buffer reuse / homogeneous layouts over per-item object creation in hot loops. [8,35]
- **T7.11** Break reference cycles in iterator/manifest/callback chains; weakref + context managers. [8]
- **T7.12** Audit PageSpan consumers + retired-queue DECREF timing so zero-copy views don't prolong lifetimes. [14]
- **T7.13** Cap L0 span / sealing batch sizes to bound peak compaction memory. [14]
- **T7.14** memray flamegraphs to locate native allocator hotspots. [3,14]
- **T7.15** `sys._debugmallocstats`/`getallocatorsname`/tracemalloc to diagnose binding-layer RSS. [8,3]
- **T7.16** Use process isolation for memory-sensitive phases when RSS return-to-OS matters: run worker subprocesses per phase/cell so allocator arenas die with the process. [8]

## T8 — CI, benchmarking & profiling harness  ·  src 9,10,14,20,27,28,32,5,6,35,34
- **T8.1** Microbench harness: call-through latency, arg-marshalling, buffer zero-copy scan; ST / MT(GIL & no-GIL) / multi-interp variants. [20,32]
- **T8.2** Emit p50/p95/p99 + stdev JSON; baseline on main; fail PR on >X% p95/p99 regression. [20,10,32,28]
- **T8.3** Fast PR smoke (~30s point reads) + nightly/weekly full matrix split. [10,32]
- **T8.4** CPU pinning + turbo/governor off + warmup + NUMA logging for low variance. [28,32,6]
- **T8.5** Standalone C benchmark linking the same inner-C routines (no FFI/interpreter noise). [35]
- **T8.6** Env-configurable bench (scenarios/runs/dataset/seed). [10]
- **T8.7** `perf record` + Brendan-Gregg flamegraph CI artifacts. [10,3]
- **T8.8** Wire the memory CI harness (T7.1–T7.5) as a gate. [14]
- **T8.9** Compaction runbook: WA = written/ingested, SA = space/logical, HDR histograms, 5 paired seeds, mean+95%CI. [6]
- **T8.10** Three Timelog workloads: steady (10k/s), bursty (1M/30s), mixed 90/10 @ 50k/s; shared seeds. [6]
- **T8.11** Strategy-accept rubric: WA −≥5% AND p95 within 3% AND p99 within 2× SLO. [6]
- **T8.12** Record `experiment.json` (knobs+SHA+seed) + `metrics.parquet` for reproducibility. [6,11]
- **T8.13** CLI flags (memtable_size, tombstone_canonicalize, max_compaction_windows, reshape_cooldown) for sweeps. [11]
- **T8.14** Instrumentation counters (compaction_cpu_secs, reshape_total, window_bound_exceeded, rebase_publish_{ok,fallback,conflict}, reclaim_lag p50/95/99, space_amp, write_amp). [11,15]
- **T8.15** OOO-heavy seeded CI job (`--ooo_ratio=0.3`) uploading `metrics.json`. [9]
- **T8.16** Buffer pointer-stability + read-only/writable-rejection CI tests across wheel flavors. [27]
- **T8.17** Phase-2 sanitizer validation on compaction changes + before/after bench deltas w/ commit hash. [9,7]
- **T8.18** LLD doc freezing handle pointer encoding (layout/atomicity/portability/test-matrix/perf-budget). [9]
- **T8.19** Extract `select_L0_windows()` into its own TU with pure I/O + a boundary fuzz test. [9]
- **T8.20** Build flags `-O3 -fno-exceptions -fvisibility=hidden` (+ `-march=native` dev-bench only). [35]
- **T8.21** pytest under `PYTHONMALLOC=debug` + `PYTHONWARNDEFAULTENCODING=1`. [35]
- **T8.22** Explicit GIL-overhead logging: append latency 1 thread vs N free-threaded; detect CAS-spin contention. [32]
- **T8.23** Go-to metrics: ingest events/s vs handle-cardinality; p99 read under mixed load; p50/99 hot-window vs cold-layer; bytes/point. [34,6]

---

### Coverage check
Every non-dropped source document and idea family is represented above (dropped: doc_2, doc_22,
doc_33 — see catalog). The raw digest artifact did not preserve a `raw_atom -> canonical_id` field, so
this registry is the canonical deduped coverage artifact rather than a machine-verifiable one-to-one atom
map. Cross-theme overlaps were resolved by **best-fit single placement** (e.g. canonicalization mechanics →
T4; delete-specific *measurement* → T5; thread-state-detach-around-batch → T2; allocator knobs → T7).
