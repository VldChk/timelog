# Phase 1 — Raw Catalog (per-document digest)

37 input files → **34 unique** (3 exact-dup pairs removed) → digested into **176 raw digest atoms**
by a 12-agent fan-out (`_data/raw-digests.json` holds the full structured output).
The count includes negative "do not apply" atoms for two off-topic documents; doc_33 has an empty
structured idea list and is represented by the table/drop rationale. The table's `#ideas` column
counts actionable Timelog ideas after that filtering.

**Relevance tally:** 23 core · 8 tangential · 3 irrelevant.

Relevance is judged against Timelog's *actual* architecture (in-memory, C17 core + hand-written
CPython C-API, no disk/network I/O). "Transfer" = does the underlying *technique* apply even if the
doc's framing (Rust/Arrow/sockets/disk) does not.

| Doc | Gist | Relevance | Primary theme | #ideas | Notes / dup |
|-----|------|-----------|---------------|:------:|-------------|
| doc_1 | vectorcall vs PyObject_Call microbench (C ext) | 🟢 core | vectorcall | 3 | — |
| doc_2 | Merkle-tree anti-entropy replica repair | 🔴 irrelevant | (distributed) | 0 | single-process; no replication; raw digest has one negative do-not-apply atom |
| doc_3 | CPython memory primer (pymalloc/tracemalloc/memray) | 🟡 tangential | memory-allocator | 5 | profiling transfers |
| doc_4 | HPy handle safety across subinterpreters | 🟢 core | free-threading-gil | 3 | — |
| doc_5 | Subinterpreter pytest harness + CI YAML | 🟢 core | testing | 7 | — |
| doc_6 | Leveled vs universal compaction measurement runbook | 🟢 core | compaction-lsm | 7 | — |
| doc_7 | HPy migration (8-pass) for subinterp/free-threading | 🟢 core | hpy | 10 | **≡ doc_19** |
| doc_8 | pymalloc arena pinning avoidance | 🟡 tangential | memory-allocator | 4 | — |
| doc_9 | Phase-2 compaction validation + LLD + CI plan | 🟢 core | ci-benchmarking | 5 | Timelog-specific |
| doc_10 | GitHub Actions perf matrix + flamegraphs | 🟢 core | ci-benchmarking | 5 | assumes pyo3/maturin (off-stack) |
| doc_11 | memtable×tombstone-canon factorial sweep | 🟢 core | tombstones-deletes | 8 | Timelog-specific |
| doc_12 | LSM compaction strategies (STCS/LCS/TWCS/hybrid) | 🟢 core | compaction-lsm | 8 | **≡ doc_23** |
| doc_13 | Batching Python→C via memoryview (scan_many) | 🟢 core | buffer-protocol | 6 | **≡ doc_25** |
| doc_14 | Memory leak/fragmentation CI harness (RSS+tracemalloc) | 🟢 core | ci-benchmarking | 11 | — |
| doc_15 | Compaction ROI gate (cost/benefit per task) | 🟢 core | compaction-lsm | 8 | — |
| doc_16 | FFI break-even + Arrow zero-copy proof | 🟡 tangential | c-api-binding | 3 | Arrow-specific; break-even transfers |
| doc_17 | Auto-tune compaction modes (p99/WA/L0 signals) | 🟢 core | compaction-lsm | 6 | — |
| doc_18 | vectorcall (PEP 590) overhead explainer | 🟡 tangential | c-api-binding | 3 | near-dup of doc_1 |
| doc_19 | (HPy migration) | — dup | — | — | **exact dup of doc_7** |
| doc_20 | vectorcall+HPy+buffer microbench CI gate | 🟢 core | ci-benchmarking | 5 | ⚠ wrongly assumes FASTCALL exists |
| doc_21 | HPy porting 3-phase migration plan | 🟢 core | free-threading-gil | 5 | — |
| doc_22 | Zero-copy file/socket I/O (readinto/mmap) | 🔴 irrelevant | (I/O) | 0 | no I/O path in Timelog; raw digest has one negative do-not-apply atom |
| doc_23 | (compaction strategies) | — dup | — | — | **exact dup of doc_12** |
| doc_24 | Arrow C Data Interface zero-copy export | 🟢 core | buffer-protocol | 5 | — |
| doc_25 | (batching memoryview) | — dup | — | — | **exact dup of doc_13** |
| doc_26 | Bulk/batch Python↔C API patterns | 🟢 core | c-api-binding | 8 | — |
| doc_27 | CI tests for silent copies / writable buffers | 🟡 tangential | ci-benchmarking | 5 | struct-dtype focus; pointer test transfers |
| doc_28 | HPy vs C-API microbench decision gates | 🟡 tangential | c-api-binding | 3 | — |
| doc_29 | vectorcall vs bulk vs GIL-release amortization | 🟢 core | vectorcall | 5 | ⚠ wrongly assumes vectorcall exists |
| doc_30 | EWMA+CUSUM CompactDetector (drop-in, Timelog-named) | 🟢 core | compaction-lsm | 7 | — |
| doc_31 | Velox vs Arrow Flight decision | 🟡 tangential | buffer-protocol | 4 | analytics out of scope; Arrow adapter transfers |
| doc_32 | FFI round-trip + Arrow Flight microbench checklist | 🟢 core | ci-benchmarking | 6 | — |
| doc_33 | io_uring + eBPF for disk-LSM compaction | 🔴 irrelevant | (disk I/O) | 0 | in-memory; no syscalls |
| doc_34 | Storage-engine paradigm survey + metrics | 🟡 tangential | memory-allocator | 4 | metrics framing transfers |
| doc_35 | CPython binding patterns (hot-path/buffer/C-bench) | 🟢 core | c-api-binding | 5 | — |
| doc_36 | vectorcall calling-convention explainer | 🟢 core | c-api-binding | 4 | conceptual; names Timelog |
| doc_37 | C-API perf mental model (fewer calls, not faster) | 🟢 core | c-api-binding | 6 | conceptual; validates design |

## Exact-duplicate pairs (md5-confirmed)
`doc_7 ≡ doc_19` · `doc_12 ≡ doc_23` · `doc_13 ≡ doc_25` — canonical kept = lower number.

## Dropped as irrelevant (no technique transfer to an in-memory C-extension index)
- **doc_2** — Merkle-tree anti-entropy is for multi-node replica reconciliation; Timelog is single-process.
- **doc_22** — readinto/mmap/socket zero-copy is disk/network I/O; Timelog has none. Its generic
  `memoryview`/`numpy.frombuffer` material is a semantic duplicate of the in-memory buffer work already
  represented by docs 13/24/27/35, so it was not counted as a new idea atom.
- **doc_33** — io_uring/eBPF cut *syscall* cost in disk-LSM compaction; Timelog's compaction is pure memory.

> Note: "irrelevant" here means **for direct application**. doc_2's *interval-hashing* and doc_33's
> *push-compute-down* mindsets reappear, transformed, as my own ideas in Phase 4 — flagged there.
