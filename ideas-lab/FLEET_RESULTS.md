# Serious Audit — Prototype, measurement, and audit results

Built prototype rows branched off baseline `e7e7efb` in isolated worktrees and saved patches under
`experiments/<id>/`. Rows now distinguish reproducible saved measurements from patch-only provenance:
C2/C3 retain useful patch/design evidence and prior-run claims, but their raw bench/test transcripts are not
preserved in this tree. Measurement-only and already-implemented audit rows are labeled as such.
"Reviewed" = I read the diff for correctness; "re-verified" = I rebuilt+remeasured independently.

## Fleet 1 — binding / interop

### C3-arrow — Arrow C Data Interface export on PageSpan  🟦 medium feature
- **Prior lab run reported:** `test_timelog` 480/480, pytest 98+16skip (== baseline). Current saved artifact set has
  no raw command transcript or sanitizer log; productionization must rerun and save ASan/UBSan evidence.
- **Prior lab run reported:** `pa.array(span)` accepted by **pyarrow 24.0** and **polars 1.41** directly; **pointer identity confirmed**
  (`span ts ptr == arrow buffers()[1].address`) → truly zero-copy. `close()` raises `BufferError` while an Arrow array is
  live; the array outlives the Python span (owner pin holds page memory). Timing: `pa.array` 1.12 µs/span vs
  `np.frombuffer` 0.51 µs (2.2× — pyarrow wrapper overhead, *not* a copy; both O(1) in rows).
- +387 LOC (hand-rolled ArrowSchema/ArrowArray; no nanoarrow dep). **Reviewed: partial** (owner pin + capsule
  teardown are sound for the Python PyCapsule consumers tested; production review must pin down the release-callback
  thread-state contract, because `ArrowArray.release` currently uses Python C-API/`Py_DECREF` and therefore must run on
  the owning interpreter with an attached thread state).
- Verdict: 🟦 measured ecosystem win, but **not a tiny low-risk patch** — productionize as feature work with a shared
  PageSpan export-pin helper and an explicit Python-consumer release contract.

### C3-dlpack — DLPack export on PageSpan  🟦 medium feature
- **Prior lab run reported:** `test_timelog` 480/480, pytest **104**+16skip (98 + 6 new DLPack tests). Current saved
  artifact set has no raw command transcript or sanitizer log; productionization must rerun and save ASan/UBSan evidence.
- **Prior lab run reported:** `np.from_dlpack(span)` zero-copy (**pointer identity == buffer-protocol ptr**), **read-only** (`arr[0]=…`
  raises), survives `close()` (owner pin). `__dlpack_device__()==(kDLCPU,0)`; `copy=True`/non-CPU/`max_version<1.0`/closed
  all raise correctly. +499 LOC (262 prod + 120 tests + 142 vendored `dlpack.h`).
- Review caveat: the deleter ultimately drops a `tl_pagespan_owner_t`; owner release hooks can run Python binding cleanup
  (`pins_exit`, handle-context decrefs). As with Arrow, production must guarantee deleter execution on the owning
  interpreter with an attached thread state or route cleanup through a Python-owned finalizer.
- Verdict: 🟦 measured interop win — reaches torch/jax/cupy (which can't speak PEP 3118) — but productionize as a
  medium feature, not as a trivial one-file optimization.

### C2-bulk — typed-buffer `bulk_append(int64_buffer, objects)`  🟩 strict fast path
- **Prior lab run reported:** `test_timelog` 480/480, pytest 98+16skip; integrity + rejection (length-mismatch/empty/float/int32/non-contiguous) + refcount checks pass. Current saved artifact set has no raw command transcript.
- **Prior lab run reported (N=500k, in-order, best-of-5):** per-append **115.7** ns/rec · extend **30.2** · **bulk_append 12.4** →
  **2.44–2.49× vs extend, 9.4–10× vs per-append.** +227 LOC.
- **Reviewed with one blocking production nit:** the native-endian path is sound (length-match, per-element
  `validate_ts`+INCREF+encode with rollback-on-failure, **TL_EBUSY = committed (no rollback)**, true-failure rolls back all
  INCREFs, handle_ctx owned under lock). But the patch accepts byte-order-prefixed buffer formats (`<q`, `>q`, etc.) and
  then direct-casts `ts_view.buf` to `int64_t*`; a non-native-endian NumPy array would be accepted and misread. Production
  must either reject non-native endian formats or byteswap into scratch. Also swap raw `malloc` → `PyMem_Malloc`.
- API scope: this is **not** an `extend()` replacement. It requires a contiguous typed timestamp buffer and concrete object
  sequence, so it intentionally does not cover generators, `insert_on_error`, or every facade coercion path. Preserve
  facade `extend()` and document `bulk_append` as the strict zero-unpack ingest path.
- Verdict: 🟩 — closes the batch-overhead headroom and remains the fastest ingest path, **after** the endian validation fix.

### C6-exports — atomic FT exports counter  🟥/✅ already-hardened (honest negative)
- **No production change needed:** the `exports` counter + close-while-exported check are **already** consistently under the
  per-object critical section (`Py_BEGIN_CRITICAL_SECTION`, gil-free commits 2c1d252/0bbe8b7); check-then-act sequences are
  each one CS. Verified on **real 3.14t**: a +1 FT test + a standalone reproducer (287,573 reads, 175,461 correct
  `BufferError`-on-close, **0 spurious, 0 crashes**, stable ×3). `test_timelog` 480/480.
- **Honest limitation:** a later review found and fixed the TSan build wiring, so native/core TSan is now confirmed on the
  production branch. The remaining local gap is narrower: workflow-equivalent free-threaded Python under GCC libtsan aborts
  at process startup before user code. FT safety for this specific export-counter surface still rests on the static
  all-accesses-under-CS guarantee + the dynamic reproducer until that Python+TSan leg runs on a compatible host.
- Verdict: ✅ already correct — a valuable "this is sound, don't touch it" result, not a change.

---
*Fleet 2 (compaction whole-window-drop, granular, memory/allocator, tombstone-canon) appended below as it lands.*

## Fleet 2 — compaction / memory (partial; WWD still finishing)

### C6-cs — critical-section blocking audit  ✅ sound (no change)
Audited the highest-risk region myself: `pytimelogiter_step` (py_iter.c:261) holds the per-object critical section while
calling `tl_iter_next` (py_iter.c:265). Verified `tl_iter_next` (tl_timelog.c:1410) takes **no lock** — it's a lock-free
snapshot read (`tl_filter_iter_next` over the pinned snapshot). So the CS is never suspended by a blocking call; it
correctly serializes concurrent `__next__` on the same iterator (protecting `self->iter`). No block-while-held footgun.
Combined with C6-exports, the specific audited FT surfaces are sound; this is not a whole-codebase race proof.

> **Emerging audit theme:** a large share of the notes' "improvements" are **already implemented** in Timelog
> (CS-protected exports, lock-free iterator under CS, multiphase init, FT-without-HPy). The
> genuinely *new* wins are the **binding/interop** surfaces (Arrow, DLPack, bulk_append, FASTCALL, facade-fold) and,
> pending, **whole-window-drop**. The notes materially overestimated what was missing.

### C4-wwd — whole-window drop  🟦 cool-but-costly / workload-specific (see experiments/C4-wwd/RESULT.md)
Built (+135 LOC), **480/480 + handle-leak gate pass (I re-verified the build myself)**. Pure-C TTL best case
**67–275×** compaction-CPU; but a **wash** in the CPython binding (mandatory on_drop flat-scan) and the default
streaming path. **My review found a false-negative** in the coverage test (`tl__l1_window_fully_deleted` bails at the
first `start≤window_start` interval → misses multi-`delete_range` windows; small fix noted) — the agent's
single-tombstone gates missed it. Correct & leak-free, but not the unconditional win the notes implied.

### C4-gran — granular compaction  🟥 not-for-us (honest negative)
The existing `max_compaction_windows` cap does **not** bound wide-OOO transient RAM: one wide-OOO L0 segment spans all
windows → forces repeated L1 fan-in. Fresh C-level spot sweep in `experiments/C4-gran/RESULT.md`: the cap preserved
correct query fingerprints and slightly reduced the largest transient, but changed one merge into 30 maintenance steps,
`select_l1_inputs` 80→4160, and roughly 10x drain CPU. Works as a compaction-shaping knob; actually bounding wide-OOO
RSS needs new sub-window-slice code or a different policy, not a config flip.

### C7-mem — memory / allocator  🟦 cool-but-costly
**~87% of RSS is native C-core** (not Python). **mimalloc** (LD_PRELOAD): agent measured peak RSS **−12.7%/−11.2%**
(3M/5M) + after-close fragmentation **−36.7%**; my independent steady-state check saw only **−2%** (mimalloc helps
peak/fragmentation, not steady-state). MALLOC_ARENA_MAX=2 ≈ 0% (single-threaded). jemalloc unavailable (no root).
Worth recommending mimalloc for memory-sensitive deployments; adopting it = a packaging change → cool-but-costly.

### C5-canon — tombstone / delete reclaim  🟦 real gap (recovered after agent's structured-output failure)
Measured (delete_lab.py): in the lab's retention-shaped workload, deleting **50%** of data reclaims **0 space** — pages
77→77, **space_amp stays 2.103×**, 20 tombstones accumulate, **no compaction fires**, reclaim_lag = ∞ (>200 cap) for every
`delete_debt_threshold` ∈ {0,0.1,0.25,0.5}. Confirmed `delete_debt_threshold` IS wired (not ignored). Independent review
also found a spot case where lowering `delete_debt_threshold` and using a different window/debt shape does reclaim pages
(12→6), so the honest gap is **default-disabled / workload-sensitive delete-driven L1 reclaim**, not "no reclaim path
exists." Root: pure-retention deletes can leave deleted L1 data resident until enough eligible debt/new work drives a
merge. This remains a genuine improvement area, but it needs policy + regression coverage rather than a config flip.
