# Ponytail Audit — Unit "delta" (write path)

Auditor: lazy-senior ("ponytail") pass. Read every line of the 10 assigned files (4,089 LOC).
Safety net: `core/tests/test_delta_internal.c` (3,387 lines, ~115 test functions) plus flush/seal
coverage in the core suite and Python facade drop-callback tests.

Files reviewed in full:

| File | LOC |
|---|---|
| core/src/delta/tl_memtable.c | 1217 |
| core/src/delta/tl_memtable.h | 467 |
| core/src/delta/tl_memview.c | 648 |
| core/src/delta/tl_memview.h | 325 |
| core/src/delta/tl_memrun.c | 347 |
| core/src/delta/tl_memrun.h | 281 |
| core/src/delta/tl_flush.c | 332 |
| core/src/delta/tl_flush.h | 150 |
| core/src/delta/tl_ooorun.c | 206 |
| core/src/delta/tl_ooorun.h | 116 |

## Executive summary

The delta unit is disciplined code: failure-atomicity on the seal path, documented invariants
(H-07 ring index, H-09 two-phase capture) are respected everywhere, and hot paths (single/batch
insert) are lean. The fat is in three places:

1. **Production-dead machinery** (~250 LOC): a two-way merge iterator that flush no longer uses
   (it k-way merges via `tl_heap`), two constructors (`tl_memrun_create`, `tl_ooorunset_create`)
   used only by tests, a test-only `tl_memtable_seal` shim, and six dead inline accessors.
2. **Three hand-rolled copies of "growable record array"** (~105 LOC) when `tl_recvec_t` already
   exists in this codebase with geometric growth, overflow guards, and `take()` ownership
   transfer.
3. **A copy-and-sort drop pre-count** that sorts the OOO head **twice** on every seal (and twice
   per opportunistic head-flush when tombstones are active) — deletable with an upper-bound
   reservation plus a conservative gate, which is *faster*, not just smaller.

Total realistic savings: **~500 LOC (~12% of the unit)** with zero hot-path perf cost; findings
S1 and S4 are perf-positive. No external library adoption is recommended: every prior-art
sub-problem here is either already solved in-repo, or the in-house version earns its keep via a
documented invariant, the allocator seam, or MSVC/TSan constraints (details in the leads
section).

---

## Findings (ranked by value)

### S1. Delete the production-dead two-way merge iterator — rung 1 (does-not-need-to-exist)

**Where:** `core/src/delta/tl_flush.h:39-116` (struct + API + docs),
`core/src/delta/tl_flush.c:5-66` (impl), `core/src/internal/tl_defs.h:109`
(`typedef struct tl_merge_iter tl_merge_iter_t;`).

**Evidence:** `tl_flush_build` performs a k-way merge through `tl_heap`
(`tl_flush.c:199-291`, "Stable k-way merge across the in-order run and every OOO run"); it never
touches `tl_merge_iter_*`. Grep over `core/` + `bindings/` shows the only callers are tests
(`core/tests/test_delta_internal.c:1902-1993`). This is a leftover from before the Option-B OOO
mini-LSM made flush k-way. Even the query-side header still advertises it:
`core/src/query/tl_merge_iter.h:16-17` — "Distinct from the simple two-way merge used by flush;
that lives in tl_flush.h" — which is now false (flush does not use it).

**Action:** delete struct, five functions (`init/peek/next/done/remaining` —
`tl_merge_iter_remaining` is self-described as "test/diagnostic helper", `tl_flush.h:112-116`),
the `tl_defs.h` typedef, the four tests that test dead code, and fix the stale comment in
`query/tl_merge_iter.h`.

**LOC saved:** ~140 in src, ~100 more in tests. **Risk:** low (nothing in production references
it; compile proves it). **Perf:** none (dead code). Tests: the deleted tests only covered the
deleted code.

### S2. Retire test-only constructors `tl_memrun_create` and `tl_ooorunset_create` — rung 1/2

**Where:** `core/src/delta/tl_memrun.c:94-133` + `tl_memrun.h:90-119`;
`core/src/delta/tl_ooorun.c:76-127` + `tl_ooorun.h:63-66`.

**Evidence:** Production code only ever uses the two-phase `tl_memrun_alloc` + `tl_memrun_init`
(`tl_memtable.c:891, 1006`) and `tl_ooorunset_append` (`tl_memtable.c:547`). Grep over
`core/src` + `bindings`: zero production callers of either `_create`. All callers live in
`test_delta_internal.c`, which *already wraps* `tl_memrun_create` in its own helper
(`test_delta_internal.c:119-127`: `#define tl_memrun_create test_memrun_create`).
`tl_ooorunset_create` additionally duplicates `tl_ooorunset_append`'s pin-and-sum loop almost
line-for-line (compare `tl_ooorun.c:104-123` with `tl_ooorun.c:157-178`).

**Action:** move `tl_memrun_create`'s 10-line body into the existing test wrapper; rewrite the
test helper for runsets as chained `tl_ooorunset_append` calls (test counts are 1–3 runs). This
also resolves the create/append duplication by deletion — the last copy standing is the one
production uses.

**LOC saved:** ~70 net in production source (some lines move to the test file). **Risk:** low.
**Perf:** none (cold, test-only).

### S3. Replace three hand-rolled "growable dropped-record array" implementations with `tl_recvec_t` — rung 2 (already-in-this-codebase)

**Where:** `core/src/delta/tl_memtable.c:229-275` (`memtable_collect_drop`, 47 LOC),
`tl_memtable.c:277-313` (`memtable_reserve_drops`, 37 LOC),
`core/src/delta/tl_flush.c:249-269` (inline doubling block inside the merge loop, 21 LOC), plus
the `tl_record_t** / size_t* len / size_t* cap` triple-pointer plumbing threaded through
`memtable_flush_ooo_head` and `tl_memtable_seal_ex` signatures.

**Evidence:** All three re-implement start-at-64-then-double growth with overflow guards —
exactly what `tl_recvec_t` provides: geometric `tl_recvec_reserve` via `tl__grow_capacity`
(`internal/tl_recvec.c:52-73`), infallible-after-reserve `tl_recvec_push`, and
`tl_recvec_take` (`tl_recvec.h:182`) which detaches a buffer the caller frees with `tl__free` —
the exact ownership contract `out_dropped` already documents (`tl_memtable.h:265`,
"caller owns *out_dropped and must free with tl__free"). `tl_memtable_seal_ex` itself already
uses `tl_recvec_take` for the active run (`tl_memtable.c:957`), so the pattern is native here.

**Action:** hold drops in a local `tl_recvec_t` (+ the paired seq handling is not needed —
drops carry no seqs); `collect` becomes `tl_recvec_push`, `reserve` becomes
`tl_recvec_reserve`, output becomes `tl_recvec_take`. The triple-pointer parameters collapse to
one `tl_recvec_t*`. As a side effect the three near-identical 8-line manual cleanup blocks in
`tl_memtable_seal_ex` (`tl_memtable.c:964-971, 985-992, 1014-1019`) shrink, and could further
collapse to the project's own documented `goto cleanup` pattern (CLAUDE.md "Cleanup Pattern"),
which this function ironically does not use.

**Behavioral deltas to note:** growth floor 16 (RECVEC_MIN_CAPACITY) instead of 64; SIZE_MAX
saturation returns `TL_ENOMEM` from recvec instead of `TL_EOVERFLOW` (`tl_memtable.c:239-240`) —
callers treat both as fatal, and `handle_seal_with_backpressure` remaps any non-EBUSY failure to
EBUSY anyway (`tl_timelog.c:573-579`).

**LOC saved:** ~90. **Risk:** low–medium (seal failure-atomicity must be preserved: reserve
before `tl_recvec_take` keeps post-detach pushes infallible, same as today). **Perf:** drop
collection only runs when tombstones physically delete records at seal/flush — off the append
and query hot paths. Existing coverage: seal/flush drop tests in `test_delta_internal.c` and
Python `on_drop` facade tests.

### S4. Kill the copy-and-sort drop pre-count (`memtable_count_tomb_drops`) — rung 7 (minimal-rewrite), perf-positive

**Where:** `core/src/delta/tl_memtable.c:344-396` (the unsorted wrapper: malloc two copies,
sort, count, free), call sites `tl_memtable.c:417-437` (opportunistic-flush gate) and
`tl_memtable.c:897-937` (seal pre-count/pre-reserve).

**Evidence of the double work:** on every `tl_memtable_seal_ex` with an unsorted OOO head and
active tombstones, the head is copied+sorted once to *count* drops (`:899-906` →
`:361-396`), then `memtable_flush_ooo_head(required=true)` copies+sorts the **same data again**
(`:446-474`) to actually collect them. On the opportunistic path (`tl_memtable_insert` →
`memtable_flush_ooo_head(required=false)`), the gate at `:417-437` also copies+sorts the head to
count, and if zero drops, the function immediately copies+sorts again — two O(H log H) sorts and
four mallocs per chunk flush whenever tombstones exist.

**Why the count exists:** the exact count pre-reserves `dropped` so that the record filtering
that runs *after* `tl_recvec_take` detaches the active arrays (`:974-999`) cannot fail — a real
failure-atomicity requirement (an ENOMEM there loses data, see the apologetic comment at
`:1012-1015`).

**Replacement that preserves the contract:**
- *Seal path:* reserve `active_drop_count + head_len` instead of
  `active_drop_count + exact_ooo_drop_count`. `head_len` is a trivially correct upper bound for
  OOO drops; `active_drop_count` still comes from `memtable_count_sorted_tomb_drops`
  (`:315-342`, kept — it is O(n) with a cursor and allocates nothing because the active run is
  already sorted). Reservation still happens before any mutation, so every failure path remains
  retryable. Cost: transient over-allocation of the drop buffer, bounded by the head chunk size,
  only when tombstones exist.
- *Opportunistic gate:* replace the exact count with a conservative O(H) no-alloc check
  (does any tombstone with `max_seq >` the head's minimum seq overlap the head's [min_ts,max_ts]
  range?). Conservative skips just leave records in the head until seal, which already handles
  drops exactly; the head stays bounded by the OOO budget → forced seal
  (`tl_memtable_should_seal`, `:816-836`). Note this changes *when* opportunistic flushes
  happen under tombstone overlap — tests that assert run counts after opportunistic flush may
  need adjustment.

With both call sites converted, `memtable_count_tomb_drops` (53 LOC) is deleted outright.

**LOC saved:** ~60. **Risk:** medium — the seal failure-atomicity contract
(`tl_memtable.h:213-214`: "On TL_ENOMEM or TL_EBUSY, active state is PRESERVED") is subtle and
must be re-verified; ordering of reserve-before-mutate is load-bearing. **Perf:** strictly
positive — removes one full copy+sort per seal and per gated chunk flush. Needs a couple of new
tests for the conservative-gate behavior; drop-accounting tests already exist.

### S5. Extract the bounds-merge tail shared by five `update_bounds_from_*` functions — rung 7

**Where:** `core/src/delta/tl_memview.c:21-139` (115 LOC across
`..._records`, `..._records_unsorted`, `..._runs`, `..._tombs`, `..._memrun`).

**Evidence:** each function ends with the identical 10-line block:
```c
if (!*has_data) { *min_ts = rec_min; *max_ts = rec_max; *has_data = true; }
else { if (rec_min < *min_ts) *min_ts = rec_min; if (rec_max > *max_ts) *max_ts = rec_max; }
```
(five verbatim copies at `:31-38`, `:55-62`, `:80-87`, `:108-115`, `:131-138`). A 10-line
`bounds_include(tl_ts_t* mn, tl_ts_t* mx, bool* has, tl_ts_t lo, tl_ts_t hi)` helper reduces
each function to its source-specific min/max computation plus one call.

**LOC saved:** ~45. **Risk:** low; capture-time only (off query hot path), behavior byte-identical,
covered by `tl_memview_validate` and capture tests.

### S6. Collapse `copy_intervals` + `copy_seqs` into one dup helper — rung 7 (pattern already exists as `tl_records_copy`)

**Where:** `core/src/delta/tl_memview.c:141-195` (two 27-line functions).

**Evidence:** both are byte-for-byte the same "len==0 → NULL / src NULL → EINVAL / overflow
check / malloc / memcpy" pattern, and a third sibling already lives at
`core/src/internal/tl_records.h:17-43` (`tl_records_copy`). One
`static tl_status_t dup_array(tl_alloc_ctx_t*, const void* src, size_t len, size_t esz, void** out)`
covers both call-site families (`:334, :347-348, :359`).

**LOC saved:** ~33. **Risk:** low. **Perf:** capture path, memcpy-bound either way.

### S7. Delete six dead inline accessors — rung 1

**Where / evidence** (zero uses anywhere in `core/` + `bindings/`, tests included):
- `tl_ooorun_gen` — `tl_ooorun.h:96-98` (validators read `run->gen` directly).
- `tl_memview_shared_epoch` — `tl_memview.h:207-209`.
- `tl_memview_min_ts` / `tl_memview_max_ts` — `tl_memview.h:218-234` (overlap checks go
  through `tl_memview_overlaps`, which reads the fields directly).
- `tl_memrun_is_empty` — `tl_memrun.h:214-216`.
- `tl_memrun_tombs_data` — `tl_memrun.h:243-245` (read path uses `tl_memrun_tombs_imm`).

**LOC saved:** ~40 including doc comments. **Risk:** none (compiler proves it).

### S8. Fold `tl_memtable_seal` into `tl_memtable_seal_ex` — rung 6 (one-liner)

**Where:** `core/src/delta/tl_memtable.c:1059-1062`, header docs `tl_memtable.h:243-259`.

**Evidence:** production exclusively calls `seal_ex` (`tl_timelog.c:551, 607, 1138`); the plain
wrapper's only callers are tests (`test_delta_internal.c:111, 154, 1218, ...`). Rename `seal_ex`
to `seal` (internal API, not in `timelog.h`) or have tests pass `NULL, NULL`.

**LOC saved:** ~25 (mostly duplicated header docs). **Risk:** low; churns ~10 test call sites.
Low priority — do it opportunistically.

### S9. Simplify the two-phase retry loop's duplicated fallback body in `copy_sealed_memruns` — rung 7 (protocol-preserving)

**Where:** `core/src/delta/tl_memview.c:205-305`.

**Evidence:** the fallback (`:271-304`) duplicates the loop body's lock/len-check/alloc/pin
sequence (~35 LOC). Restructuring to `for (attempt = 0; attempt <= max_retries; attempt++)` with
`bool alloc_under_lock = (attempt == max_retries)` keeps the H-09 protocol *exactly* (N
epoch-validated off-lock attempts, then locked allocation) with one body.

**LOC saved:** ~25. **Risk:** medium — concurrency-adjacent code; but the H-09 protocol,
lock ordering, and the `TL_TEST_HOOKS` branches (`:249-256, :271-273`) are all preserved, and
the hooks give direct test coverage of retry and fallback.

### S10. Trivia bucket (fold into any nearby PR)

- **Redundant memset:** `tl_memview.c:473` memsets a struct freshly returned by `TL_NEW`, which
  is `tl__calloc` (`internal/tl_alloc.h:173-174`) — already zeroed. 1 line.
- **Reuse the saturating helper:** `tl_memview.c:355-356` computes
  `ooo_head_len + tl_ooorunset_total_len(...)` by hand; `tl_memtable_ooo_total_len`
  (`tl_memtable.h:432-439`) is the same computation *with* the SIZE_MAX saturation guard. 1 line,
  and it upgrades an unguarded add.
- **Dead defensive branches:** `tl_memtable_sealed_index` (`tl_memtable.h:335-341`) carries
  `if (cap == 0) return 0;` directly after `TL_ASSERT(mt->sealed_max_runs > 0)` (init rejects 0,
  `tl_memtable.c:17`), and `if (offset >= cap) offset %= cap;` though every caller passes
  `offset < sealed_len <= cap`. The H-07 subtraction formula itself must stay. ~5 lines; keep if
  the team prefers belt-and-braces, but they are provably unreachable.
- **`dec` bookkeeping verbosity:** `tl_memtable.c:506-527` — 22 lines of saturating arithmetic
  that two calls to the existing `memtable_sub_bytes`-style helpers would express in ~8.
- **Impossible-state EINTERNAL paths in flush:** `tl_flush.c:143-146` and `:193-197`
  (`src_count == 0` / `src_idx == 0`) cannot fire given `total_records > 0` at `:102-104`.
  Cheap and cold; acceptable to keep, but they are error paths for impossible states.

### API-anchored observation (flag loudly: api-change if acted on)

**`TL_APPEND_HINT_MOSTLY_IN_ORDER` is a fully-plumbed no-op.** The flag travels from the Python
binding (`py_timelog.c:1955, 2036, 2507`) through `timelog.h:386-387` into
`tl_memtable_insert_batch`, which discards it: `(void)flags;` (`tl_memtable.c:655`). The fast
path is chosen purely by the mandatory full sortedness verification
(`batch_is_sorted`, `:637-647`), as the header contract requires ("This is NOT a guarantee.
Implementation MUST verify ... NO SAMPLING", `tl_memtable.h:154-160`). The hint neither enables
nor disables anything. Removing it is a public-API change (do not do it casually); the honest
minimum is documenting it as advisory-and-currently-ignored so future readers don't hunt for its
effect. LOC saved if ever removed at a major version: ~15 across binding + header.

---

## Prior-art leads (honest fit notes; later phases verify)

1. **Growable typed array** (drop buffers, S3). Candidates: in-repo `tl_recvec_t` (rung 2 —
   preferred), `klib/kvec.h` (MIT), `stb_ds.h` (MIT/public-domain). Fit: in-repo wins outright;
   external options would need allocator-seam glue (`tl__realloc`) and add a vendored file for
   something already solved two directories away.
2. **Refcounted immutable objects** (memrun/ooorun/ooorunset/memview_shared). Candidates:
   Concurrency Kit `ck_pr`-based refcounts (BSD-2), liburcu `urcu/ref.h` (**LGPL — fails the
   license gate**). Fit: the in-house `TL_REFCOUNT_ACQUIRE/RELEASE` macros already centralize
   the idiom *and* encode the GCC-TSan-specific acq_rel-on-decrement workaround
   (`tl_memrun.h:141-153`); adopting a library re-imports the exact false-positive problem the
   project already engineered around. Recommend: no adoption.
3. **K-way merge via binary min-heap** (`tl_flush_build`, `tl_flush.c:199-291`). Candidates:
   `klib/ksort.h` heap macros (MIT), CCAN `heap` (BSD-MIT). Fit: heap entries carry
   `(ts, tie_break_key, watermark, handle, iter)` with tie-breaks required for deterministic
   equal-timestamp ordering; generic comparator-pointer heaps add indirect calls inside the
   per-record merge loop (flush is O(S log K) and semi-hot), and `tl_heap` is already shared with
   the query read path. Recommend: no adoption.
4. **Fixed-capacity ring buffer** (sealed queue, `tl_memtable.c:1093-1121`). Candidates: CCAN
   `ringbuf`, `ck_ring` (BSD-2). Fit: this is a mutex-protected FIFO of a handful of pointers
   whose index arithmetic is a **documented invariant (H-07)**; `ck_ring` is lock-free MPMC —
   a different concurrency contract with a new TSan surface. Recommend: no adoption.
5. **Epoch-validated optimistic capture** (H-09, `tl_memview.c:205-305`). Candidate:
   `ck_sequence` (seqlock, BSD-2). Fit: the protocol here is mutex + epoch counter with a locked
   fallback, per documented invariant H-09; a seqlock would restructure who publishes what and
   saves no lines. Recommend: no adoption (see also S9 for the in-place cleanup).
6. **Co-sorting a record array with a parallel seq array** (`tl_recvec_sort_with_seqs`, consumed
   at `tl_memtable.c:387, 468` and `tl_memview.c:415`). Candidates: `qsort_r`/`qsort_s`
   (platform — but GNU, BSD, and MSVC disagree on signature and argument order; a portability
   minefield under `-Werror`/`/WX`), `klib/ksort.h` (MIT, macro-generated, would sort a zipped
   struct instead). Fit: the in-house co-sort avoids zipping records (which would double copies
   on the seal path) and sidesteps the qsort_r portability mess. Recommend: keep in-house; a
   later phase could still benchmark ksort's macro sort if the seal sort ever shows up in
   profiles.

---

## NO-and-NO (machinery that earns its keep)

- **H-07 subtraction-based ring index** (`tl_memtable.h:328-348`): documented critical invariant;
  the formula is the point. Only the unreachable defensive branches are fat (S10).
- **H-09 two-phase memview capture** (`tl_memview.c:205-305`): the lazy move — always allocate
  under `memtable_mu` (~40 LOC simpler) — would violate documented invariant #8, whose purpose is
  bounding lock hold time against snapshot-heavy readers. Non-finding by rule; S9 removes the
  duplication *within* the protocol instead.
- **Full O(n) `batch_is_sorted` verification** (`tl_memtable.c:637-647`): the header contract
  explicitly forbids sampling (`tl_memtable.h:158-160`); a wrong fast-path would violate the
  sortedness invariant (#3). The scan is branch-predictable and feeds the 4.3x bulk path.
- **Parallel `recvec` + `seqvec` (SoA) instead of a combined (record, seq) struct**: seqs are
  dropped at memrun creation (`tl_memtable.c:1001-1004`) and flush merges raw `tl_record_t`
  arrays straight into segments; an AoS layout would bloat every downstream memcpy/merge on the
  hot path by 50%.
- **Reserve-then-push pairing in `tl_memtable_insert`** (`tl_memtable.c:582-593`): looks
  redundant (push grows itself) but guarantees the record and seq arrays cannot diverge if the
  second push's allocation fails — the atomicity that keeps `tl_memtable_validate`'s
  len-equality invariant.
- **Double queue-full check in seal** (`tl_memtable.c:881-886` and `:1025-1031`): the pre-check
  avoids building a memrun that will be thrown away; the publish-time re-check is mandatory
  because flushers pop concurrently under `memtable_mu`. Both documented in the function comment.
- **`tl_memrun_alloc`/`tl_memrun_init` two-phase** (`tl_memrun.c:135-148`): the shell is
  allocated *before* the active arrays are detached (`tl_memtable.c:889-894` comment) so ENOMEM
  stays on the retryable side of the point of no return.
- **Per-run refcount on `tl_ooorun_t`**: not redundant with the runset refcount — after
  `tl_ooorunset_append`, the old and new sets share the same run objects (`tl_ooorun.c:157-170`),
  and old sets stay pinned by live memviews/memruns.
- **Opportunistic-flush "no drop sink" gate** (`tl_memtable.c:417-437` comment): the *decision*
  (never silently drop records without a callback sink, don't collapse per-record seqs into a
  uniform watermark) is correct and must survive S4; only its *implementation* (copy+sort to
  count exactly) is fat.
- **`tl_memview_validate` / `tl_memrun_validate` / `tl_memtable_validate`** (debug-only, ~330
  LOC combined): pure invariant checkers behind `TL_DEBUG`, exercised by the ASan CI builds;
  this is the safety net the audit itself leans on. Zero release-mode cost.
- **TL_TEST_HOOKS variables** (`tl_memview.c:12-15`): only way to deterministically reach the
  H-09 retry/fallback branches; cost is two `volatile int`s behind an ifdef.

## Per-file walkthrough notes

- **tl_memtable.c/h** — ingest paths are tight; all findings are in the drop-count/collect
  support machinery (S3, S4) and the test-only seal shim (S8). Comment nit: `epoch` is
  documented "protected by writer_mu only" (`tl_memtable.h:80`) but `tl_memtable_pop_oldest`
  increments it from the flush path (`tl_memtable.c:1116`) — worth one clarifying comment line,
  not code change (out of scope for this audit's simplification mandate).
- **tl_memview.c/h** — capture is a clean deep-copy; fat is in the five-way bounds duplication
  (S5), the copy-helper twins (S6), the fallback duplication (S9), and dead accessors (S7).
- **tl_memrun.c/h** — minimal and correct; only `tl_memrun_create` (S2) and two dead accessors
  (S7) are removable. Validators earn their keep.
- **tl_flush.c/h** — the k-way merge build is the right shape; the entire two-way iterator
  section is dead (S1) and the drop-array growth block joins S3.
- **tl_ooorun.c/h** — smallest file, one test-only constructor (S2), one dead accessor (S7);
  refcount layering is justified (see NO-and-NO).
