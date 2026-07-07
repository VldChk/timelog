# Ponytail Audit — Unit: internal-platform

Platform/concurrency shims: mutex/condvar wrapper, atomics shim, allocator wrappers,
seqlock, refcount idiom, math/overflow helpers, logging, misc defs.

**Files reviewed (2,825 LOC, every line read):**

| File | LOC |
|---|---|
| core/src/internal/tl_sync.c | 621 |
| core/src/internal/tl_atomic.h | 389 |
| core/src/internal/tl_alloc.c | 254 |
| core/src/internal/tl_timelog_internal.h | 215 |
| core/src/internal/tl_alloc.h | 200 |
| core/src/internal/tl_defs.h | 186 |
| core/src/internal/tl_sync.h | 185 |
| core/src/internal/tl_platform.h | 172 |
| core/src/internal/tl_locks.h | 151 |
| core/src/internal/tl_seqlock.h | 114 |
| core/src/internal/tl_math.h | 99 |
| core/src/internal/tl_log.c | 85 |
| core/src/internal/tl_log.h | 81 |
| core/src/internal/tl_refcount.h | 41 |
| core/src/internal/tl_test_hooks.c | 32 |

---

## Executive Summary

This unit is **well-engineered but carries a thick layer of speculative shim surface
that nothing calls**. The load-bearing machinery — mutex/cond wrapper with monotonic
condvar clocks, the debug lock-order tracker, the refcount idiom, the allocator seam —
earns its keep and I say so explicitly in the NO-and-NO section. But grep-verified
dead code is everywhere around it:

- The **entire `tl_atomic_ptr` family, all atomic stores, the fence, and half the
  convenience macros** have zero production callers (the stated use case — "manifest/
  memtable pointers", tl_atomic.h:39 — never materialized; the manifest pointer is
  mutex+seqlock-protected, not an atomic ptr).
- The **seqlock has no production reader**. `tl_seqlock_read`/`validate`/`is_even`/
  `current` are test-only; production performs write windows that no reader ever
  validates. The header itself admits it is "a hook for future lock-free
  optimisations" (tl_seqlock.h:21-22) — textbook speculative machinery, though
  deleting it collides with documented invariant #6, so I split the recommendation.
- `tl_thread_set_name` (including a 50-line Windows GetProcAddress/InitOnce dance),
  `tl_mutex_is_held`, `tl_thread_self_id`, `tl_cond_broadcast`, `tl__reallocarray`,
  `tl__alloc_get_{total,count,peak}`, peak-allocation tracking, `TL_TRYLOCK`,
  `tl_lock_is_held`, `tl_lock_highest_held`, `TL_ALIGN_UP`, `TL_IS_ALIGNED`,
  `TL_ARRAY_SIZE`, `TL_PREFETCH_*`, `TL_LIKELY/UNLIKELY`, `TL_RESTRICT`,
  `TL_NOINLINE`, `TL_CACHE_ALIGNED`, `TL_UNREACHABLE`, `TL_LOG_STATIC_*` — all dead.
- The **GCC/Clang `__atomic` fallback backend** of tl_atomic.h is unreachable on any
  supported toolchain (self-described as "unlikely with C17 but defensive",
  tl_atomic.h:277-284).
- One genuine cross-cutting lead: the **Windows wheels already build the binding with
  `/experimental:c11atomics`** (bindings/cpython/CMakeLists.txt:210 and 8 more sites),
  so the core's 140-line MSVC Interlocked backend is protecting a configuration the
  shipped product doesn't use — and it makes every relaxed load a full `lock cmpxchg`
  on MSVC.

Aggregate honest estimate: **~600–680 LOC deletable at low-to-medium risk** (plus
~150 more if the maintainer decides to drop the write-only seqlock entirely).

On the classic question (extra instruction): **C11 `<threads.h>` cannot replace
tl_sync** — Apple's SDK does not ship `<threads.h>` at all, glibc needs 2.28+ (vs
the manylinux floor), MSVC needs 17.8+, and `cnd_timedwait` is specified against
`TIME_UTC` wall time, which would regress the deliberately monotonic condvar waits
(tl_sync.c:296-309). Full grounding below.

---

## Per-File Walkthrough & Findings

### 1. tl_atomic.h (389 LOC) — atomics shim, 3 backends

Three backends: C11 `<stdatomic.h>` (lines 42-135), MSVC Interlocked (137-275),
GCC/Clang `__atomic` builtins fallback (277-363), plus convenience macros (365-388).

**What production actually uses** (grep of core/src + internal consumers):
`tl_atomic_u32/u64` types, `init_u32/u64`, `load_u32/u64` (relaxed/acquire),
`fetch_add_u32/u64`, `fetch_sub_u32`, `cas_u32/u64`, and the macros
`load_relaxed_u32/u64`, `load_acquire_u64` (via seqlock), `inc_u64`. That's it.

**F-1 (rung 1, dead): the pointer family.** `tl_atomic_ptr` + `init_ptr`, `load_ptr`,
`store_ptr`, `cas_ptr`, `exchange_ptr` — five ops × three backends. Zero callers in
core/src or bindings (bindings use CPython/C11 atomics directly and include no
internal headers). Only user: `core/tests/test_internal_sync.c:113`
(`sync_atomic_ptr_exchange`), a test of the shim itself. The design comment
tl_atomic.h:39 ("tl_atomic_ptr: manifest/memtable pointers") describes a plan that
was never executed — `tl_timelog.manifest` is a plain pointer guarded by `writer_mu`
+ seqlock window (tl_timelog_internal.h:180, tl_timelog.c:883-884). **Delete
(~45 LOC + test).**

**F-2 (rung 1, dead): all atomic stores.** `tl_atomic_store_u32/u64/ptr` — zero
production callers (`src=0` for direct calls and for every `store_relaxed_*` /
`store_release_*` macro). The core writes atomics only via `init`, `fetch_add/sub`,
and `cas`. Three ops × three backends ≈ 35 LOC. **Delete** (the convenience store
macros at tl_atomic.h:372-381 go with them).

**F-3 (rung 1, dead): `tl_atomic_fence`.** Three implementations
(tl_atomic.h:133,271,359), zero callers anywhere including tests. This is a fossil:
tl_refcount.h:11-14 documents that fences were deliberately *removed* from the
refcount idiom because GCC TSan cannot model `atomic_thread_fence`. **Delete
(~12 LOC).** Bonus: removes the temptation to reintroduce a TSan-invisible fence.

**F-4 (rung 1, dead): unused convenience macros.** `tl_atomic_inc_u32`, `dec_u32`,
`dec_u64` (tl_atomic.h:384-387, src=0), `load_acquire_u32`, `load_acquire_ptr`,
`store_release_*` (376-381, src=0), `TL_MO_SEQ_CST` (src=0, but it's one line of a
coherent enum — keep for symmetry if you like). **~8 LOC.**

**F-5 (rung 1, dead-in-practice): the GCC/Clang `__atomic` fallback backend**
(tl_atomic.h:277-363, ~87 LOC). Reachable only when a GCC/Clang compiler in C17 mode
defines `__STDC_NO_ATOMICS__` — the header itself calls this "unlikely with C17 but
defensive" (line 283-284). Every supported toolchain (GCC ≥ 4.9, any modern Clang,
CI's GCC 13) ships `<stdatomic.h>`. Replace the whole branch with
`#error "compiler lacks C11 atomics"` — if the config ever appears, you want a build
break, not a silently different third backend that no CI leg compiles or tests.
**Delete (~85 LOC).**

**F-6 (rung 3/4, flag loudly): MSVC backend vs `/experimental:c11atomics`.**
The 140-line Interlocked backend (tl_atomic.h:137-275) exists so the core builds on
MSVC without C11 atomics. But the shipped product already crossed that bridge:
**every Windows wheel compiles the binding with `/experimental:c11atomics`**
(bindings/cpython/CMakeLists.txt:210, 293, 345, 398, 450, 502, 551, 589, 641).
Enabling the same flag for the core would delete the entire backend and switch MSVC
to the identical C11 code path used by GCC/Clang. Performance is strictly *better*
on MSVC: today every load — including relaxed stat-counter loads in `tl_stats()`
(tl_timelog.c:2164-2174) and hot-path refcount reads — compiles to
`InterlockedCompareExchange`, a full-barrier `lock cmpxchg` RMW
(tl_atomic.h:177-190, comment at 166-176 acknowledges this), where C11 relaxed
loads are plain `mov`s. Risks to verify in a later phase: the flag is still labelled
"experimental" by Microsoft (requires VS2022 17.5+); `/WX` interaction; standalone
core consumers building with older MSVC. **~135 LOC, medium risk, no API change.**
If rejected: the seq_cst-everything Interlocked design is the safe conservative
choice and I have no cheaper in-tree fix that doesn't add a fourth code shape.

### 2. tl_sync.{h,c} (806 LOC) — mutex/cond/thread wrapper

The core wrapper is load-bearing (see NO-and-NO N-1). The dead fringe is not:

**F-7 (rung 1, dead): `tl_thread_set_name`.** Debug-only, declared at
tl_sync.h:154-164, implemented twice — the Windows version drags in a
`GetProcAddress`/`INIT_ONCE` runtime-resolution mechanism plus a hand-rolled
ASCII→wide widening loop (tl_sync.c:216-264, ~49 LOC), the POSIX version another
~16 LOC (tl_sync.c:572-588), plus the `pthread_setname_np` forward-declaration
workaround at the top of the file (tl_sync.c:5-13). **Nothing ever calls it** — the
maintenance worker (tl_timelog.c:1914) never names its thread. ~85 LOC of carefully
commented machinery serving nobody. **Delete**, or (one line) actually call it in
the worker if named threads in `htop` are wanted — either resolution beats the
status quo.

**F-8 (rung 1, dead): `tl_mutex_is_held`.** Two implementations
(tl_sync.c:86-90, 393-397) + declaration (tl_sync.h:69-72). Zero callers in src or
tests — lock-order assertions go through the separate tl_locks.h tracker instead.
**Delete (~15 LOC).** Note this also unlocks slimming the POSIX debug
`owner`/`locked` fields (see F-9).

**F-9 (rung 7, debug-only, optional): POSIX debug owner tracking is partially
redundant with ERRORCHECK.** Debug builds already create
`PTHREAD_MUTEX_ERRORCHECK` mutexes (tl_sync.c:318-325) and `TL_VERIFY(rc == 0)`
aborts on the EDEADLK/EPERM they return (tl_sync.c:358, 376), so recursive-lock and
unlock-by-non-owner are caught by the platform. The manual `owner`/`locked`
bookkeeping (tl_sync.h:42-50 and ~10 blocks in tl_sync.c) re-detects the same
misuse plus wait-without-lock. With `tl_mutex_is_held` dead (F-8), the only extra
coverage the fields buy is the `TL_ASSERT(mu->locked)` in cond_wait paths. Honest
call: keep the Windows owner field (SRWLOCK has no errorcheck mode and silently
deadlocks on recursion, tl_sync.c:53-55) and optionally drop the POSIX fields
(~30 LOC). Low value; debug-only either way.

**F-10 (rung 1, dead): `tl_thread_self_id`** (tl_sync.c:212-214, 558-570 incl. the
memcpy-the-opaque-pthread_t dance, decl tl_sync.h:151-152). Zero callers; its
stated purpose "log output and lock tracking" (tl_sync.c:562-563) is served by
neither the logger nor the tracker. **Delete (~22 LOC).**

**F-11 (rung 1, dead): `tl_cond_broadcast`** (tl_sync.c:139-142, 518-521). Zero
callers anywhere — the engine's condvars are single-waiter (one maintenance worker;
one flusher waiting for queue space) and only ever `tl_cond_signal`. **Delete
(~10 LOC).** If a multi-waiter design ever arrives, five lines come back with it.

**Test-only surface (note, not a strong finding):** `tl_mutex_trylock`
(tl_sync.c:72-84, 380-391) and `tl_cond_wait` (untimed; tl_sync.c:107-118, 444-461)
have zero engine callers — production exclusively uses lock/unlock and
`tl_cond_timedwait`. Both are used by the C test suites
(test_internal_sync.c:145,156,190; test_compaction_internal.c:635,689), i.e. the
safety net itself. Keeping shim completeness for the test harness is a defensible
lazy trade; I flag it so the census is honest. Same for `tl_thread_yield` /
`tl_sleep_ms` (test_stress.c + two real callers in tl_timelog.c:1822,1855 and
tl_memtable.c backpressure — those two are genuinely used).

### 3. tl_seqlock.h (114 LOC) — the write-only seqlock

**F-12 (rung 1, two tiers): production has writers but no readers.**
Call census: `tl_seqlock_init` ×1, `write_begin`/`write_end` ×3 pairs
(tl_timelog.c:882/895, 912/916; tl_compaction.c:1331/1336). The read half —
`tl_seqlock_read`, `tl_seqlock_is_even`, `tl_seqlock_validate`,
`tl_seqlock_current` (tl_seqlock.h:86-113) — is called **only** by
test_internal_sync.c. No production code ever samples the counter: snapshot
acquisition holds `writer_mu` for the whole capture (documented in CLAUDE.md
invariant #6: "current snapshot acquisition does not run a standalone seqlock retry
loop because writer_mu already prevents torn manifest/memview captures"). The
header itself says the counter is "a hook for future lock-free optimisations on the
read side" (tl_seqlock.h:20-22).

- **Tier A (low risk, recommend): delete the four dead reader helpers** (~35 LOC
  + their two tests). The write windows remain, the documented invariant remains
  intact, nothing observable changes.
- **Tier B (maintainer decision, medium-high risk): delete the seqlock entirely** —
  header, `view_seq` field (tl_timelog_internal.h:105), 7 call sites, init, tests
  (~170 LOC total). Today the two `fetch_add(ACQ_REL/RELEASE)` per publication are
  pure overhead — cheap and off the hot path (publications are flush/compaction
  frequency), so there is no perf urgency. Against deletion: CLAUDE.md invariant #6
  and pitfall #2 explicitly document the `view_seq` window, and the flush publish
  comment (tl_timelog.c:886-891) frames the memrun-pop-inside-the-window as "the
  invariant that prevents a reader from counting a record twice" — that framing is
  only meaningful if a future lock-free reader exists. This is speculative
  flexibility by the book, but it is *documented, deliberate* speculative
  flexibility with a stated roadmap. I report it; I do not recommend Tier B
  unilaterally.

**F-13 (rung 6, trivial):** `TL_CACHE_LINE_SIZE` fallback re-definition at
tl_seqlock.h:31-33 duplicates tl_platform.h:65-67, which is always already included
via tl_atomic.h → tl_platform.h. The `#ifndef` guard makes it harmless; ~6 LOC.

### 4. tl_alloc.{h,c} (454 LOC) — allocator seam

The vtable + default-libc design is the public-API allocator seam
(timelog.h:199-206) — required, minimal, keep (N-10). Findings on the fringe:

**F-14 (rung 1, dead): `tl__alloc_get_total/count/peak`** (tl_alloc.c:242-254,
tl_alloc.h:194-198). Zero callers in src *and* tests. **Delete (~18 LOC).**

**F-15 (rung 1, dead + misleading): `peak_allocated` and `total_allocated`
tracking.** `peak_allocated` is written by two identical CAS-max loops
(tl_alloc.c:102-108, 146-152) and read only by the dead getter → the loops are dead
weight in every debug allocation. `total_allocated` is incremented on alloc but
**never decremented on free**, so the debug leak warning
(tl_alloc.c:77: "Memory leak detected: %zu allocations, %zu bytes") reports
*cumulative bytes ever allocated* as leaked bytes — actively misleading.
Keep `allocation_count` (the leak signal that is actually correct); delete the
other two fields, both CAS loops, and fix the message. **~45 LOC, debug-only, zero
release-path impact.** CI's new LSan leg (v1.3) covers the default-allocator case
independently; `allocation_count` still earns its keep for custom-allocator runs.

**F-16 (rung 2, one-liner): duplicate overflow guard.** tl__calloc hand-rolls the
division round-trip check (tl_alloc.c:122-126: `total / count != size`) while the
same header already exports `tl__alloc_would_overflow` (tl_alloc.h:127-129), used
by tl__mallocarray/tl__reallocarray four lines away. Use the helper; one concept
fewer. ~4 LOC.

**F-17 (rung 1, dead): `tl__reallocarray`** (tl_alloc.c:173-188, tl_alloc.h:98-104).
Zero callers — growth sites call `tl__grow_capacity` + `tl__realloc` directly
(tl_page.c:302, tl_manifest.c:207, tl_compaction.c:752). **Delete (~22 LOC).**
(`tl__mallocarray` has exactly one caller, tl_point.c:38 — borderline, but it
carries the overflow check at that site; keep.)

**F-18 (rung 6, debug-only): tl__free's CAS underflow loop** (tl_alloc.c:220-233).
Ten lines of load+CAS retry to decrement a debug counter with an underflow check.
`uint64_t old = tl_atomic_fetch_sub_u64(...); TL_VERIFY(old > 0);` does the same
job in two lines — exactly the shape TL_REFCOUNT_RELEASE already uses
(tl_refcount.h:32-39). The transient wrapped value after a racing double-free is
observable only by the debug leak report; the VERIFY still fires. ~8 LOC.

### 5. tl_locks.h (151 LOC) — lock-order tracker

The tracker core (`tl_lock_acquire_check`/`release_check`, TL_LOCK/TL_UNLOCK, named
macros) has 43 production use sites and directly enforces the
maint→flush→writer→memtable ordering invariant. Keep (N-6).

**F-19 (rung 1, dead):** `TL_TRYLOCK` (both debug and release variants,
tl_locks.h:109-115, 122), `tl_lock_is_held` (81-87, 126), `tl_lock_highest_held`
(92-96, 127). Zero callers. **Delete (~40 LOC).** (`tl_mutex_trylock` underneath
stays for tests, or goes too if you accept touching test_internal_sync.c.)

### 6. tl_defs.h (186 LOC)

Constants and TL_MIN/TL_MAX (40 use sites) all earn their keep;
`tl_align_up_safe` has 2 real callers (tl_page.c:78,88).

**F-20 (rung 1, dead):** `TL_ARRAY_SIZE` (line 141), `TL_IS_ALIGNED` (144),
`TL_ALIGN_UP` (147) — zero code callers; TL_ALIGN_UP survives only inside comments
(tl_page.h:48,52) which can name `tl_align_up_safe` instead. **Delete (~8 LOC).**

### 7. tl_platform.h (172 LOC)

Platform/compiler detection, TL_INLINE, TL_ASSERT/TL_ASSUME/TL_VERIFY, test-hook
assert — all load-bearing (N-4). TL_THREAD_LOCAL used by the lock tracker.

**F-21 (rung 1, dead, with a caveat):** `TL_NOINLINE`, `TL_RESTRICT`,
`TL_LIKELY`, `TL_UNLIKELY`, `TL_ALIGNED`/`TL_CACHE_ALIGNED`, `TL_UNREACHABLE`,
and both `TL_PREFETCH_*` macros (three-way definition block, lines 156-170) have
**zero users** in core/src, bindings, and tests. That surprised me given the v1.3
branchless-search work — verified: the shipped search code uses none of them.
**Caveat:** in-flight perf worktrees (feat/perf-wins) may use these; check before
deleting. ~25 LOC, low value but real.

### 8. tl_math.h (99 LOC) — overflow helpers

Hand-rolled `tl_add/sub/mul_overflow_i64`. All three are used (window math:
tl_window.c:35,72,85,100; adaptive/compaction debt spans) and unit-tested
(test_internal_data_structures.c:159-175). See P-3 for the builtin/stdckdint lead
and N-9 for why the hand-rolled form stays as the portable default. One honest
perf note: `tl_mul_overflow_i64` pays 1-2 integer divisions per call
(tl_math.h:71-89); on GCC/Clang `__builtin_mul_overflow` is a single
`imul`+overflow-flag. The call sites are compaction-selection/window-bound
frequency, not per-record — so this is an optimization lead, not a simplification;
adding a `#if __has_builtin` fast path *adds* lines and a second code shape.

### 9. tl_log.{h,c} (166 LOC)

Callback-formatter with 8 production call sites (4×ERROR, 2×WARN, 2×INFO;
DEBUG/TRACE macros currently have zero emitters). The facility is public API
(`log_fn`/`log_level` in tl_config, timelog.h:296-298) so it must exist (N-7).

**F-22 (rung 1, dead):** `TL_LOG_STATIC_ERROR`/`TL_LOG_STATIC_WARN`
(tl_log.h:73-79) — no-op placeholders with zero callers. **Delete (~7 LOC).**
Minor: `tl__log_v` has no external caller (tl_log.c:83 only) and could lose its
header declaration; kept as the conventional va_list pair, I won't fight it.

### 10. tl_refcount.h (41 LOC)

Two macros, 17 production use sites across 6 files. The CAS-acquire loop and the
acq_rel-folded release are deliberately shaped around the GCC-TSan fence blindness
(documented at tl_refcount.h:8-14 and in the maintainer's memory notes). No
finding — see N-3.

### 11. tl_timelog_internal.h (215 LOC)

Single authoritative struct definition with per-field lock-ownership docs. Dense,
accurate, nothing speculative — the `memview_cache` and counter blocks all have
live users. No findings.

### 12. tl_test_hooks.c (32 LOC)

Assert-hook plumbing used by 3 test sites via `tl__test_set_assert_hook`. Minimal
already. No findings.

---

## The C11 `<threads.h>` Question (extra instruction)

Could tl_sync.{h,c} (~800 LOC) collapse onto C11 `<threads.h>`? **No — and the
blockers are hard, not aesthetic:**

1. **macOS: Apple has never shipped `<threads.h>`.** The macOS SDK (through current
   releases) provides pthreads but not C11 threads. The project ships macOS x86_64
   + arm64 wheels (pyproject.toml `[tool.cibuildwheel.macos] archs = ["x86_64",
   "arm64"]`). Hard blocker on its own.
2. **Linux wheels: glibc gained `<threads.h>` in 2.28**, while manylinux baselines
   in common use (manylinux2014 = glibc 2.17) predate it. Adoption would silently
   couple the wheel matrix to manylinux_2_28+.
3. **MSVC: `<threads.h>` only exists in VS 2022 17.8+ (late 2023)** — newer than
   the "Visual Studio 17 2022" floor the docs advertise.
4. **Functional regression: `cnd_timedwait` is specified against `TIME_UTC`**
   (wall clock) with no monotonic option. tl_sync deliberately creates condvars on
   CLOCK_MONOTONIC precisely to make bounded waits immune to NTP/wall-clock jumps
   (tl_sync.c:294-309, 469-482, and the tl_sync.h:90-93 comment). threads.h cannot
   express this.
5. **Half the shim survives anyway:** `tl_monotonic_ms`, debug lock tracking, the
   ERRORCHECK/owner diagnostics, and Windows-specific choices (`_beginthreadex`
   for CRT safety, tl_sync.c:146-153) have no threads.h equivalent.

Same verdict for **tinycthread** (zlib license, would pass licensing): it is a
`TIME_UTC`-based portability layer with the same monotonic-clock gap, effectively
unmaintained since ~2016, and would still need the debug layer wrapped around it.
The hand-rolled shim earns its keep. (Entered as N-1 + P-1.)

---

## Prior-Art Leads (with honest fit notes)

**P-1. Threads/mutex/condvar shim** — candidates: C11 `<threads.h>`,
tinycthread (zlib), pthreads-win32 (LGPL — fails license). Fit: all fail on either
platform reality (no macOS threads.h; glibc 2.28+; MSVC 17.8+) or the monotonic
condvar requirement (TIME_UTC-only `cnd_timedwait`). pthreads-win32 additionally
fails MIT-compat. Verdict-shaped lead: keep hand-rolled.

**P-2. Atomics shim** — candidates: MSVC `<stdatomic.h>` via
`/experimental:c11atomics` (F-6; strongest lead since Windows wheels already
require the flag for the binding), Concurrency Kit `ck_pr` (BSD-2 but
GCC/Clang-asm oriented, MSVC support effectively absent — fails the three-compiler
gate), portable-snippets `psnip/atomic` (CC0, unmaintained, still a third-party
shim replacing a working in-tree shim — lateral move). Best move is the platform
rung (MSVC C11 atomics), not a library.

**P-3. Overflow-checked int64 math** — candidates: `__builtin_{add,sub,mul}_overflow`
(GCC 5+/Clang 3.8+, free and single-instruction), C23 `<stdckdint.h>`
(`ckd_add/sub/mul` — GCC 14/Clang 18+; MSVC support not yet dependable under
`/std:c17`, needs verification), Windows `<intsafe.h>` (unsigned-only, wrong
types). Fit: a builtin fast path is a *perf* lead for `tl_mul_overflow_i64`'s
division (tl_math.h:71-89); it cannot delete the hand-rolled code while MSVC stays
supported, so as a simplification it is a wash (adds ~10 lines of preprocessor to
save 0). Revisit when MSVC ships stdckdint cleanly.

**P-4. Seqlock** — candidates: liburcu urcu/seqlock (LGPL — fails license),
ck_sequence (BSD-2 — MSVC problem again), Linux seqcount (GPL — fails). The
in-tree seqlock is 114 LOC, correct, and TSan-visible by construction. No adoptable
prior art beats it; the real question is F-12 (does it need to exist at all).

**P-5. Refcount idiom** — candidates: ck_ref / folly-style intrusive counts.
The in-tree idiom is 41 LOC and encodes a project-specific constraint (GCC TSan
fence blindness → acq_rel folded into the RMW, tl_refcount.h:8-14) that generic
libraries do not promise to preserve. Keep.

**P-6. Debug lock-order tracker** — candidate: Clang Thread Safety Analysis
(`-Wthread-safety` + capability annotations) gives compile-time ordering proofs.
Fit: Clang-only (GCC/MSVC ignore the annotations), so it could complement but not
replace the 60-line runtime tracker that must work on all three compilers.

**P-7. Test framework / assert hook** — candidates: greatest/µnit/Unity
(MIT/ISC). The in-tree RUN_TEST harness + assert hook (tl_platform.h:89-132,
tl_test_hooks.c) is tiny and already amortized across ~485 tests; migrating
frameworks is churn with no deletion payoff in this unit.

---

## NO-and-NO (earns its keep, grounded)

- **N-1. The pthread/Win32 sync shim itself** (tl_sync.{h,c} core paths): needed
  because no portable stdlib alternative exists on the supported platform matrix
  (see threads.h section); monotonic condvar clocks are a real correctness property
  (tl_sync.c:469-482 explains the wrong-clock failure modes: always-immediate or
  effectively-infinite timeouts); SRWLock choice on Windows is the light-weight
  correct primitive; `_beginthreadex` over CreateThread is a CRT requirement
  (tl_sync.c:146-153).
- **N-2. Seqlock write-window memory ordering** (tl_seqlock.h:59-84): ACQ_REL on
  begin / RELEASE on end is the canonical protocol; if the seqlock stays (F-12
  Tier A), its implementation should not be touched — it is minimal and the
  ordering comments are load-bearing documentation.
- **N-3. TL_REFCOUNT_ACQUIRE's CAS loop instead of a bare `fetch_add`**
  (tl_refcount.h:16-30): the loop exists to `TL_VERIFY` against
  resurrection-after-zero and overflow *before* publishing the increment;
  uncontended cost is one `lock cmpxchg` vs one `lock xadd` — same class. The
  release's acq_rel-in-RMW (no standalone fence) is mandatory for GCC TSan
  cleanliness on 3.14t (documented in-header and in the maintainer's TSan notes).
  Do not "simplify" to fetch_add/fence idioms.
- **N-4. TL_ASSERT→TL_ASSUME release semantics + TL_VERIFY split**
  (tl_platform.h:71-154): deliberate two-tier contract — internal invariants
  become optimizer hints in release; OS-primitive results get always-on aborts
  (tl_sync.c:355-358). The header's warning about never TL_ASSERT-ing
  caller-supplied data is the right guardrail. Keep exactly as is.
- **N-5. `tl__grow_capacity` + `tl__alloc_would_overflow`** (tl_alloc.h:127-163):
  three real call sites each, overflow-safe, 30 LOC total. This *is* the minimal
  form of the dynamic-array-growth subproblem; klib's kv_push etc. would replace
  it with a macro library and no net deletion.
- **N-6. The debug lock-order tracker core** (tl_locks.h:52-107): 43 TL_LOCK/
  TL_UNLOCK sites enforce the documented maint→flush→writer→memtable order at
  runtime in every Debug/ASan CI leg; it is ~55 LOC and has caught the exact class
  of bug the invariant list warns about. No portable compile-time replacement
  exists (P-6).
- **N-7. The logging facility** (tl_log.{h,c}): `log_fn`/`log_level` are public
  API (timelog.h:296-298), so the formatter must exist; 166 LOC for a bounded,
  level-gated, callback-safe vsnprintf wrapper is already the floor. The
  two-stage snprintf+vsnprintf into a stack buffer is the standard shape.
- **N-8. MSVC Interlocked-everything (if F-6 is rejected)**: making every op
  seq_cst is the only *safe* choice absent C11 atomics — the header correctly
  refuses the volatile+`_ReadWriteBarrier` trap on ARM64 (tl_atomic.h:144-148).
  Slow but sound; do not hand-roll acquire/release Interlocked variants (more
  code, subtle ARM64 semantics) unless a profiler demands it.
- **N-9. Hand-rolled overflow math as the default path** (tl_math.h): MSVC has no
  signed-overflow builtins and stdckdint is not yet dependable there; the
  implementations are branch-exact, unit-tested (test_internal_data_structures.c:
  159-175), and off the per-record hot path. The builtin fast path (P-3) is
  optional tuning, not debt.
- **N-10. The allocator vtable + context** (tl_alloc.h:17-27): this is the public
  allocator seam (timelog.h:199-206) the whole adoption-constraint list depends
  on; inline storage avoids a pointer chase per allocation. Required.
- **N-11. `tl_sleep_ms` nanosleep-EINTR resume loop and `tl_monotonic_ms`**
  (tl_sync.c:594-619): both used by production backpressure/backoff paths
  (tl_timelog.c:1822,1855; tl_memtable.c:1141-1154); correct EINTR handling and
  clock choice in ~25 LOC. Floor reached.
- **N-12. Ring-buffer/H-07, memview/H-09 adjacent code**: not in this unit, but
  noting for the record that nothing proposed here touches sealed-queue index
  arithmetic, epoch validation, lock ordering, or publication windows — every
  deletion above is grep-verified unreachable or debug-only, except F-12 Tier B
  which is explicitly gated on a maintainer decision about documented invariant #6.

---

## Test-Coverage Notes

- Deletions F-1/F-2/F-3, F-12 Tier A, and the trylock note remove their own
  shim-self-tests in test_internal_sync.c (21 RUN_TESTs; ~6 would go). No
  engine-behavior test depends on any deleted symbol — verified by grep.
- F-6 (MSVC C11 atomics) is covered by the existing Windows CI legs + wheel
  build; it needs a Windows compile+ctest pass and a wheel smoke test, no new
  tests.
- F-15's leak-warning message change is observable only in debug stderr; no test
  asserts on it (grep: no test references "Memory leak detected").
- F-12 Tier B would require updating CLAUDE.md invariant #6, pitfall #2, the
  read-path/storage internals docs, and the lab CONCURRENCY_CONTRACT — that doc
  surface is most of the cost.
