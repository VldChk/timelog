# Prior-Art Landscape: Hard Facts for the Dependency-Adoption Audit

**Compiled:** 2026-07-07. All facts verified live against primary sources (GitHub/GitLab APIs,
raw LICENSE/header files, CI workflow files, release pages, vendor docs) on that date —
not from memory. Each record cites its sources.

**Consuming-project constraints (the bar every candidate is measured against):**

- MIT license (copyleft in a vendored/wheel-bundled dependency is disqualifying friction)
- C17 core, strict mode: GCC/Clang `-Werror`, MSVC `/WX`
- Wheels for Linux/macOS/Windows via scikit-build-core, incl. free-threaded CPython 3.14t
- Custom allocator (`tl__malloc` family) must be injectable
- ASan/UBSan/TSan are mandatory CI legs (fork-per-test and asm-based atomics are hostile)

**Legend for the MSVC column:** "yes (CI)" = upstream runs a Windows/MSVC CI job;
"in-code" = explicit `_MSC_VER` paths but no upstream Windows CI; "no" = fails or unsupported.

---

## 0. Master Fit Matrix

| # | Library | License | C std | MSVC | Form | Alloc injection | Maintained (2026)? | Hard disqualifier for timelog? |
|---|---------|---------|-------|------|------|-----------------|--------------------|-------------------------------|
| 1a | klib khash.h | MIT | C89/99 | in-code (no CI) | header | **yes** (`kmalloc`…) | repo active; header frozen 2018 | none (vendor-and-own) |
| 1b | klib kvec/kbtree/ksort | MIT | C89/99 | no CI | header | **no** (hardcoded libc) | frozen 2013–2021 | no allocator injection |
| 2 | CCAN | **per-module** (CC0…GPL-3) | C89/99+probes | AppVeyor **disabled** ("FIXME") | per-module dirs | module-dependent | active (pushed 2026-07-03) | GPL/LGPL contamination risk |
| 3 | stb_ds.h | MIT OR Unlicense | **C99 + `typeof`** | works, fuzz-only CI | header | partial (context always NULL) | stb active-ish; stb_ds frozen v0.67 (2021) | breaks strict `-std=c17` (#1735) |
| 4 | uthash family | BSD 1-clause (revised) | C89 | in-code (no CI) | header | uthash yes; utarray/utstring OOM-hook only | **yes** — v2.4.0 tagged 2026-06-11 | none for uthash.h itself |
| 5 | Concurrency Kit (ck) | BSD-2 (+Apache-2.0, Intel parts) | C99 | **no** (`ck_pr.h` needs `__GNUC__`) | mixed (ring/stack/seq headers; epoch compiled) | yes where it allocates | active commits; releases ~3-yr cadence | **MSVC hard-fail** + TSan-blind default |
| 6 | liburcu | **LGPL-2.1+** (some MIT headers) | C99 | **no** (Cygwin only) | compiled lib | yes (rculfhash) | excellent (v0.15.6, 2026-01) | **LGPL + no MSVC** |
| 7 | liblfds | public domain (blanket grant) | pre-C11 (own PAL) | yes historically (MSVC 2008+) | compiled static | moot (caller allocates all) | **dead** — last release 2017-02 | **abandonment** |
| 8 | tlsf (mattconte) | BSD-3 (in-file; no LICENSE file) | C89/99 (C17-clean) | **yes, in-code first-class** | tlsf.c + tlsf.h | it *is* the allocator | dormant (last commit 2020-03) | none — best overall fit |
| 9 | Unity | MIT | C89+ (CMake sets C11) | claims yes, Linux-only CI | 1 .c + 2 .h | n/a | **yes** (commits 2026-07-06) | Ruby toolchain for params/runners |
| 10 | greatest | ISC | C89 | partial (PR #118 unmerged) | single header | n/a (no allocation) | dormant (frozen v1.5.0, 2021-02) | no CI at all; MSVC /WX on you |
| 11 | munit | MIT | C89/99 | broken on MSVC 2019+ (fix unmerged) | munit.c + .h | n/a | **abandoned** (master frozen 2020-05, never 1.0) | abandonment + fork-per-test default |
| 12 | cmocka | Apache-2.0 | C99 (since 2.0.0) | **yes (GitLab Windows CI)** | compiled lib | n/a | **yes** — 2.0.2 on 2026-01-12 | none; heaviest vendoring of the group |
| 13 | Criterion | MIT | C99/C++11 | claimed; **CI leg commented out** | compiled + deps (BoxFort, libffi…) | n/a | slow (v2.4.3, 2025-10) | **mandatory fork/exec-per-test** |
| 14 | utest.h | Unlicense | feature-gated (C99/C11) | **yes (windows-latest MSVC+ClangCL CI)** | single header | n/a | active (commits 2026-06-15) | no versioned releases; "pre-ai" tag policy |
| 15 | sds | BSD-2 root / BSD-3 file headers | C99 | **no** (`__attribute__((packed)))` | .c + .h | yes (`s_malloc`) | dormant; lives on in Redis/Valkey | MSVC-hostile attributes |
| 16 | c-vector (eteran) | MIT | C89 | no Windows CI (likely clean) | single header | **yes, complete** | active (2026-06-12, 0 open issues) | none noted |
| 17 | cgranges (lh3) | MIT | C99 | no CI | .c + .h (+bundled khash) | **no** | dormant (2024-05) | **static index — no insert/delete** |
| 18 | Pure-C LSM/k-way-merge libs | — | — | — | — | — | — | **none exist** (see §15) |

---

## 1. klib (attractivechaos) — khash.h, ksort.h, kvec.h, kbtree.h

Repo: <https://github.com/attractivechaos/klib>

- **License:** MIT/X11 (GitHub SPDX `MIT`; README "distributed under MIT/X11 license"; MIT grant in each header, e.g. kvec.h/ksort.h line 5).
- **C standard:** C89-friendly macro style, no `__STDC_VERSION__` gate; effectively C89/C99. Compiles as C17.
- **MSVC:** No CI of any kind (`.github/workflows` → 404, no AppVeyor). khash widely reported MSVC-clean; only Windows issue found is #129 (`drand48`, unrelated files). Treat as "likely clean, upstream-unverified."
- **Form:** header-only; copy the individual `.h`.
- **Allocator injection — UNEVEN (the gotcha):**
  - `khash.h`: full override via `#ifndef`-guarded `kcalloc/kmalloc/krealloc/kfree` (lines 179–189), plus `kh_inline`.
  - `kvec.h`: **none** — hardcodes `realloc()`/`free()` (lines 57–86).
  - `kbtree.h`: **none** — hardcodes `calloc()/realloc()/free()`.
  - `ksort.h`: no heap allocation on the hot path.
- **Maintenance:** repo pushed 2025-12-22 ("added block arena"), but the four headers are effectively frozen: khash.h last real change **2018-10-31**, kvec.h **2013-01-26**, kbtree.h **2015-09-29**, ksort.h **2021-03-26**. **No tagged releases ever.** 93 open issues. (Per-file `commits?path=` API.)
- **Thread-safety:** none built in; caller locks.
- **Vendoring:** drop-in single header (README: "copy a couple of files to your source code tree").
- **Audit note:** only khash reaches the custom-allocator bar; kvec/kbtree would need patching for `tl__malloc` to see their memory. klib also has **no k-way merge iterator** — ksort provides heap make/adjust primitives only.

## 2. CCAN — Comprehensive C Archive Network

Repo: <https://github.com/rustyrussell/ccan> · **ccodearchive.net is dead** (README warns the domain was squatted).

- **License — PER MODULE, the critical fact:** no repo-level license (GitHub API `license: null`). Each module's `_info` file carries a `License:` line; canonical texts in `/licenses/` (APACHE-2, BSD-3CLAUSE, BSD-MIT, CC0, GPL-2, GPL-3, LGPL-2.1, LGPL-3). Verified samples:
  - BSD-MIT: `list`, `tal`, `time` · MIT: `avl`
  - CC0: `hash`, `intmap`, `str`, `take`, `typesafe_cb`, `build_assert`, `array_size`
  - CC0 with a warning: `strmap` — "*but some dependencies are LGPL!*" (declared inline in `_info`)
  - **LGPL-2.1+:** `talloc`, `htable`, `timer` · **GPL-3+:** `rbtree`
- **C standard:** C89/C99 GNU-leaning; relies on a generated `config.h` from `tools/configurator` feature probes (adaptive, not fixed).
- **MSVC:** essentially broken. `appveyor.yml` drives cl/vcvarsall (VS14), but build/test steps are **commented out**: "FIXME: Work in progress. Disabled due to unfixed compile errors." Only config.h generation runs. (<https://raw.githubusercontent.com/rustyrussell/ccan/master/appveyor.yml>)
- **Form:** not header-only — module dirs with `.h` + `.c` + `_info` + `test/`.
- **Allocator injection:** module-dependent; `tal`/`talloc` are themselves allocator frameworks; no uniform override convention.
- **Maintenance:** **active** — pushed 2026-07-03; 2026-07-01 commits (asort mergesort+heapsort fallback, talloc `realloc(ptr,0)` fix). No versioned releases (rolling, vendored per module).
- **Vendoring:** official tool `tools/create-ccan-tree` copies a module **plus its transitive deps** into your tree.
- **Audit note — biggest license risk in this whole document:** `create-ccan-tree` auto-pulling dependencies makes accidental GPL/LGPL contamination easy (strmap self-documents this). Adoption would require a strict CC0/BSD-MIT/MIT whitelist with transitive-dependency auditing per module.

## 3. stb (nothings) + stb_ds.h

Repo: <https://github.com/nothings/stb>

- **License:** dual — MIT **or** public domain (Unlicense), "choose whichever you prefer" (repo LICENSE; GitHub reports NOASSERTION because it can't auto-classify the dual grant).
- **C standard (stb_ds):** C99+ or C++ (gates on `__STDC_VERSION__ >= 199901L`, line 516). **Gotcha:** `STBDS_ADDRESSOF` needs `typeof` (GNU/C23 extension); under strict `-std=c99…c18` it degrades to `&(value)`, **breaking `hmput`/`hmget` with rvalue keys/values** — open issue [#1735](https://github.com/nothings/stb/issues/1735) ("build error with gcc -std=c99 up to c18"; works only under `-std=gnuXX`). Directly hostile to a strict `-std=c17 -Werror` core.
- **MSVC:** stb broadly targets MSVC, but the only CI is `ci-fuzz.yml` (OSS-Fuzz on image codecs) — no Windows build matrix, nothing exercising stb_ds.
- **Form:** single header, `STB_DS_IMPLEMENTATION` in one TU.
- **Allocator injection:** `STBDS_REALLOC(context,ptr,size)` / `STBDS_FREE(context,ptr)` — must define both or neither (`#error`, line 455). **Caveat:** the `context` parameter is always passed `NULL` (in-header `@TODO`) — no working context-pointer plumbing, so stateful allocators can't be reached cleanly.
- **Maintenance:** repo pushed 2026-04-15, but 2025–26 activity is almost entirely `stb_image_resize2` (contributor jeffrbig2) plus anti-LLM policy documentation churn (2026-03/04). **168 open PRs, 413 open issues.** `stb_ds.h` frozen at **v0.67** — last functional change 2021-07-12, last touch a typo fix 2024-11-09.
- **Thread-safety:** not thread-safe (closed issue #837 confirms).
- **Known stb_ds correctness/usability issues:** #1668 (char[20] keys), #1666 (side effects in key expression), #1436 (const discard), #1141 (custom realloc/free docs incorrect).
- **Vendoring:** drop-in header. **Verdict:** vendor-and-own-it at best; the `typeof` requirement is a hard problem for this project's build flags.

## 4. uthash / utarray / utlist / utstring

Repo: <https://github.com/troydhanson/uthash>

- **License:** revised 1-clause BSD — keeps only source-redistribution copyright retention + warranty disclaimer (drops binary-redistribution and no-endorsement clauses). GitHub reports NOASSERTION; commonly cataloged BSD-1-Clause. Copyright line updated **2005–2026**.
- **C standard:** C89-compatible (`NO_DECLTYPE` fallback for compilers without `typeof`/`decltype`); CI runs `-pedantic`.
- **MSVC:** supported per docs (userguide lists VS2008/2010; `do_tests_win32.cmd` ships; explicit `_MSC_VER` branches — VS2010+ uses `decltype`). **But current GitHub Actions CI is ubuntu+macos only** — no Windows runner today.
- **Form:** header-only macro libraries under `src/`.
- **Allocator injection:**
  - `uthash.h`: yes — `uthash_malloc(sz)` / `uthash_free(ptr,sz)` (free takes a size), `#ifndef`-guarded.
  - `utarray.h` / `utstring.h`: **no allocator retargeting** — hardcode malloc/realloc; only the OOM handler (`utarray_oom()` / `utstring_oom()`, default `exit(-1)`) is overridable.
  - `utlist.h`: intrusive, no allocation at all.
- **Maintenance — SURPRISE, NOT dormant:** the "last release 2.3.0 (2021)" prior is outdated. **v2.4.0 tagged 2026-06-11**, version-bump commit 2026-06-25; repo pushed 2026-06-25. New maintainer: **Arthur O'Dwyer** (e.g. utlist `CDL_CONCAT` #280). Note v2.4.0 is a git tag, not a GitHub "release" (releases API empty).
- **Thread-safety:** none; caller locks.
- **Vendoring:** copy the header(s); also packaged (Debian/Homebrew/vcpkg).
- **Audit note:** healthiest classic macro lib in the set. Caveats: unusual 1-clause BSD text (confirm attribution posture), utarray/utstring can't reach `tl__malloc`, and MSVC support is in-code, not CI-verified.

## 5. Concurrency Kit (ck) — ck_ring, ck_stack, ck_sequence, ck_epoch

Repo: <https://github.com/concurrencykit/ck>

- **License:** BSD-2-Clause primary (Samy Al Bahra 2010–14; AppNexus 2011–13) **plus** Apache-2.0 for `src/ck_hp.c` (IBM 2008) and an Intel BSD-style license for `ck_pr_rtm`. All MIT-compatible but multi-notice. (<https://raw.githubusercontent.com/concurrencykit/ck/master/LICENSE>)
- **C standard:** C99 minimum (maintainer in issue #160: "as long as we don't revert to < C99").
- **MSVC: NO — disqualifying.** Issue [#160](https://github.com/concurrencykit/ck/issues/160) ("Windows support?", 2020, closed unfixed): compilation fails at `ck_pr.h` line 55 because `__GNUC__` is undefined. Historically tested compilers: gcc/clang/cygwin/icc/mingw — never cl.exe. Current CI (`.github/workflows/ci.yml`): Linux x86_64/arm64, macOS arm64/x86_64, FreeBSD — **no Windows job**. Build is a hand-rolled POSIX-shell `configure` (no CMake/Meson upstream).
- **Form:** mixed — `ck_ring.h`, `ck_stack.h`, `ck_sequence.h`, `ck_pr.h`, `ck_spinlock.h` are header-only inline; **`ck_epoch` is compiled** (`src/ck_epoch.c`), as are ck_hs/ck_ht/ck_hp/ck_array/ck_rhs/ck_ec. Even header-only use needs the configure-generated `ck_md.h`.
- **Allocator injection:** `ck_malloc.h` defines `struct ck_malloc` passed into allocating structures (ck_hs/ck_ht/ck_array). ck_ring/ck_stack/ck_epoch do no internal allocation — caller supplies buffers/records.
- **Maintenance:** alive but release-starved — last release **0.7.2 (2024-03-24)** on a ~3-year cadence (0.7.1: 2021, 0.7.0: 2019); commits current through **2026-07-04** ("ck_pr: Fix signature of generic ck_pr_add_ptr (#279)").
- **TSan story: poor by default.** Default atomics are ck's own per-arch inline asm under `include/gcc/` with its own fence model (`ck_pr_fence_*`) — invisible to TSan, guaranteed false positives. `configure --use-cc-builtins` (`-DCK_USE_CC_BUILTINS=1`) switches to compiler builtins (instrumentable), but `ck_sequence` is a racy-by-design seqlock and the fence-based ordering collides with GCC-TSan fence blindness (a limitation this project already tracks) — suppressions would still be needed.
- **Vendoring:** distro packages (Debian 13/14, Fedora 42+, Alpine 3.20+, FreeBSD port all at 0.7.2 — [repology](https://repology.org/project/concurrencykit/versions)); otherwise submodule + shell configure (breaks on native Windows). No amalgamation.
- **Verdict:** architecturally the closest match for timelog's primitives (ring / Treiber stack / seqlock / epoch), but **MSVC hard-fail** and TSan-hostile defaults make it unadoptable for this wheel matrix.

## 6. liburcu (userspace RCU)

Repo: <https://github.com/urcu/userspace-rcu> (mirror of git.lttng.org) · <https://liburcu.org>

- **License — gotcha:** library code is **LGPL-2.1-or-later**. REUSE/SPDX-compliant split (`LICENSES/` + `LICENSE.md`): most headers LGPL-2.1+; a few headers MIT (the `xchg()` primitive rewritten from atomic_ops 1.2 "to allow use in both free and proprietary software"); some Boehm-GC-licensed code; tests GPL-2.0; docs CC-BY-4.0. `lgpl-relicensing.md` documents the `_LGPL_SOURCE` static-inlining permission. **For MIT wheels that bundle the .so (auditwheel/delocate/delvewheel), LGPL-2.1 imposes relink/notice obligations — workable but real compliance burden.**
- **C standard:** C99 (C++11 for C++); GCC ≥ 4.8, Clang ≥ 3.0.
- **MSVC: NO.** Tested platforms: Linux, FreeBSD 13, **Cygwin**, macOS. No native Windows, autotools-only build. Still Cygwin-only in 2026.
- **Form:** compiled shared/static libs — link a flavor (`-lurcu-memb`/`-qsbr`/`-mb`/`-bp`) + `liburcu-cds`; hot-path read primitives inline via headers under `_LGPL_SOURCE`.
- **Allocator injection:** yes for the lock-free hash table — `struct cds_lfht_alloc { malloc, calloc, realloc, aligned_alloc, free, state }` with `cds_lfht_new_with_flavor_alloc()` (verified in `include/urcu/rculfhash.h`). Core RCU flavors don't allocate on hot paths.
- **Maintenance: excellent.** **v0.15.6 and v0.14.2 both tagged 2026-01-26**; steady 0.15.x releases through 2025; repo pushed 2026-07-01. Maintained by Mathieu Desnoyers / EfficiOS.
- **TSan story: best in class, behind a flag.** v0.15.0's headline: C11-memory-model rewrite on compiler atomic builtins "allowing ThreadSanitizer to understand the ordering guarantees provided by liburcu" — **requires `--enable-compiler-atomic-builtins` (off by default)**; macros inject TSAN annotations to compensate for TSan's fence blindness. Known caveat: TSan's `sigaction` interception can deadlock the signal-based flavor. (<https://lists.lttng.org/pipermail/lttng-dev/2024-December/030893.html>)
- **Vendoring:** system package or tarball + autotools; awkward inside a CMake/scikit-build-core wheel build; impossible for the Windows leg.
- **Verdict:** two independent disqualifiers (LGPL, no MSVC) despite exemplary maintenance and the best TSan story of any concurrency candidate.

## 7. liblfds

Site: <https://liblfds.org> · mirror: <https://github.com/liblfds/liblfds7.1.1>

- **License:** public domain with an explicit blanket grant ("You are free to use this library in any way"), plus pre-granted MIT/BSD/Apache/GPL/LGPL/CC fallbacks for no-public-domain jurisdictions. Zero license friction.
- **C standard:** pre-C11 design; own porting abstraction layer (PAL macros → MSVC `_Interlocked*` / GCC builtins per port), not `<stdatomic.h>`.
- **MSVC:** yes, historically strong — MSVC 2008+ user-mode (x64/x86/ARM32), WDK 7.1 kernel-mode. 7.1.1 dropped VS solution files (own makefiles). Best on-paper Windows story of the concurrency candidates. (<https://www.liblfds.org/mediawiki/index.php?title=r7.1.1:Building_Guide_(liblfds)>)
- **Form:** compiled static library. **Allocator:** moot — no internal allocation by design; callers pass in all state/elements.
- **Maintenance: DEAD.** Last release **7.1.1, 2017-02-20**; the promised 7.2.0 never shipped. The site's only post-2016 news item: "2026-05-09 — Server Migration… converted Mediawiki to static HTML" — the site was archived, not revived. GitHub mirror last pushed 2022-12-26. No aarch64-era ports, no C11-atomics migration, no CI, no triage.
- **TSan story:** own PAL atomics, designed pre-TSan; no annotations or CI; treat as unverified/unfriendly.
- **Vendoring:** source drop (designed for embedding; not in mainstream distros) — but adopting it means owning a 2017 lock-free codebase against 2026 compilers and memory models.
- **Verdict:** perfect license, real historical MSVC support, **disqualified by 9.5 years of abandonment** — unacceptable for lock-free concurrency code.

## 8. TLSF (two-level segregated fit allocator)

### 8a. mattconte/tlsf — the canonical BSD implementation

Repo: <https://github.com/mattconte/tlsf>

- **License:** BSD-3-Clause (Matthew Conte, 2006–2016), carried in the `tlsf.h`/`tlsf.c` header comments; **no separate LICENSE file** (GitHub license detector returns null — cosmetic, but flags in compliance tooling). README: "License changed to BSD" at v3.1.
- **C standard:** C89/C99-compatible, no C11 features, no inline asm; compiles clean as C17.
- **MSVC: yes, first-class in-code.** Verified in `tlsf.c`: explicit `#elif defined (_MSC_VER) && (_MSC_VER >= 1400) && (_M_IX86 || _M_X64)` branch using `_BitScanReverse`/`_BitScanForward`; also ARMCC, Green Hills, GCC builtins, and a generic portable C fallback. No GCC-only requirement anywhere.
- **Form:** exactly one `tlsf.c` + one `tlsf.h` — amalgamation-grade.
- **Allocator injection:** it *is* the allocator — caller supplies raw memory (`tlsf_create_with_pool`, `tlsf_add_pool`); zero libc-malloc dependency. README caveat: assumes 4-byte-aligned access capability.
- **Maintenance:** dormant — last commit **2020-03-29** (14 commits since 2015; v3.1 = 2016-04-10); unmerged PRs idle. For a ~1.2 kLOC allocator this is a vendor-audit-once-and-own proposition.
- **Thread-safety/TSan:** README: "Not designed to be thread safe; the user must provide this." O(1) malloc/free/realloc/memalign (real-time heritage). Contains **no atomics or fences at all** — the cleanest possible TSan story (reduces entirely to your external locking).
- **Vendoring:** copy two files (the universal practice — ESP-IDF, game engines).

### 8b. Original TLSF (Masmano, gii.upv.es) — LICENSE TRAP

The original academic implementation (ECRTS'04, 2.x) is **dual GPL/LGPL**, not BSD (<http://www.gii.upv.es/tlsf/main/license>). Do not use this lineage in an MIT project; Conte's is an independent BSD-3 implementation.

### 8c. espressif/tlsf — the maintained fork

Fork of Conte's carrying ESP-IDF patches. **Active** (commits Nov 2025 – **2026-01-05**), BSD heritage retained ("Released under the BSD license"), but restructured layout and API divergence toward embedded targets; also no root LICENSE file. Best used as a patch/reference source while vendoring upstream Conte. (<https://github.com/espressif/tlsf>)

**Verdict:** mattconte/tlsf is the **only candidate in the entire audit with zero license friction, verified MSVC in-code support, trivial vendoring, and a perfect TSan story**. Weaknesses: dormancy (own it after audit) and deliberate no-thread-safety (matches timelog's caller-locks model).

## 9. Unity (ThrowTheSwitch)

Repo: <https://github.com/ThrowTheSwitch/Unity>

- **License:** MIT (LICENSE.txt; GitHub SPDX MIT).
- **C standard:** ANSI C/C89 upward; auto-detects C99+ features (UnityConfigurationGuide, "C Standards, Compilers and Microcontrollers"). Shipped CMakeLists sets `C_STANDARD 11` on the target — fine for C17.
- **MSVC:** claims universal compiler support; **no first-party MSVC CI** — the only workflow (`.github/workflows/main.yml`) is ubuntu-only (Ruby 2.7–3.2 matrix, `rake ci`); `test/targets/` covers gcc/clang/IAR/HiTech, no MSVC file. Works in practice (large Ceedling/Windows user base) but `/WX` regressions wouldn't be caught upstream.
- **Form:** compiled — `src/unity.c` + `unity.h` + `unity_internals.h`.
- **Fixtures/params/registration:** per-file `setUp()`/`tearDown()`; fixture add-on `extras/fixture` (TEST_GROUP model); **parameterized tests (`TEST_CASE`/`TEST_RANGE`) exist only via the Ruby runner generator** (`auto/generate_test_runner.rb`). Registration: manual `RUN_TEST` in main, or Ruby-generated runners.
- **Maintenance:** **active** — v2.6.1 released 2025-01-01; commits on master dated **2026-07-06** (float-compare fix #819 etc.). 86 open issues, ~5.3k stars.
- **Sanitizer/CTest:** good — single process, no fork; setjmp/longjmp (`TEST_PROTECT`) tolerated by ASan/UBSan/TSan; one runner exe per test file → clean CTest granularity; no auto-discovery.
- **Vendoring:** copy 3 files, or add_subdirectory/FetchContent (proper CMake + `unityConfig.cmake`); Meson and PlatformIO shipped.

## 10. greatest (silentbicycle)

Repo: <https://github.com/silentbicycle/greatest>

- **License:** ISC (README; GitHub API).
- **C standard:** C89 ("doesn't depend on anything beyond ANSI C89"; clean under `-Wall -Wextra -pedantic`; <1000 LOC; no dynamic allocation). C99 needed only for `RUN_TESTp` variadic parametric syntax.
- **MSVC:** partial/DIY — **no CI at all** (no workflows dir); open PR [#118](https://github.com/silentbicycle/greatest/issues/118) "CMake and no-warn MSVC support" (2023-05-06, never merged) exists precisely because warning-clean MSVC needed patches (`strncat_s` guard etc.).
- **Form:** single header (`greatest.h`).
- **Fixtures/params/registration:** suites with per-suite setup/teardown callbacks + userdata (`GREATEST_SET_SETUP_CB`/`GREATEST_SET_TEARDOWN_CB`, greatest.h lines 317–318); `RUN_TEST1(test, arg)` and C99 `RUN_TESTp`; **fully manual registration**; CLI filtering (`-s`, `-t`).
- **Maintenance:** dormant — frozen at **v1.5.0 (2021-02-15)** on the default `release` branch; `develop` last touched 2023-01-10; repo pushed 2023-06-11; zero commits in 3+ years. "Finished" more than "dead," but MSVC `/WX` cleanliness is on you.
- **Sanitizer/CTest:** structurally excellent — single process, no fork, no allocation. (Historical: `GREATEST_USE_LONGJMP` + `RUN_TESTp` segfault, issue #58, closed 2017.)
- **Vendoring:** single-header drop-in; no upstream CMake package.

## 11. munit / µnit (nemequ) — ABANDONED

Repo: <https://github.com/nemequ/munit> · site: <https://nemequ.github.io/munit/>

- **License:** MIT — the `COPYING` file is verbatim MIT (Evan Nemerson, 2013–2016); GitHub reports NOASSERTION only because of the file layout.
- **C standard:** C89-compatible with C99 niceties (`MUNIT_ARRAY_PARAM` on C99; exact-width-type fallbacks for old VS without stdint.h).
- **MSVC:** historically good (AppVeyor badge; `wip/msvc-old` branch) — **but MSVC 2019 broke (issue #68) and fix PR #71 was closed UNMERGED on 2022-12-15.** Modern MSVC needs local patching.
- **Form:** compiled — `munit.c` + `munit.h`.
- **Features:** the differentiators are a reproducible cross-platform PRNG (CLI seed), first-class parameterized tests (`MunitParameterEnum`), nested suites, wall+CPU timing. Manual registration via `MunitTest`/`MunitSuite` struct arrays.
- **Maintenance: ABANDONED — decision-critical.** Master frozen since **2020-05-12** (6+ years). Only release ever: **v0.2.0 — never reached 1.0.** 40 open issues + 25 open PRs. Issue [#104](https://github.com/nemequ/munit/issues/104) "Project and maintainer status" (2024-06-06): **zero maintainer response in two years.**
- **Sanitizer/CTest:** **forks per test by default on POSIX** (`--no-fork` available; no fork on Windows at all, issue #2) — the known-bad pattern for ASan/TSan; disabling loses crash isolation.
- **Vendoring:** drop in 2 files; Meson wrap documented; no CMake upstream.

## 12. cmocka

Repo: <https://gitlab.com/cmocka/cmocka> · <https://cmocka.org>

- **License:** Apache-2.0.
- **C standard:** **C99 required since 2.0.0** (cmocka.org). No C11 requirement.
- **MSVC: yes, with first-party CI evidence** — `.gitlab-ci.yml` on master runs `visualstudio/x86_64` and `visualstudio/x86` jobs on GitLab `saas-windows-medium-amd64` runners, plus mingw64/mingw32 (Wine) legs. README: GCC/Clang/MSVC/MinGW.
- **Form:** compiled library (static/shared), CMake-built; Meson support added in 2.0.0.
- **Features:** the differentiator is **mocking** (`will_return`/`mock()`, `expect_*`/`check_expected`) — unique in this set. Per-test and per-group setup/teardown; no first-class parameterized tests (state pointers are the idiom); signal handling (SIGSEGV/SIGILL reported as failures); output: stdout, **TAP-14 (+YAML diagnostics), JUnit XML, Subunit**.
- **Maintenance: active, major line just shipped.** Verified from cmocka.org/files: 1.1.7 = 2023-02-23, 1.1.8 = 2025-07-17, **2.0.0 = 2025-12-04, 2.0.1 = 2025-12-19, 2.0.2 = 2026-01-12** (latest). Commits Feb 2026; GitLab activity 2026-06-15. Institutional users: Samba, libssh, coreboot, BIND, OpenVPN, Knot DNS, SSSD, Netdata.
- **Sanitizer/CTest:** excellent — README explicitly "**No fork()**"; single-process with signal/SEH handling; natural per-suite-executable CTest fit; TAP/JUnit for dashboards.
- **Vendoring:** proper CMake project (`find_package`/FetchContent-able), distro-packaged everywhere — a real dependency, not a drop-in.
- **Version-scheme note:** master CMakeLists says `VERSION 1.9.0` — that's the libssh-style odd-minor dev version for the 2.x line; the `cmocka-2.0.2` tag correctly says 2.0.2.

## 13. Criterion (Snaipe) — brief

Repo: <https://github.com/Snaipe/Criterion>

- MIT; C99/C++11. README claims Windows/VS2015+, **but the Windows x86-64 CI leg is currently commented out** in `.github/workflows/ci.yml` (active: Ubuntu, macOS AArch64, Debian, Fedora, Alpine).
- Compiled with heavy deps (BoxFort, libffi, nanomsg, dyncall…), Meson-built; not FetchContent-friendly.
- Best ergonomics of the set: automatic registration, default main, fixtures, parameterized tests + theories, TAP.
- Maintained slowly: v2.4.3 = 2025-10-14; commits 2026-06-12; single-maintainer; 80 open issues.
- **Structural disqualifier:** **fork/exec-per-test via BoxFort is the core design, with no documented no-fork mode** (Valgrind needs `--trace-children=yes`) — worst possible fit for a mandatory ASan/TSan matrix; BoxFort has arch-sensitivity issues (#198 32-bit, #376 Apple M1).

## 14. utest.h (sheredom) — brief

Repo: <https://github.com/sheredom/utest.h>

- **License:** Unlicense (public domain; no MIT alternative offered — occasionally bothers corporate legal).
- **C standard:** feature-gated on `__STDC_VERSION__` (C99/C11 checks with fallbacks; `_Generic` printing only under C11); explicit old-MSVC (`_MSC_VER < 1920`) and tcc handling.
- **MSVC: yes, with CI evidence** — `.github/workflows/cmake.yml` matrix includes `windows-latest` with default cl.exe, `-T ClangCL`, and MinGW, across 4 build types (+ubuntu gcc/clang/tcc, macOS).
- Single header; **automatic registration** (GCC/Clang constructor attribute; MSVC `.CRT$XCU` section, header line 253); `UTEST_MAIN()`; fixtures `UTEST_F` + setup/teardown; indexed fixtures `UTEST_I` (lightweight parameterization); `--filter`, `--list-tests`, `--random-order[=seed]`, xunit XML output.
- **Maintenance:** active (commits **2026-06-15**, "Sort tests by source location"). **Surprise:** the only tag ever is **`pre-ai`** (2026-06-04) — README's new "AI Usage" section permits AI-assisted commits; the tag marks the last AI-free state. **No semver releases** — vendoring = pinning a commit, and the AI-policy question is left to the adopter's audit posture.
- Single process, no fork — sanitizer-friendly; single runner exe with `--filter` for CTest splitting.

## 15. Minimal dynamic-array / string libs

### sds (antirez) — Simple Dynamic Strings

Repo: <https://github.com/antirez/sds>

- **License discrepancy:** root LICENSE classifies as BSD-2-Clause, but per-file headers in `sds.c`/`sdsalloc.h` carry BSD-3-Clause text **with a non-endorsement clause** ("Neither the name of Redis…") and Oran Agra / Redis Labs copyrights. Effective grant: 3-clause per-file.
- C99 (flexible array members). **MSVC-hostile:** every `sdshdr` struct uses `__attribute__((__packed__))` and printf-format attributes — GCC/Clang only; needs a `#pragma pack` port for cl.exe. No CI at all.
- Not header-only (`sds.c/.h` + `sdsalloc.h`). Allocator injection: yes, compile-time `s_malloc`/`s_realloc`/`s_free` in `sdsalloc.h`.
- **Dormant:** only 2025 commit is a Makefile fix (#153); substantive history ends 2022 ("Merge general improvements from Redis"). **The living sds is inside Redis/Valkey** (`src/sds.c` there); the standalone repo is a stale snapshot.

### c-vector (eteran)

Repo: <https://github.com/eteran/c-vector>

- **MIT** (header: Copyright 2015 Evan Teran). **C89** (per README). Single header (`cvector.h` + optional `cvector_utils.h`).
- **Complete allocator injection:** `cvector_clib_malloc/free/realloc/calloc` + `assert/memcpy/memmove` overrides, `#ifndef`-guarded (lines 14–42) — the fullest injection surface in this audit.
- CI is ubuntu+macos only (workflow comment says "should work equally well on Windows" but doesn't test it).
- **Active:** pushed 2026-06-12 (C++ support #94; `cvector_data()` #93 2026-03; NULL-resize fix #92 2025-11). **0 open issues.** No tagged releases (rolling).
- **Verdict:** the best-behaved small dynamic-array option for these constraints; only gap is no upstream MSVC CI.

## 16. Interval-tree offerings in pure C

### cgranges (lh3 / Heng Li) — implicit augmented interval tree

Repo: <https://github.com/lh3/cgranges>

- **MIT** (Copyright 2019 Dana-Farber Cancer Institute). C99 (stdint, bitfields). No CI; no obviously MSVC-hostile constructs, but unverified.
- **Not header-only in C:** `cgranges.h` + `cgranges.c`, and it **bundles its own `khash.h`** (contig-name dictionary). A header-only **C++** variant exists (`cpp/IITree.h`).
- **No allocator injection** — `cr_init/cr_add/cr_index/cr_destroy` use libc malloc/realloc directly.
- Dormant: last commit 2024-05-28 ("added citation"); last release v0.1.1 = 2023-09-24.
- **The decisive architectural fact:** strictly **build-once / query-many** — `cr_add()` (append) → `cr_index()` (sort + build implicit tree) → `cr_overlap()`/`cr_contain()`. **No insert-after-index, no delete API at all**; any mutation requires full re-index (re-sort of the entire array).

### NCList / AIList / others

- **NCLS** (<https://github.com/pyranges/ncls>, the maintained NCList C/Cython implementation used by pyranges): build-once/query-many, no online mutation.
- **AIList** (<https://github.com/databio/AIList>): C, fast, permissive — again a static index (decompose → sort → query).
- Erik Garrison's `IntervalTree.h`: C++ header-only, not C.
- **General finding:** every mature standalone C interval library in this space is optimized for bulk-load-then-query genomics workloads. **None offers an online insert+delete mutable interval set**, and none does merge-on-insert canonicalization. Timelog's tombstone model (sorted, coalesced, half-open `[start,end)` set with incremental add) has no off-the-shelf C replacement; the in-house coalescing interval set remains the right structure.

## 17. Pure-C k-way merge / LSM building blocks

**Conclusion: no mature, maintained pure-C LSM-component library (k-way merge iterators, loser trees, SSTable/segment abstractions) exists as an adoptable dependency in 2026.** Findings:

- **SQLite4 LSM / `ext/lsm1`** — the one credible pure-C LSM in existence (`lsm.h`, "roughly similar in scope to… LevelDB", lives at `ext/lsm1/` in the SQLite repo). **Explicitly disowned by its own developers**: forum statements call it "an experimental extension from over a decade ago… not used or supported"; devs "not interested in supporting it." Also a whole disk-backed engine, not a component library; had a reported OOB read in checkpoint parsing. Not adoptable. (<https://sqlite.org/src4/doc/trunk/www/lsmusr.wiki>, <https://www.sqlite.org/src/dir?name=ext/lsm1>, <https://sqlite.org/forum/info/7f10e4d18e0e2c946e9364a15d9d6f2f7b4bca9774a7bdb92f0d5ba94f82f941>)
- **klib** — offers heap primitives (`ksort.h`), not a merge iterator; no LSM primitives.
- **LevelDB / RocksDB** — C++ engines exposing C APIs; merge iterators are C++ internals, not extractable as pure C. Engine adoption out of scope; confirmed no pure-C sibling of note.
- **LMDB** — pure C and mature, but a memory-mapped COW **B-tree** engine (not LSM), OpenLDAP Public License. Noted for completeness only.
- **UnQLite** — embedded C KV/document engine, Symisc dual-licensing; not a component library; out of scope.
- No standalone "kmerge"/loser-tree C library of any credibility surfaced.

**Timelog's in-house `tl_submerge`/`tl_merge_iter` has no off-the-shelf pure-C replacement.**

---

## Meta-Question A — Pure-C CPython extension boilerplate helpers

**VERDICT: prior CONFIRMED. No mature pure-C boilerplate-reduction library exists as of mid-2026.**
pythoncapi-compat is the only broadly adopted helper, and it is a compatibility polyfill, not a
framework. The hand-rolled Layer A/B code (heap types, PEP 489 multi-phase init, PEP 573 module
state, `Py_mod_gil`) is the officially sanctioned state of the art.

- **pythoncapi-compat** (<https://github.com/python/pythoncapi-compat>): single header + upgrade script that backfills *new* C API onto *old* Pythons — the inverse of a boilerplate framework; wraps nothing for heap types/multi-phase init/module state/critical sections. **License: 0BSD** (changed from MIT 2022-02-11 — no attribution needed when vendoring). Actively maintained and now **semi-official** (hosted under the `python` GitHub org; last push 2026-03-19; 1 open issue). Worth vendoring only if targeting older CPythons with newer API calls. (<https://pythoncapi-compat.readthedocs.io/en/latest/changelog.html>)
- **HPy** (<https://github.com/hpyproject/hpy>): **effectively dormant, not production-viable.** Last release 0.9.0 (2023-09-22), still explicitly "the latest **alpha**"; repo `pushed_at` = 2025-05-26 — 13+ months of zero pushes; **no free-threading support or plan** (issue/PR search for "free-threading" returns nothing; absent from <https://py-free-threading.github.io/> ecosystem tracking). Website still claims "active development" — contradicted by the API data. Adopting it for cp312–cp314+cp314t wheels would be a dead end.
- **Others, all negative:** "picobind" — does not exist (searches resolve to pybind11/nanobind, both C++). **PyBindGen** — dead (last release 0.22.1, 2022-03-30; "Inactive"; targets C++ anyway). **Argument Clinic** — explicitly internal-only: "Its use is not supported for files outside CPython" (<https://devguide.python.org/development-tools/clinic/>). PyO3 — Rust, out of scope.
- **Core-dev guidance recommends no library:** the official "Isolating Extension Modules" HOWTO (successor to PEP 630) walks through `PyType_FromModuleAndSpec`, `METH_METHOD` + `defining_class` + `PyType_GetModuleState`, and `m_traverse`/`m_clear`/`m_free` **by hand**, conceding "Adding them will require some work and make the code longer; this is the price for modules which can be unloaded cleanly" (<https://docs.python.org/3/howto/isolating-extensions.html>). The free-threading HOWTO likewise hands you raw `Py_BEGIN_CRITICAL_SECTION` macros (<https://docs.python.org/3/howto/free-threading-extensions.html>). PEP 733 catalogs the boilerplate pain but no framework has shipped from that effort (<https://peps.python.org/pep-0733/>).

## Meta-Question B — MSVC + C11/C17 atomics in 2026

**VERDICT: still experimental — in both the latest VS 2022 (17.x) and VS 2026 (18.x / MSVC 14.51,
May 2026). `__STDC_NO_ATOMICS__` is still defined, locking atomics remain unimplemented, and
Microsoft has published no graduation. The hand-rolled `tl_atomic.h` (Interlocked-based) shim
remains load-bearing.**

- **`/experimental:c11atomics`**: introduced in **VS 2022 17.5 Preview 2** (blog 2022-12-13); requires `/std:c11` or `/std:c17`; provides `<stdatomic.h>`, `_Atomic(T)`, `_Atomic` qualifier. **Only lock-free atomics implemented** — locking (e.g. large `_Atomic` structs) deferred to "an upcoming release" that never fully materialized; no documented 128-bit/DCAS. **`__STDC_NO_ATOMICS__` stays defined even with the flag on** "until locking atomics are implemented", so standard feature detection reports *no atomics*. (<https://devblogs.microsoft.com/cppblog/c11-atomics-in-visual-studio-2022-version-17-5-preview-2/>)
- **Still experimental in the latest releases — multiply confirmed:**
  1. MS "What's new for C++" lists exactly one atomics entry — the 17.5 experimental one; nothing later graduates it (<https://learn.microsoft.com/en-us/cpp/overview/what-s-new-for-visual-cpp-in-visual-studio>).
  2. The `/std` docs (ms.date 2025-01-29): "There's no conforming multithreading, atomic, or complex number support" (<https://learn.microsoft.com/en-us/cpp/build/reference/std-specify-language-standard-version>) — note this sentence is partially stale re: threads (see below); use it only alongside the other anchors.
  3. Microsoft Q&A answer (2024-10-10) confirms `__STDC_NO_ATOMICS__` still defined with the flag; recommended detection is a test-compile (<https://learn.microsoft.com/en-us/answers/questions/2100492/how-can-i-check-for-experimental-c11atomics-flag-i>).
  4. **VS 2026 exists** (18.x; MSVC 14.50 with 18.0 on 2025-11-11; **14.51 GA 2026-05-12**). Its entire C-atomics content in the notes is one line: "**Added `_Atomic` qualifier support**…" — Microsoft was still filling in basic C11-atomics *front-end* pieces in May 2026; no graduation statement anywhere (release notes, 14.51 blogs, conformance page updated 2026-05-13). (<https://learn.microsoft.com/en-us/visualstudio/releases/2026/release-notes>, <https://devblogs.microsoft.com/cppblog/msvc-version-1451-available/>, <https://learn.microsoft.com/en-us/cpp/overview/msvc-conformance-improvements?view=msvc-180>)
  5. Current ecosystem guidance (py-free-threading porting guide, Aug 2025): "MSVC does not officially support C atomics yet, but it is possible to enable experimental support… using `/experimental:c11atomics`" (<https://py-free-threading.github.io/porting-extensions/>).
  6. Real-world 2026 friction: aws-lc-rs #961 (2025-11-24, affects VS 2022 **and** VS 2026) — VS 2026 ships `vcruntime_c11_stdatomic.h` that hard-errors without `/std:c11`; C11 feature detection on MSVC remains fragile (<https://github.com/aws/aws-lc-rs/issues/961>).
- **Contrast:** C11 `<threads.h>` shipped **non-experimental** in VS 2022 17.8 (`vcruntime140_threads.dll`) — atomics conspicuously never got the same graduation (<https://devblogs.microsoft.com/cppblog/c11-threads-in-visual-studio-2022-version-17-8-preview-2/>).
- **clang-cl is a viable escape hatch** — clang ships a complete `<stdatomic.h>` on `__c11_atomic_*` builtins, full C11 atomics on Windows; named as the alternative in the free-threading compatibility discussion. Caveat: a toolchain change with its own `/WX` warning surface. (<https://github.com/Quansight-Labs/free-threaded-compatibility/issues/244>, <https://github.com/dotnet/runtime/issues/91748>)
- **CPython's own practice confirms the shim pattern:** `Include/cpython/pyatomic_msc.h` opens with "This is the implementation of Python atomic operations for MSVC if the compiler does not support C11 or C++11 atomics" and builds everything on `_InterlockedExchange`/`_InterlockedCompareExchange` — CPython itself and the extension ecosystem run on Interlocked-based shims on Windows; MSVC C11 atomics are load-bearing nowhere in this stack. (<https://github.com/python/cpython/blob/main/Include/cpython/pyatomic_msc.h>)
- **Traps flagged during verification:** (1) VS 2026's "_Atomic qualifier support" line is a misread trap — narrow front-end completion, not graduation; (2) there is **no MS Learn page for `/experimental:c11atomics` at all** (URL 404s; absent from the compiler-options index) — 3.5 years documented only by one blog post is itself a limbo signal; (3) the `/std` docs' "no multithreading" sentence is stale re: `<threads.h>`, so don't cite it alone.

---

## Cross-Cutting Conclusions

1. **Concurrency primitives:** all three candidates fail a hard constraint — ck (MSVC hard-fail + TSan-blind default asm), liburcu (LGPL + Cygwin-only Windows), liblfds (dead since 2017). The in-house `internal/` sync/seqlock/Treiber-stack/ring primitives have no adoptable replacement for this wheel matrix.
2. **The single clean pass:** **mattconte/tlsf** — BSD-3, MSVC in-code first-class, two-file vendor, zero atomics (perfect TSan), matches the caller-locks model. Cost: dormant since 2020, so vendoring = owning ~1.2 kLOC after audit.
3. **Containers:** khash (MIT, allocator-injectable) and c-vector (MIT, full allocator surface, active, 0 issues) are the only container libs meeting the custom-allocator bar. stb_ds is disqualified for strict `-std=c17` by its `typeof` dependency (#1735) and its dead `context` parameter; kvec/kbtree hardcode libc alloc; CCAN requires per-module GPL/LGPL contamination auditing.
4. **Test frameworks:** cmocka (2.0.2, Jan 2026, MSVC CI, no-fork, Apache-2.0) and utest.h (Unlicense, MSVC+ClangCL CI, no fork, auto-registration, but unversioned + AI-policy question) are the two live fits; munit is abandoned (frozen 2020, never 1.0), greatest dormant, Criterion structurally disqualified (mandatory fork/exec-per-test).
5. **Interval sets & merge machinery:** nothing exists. All C interval libraries (cgranges/AIList/NCLS) are static build-once indexes with no insert/delete; no pure-C k-way-merge/LSM-component library exists (the closest artifact, SQLite lsm1, is disowned by its own authors). Tombstone interval set and `tl_submerge`/`tl_merge_iter` stay in-house by necessity, not preference.
6. **CPython boilerplate & atomics shim:** both hand-rolled layers are validated as necessary — no pure-C binding helper exists (HPy is dormant/alpha/no-3.14t; pythoncapi-compat is a polyfill), and MSVC C11 atomics remain experimental through VS 2026 18.7 (June 2026), with CPython itself shipping an Interlocked shim.
