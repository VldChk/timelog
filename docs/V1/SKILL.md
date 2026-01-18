---
name: c-timelog-engineering
description: |
  High-performance C development for data-intensive systems, with explicit emphasis on
  time-indexed / log-structured in-memory engines (e.g., Timelog-class designs).
  Use when building advanced data structures, algorithms, or libraries in C with focus on:
  memory efficiency, cache locality, immutable segment layouts, atomic publication, snapshot reads,
  SIMD/bit operations, and (future) Python bindings.

  Applies to: custom allocators, paged/segment storage, compression and bitmaps, index structures,
  single-writer/multi-reader concurrency patterns, background maintenance (flush/compaction),
  and performance-critical library development.
---

# High-Performance C Development

This skill is a “theoretical + practical” checklist for engineers who write **fast, safe, maintainable C**
for **data-intensive systems**—especially systems that look like Timelog: sorted runs, pages/segments,
range queries, tombstones, and atomic publication.

It assumes you already understand basic C syntax. The goal here is competence at the level where you
can implement sophisticated, performance-oriented designs **without introducing undefined behavior,
data races, or fragile micro-optimizations**.

The document is intentionally written as “ready-to-open and learn” material.

---

## What “high-performance C” actually means

Performance in modern systems is dominated by a short list of realities:

1. **Memory dominates compute** for most real workloads. Avoiding cache misses and pointer chasing
   frequently beats shaving a handful of instructions.
2. **Correctness is a prerequisite**. A fast data structure with undefined behavior (UB) is a time bomb.
3. **Predictability matters**. Fast steady-state performance is valuable; eliminating latency spikes
   (e.g., by avoiding stop-the-world maintenance) is often even more valuable.
4. **Measurement is part of engineering**. If you can’t profile, you can’t optimize.

---

## Standards and portability

### Target standard

- **Primary**: C17 (ISO/IEC 9899:2018)
- **Optional additions**: C23 features where compiler support exists
- Compile with `-std=c17` (or `-std=c23` when available)
- Use `#if __STDC_VERSION__ >= 202311L` guards for C23 features

### C23 features worth adopting (with fallbacks)

```c
// Attributes (safe to use now with fallback macros)
[[nodiscard]] int compute_hash(const void *data, size_t len);
[[maybe_unused]] static void debug_dump(const ctx_t *ctx);
[[deprecated("use v2_create")]] ctx_t *create(void);

// nullptr (with fallback)
#if __STDC_VERSION__ >= 202311L
    #define MY_NULL nullptr
#else
    #define MY_NULL ((void*)0)
#endif

// constexpr for compile-time constants
#if __STDC_VERSION__ >= 202311L
    constexpr size_t CACHE_LINE = 64;
#else
    #define CACHE_LINE 64
#endif
```

### Portability mindset

Performance code tends to “accidentally” become platform-specific. The right mindset is:

- Keep **portable baseline** always correct.
- Add platform-specific fast paths via:
  - compile-time detection (`#if defined(__AVX2__)`, etc.)
  - runtime dispatch (`__builtin_cpu_supports`)
- Maintain “one source of truth” semantics: fast paths must match baseline results exactly.

### Avoid these

- Variable-length arrays (VLAs) in production code—stack overflow risk, unpredictable stack usage.
- `gets()`, `sprintf()`, `strcpy()` without bounds—use `snprintf()`, `memcpy()` with validated sizes.
- Implicit function declarations—always include proper headers.
- K&R function definitions—use prototypes.
- “It seems to work” reliance on UB (strict aliasing, out-of-bounds, signed overflow).

---

## C correctness fundamentals that directly impact performance

### Undefined behavior (UB) and why it matters

UB is not “maybe wrong.” It is **permission for the compiler to assume it never happens** and optimize
accordingly. In performance builds (`-O2/-O3`), UB often becomes miscompilation.

You must be fluent in the common UB sources:

- Out-of-bounds reads/writes (even one byte).
- Signed integer overflow.
- Using uninitialized values.
- Violating alignment requirements (e.g., misaligned `int64_t*` access).
- Strict aliasing violations (treating memory as unrelated pointer types).
- Data races (non-atomic concurrent access to shared state).

Practical rule: if you cannot explain why the code is defined by the standard, do not ship it in a
high-performance library.

### Integer and timestamp discipline (important for Timelog-class systems)

When timestamps are `int64_t`:

- Decide upfront whether you treat them as:
  - **signed epoch** (allow negative for pre-epoch) or
  - **non-negative only** (enforced by validation)
- Be explicit about unit (s/ms/us/ns) and **never silently mix units**.
- Avoid overflow in computations like `now - duration`:
  - validate ranges,
  - clamp or return `TL_EINVAL` when out of range.

### `restrict`, aliasing, and enabling the compiler

Competent performance engineers know when to use:

- `const` for semantic immutability (also helps optimization).
- `restrict` for non-aliasing guarantees in hot loops.

```c
void scale(float *restrict out,
           const float *restrict in,
           float factor, size_t n) {
    for (size_t i = 0; i < n; i++) out[i] = in[i] * factor;
}
```

### `volatile` vs atomics

- `volatile` is not a concurrency primitive.
- Use C11 `_Atomic` and the memory model for synchronization.
- Use `volatile` only for:
  - memory-mapped I/O,
  - signal-safe shared flags (with constraints),
  - preventing compiler optimizations in very specific cases.

---

## Memory architecture (the dominant performance lever)

### Cache hierarchy awareness

Modern x86 cache lines are typically 64 bytes (Apple M-series often uses 128 bytes).

Design implications:

- Strive to keep “hot metadata” in a cache line.
- Avoid false sharing across threads.

```c
// BAD: False sharing between threads
struct counters {
    uint64_t thread0_count;  // Same cache line!
    uint64_t thread1_count;
};

// GOOD: Padding prevents false sharing
struct counters {
    _Alignas(64) uint64_t thread0_count;
    _Alignas(64) uint64_t thread1_count;
};
```

### Data-oriented design: AoS vs SoA

Array-of-Structs (AoS) wastes cache when scanning one field across many records.
Struct-of-Arrays (SoA) keeps scans tight and SIMD-friendly.

```c
// AoS: poor for scanning one field across many records
struct point_aos { float x, y, z, w; };
struct point_aos points[N];

// SoA: excellent for columnar access
struct points_soa { float *x, *y, *z, *w; };
```

For Timelog-like designs, the SoA lesson generalizes:

- The hot loop compares timestamps (keys) far more often than it touches payloads.
- Store timestamps contiguously; keep handles/payloads in a parallel array.

### Prefetching, TLBs, and working set

Practical proficiency includes:

- Understanding that random access across a huge array is limited by cache/TLB misses.
- Designing **two-level navigation** (catalog/fence pointers + within-page search) so that most accesses
  are localized to a small “index” structure and then a sequential scan.

### NUMA awareness (server-class systems)

If you care about very high throughput:

- Know what NUMA is (multiple memory domains).
- Know that allocating on one socket and reading on another can be costly.
- Initial versions may ignore NUMA, but the engineer should at least recognize the symptoms in profiling.

---

## Memory allocation patterns (performance + correctness)

### Core principle

Avoid `malloc/free` in hot loops. Prefer:

- preallocation,
- arenas,
- pools,
- slab allocators,
- per-thread caches where relevant.

### Arena allocators (bump allocators)

Great for batch allocations and “build-then-publish” workflows (e.g., page/segment construction):

```c
typedef struct {
    uint8_t *buf;
    size_t capacity;
    size_t offset;
} arena_t;
```

Key skill: design arena ownership around lifetimes:

- Builder arena: used while constructing a segment; freed after publish.
- Snapshot arena: used for temporary query plan allocations.

### Pool allocators (freelists)

Best for fixed-size objects (iterators, small structs):

```c
typedef struct pool_block { struct pool_block *next; } pool_block_t;
typedef struct { pool_block_t *free_list; size_t block_size; uint8_t *storage; } pool_t;
```

### “Slab” allocations for contiguous blocks

Many high-performance engines allocate a page as one slab containing:

- the page header,
- the timestamp array,
- the handle array,
- optional metadata.

You should be comfortable reasoning about alignment and pointer arithmetic to build this safely.

### Production allocators

Know when the default allocator becomes a bottleneck and what alternatives exist:

- **jemalloc** (fragmentation control)
- **tcmalloc** (thread-caching)
- **mimalloc** (locality)

The skill is not “always use X,” but “know how to evaluate allocator impact.”

---

## Concurrency and atomic publication (critical for Timelog-class designs)

Even if your external contract is single-writer, internal background maintenance introduces
concurrency hazards that require real competence.

### C11 atomics: minimum competence

You must understand:

- `_Atomic(T)` and atomic operations
- memory orders:
  - `memory_order_relaxed`
  - `memory_order_release`
  - `memory_order_acquire`
  - `memory_order_acq_rel`
  - `memory_order_seq_cst`
- what a data race is and why it is UB in C

### Atomic pointer publication

A common pattern in snapshot systems:

- Build a new immutable structure off-thread/off-lock.
- Publish it with an atomic swap.
- Readers obtain a stable pointer by acquiring a reference.

The skill is knowing which memory order is required:

- Writer publishes with **release**
- Reader loads with **acquire**
- That establishes a “happens-before” relation so readers see a fully initialized structure.

### Seqlock-style coordination

When you have *two* independently published roots (e.g., manifest pointer + memtable view),
you may need a lightweight protocol to prevent readers from observing inconsistent combinations.

A common technique is a seqlock-like “even/odd sequence” counter:

- Publisher makes seq odd → performs updates → makes seq even.
- Readers retry if they observe odd or mismatch.

Engineers must be able to reason about:

- progress properties (retry loops),
- starvation risk,
- memory ordering guarantees.

### Safe reclamation (RCU / epochs / hazard pointers)

Atomic swap is easy. Safe freeing is hard.

If readers can hold snapshots that reference old manifests/segments:

- You cannot free old objects immediately after publication.
- You need a reclamation strategy.

Minimum competence includes understanding at least one of:

- reference counting (simple but can be expensive; beware cycles)
- epoch-based reclamation (QSBR-style)
- hazard pointers
- RCU-like patterns

The “right choice” depends on workload and implementation, but an engineer must be able to implement
one correctly and test it.

### Threading primitives

Even if you wrap threads behind a small abstraction, engineers must know:

- mutexes and condition variables (or equivalents)
- how to avoid deadlocks:
  - lock ordering
  - minimal critical sections
- how to avoid priority inversion and long stop-the-world pauses
- how to design background work that is cooperative and bounded when needed

---

## Algorithms and low-level data structure skills that matter in C

### Binary search: lower_bound correctness

You should be able to implement `lower_bound` for `int64_t` arrays without off-by-one errors,
and understand how half-open ranges `[t1, t2)` map to:

- `i1 = lower_bound(t1)`
- `i2 = lower_bound(t2)`
- scan `i1..i2`

### K-way merge (iterator merge)

A Timelog-class read path often merges multiple sorted iterators:

- memtable view iterators
- delta segment iterators
- main segment iterators

To implement this in C efficiently, you must know:

- min-heap / priority queue implementation
- stable vs unstable ordering and what your semantics require
- how to structure iterators to avoid per-row virtual dispatch overhead

### Interval sets and coalescing (tombstones)

Time-range deletes are naturally represented as intervals `[t1, t2)`.

Competence requirements:

- maintain a sorted, non-overlapping interval set
- coalesce overlapping and adjacent intervals
- reason about boundary semantics (half-open)

This is the algorithmic foundation behind efficient retention/eviction.

### Bit operations and bitsets

Even if V1 uses tombstone intervals, future versions may add bitsets/bitmaps.
You should know:

- word-at-a-time bit operations
- `popcount`, `ctz`, `clz` primitives
- iterating set bits efficiently

---

## SIMD vectorization (useful, but only when it fits)

### Auto-vectorization

Enable with compiler flags and write vectorization-friendly loops:

```bash
# GCC/Clang
-O3 -march=native -ftree-vectorize

# Debug vectorization failures
-fopt-info-vec-missed            # GCC
-Rpass-missed=loop-vectorize     # Clang
```

Vectorization requirements:

- simple loops (single entry/exit)
- no loop-carried dependencies
- no hidden aliasing (use `restrict`)
- preferably aligned access

### Manual SIMD with intrinsics

For hot paths that are proven bottlenecks:

- compare timestamps in blocks
- accelerate bitset filtering
- accelerate copies during page build

If you use intrinsics, you must also implement:

- scalar fallback
- runtime dispatch (or compile-time selection)

### SIMD realism for Timelog

Timelog V1 is not “vectorized analytics on payloads.”
The primary SIMD wins are typically:

- fast comparisons on timestamp arrays
- fast filtering/mask application when needed

---

## Branch prediction and control-flow engineering

### Likely/unlikely hints

```c
#define likely(x)   __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
```

Use hints only when the skew is strong and stable (fast path is truly dominant).

### Branchless programming

Know the technique, but use it judiciously. Branchless code is not automatically faster;
it helps when branches are unpredictable and expensive.

---

## Error handling and resource management

### The “goto cleanup” pattern

In C, a single cleanup path prevents leaks and makes failure cases auditable.

```c
int init_system(...) {
    int rc = -1;
    A *a = NULL; B *b = NULL;

    a = alloc_a(); if (!a) goto out;
    b = alloc_b(a); if (!b) goto out;

    rc = 0;
out:
    if (rc != 0) { free_b(b); free_a(a); }
    return rc;
}
```

### Status codes and diagnostics

A robust performance library:

- uses small error enums for hot paths,
- optionally provides a thread-local “last error string” or debug logging for diagnosis.

Engineers must be able to design “cheap by default, informative when needed.”

---

## API and ABI design (library engineering discipline)

### Opaque pointers and encapsulation

This is non-negotiable for a reusable library:

- public headers expose opaque types
- internal structs are private

### Ownership and lifetime contracts

For each handle returned by the API, the engineer must be able to answer:

- Who owns this memory?
- When can it be freed?
- Is it valid across snapshots?
- Is it valid across background maintenance?

### Versioning and ABI stability

If you intend to publish a shared library:

- namespace all symbols (`tl_*`)
- avoid exposing struct layouts in headers
- consider semantic versioning
- consider symbol visibility controls (`-fvisibility=hidden`)

---

## Python C extension patterns (future integration)

Timelog V1 core is handle-based; Python integration is a later phase.
Still, an engineer working on the core should understand:

- CPython reference counting (`Py_INCREF`, `Py_DECREF`)
- GIL rules and safe GIL release for pure C work
- buffer protocol and zero-copy for arrays
- how to expose opaque C pointers via capsules

The key conceptual skill is to **avoid contaminating the core with Python semantics**:
keep a clean boundary (payload handles + callbacks).

---

## Build, tooling, and verification

### Compiler warnings and hygiene

Use aggressive warnings and treat them as errors in CI for the core library.

### Sanitizers (non-negotiable during development)

- AddressSanitizer (ASan)
- UndefinedBehaviorSanitizer (UBSan)
- ThreadSanitizer (TSan) when you introduce background threads

### Static analysis

- clang-tidy (bugprone, cert, analyzer, performance checks)
- compiler static analyzer

### Fuzzing and property tests

For complex merge / tombstone / boundary logic:

- fuzz range queries vs a simple reference model
- property tests for invariants (sortedness, half-open correctness, coalescing)

---

## Profiling and performance methodology

A high-performance C engineer must be comfortable with:

- microbenchmarks (stable harness, pinned CPU, warmups, multiple runs)
- `perf` / hardware counters:
  - cache misses
  - branch misses
  - cycles/instructions
- flame graphs
- reasoning about “why” a change helped

A common failure mode is optimizing the wrong thing. The skill is to instrument, measure,
and iterate.

---

## Timelog-specific competency checklist

An engineer is “ready” to implement Timelog-class designs when they can:

- Build immutable, contiguous pages with SoA layout (timestamp array + handle array).
- Implement correct binary search boundaries and half-open range scans.
- Maintain tombstone interval sets with coalescing and strict `[t1, t2)` semantics.
- Implement snapshot-safe publication:
  - atomic manifest swap,
  - consistent snapshot acquisition even when memtable and manifest update independently.
- Implement safe reclamation of old immutable structures (refcount or epochs).
- Implement efficient iterators and k-way merge without excessive allocation or function-call overhead.
- Design background maintenance that avoids stop-the-world latency spikes.

If an engineer lacks any one of these competencies, the project is at high risk.

---

## Recommended reading (high ROI)

These are “best bang for time” references for the skills above:

- **Effective C** (core language correctness and idioms)
- **Modern C** (modern C style and correctness discipline)
- **Write Great Code, Vol 1–2** (low-level optimization mindset)
- **Systems Performance** (observability, measurement, CPU/memory realities)
- **CPython Internals** (when you move toward Python bindings)
- Research papers / docs relevant to time-indexed systems:
  - LSM-tree fundamentals
  - roaring bitmaps
  - cache-friendly tree structures (ART)

---

## Checklist before shipping performance-critical code

1. **Correctness / UB**
   - [ ] UBSan clean, no undefined behavior
   - [ ] ASan clean, no leaks or overflows
   - [ ] Clear ownership/lifetime rules

2. **Concurrency**
   - [ ] No data races (TSan clean where applicable)
   - [ ] Atomic publication uses correct memory ordering
   - [ ] Reclamation strategy proven by tests

3. **Memory layout**
   - [ ] Hot metadata is compact
   - [ ] Contiguous arrays for hot scans
   - [ ] Minimal pointer chasing

4. **Algorithmic complexity**
   - [ ] Hot paths are O(1) amortized or O(log n) where appropriate
   - [ ] Merge width bounded (operational controls exist)

5. **Measurement**
   - [ ] Profiling confirms the chosen optimizations matter
   - [ ] Benchmarks are reproducible and documented
