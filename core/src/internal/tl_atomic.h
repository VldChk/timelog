#ifndef TL_ATOMIC_H
#define TL_ATOMIC_H

#include "tl_platform.h"
#include <stdint.h>
#include <stdbool.h>

/*===========================================================================
 * Compiler and Standard Detection
 *
 * C17 (201710L) is a superset of C11 (201112L) with bug fixes.
 * All supported toolchains provide <stdatomic.h>:
 * - GCC/Clang: always in C11+ mode.
 * - MSVC: VS2022 17.5+ with /experimental:c11atomics (supplied by the
 *   build system for every target). The shipping Windows wheels have
 *   compiled the binding this way since v1.0.0 — py_handle.c uses
 *   _Atomic directly and hard-#errors on __STDC_NO_ATOMICS__ — so the
 *   core sharing the same backend widens an existing, release-proven
 *   dependency rather than adding a new one. (D1, audit 2026-07.)
 *===========================================================================*/

#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L && !defined(__STDC_NO_ATOMICS__)
    #define TL_HAS_C11_ATOMICS 1
    #include <stdatomic.h>
#endif

/*===========================================================================
 * Atomic Types
 *
 * We define our own types to ensure consistent semantics across platforms.
 * These are sized for specific use cases:
 * - tl_atomic_u32: reference counts, flags
 * - tl_atomic_u64: seqlock counter, large counters
 *===========================================================================*/

#if defined(TL_HAS_C11_ATOMICS)

typedef _Atomic uint32_t tl_atomic_u32;
typedef _Atomic uint64_t tl_atomic_u64;

/*===========================================================================
 * Memory Order Aliases
 *===========================================================================*/

#define TL_MO_RELAXED memory_order_relaxed
#define TL_MO_ACQUIRE memory_order_acquire
#define TL_MO_RELEASE memory_order_release
#define TL_MO_ACQ_REL memory_order_acq_rel
#define TL_MO_SEQ_CST memory_order_seq_cst

/*===========================================================================
 * Atomic Operations - C11 Implementation
 *===========================================================================*/

/* Initialize */
#define tl_atomic_init_u32(ptr, val) atomic_init((ptr), (val))
#define tl_atomic_init_u64(ptr, val) atomic_init((ptr), (val))

/* Load */
TL_INLINE uint32_t tl_atomic_load_u32(const tl_atomic_u32* ptr, int order) {
    return atomic_load_explicit((tl_atomic_u32*)ptr, order);
}

TL_INLINE uint64_t tl_atomic_load_u64(const tl_atomic_u64* ptr, int order) {
    return atomic_load_explicit((tl_atomic_u64*)ptr, order);
}

/* Store */
TL_INLINE void tl_atomic_store_u32(tl_atomic_u32* ptr, uint32_t val, int order) {
    atomic_store_explicit(ptr, val, order);
}

TL_INLINE void tl_atomic_store_u64(tl_atomic_u64* ptr, uint64_t val, int order) {
    atomic_store_explicit(ptr, val, order);
}

/* Fetch-Add (returns old value) */
TL_INLINE uint32_t tl_atomic_fetch_add_u32(tl_atomic_u32* ptr, uint32_t val, int order) {
    return atomic_fetch_add_explicit(ptr, val, order);
}

TL_INLINE uint64_t tl_atomic_fetch_add_u64(tl_atomic_u64* ptr, uint64_t val, int order) {
    return atomic_fetch_add_explicit(ptr, val, order);
}

/* Fetch-Sub (returns old value) */
TL_INLINE uint32_t tl_atomic_fetch_sub_u32(tl_atomic_u32* ptr, uint32_t val, int order) {
    return atomic_fetch_sub_explicit(ptr, val, order);
}

TL_INLINE uint64_t tl_atomic_fetch_sub_u64(tl_atomic_u64* ptr, uint64_t val, int order) {
    return atomic_fetch_sub_explicit(ptr, val, order);
}

/* Compare-Exchange (strong, returns true on success) */
TL_INLINE bool tl_atomic_cas_u32(tl_atomic_u32* ptr, uint32_t* expected,
                                  uint32_t desired, int succ, int fail) {
    return atomic_compare_exchange_strong_explicit(ptr, expected, desired, succ, fail);
}

TL_INLINE bool tl_atomic_cas_u64(tl_atomic_u64* ptr, uint64_t* expected,
                                  uint64_t desired, int succ, int fail) {
    return atomic_compare_exchange_strong_explicit(ptr, expected, desired, succ, fail);
}

#else

/*
 * No usable atomics backend. Timelog requires C17 with <stdatomic.h>:
 * GCC/Clang provide it unconditionally in C11+ mode; MSVC requires
 * VS2022 17.5+ with /experimental:c11atomics (the build system passes
 * the flag; if you hit this on MSVC, check the compiler version and
 * that the flag survived your build configuration). This #error is the
 * single load-bearing guard for both the core and the CPython binding —
 * do not add a weaker fallback here.
 */
#error "Timelog requires C11/C17 <stdatomic.h> atomics (MSVC: VS2022 17.5+ with /experimental:c11atomics)"

#endif /* Compiler selection */

/*===========================================================================
 * Convenience Macros for Common Patterns
 *===========================================================================*/

/* Relaxed load/store for counters where ordering doesn't matter */
#define tl_atomic_load_relaxed_u32(ptr)      tl_atomic_load_u32((ptr), TL_MO_RELAXED)
#define tl_atomic_load_relaxed_u64(ptr)      tl_atomic_load_u64((ptr), TL_MO_RELAXED)
#define tl_atomic_store_relaxed_u32(ptr, v)  tl_atomic_store_u32((ptr), (v), TL_MO_RELAXED)
#define tl_atomic_store_relaxed_u64(ptr, v)  tl_atomic_store_u64((ptr), (v), TL_MO_RELAXED)

/* Acquire/release for synchronization points */
#define tl_atomic_load_acquire_u32(ptr)      tl_atomic_load_u32((ptr), TL_MO_ACQUIRE)
#define tl_atomic_load_acquire_u64(ptr)      tl_atomic_load_u64((ptr), TL_MO_ACQUIRE)
#define tl_atomic_store_release_u32(ptr, v)  tl_atomic_store_u32((ptr), (v), TL_MO_RELEASE)

/* Increment helper */
#define tl_atomic_inc_u64(ptr) tl_atomic_fetch_add_u64((ptr), 1, TL_MO_ACQ_REL)

#endif /* TL_ATOMIC_H */
