#ifndef TL_ATOMIC_H
#define TL_ATOMIC_H

#include "tl_platform.h"
#include <stdint.h>
#include <stdbool.h>

/*===========================================================================
 * Compiler and Standard Detection
 *
 * C17 (201710L) is a superset of C11 (201112L) with bug fixes.
 * Both include <stdatomic.h>. We check for C11+ and __STDC_NO_ATOMICS__.
 * MSVC may not define __STDC_NO_ATOMICS__ correctly, so we also check
 * for MSVC specifically and use intrinsics there.
 *===========================================================================*/

#if defined(TL_COMPILER_MSVC)
    /* MSVC: Use intrinsics regardless of C standard version.
     * MSVC's <stdatomic.h> support varies by version (full in VS2022 17.5+).
     * For maximum compatibility, we use intrinsics on all MSVC versions. */
    #define TL_USE_MSVC_INTRINSICS 1
    #ifndef WIN32_LEAN_AND_MEAN
        #define WIN32_LEAN_AND_MEAN
    #endif
    #include <windows.h>
    #include <intrin.h>
#elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L && !defined(__STDC_NO_ATOMICS__)
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

#elif defined(TL_USE_MSVC_INTRINSICS)

/*===========================================================================
 * MSVC Intrinsics Implementation
 *
 * Used on all MSVC versions for maximum compatibility.
 *
 * IMPORTANT: We use Interlocked* primitives for ALL atomic operations.
 * volatile + _ReadWriteBarrier() is only a compiler barrier and does NOT
 * provide hardware memory ordering on ARM64 or proper atomicity guarantees.
 * All Interlocked* operations provide full memory barriers (seq_cst).
 *===========================================================================*/

/* Types still use volatile for compatibility, but all access uses Interlocked* */
typedef volatile LONG      tl_atomic_u32;
typedef volatile LONG64    tl_atomic_u64;

#define TL_MO_RELAXED 0
#define TL_MO_ACQUIRE 1
#define TL_MO_RELEASE 2
#define TL_MO_ACQ_REL 3
#define TL_MO_SEQ_CST 4

/* Init can use plain store since no concurrent access exists yet */
#define tl_atomic_init_u32(ptr, val) (*(ptr) = (LONG)(val))
#define tl_atomic_init_u64(ptr, val) (*(ptr) = (LONG64)(val))

/*
 * Atomic loads use InterlockedCompareExchange with matching expected/desired
 * to atomically read without modifying. This is preferred over InterlockedOr
 * because:
 * - InterlockedOr(ptr, 0) is technically a read-modify-write that can
 *   generate extra cache coherency traffic (it writes back the same value)
 * - InterlockedCompareExchange(ptr, 0, 0) only writes on match, and since
 *   it can only match when value is already 0, it minimizes write traffic
 *
 * All Interlocked* operations provide full memory barriers (seq_cst).
 */
TL_INLINE uint32_t tl_atomic_load_u32(const tl_atomic_u32* ptr, int order) {
    (void)order;
    return (uint32_t)InterlockedCompareExchange((volatile LONG*)ptr, 0, 0);
}

TL_INLINE uint64_t tl_atomic_load_u64(const tl_atomic_u64* ptr, int order) {
    (void)order;
    return (uint64_t)InterlockedCompareExchange64((volatile LONG64*)ptr, 0, 0);
}

/*
 * Atomic stores use InterlockedExchange for proper atomicity.
 * This provides a full memory barrier.
 */
TL_INLINE void tl_atomic_store_u32(tl_atomic_u32* ptr, uint32_t val, int order) {
    (void)order;
    InterlockedExchange((volatile LONG*)ptr, (LONG)val);
}

TL_INLINE void tl_atomic_store_u64(tl_atomic_u64* ptr, uint64_t val, int order) {
    (void)order;
    InterlockedExchange64((volatile LONG64*)ptr, (LONG64)val);
}

TL_INLINE uint32_t tl_atomic_fetch_add_u32(tl_atomic_u32* ptr, uint32_t val, int order) {
    (void)order;
    return (uint32_t)InterlockedExchangeAdd((volatile LONG*)ptr, (LONG)val);
}

TL_INLINE uint64_t tl_atomic_fetch_add_u64(tl_atomic_u64* ptr, uint64_t val, int order) {
    (void)order;
    return (uint64_t)InterlockedExchangeAdd64((volatile LONG64*)ptr, (LONG64)val);
}

TL_INLINE uint32_t tl_atomic_fetch_sub_u32(tl_atomic_u32* ptr, uint32_t val, int order) {
    (void)order;
    return (uint32_t)InterlockedExchangeAdd((volatile LONG*)ptr, -(LONG)val);
}

TL_INLINE uint64_t tl_atomic_fetch_sub_u64(tl_atomic_u64* ptr, uint64_t val, int order) {
    (void)order;
    return (uint64_t)InterlockedExchangeAdd64((volatile LONG64*)ptr, -(LONG64)val);
}

TL_INLINE bool tl_atomic_cas_u32(tl_atomic_u32* ptr, uint32_t* expected,
                                  uint32_t desired, int succ, int fail) {
    (void)succ; (void)fail;
    LONG old = InterlockedCompareExchange(
        (volatile LONG*)ptr, (LONG)desired, (LONG)*expected);
    if ((uint32_t)old == *expected) {
        return true;
    }
    *expected = (uint32_t)old;
    return false;
}

TL_INLINE bool tl_atomic_cas_u64(tl_atomic_u64* ptr, uint64_t* expected,
                                  uint64_t desired, int succ, int fail) {
    (void)succ; (void)fail;
    LONG64 old = InterlockedCompareExchange64(
        (volatile LONG64*)ptr, (LONG64)desired, (LONG64)*expected);
    if ((uint64_t)old == *expected) {
        return true;
    }
    *expected = (uint64_t)old;
    return false;
}

#else

/*
 * No usable atomics backend. Timelog requires C17 with <stdatomic.h>
 * (GCC/Clang; __STDC_NO_ATOMICS__ must not be defined) or MSVC with its
 * Interlocked intrinsics. A toolchain that reaches this branch is not
 * supported — do not add a weaker fallback here.
 */
#error "Timelog requires C11/C17 <stdatomic.h> atomics or MSVC Interlocked intrinsics"

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
