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
 * - tl_atomic_ptr: manifest/memtable pointers
 *===========================================================================*/

#if defined(TL_HAS_C11_ATOMICS)

typedef _Atomic uint32_t tl_atomic_u32;
typedef _Atomic uint64_t tl_atomic_u64;
typedef _Atomic(void*)   tl_atomic_ptr;

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
#define tl_atomic_init_ptr(ptr, val) atomic_init((ptr), (val))

/* Load */
TL_INLINE uint32_t tl_atomic_load_u32(const tl_atomic_u32* ptr, int order) {
    return atomic_load_explicit((tl_atomic_u32*)ptr, order);
}

TL_INLINE uint64_t tl_atomic_load_u64(const tl_atomic_u64* ptr, int order) {
    return atomic_load_explicit((tl_atomic_u64*)ptr, order);
}

TL_INLINE void* tl_atomic_load_ptr(const tl_atomic_ptr* ptr, int order) {
    return atomic_load_explicit((tl_atomic_ptr*)ptr, order);
}

/* Store */
TL_INLINE void tl_atomic_store_u32(tl_atomic_u32* ptr, uint32_t val, int order) {
    atomic_store_explicit(ptr, val, order);
}

TL_INLINE void tl_atomic_store_u64(tl_atomic_u64* ptr, uint64_t val, int order) {
    atomic_store_explicit(ptr, val, order);
}

TL_INLINE void tl_atomic_store_ptr(tl_atomic_ptr* ptr, void* val, int order) {
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

TL_INLINE bool tl_atomic_cas_ptr(tl_atomic_ptr* ptr, void** expected,
                                  void* desired, int succ, int fail) {
    return atomic_compare_exchange_strong_explicit(ptr, expected, desired, succ, fail);
}

/* Exchange (returns old value) */
TL_INLINE void* tl_atomic_exchange_ptr(tl_atomic_ptr* ptr, void* val, int order) {
    return atomic_exchange_explicit(ptr, val, order);
}

/* Fence */
TL_INLINE void tl_atomic_fence(int order) {
    atomic_thread_fence(order);
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
typedef void* volatile     tl_atomic_ptr;

#define TL_MO_RELAXED 0
#define TL_MO_ACQUIRE 1
#define TL_MO_RELEASE 2
#define TL_MO_ACQ_REL 3
#define TL_MO_SEQ_CST 4

/* Init can use plain store since no concurrent access exists yet */
#define tl_atomic_init_u32(ptr, val) (*(ptr) = (LONG)(val))
#define tl_atomic_init_u64(ptr, val) (*(ptr) = (LONG64)(val))
#define tl_atomic_init_ptr(ptr, val) (*(ptr) = (val))

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

TL_INLINE void* tl_atomic_load_ptr(const tl_atomic_ptr* ptr, int order) {
    (void)order;
    return InterlockedCompareExchangePointer((void* volatile*)ptr, NULL, NULL);
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

TL_INLINE void tl_atomic_store_ptr(tl_atomic_ptr* ptr, void* val, int order) {
    (void)order;
    InterlockedExchangePointer((void* volatile*)ptr, val);
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

TL_INLINE bool tl_atomic_cas_ptr(tl_atomic_ptr* ptr, void** expected,
                                  void* desired, int succ, int fail) {
    (void)succ; (void)fail;
    void* old = InterlockedCompareExchangePointer((void* volatile*)ptr, desired, *expected);
    if (old == *expected) {
        return true;
    }
    *expected = old;
    return false;
}

TL_INLINE void* tl_atomic_exchange_ptr(tl_atomic_ptr* ptr, void* val, int order) {
    (void)order;
    return InterlockedExchangePointer((void* volatile*)ptr, val);
}

TL_INLINE void tl_atomic_fence(int order) {
    (void)order;
    /* MemoryBarrier() provides a full hardware memory barrier on all platforms */
    MemoryBarrier();
}

#else /* GCC/Clang without <stdatomic.h> - unlikely with C17 but defensive */

/*===========================================================================
 * GCC/Clang Built-in Atomics Fallback
 *
 * Uses __atomic_* builtins available in GCC 4.7+ and Clang 3.1+.
 * This path is rarely taken since C17 mode normally provides <stdatomic.h>.
 *===========================================================================*/

typedef volatile uint32_t tl_atomic_u32;
typedef volatile uint64_t tl_atomic_u64;
typedef void* volatile    tl_atomic_ptr;

#define TL_MO_RELAXED __ATOMIC_RELAXED
#define TL_MO_ACQUIRE __ATOMIC_ACQUIRE
#define TL_MO_RELEASE __ATOMIC_RELEASE
#define TL_MO_ACQ_REL __ATOMIC_ACQ_REL
#define TL_MO_SEQ_CST __ATOMIC_SEQ_CST

#define tl_atomic_init_u32(ptr, val) (*(ptr) = (val))
#define tl_atomic_init_u64(ptr, val) (*(ptr) = (val))
#define tl_atomic_init_ptr(ptr, val) (*(ptr) = (val))

TL_INLINE uint32_t tl_atomic_load_u32(const tl_atomic_u32* ptr, int order) {
    return __atomic_load_n(ptr, order);
}

TL_INLINE uint64_t tl_atomic_load_u64(const tl_atomic_u64* ptr, int order) {
    return __atomic_load_n(ptr, order);
}

TL_INLINE void* tl_atomic_load_ptr(const tl_atomic_ptr* ptr, int order) {
    return __atomic_load_n(ptr, order);
}

TL_INLINE void tl_atomic_store_u32(tl_atomic_u32* ptr, uint32_t val, int order) {
    __atomic_store_n(ptr, val, order);
}

TL_INLINE void tl_atomic_store_u64(tl_atomic_u64* ptr, uint64_t val, int order) {
    __atomic_store_n(ptr, val, order);
}

TL_INLINE void tl_atomic_store_ptr(tl_atomic_ptr* ptr, void* val, int order) {
    __atomic_store_n(ptr, val, order);
}

TL_INLINE uint32_t tl_atomic_fetch_add_u32(tl_atomic_u32* ptr, uint32_t val, int order) {
    return __atomic_fetch_add(ptr, val, order);
}

TL_INLINE uint64_t tl_atomic_fetch_add_u64(tl_atomic_u64* ptr, uint64_t val, int order) {
    return __atomic_fetch_add(ptr, val, order);
}

TL_INLINE uint32_t tl_atomic_fetch_sub_u32(tl_atomic_u32* ptr, uint32_t val, int order) {
    return __atomic_fetch_sub(ptr, val, order);
}

TL_INLINE uint64_t tl_atomic_fetch_sub_u64(tl_atomic_u64* ptr, uint64_t val, int order) {
    return __atomic_fetch_sub(ptr, val, order);
}

TL_INLINE bool tl_atomic_cas_u32(tl_atomic_u32* ptr, uint32_t* expected,
                                  uint32_t desired, int succ, int fail) {
    return __atomic_compare_exchange_n(ptr, expected, desired, 0, succ, fail);
}

TL_INLINE bool tl_atomic_cas_u64(tl_atomic_u64* ptr, uint64_t* expected,
                                  uint64_t desired, int succ, int fail) {
    return __atomic_compare_exchange_n(ptr, expected, desired, 0, succ, fail);
}

TL_INLINE bool tl_atomic_cas_ptr(tl_atomic_ptr* ptr, void** expected,
                                  void* desired, int succ, int fail) {
    return __atomic_compare_exchange_n(ptr, expected, desired, 0, succ, fail);
}

TL_INLINE void* tl_atomic_exchange_ptr(tl_atomic_ptr* ptr, void* val, int order) {
    return __atomic_exchange_n(ptr, val, order);
}

TL_INLINE void tl_atomic_fence(int order) {
    __atomic_thread_fence(order);
}

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
#define tl_atomic_load_acquire_ptr(ptr)      tl_atomic_load_ptr((ptr), TL_MO_ACQUIRE)
#define tl_atomic_store_release_u32(ptr, v)  tl_atomic_store_u32((ptr), (v), TL_MO_RELEASE)
#define tl_atomic_store_release_u64(ptr, v)  tl_atomic_store_u64((ptr), (v), TL_MO_RELEASE)
#define tl_atomic_store_release_ptr(ptr, v)  tl_atomic_store_ptr((ptr), (v), TL_MO_RELEASE)

/* Increment/decrement helpers */
#define tl_atomic_inc_u32(ptr) tl_atomic_fetch_add_u32((ptr), 1, TL_MO_ACQ_REL)
#define tl_atomic_dec_u32(ptr) tl_atomic_fetch_sub_u32((ptr), 1, TL_MO_ACQ_REL)
#define tl_atomic_inc_u64(ptr) tl_atomic_fetch_add_u64((ptr), 1, TL_MO_ACQ_REL)
#define tl_atomic_dec_u64(ptr) tl_atomic_fetch_sub_u64((ptr), 1, TL_MO_ACQ_REL)

#endif /* TL_ATOMIC_H */
