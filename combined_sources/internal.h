/*
============================================================================

   COMBINED HEADER FILE: internal.h

   Generated from: core/src/internal/
   Generated at:   2026-01-20 23:27:38

   This file combines all .h files from the internal/ subfolder.

   Files included:
 *   - tl_alloc.h
 *   - tl_atomic.h
 *   - tl_defs.h
 *   - tl_heap.h
 *   - tl_intervals.h
 *   - tl_locks.h
 *   - tl_log.h
 *   - tl_platform.h
 *   - tl_range.h
 *   - tl_recvec.h
 *   - tl_seqlock.h
 *   - tl_sync.h
 *   - tl_timelog_internal.h

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: tl_alloc.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_ALLOC_H
#define TL_ALLOC_H

#include "tl_defs.h"

/*===========================================================================
 * Allocator Context
 *===========================================================================*/

/**
 * Internal allocator context. Wraps user-provided allocator or defaults.
 *
 * Design: Store the allocator inline to avoid pointer chasing.
 * The context pointer is passed through to user callbacks.
 */
typedef struct tl_alloc_ctx {
    tl_allocator_t alloc;
    bool           is_default;  /* True if using libc defaults */

#ifdef TL_DEBUG
    /* Debug tracking */
    size_t         total_allocated;
    size_t         allocation_count;
    size_t         peak_allocated;
#endif
} tl_alloc_ctx_t;

/*===========================================================================
 * Initialization
 *===========================================================================*/

/**
 * Initialize allocator context from user config.
 * If user allocator has NULL function pointers, uses libc defaults.
 */
void tl__alloc_init(tl_alloc_ctx_t* ctx, const tl_allocator_t* user_alloc);

/**
 * Cleanup allocator context.
 * In debug builds, reports leaks if allocation_count != 0.
 */
void tl__alloc_destroy(tl_alloc_ctx_t* ctx);

/*===========================================================================
 * Allocation Functions
 *===========================================================================*/

/**
 * Allocate memory. Returns NULL on failure.
 *
 * @param ctx  Allocator context
 * @param size Bytes to allocate (must be > 0)
 * @return Pointer to allocated memory or NULL
 */
void* tl__malloc(tl_alloc_ctx_t* ctx, size_t size);

/**
 * Allocate zeroed memory. Returns NULL on failure.
 *
 * @param ctx   Allocator context
 * @param count Number of elements
 * @param size  Size of each element
 * @return Pointer to zeroed memory or NULL
 */
void* tl__calloc(tl_alloc_ctx_t* ctx, size_t count, size_t size);

/**
 * Reallocate memory.
 *
 * NULL is returned in two cases:
 * 1. realloc_fn was not provided in the user allocator (configuration issue)
 * 2. The underlying realloc operation failed (ENOMEM)
 *
 * In case 1, the caller should ensure realloc_fn is provided during init
 * if resize operations are needed. This is a programming error.
 *
 * In case 2, the original ptr remains valid and must still be freed.
 * Callers must handle NULL return by either retrying, failing gracefully,
 * or continuing with the existing allocation.
 *
 * Note: If ptr==NULL, delegates to tl__malloc. If new_size==0, frees ptr.
 *
 * @param ctx      Allocator context
 * @param ptr      Pointer to reallocate (may be NULL)
 * @param new_size New size in bytes
 * @return Pointer to reallocated memory, or NULL on failure
 */
void* tl__realloc(tl_alloc_ctx_t* ctx, void* ptr, size_t new_size);

/**
 * Free memory.
 *
 * @param ctx Allocator context
 * @param ptr Pointer to free (NULL is safe)
 */
void tl__free(tl_alloc_ctx_t* ctx, void* ptr);

/*===========================================================================
 * Convenience Macros
 *===========================================================================*/

/**
 * Allocate typed object.
 * Usage: tl_page_t* page = TL_NEW(ctx, tl_page_t);
 */
#define TL_NEW(ctx, type) \
    ((type*)tl__calloc((ctx), 1, sizeof(type)))

/**
 * Allocate typed array.
 * Usage: int64_t* arr = TL_NEW_ARRAY(ctx, int64_t, 100);
 */
#define TL_NEW_ARRAY(ctx, type, count) \
    ((type*)tl__calloc((ctx), (count), sizeof(type)))

/**
 * Free and NULL a pointer.
 * Usage: TL_FREE(ctx, ptr);
 */
#define TL_FREE(ctx, ptr) \
    do { tl__free((ctx), (ptr)); (ptr) = NULL; } while(0)

/*===========================================================================
 * Debug Statistics (Debug Builds Only)
 *===========================================================================*/

#ifdef TL_DEBUG
size_t tl__alloc_get_total(const tl_alloc_ctx_t* ctx);
size_t tl__alloc_get_count(const tl_alloc_ctx_t* ctx);
size_t tl__alloc_get_peak(const tl_alloc_ctx_t* ctx);
#endif

#endif /* TL_ALLOC_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_alloc.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_atomic.h
/*   FROM: internal/
/*
/******************************************************************************/
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

/------------------------------------------------------------------------------/
/*   END OF: tl_atomic.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_defs.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_DEFS_H
#define TL_DEFS_H

#include "timelog/timelog.h"
#include "tl_platform.h"

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <string.h>

/*===========================================================================
 * Timestamp Bounds
 *===========================================================================*/

#define TL_TS_MIN  INT64_MIN
#define TL_TS_MAX  INT64_MAX

/*===========================================================================
 * Size Constants
 *===========================================================================*/

/* Default configuration values (use size_t to avoid implicit widening) */
#define TL_DEFAULT_TARGET_PAGE_BYTES      ((size_t)64 * 1024)   /* 64 KiB */
#define TL_DEFAULT_MEMTABLE_MAX_BYTES     ((size_t)1024 * 1024) /* 1 MiB */
#define TL_DEFAULT_SEALED_MAX_RUNS        4
#define TL_DEFAULT_SEALED_WAIT_MS         100
#define TL_DEFAULT_MAINTENANCE_WAKEUP_MS  100   /* Periodic wake interval */
#define TL_DEFAULT_MAX_DELTA_SEGMENTS     8

/* Minimum page rows to prevent degenerate pages */
#define TL_MIN_PAGE_ROWS                  16

/* Record size for byte accounting (use actual struct size to handle padding) */
#define TL_RECORD_SIZE                    (sizeof(tl_record_t))

/*===========================================================================
 * Type Size/Layout Validation
 *
 * Static asserts to catch platform issues at compile time.
 * These assumptions are critical for:
 * - Memory accounting (TL_RECORD_SIZE)
 * - Page layout calculations
 * - Serialization compatibility (if added later)
 *===========================================================================*/

_Static_assert(sizeof(tl_ts_t) == 8,
    "tl_ts_t must be 8 bytes (int64_t)");
_Static_assert(sizeof(tl_handle_t) == 8,
    "tl_handle_t must be 8 bytes (uint64_t)");
_Static_assert(sizeof(tl_record_t) == 16,
    "tl_record_t must be 16 bytes (ts + handle, no padding)");
_Static_assert(_Alignof(tl_record_t) == 8,
    "tl_record_t must be 8-byte aligned for efficient access");

/*===========================================================================
 * Window Defaults (in time units)
 *===========================================================================*/

/* 1 hour in each time unit */
#define TL_WINDOW_1H_S   (3600LL)
#define TL_WINDOW_1H_MS  (3600LL * 1000)
#define TL_WINDOW_1H_US  (3600LL * 1000 * 1000)
#define TL_WINDOW_1H_NS  (3600LL * 1000 * 1000 * 1000)

/*===========================================================================
 * Forward Declarations (Internal Types)
 *===========================================================================*/

/* Storage layer */
typedef struct tl_page          tl_page_t;
typedef struct tl_page_meta     tl_page_meta_t;
typedef struct tl_page_catalog  tl_page_catalog_t;
typedef struct tl_segment       tl_segment_t;
typedef struct tl_manifest      tl_manifest_t;
typedef struct tl_tombstones    tl_tombstones_t;

/* Delta layer */
typedef struct tl_memtable      tl_memtable_t;
typedef struct tl_memrun        tl_memrun_t;
typedef struct tl_memview       tl_memview_t;
typedef struct tl_flush_ctx     tl_flush_ctx_t;
typedef struct tl_merge_iter    tl_merge_iter_t;

/* Tombstones */
typedef struct tl_interval      tl_interval_t;
typedef struct tl_intervals     tl_intervals_t;

/* Maintenance */
typedef struct tl_maint_state   tl_maint_state_t;

/*===========================================================================
 * Internal Helper Macros
 *===========================================================================*/

/* Safe minimum/maximum */
#define TL_MIN(a, b) (((a) < (b)) ? (a) : (b))
#define TL_MAX(a, b) (((a) > (b)) ? (a) : (b))

/* Array element count */
#define TL_ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))

/* Pointer alignment check */
#define TL_IS_ALIGNED(ptr, align) (((uintptr_t)(ptr) & ((align) - 1)) == 0)

/* Round up to power of 2 alignment */
#define TL_ALIGN_UP(x, align) (((x) + ((align) - 1)) & ~((align) - 1))

/*===========================================================================
 * Internal Allocator Access
 *===========================================================================*/

/* These are defined in tl_alloc.h but forward-declared here for convenience */
struct tl_alloc_ctx;
typedef struct tl_alloc_ctx tl_alloc_ctx_t;

#endif /* TL_DEFS_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_defs.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_heap.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_HEAP_H
#define TL_HEAP_H

#include "tl_defs.h"
#include "tl_alloc.h"

/*===========================================================================
 * Min-Heap
 *
 * Provides efficient K-way merge for the read path. Stores
 * (timestamp, component_id) pairs and supports:
 * - Push/pop/peek in O(log K)
 * - Initial heapify in O(K)
 *
 * Used by:
 * - Merge iterator (Read Path LLD Section 6)
 * - Memview iterator (K-way merge of memruns)
 *
 * Thread Safety:
 * - Not thread-safe. Caller must provide synchronization.
 *===========================================================================*/

/**
 * Heap entry for K-way merge.
 * Contains the current record from a component iterator.
 */
typedef struct tl_heap_entry {
    tl_ts_t       ts;           /* Sort key (timestamp) */
    uint32_t      component_id; /* Tie-breaker / source identifier */
    tl_handle_t   handle;       /* Current record handle */
    void*         iter;         /* Opaque pointer to component iterator */
} tl_heap_entry_t;

/**
 * Min-heap for K-way merge.
 * Entries are ordered by (ts, component_id).
 */
typedef struct tl_heap {
    tl_heap_entry_t* data;
    size_t           len;
    size_t           cap;
    tl_alloc_ctx_t*  alloc;
} tl_heap_t;

/*---------------------------------------------------------------------------
 * Lifecycle
 *---------------------------------------------------------------------------*/

void tl_heap_init(tl_heap_t* h, tl_alloc_ctx_t* alloc);

/**
 * Destroy heap and free memory.
 * Idempotent: safe to call on already-destroyed or zero-initialized heaps.
 * After this call, h is in a valid empty state.
 */
void tl_heap_destroy(tl_heap_t* h);

void tl_heap_clear(tl_heap_t* h);

/**
 * Reserve capacity for at least min_cap entries.
 */
tl_status_t tl_heap_reserve(tl_heap_t* h, size_t min_cap);

/*---------------------------------------------------------------------------
 * Heap Operations
 *---------------------------------------------------------------------------*/

/**
 * Push an entry onto the heap.
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_heap_push(tl_heap_t* h, const tl_heap_entry_t* entry);

/**
 * Pop the minimum entry from the heap.
 * @param out Output for the popped entry
 * @return TL_OK on success, TL_EOF if heap is empty
 */
tl_status_t tl_heap_pop(tl_heap_t* h, tl_heap_entry_t* out);

/**
 * Peek at the minimum entry without removing it.
 * @return Pointer to minimum entry, or NULL if empty
 */
const tl_heap_entry_t* tl_heap_peek(const tl_heap_t* h);

/**
 * Build heap from array of entries (heapify).
 * More efficient than repeated push for initial construction.
 * @param entries Array of entries (copied into heap)
 * @param n       Number of entries
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_heap_build(tl_heap_t* h, const tl_heap_entry_t* entries, size_t n);

/**
 * Replace the top entry and restore heap property.
 * Equivalent to pop + push but more efficient.
 * @param new_entry New entry to replace top
 * Precondition: heap is not empty
 */
void tl_heap_replace_top(tl_heap_t* h, const tl_heap_entry_t* new_entry);

/*---------------------------------------------------------------------------
 * Accessors
 *---------------------------------------------------------------------------*/

TL_INLINE size_t tl_heap_len(const tl_heap_t* h) {
    return h->len;
}

TL_INLINE bool tl_heap_is_empty(const tl_heap_t* h) {
    return h->len == 0;
}

#endif /* TL_HEAP_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_heap.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_intervals.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_INTERVALS_H
#define TL_INTERVALS_H

#include "tl_defs.h"
#include "tl_alloc.h"

/*===========================================================================
 * Interval Set
 *
 * Stores half-open time intervals [t1, t2) representing tombstones.
 * Provides:
 * - Mutable insert with automatic coalescing
 * - Immutable snapshot for storage attachment
 * - Binary search for point containment
 * - Union of two interval sets
 * - Clipping to a range
 *
 * Used by:
 * - tl_memtable_t.active_tombs (mutable, receives new tombstones)
 * - tl_memrun_t.tombs (immutable, from sealed memtable)
 * - tl_segment_t.tombstones (immutable, attached to L0 segments)
 * - Read path effective tombstone computation (union + clip)
 *
 * Thread Safety:
 * - Not thread-safe. Caller must provide synchronization.
 *===========================================================================*/

/**
 * A single half-open interval [start, end).
 * If end_unbounded is true, represents [start, +inf).
 *
 * When end_unbounded is true, the 'end' field is ignored (set to 0 for clarity).
 * Always check end_unbounded BEFORE reading 'end'.
 */
typedef struct tl_interval {
    tl_ts_t start;        /* Inclusive start bound */
    tl_ts_t end;          /* Exclusive end bound (ONLY valid if !end_unbounded) */
    bool    end_unbounded;/* True => [start, +inf), 'end' is ignored */
} tl_interval_t;

/**
 * Mutable interval set with automatic coalescing.
 * Invariants:
 * - Intervals are sorted by start.
 * - No two intervals overlap.
 * - No two intervals are adjacent (coalesced).
 */
typedef struct tl_intervals {
    tl_interval_t*  data;
    size_t          len;
    size_t          cap;
    tl_alloc_ctx_t* alloc;
} tl_intervals_t;

/**
 * Immutable interval array (for storage/snapshot).
 * Same invariants as mutable set.
 */
typedef struct tl_intervals_imm {
    const tl_interval_t* data;
    size_t               len;
} tl_intervals_imm_t;

/*---------------------------------------------------------------------------
 * Lifecycle
 *---------------------------------------------------------------------------*/

void tl_intervals_init(tl_intervals_t* iv, tl_alloc_ctx_t* alloc);

/**
 * Destroy interval set and free memory.
 * Idempotent: safe to call on already-destroyed or zero-initialized sets.
 * After this call, iv is in a valid empty state.
 */
void tl_intervals_destroy(tl_intervals_t* iv);

void tl_intervals_clear(tl_intervals_t* iv);

/*---------------------------------------------------------------------------
 * Insertion (with coalescing)
 *---------------------------------------------------------------------------*/

/**
 * Insert a bounded interval [t1, t2).
 *
 * Semantics (Write Path LLD Section 3.8):
 * - t1 > t2:  Returns TL_EINVAL (invalid interval)
 * - t1 == t2: Returns TL_OK (no-op, empty interval not stored)
 * - t1 < t2:  Inserts and coalesces
 *
 * @return TL_OK on success (including no-op for t1==t2)
 *         TL_EINVAL if t1 > t2
 *         TL_ENOMEM on allocation failure
 *
 * Coalescing rules:
 * - Overlapping intervals are merged.
 * - Adjacent intervals (end1 == start2) are merged.
 * - Unboundedness propagates: merging with [x, +inf) yields unbounded result.
 */
tl_status_t tl_intervals_insert(tl_intervals_t* iv, tl_ts_t t1, tl_ts_t t2);

/**
 * Insert an unbounded interval [t1, +inf).
 *
 * This interval contains ALL timestamps >= t1, including INT64_MAX.
 * When merged with any overlapping/adjacent bounded interval, the result
 * is unbounded.
 *
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_intervals_insert_unbounded(tl_intervals_t* iv, tl_ts_t t1);

/*---------------------------------------------------------------------------
 * Point Containment
 *---------------------------------------------------------------------------*/

/**
 * Check if timestamp ts is contained in any interval.
 * @return true if ts is in [start, end) for some interval, false otherwise
 */
bool tl_intervals_contains(const tl_intervals_t* iv, tl_ts_t ts);
bool tl_intervals_imm_contains(tl_intervals_imm_t iv, tl_ts_t ts);

/*---------------------------------------------------------------------------
 * Set Operations
 *---------------------------------------------------------------------------*/

/**
 * Compute union of two interval sets into output.
 * Output is cleared first.
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_intervals_union(tl_intervals_t* out,
                               const tl_intervals_t* a,
                               const tl_intervals_t* b);

/**
 * Union variant with immutable inputs.
 */
tl_status_t tl_intervals_union_imm(tl_intervals_t* out,
                                   tl_intervals_imm_t a,
                                   tl_intervals_imm_t b);

/**
 * Clip intervals to [t1, t2) range.
 * Intervals fully outside the range are removed.
 * Intervals partially inside are truncated.
 * Modifies in place.
 *
 * Unbounded interval handling:
 * - An unbounded interval [start, +inf) clipped to [t1, t2) becomes:
 *   - Removed if start >= t2
 *   - Bounded [max(start, t1), t2) otherwise
 *
 * After clipping, all intervals are guaranteed to be bounded.
 *
 * Precondition: t1 < t2 (the clip range must be non-empty and bounded)
 */
void tl_intervals_clip(tl_intervals_t* iv, tl_ts_t t1, tl_ts_t t2);

/**
 * Clip intervals to [t1, +inf) - only lower bound.
 *
 * Removes intervals that end before t1 (bounded intervals where end <= t1).
 * Truncates intervals that overlap t1 (sets start = max(start, t1)).
 * Unbounded intervals [start, +inf) are kept if start >= t1 or truncated otherwise.
 *
 * This is used for unbounded queries where we cannot clip to a finite upper bound.
 *
 * Unlike tl_intervals_clip(), unbounded intervals remain unbounded after clipping.
 *
 * @param iv  Interval set to clip in place
 * @param t1  Lower bound (inclusive)
 */
void tl_intervals_clip_lower(tl_intervals_t* iv, tl_ts_t t1);

/*---------------------------------------------------------------------------
 * Accessors
 *---------------------------------------------------------------------------*/

TL_INLINE size_t tl_intervals_len(const tl_intervals_t* iv) {
    return iv->len;
}

TL_INLINE bool tl_intervals_is_empty(const tl_intervals_t* iv) {
    return iv->len == 0;
}

TL_INLINE const tl_interval_t* tl_intervals_get(const tl_intervals_t* iv, size_t idx) {
    TL_ASSERT(idx < iv->len);
    return &iv->data[idx];
}

/**
 * Create an immutable view of the intervals.
 */
TL_INLINE tl_intervals_imm_t tl_intervals_as_imm(const tl_intervals_t* iv) {
    tl_intervals_imm_t imm;
    imm.data = iv->data;
    imm.len = iv->len;
    return imm;
}

/**
 * Take ownership of intervals array.
 * @return Array pointer (caller must free), NULL if empty
 */
tl_interval_t* tl_intervals_take(tl_intervals_t* iv, size_t* out_len);

/**
 * Compute total span covered by intervals (for delete debt metric).
 * Used by compaction policy (Compaction Policy LLD Section 5).
 *
 * Unbounded interval handling:
 * - SHOULD only be called after clipping to a bounded window.
 * - If an unbounded interval is present, returns TL_TS_MAX (saturated).
 *   This signals "infinite delete debt" which forces compaction.
 *
 * Overflow handling:
 * - Uses saturating addition to prevent signed overflow.
 * - Returns TL_TS_MAX if sum would overflow.
 *
 * @return Sum of (end - start) for all intervals, or TL_TS_MAX if unbounded/overflow
 */
tl_ts_t tl_intervals_covered_span(const tl_intervals_t* iv);

/*---------------------------------------------------------------------------
 * Cursor-Based Iteration (for tombstone filtering - Read Path LLD Section 7)
 *
 * The tombstone filter uses a cursor over sorted intervals to achieve
 * amortized O(1) per-record filtering. The cursor advances forward only.
 *---------------------------------------------------------------------------*/

/**
 * Cursor for efficient tombstone filtering during iteration.
 * Maintains position in a sorted interval set.
 */
typedef struct tl_intervals_cursor {
    const tl_interval_t* data;  /* Interval array (borrowed) */
    size_t               len;   /* Array length */
    size_t               pos;   /* Current position */
} tl_intervals_cursor_t;

/**
 * Initialize cursor from immutable interval set.
 */
TL_INLINE void tl_intervals_cursor_init(tl_intervals_cursor_t* cur,
                                        tl_intervals_imm_t iv) {
    cur->data = iv.data;
    cur->len = iv.len;
    cur->pos = 0;
}

/**
 * Check if timestamp is deleted and advance cursor.
 *
 * Algorithm (Read Path LLD Section 7.1):
 * - Advance cursor while ts >= cur.end (for bounded intervals)
 * - Return true if cur.start <= ts (and ts < cur.end for bounded, always for unbounded)
 *
 * Unbounded interval handling:
 * - An unbounded interval [start, +inf) covers all ts >= start.
 * - Once cursor reaches an unbounded interval, it stays there (all future ts are deleted).
 *
 * @param ts Timestamp to check
 * @return true if ts is covered by a tombstone, false otherwise
 *
 * Precondition: Timestamps must be passed in non-decreasing order.
 */
bool tl_intervals_cursor_is_deleted(tl_intervals_cursor_t* cur, tl_ts_t ts);

/**
 * Get the next uncovered timestamp after the current position.
 * Used for skip-ahead optimization (Read Path LLD Section 7.2).
 *
 * If ts is covered by interval [start, end), sets *out = end and returns true.
 * If ts is covered by unbounded interval [start, +inf), returns false
 *   (no uncovered timestamps exist after this point).
 * If ts is not covered, sets *out = ts and returns true.
 *
 * @param cur Cursor
 * @param ts  Timestamp to check
 * @param out Output: next uncovered timestamp (only valid if returns true)
 * @return true if there is a next uncovered timestamp, false if all remaining
 *         timestamps are covered by an unbounded interval
 */
bool tl_intervals_cursor_skip_to(tl_intervals_cursor_t* cur, tl_ts_t ts,
                                  tl_ts_t* out);

/*---------------------------------------------------------------------------
 * Validation (Debug)
 *---------------------------------------------------------------------------*/

#ifdef TL_DEBUG
/**
 * Validate raw interval array invariants.
 *
 * This is the shared validator used by segment and memview validation.
 * Checks:
 * 1. Each bounded interval has start < end
 * 2. Sorted by start timestamp
 * 3. Non-overlapping (prev->end <= cur->start)
 * 4. Non-adjacent / coalesced (prev->end != cur->start)
 * 5. No intervals after an unbounded interval
 *
 * @param data  Array of intervals (may be NULL if len == 0)
 * @param len   Number of intervals
 * @return true if valid, false if any invariant violated
 */
bool tl_intervals_arr_validate(const tl_interval_t* data, size_t len);

/**
 * Validate interval set invariants.
 * Calls tl_intervals_arr_validate() on the internal array.
 *
 * @return true if valid, false if invariants violated
 */
bool tl_intervals_validate(const tl_intervals_t* iv);
#endif

#endif /* TL_INTERVALS_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_intervals.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_locks.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_LOCKS_H
#define TL_LOCKS_H

#include "tl_sync.h"

/*===========================================================================
 * Lock Ordering (from timelog_v1_engineering_plan.md)
 *
 * Strict order: maint_mu -> flush_mu -> writer_mu -> memtable_mu
 *
 * Rules:
 * - Never acquire a lock while holding one to its right
 * - Long builds happen off-lock (only short critical sections under writer_mu)
 * - Deferred signaling: set flag, then signal under maint_mu
 *===========================================================================*/

typedef enum tl_lock_id {
    TL_LOCK_NONE       = 0,
    TL_LOCK_MAINT_MU   = 1,  /* Highest priority */
    TL_LOCK_FLUSH_MU   = 2,
    TL_LOCK_WRITER_MU  = 3,
    TL_LOCK_MEMTABLE_MU = 4  /* Lowest priority */
} tl_lock_id_t;

#ifdef TL_DEBUG

/*===========================================================================
 * Debug-Mode Lock Tracking
 *
 * Each thread maintains a stack of held locks to detect ordering violations.
 * This uses thread-local storage for per-thread tracking.
 *===========================================================================*/

#define TL_MAX_HELD_LOCKS 8

typedef struct tl_lock_tracker {
    tl_lock_id_t held[TL_MAX_HELD_LOCKS];
    int depth;
} tl_lock_tracker_t;

/* Thread-local lock tracker */
#if defined(TL_PLATFORM_WINDOWS)
    extern __declspec(thread) tl_lock_tracker_t tl__lock_tracker;
#else
    extern __thread tl_lock_tracker_t tl__lock_tracker;
#endif

/**
 * Record that a lock is being acquired.
 * Asserts if acquiring out of order.
 */
TL_INLINE void tl_lock_acquire_check(tl_lock_id_t id) {
    tl_lock_tracker_t* t = &tl__lock_tracker;

    /* Check ordering: new lock must be > all held locks */
    for (int i = 0; i < t->depth; i++) {
        TL_ASSERT_MSG(t->held[i] < id,
            "Lock ordering violation: cannot acquire lower-priority lock");
    }

    TL_ASSERT(t->depth < TL_MAX_HELD_LOCKS);
    t->held[t->depth++] = id;
}

/**
 * Record that a lock is being released.
 * Asserts if releasing out of order.
 */
TL_INLINE void tl_lock_release_check(tl_lock_id_t id) {
    tl_lock_tracker_t* t = &tl__lock_tracker;

    TL_ASSERT(t->depth > 0);
    TL_ASSERT_MSG(t->held[t->depth - 1] == id,
        "Lock release order violation: must release in reverse order");
    t->depth--;
}

/**
 * Check if a specific lock is held.
 */
TL_INLINE bool tl_lock_is_held(tl_lock_id_t id) {
    tl_lock_tracker_t* t = &tl__lock_tracker;
    for (int i = 0; i < t->depth; i++) {
        if (t->held[i] == id) return true;
    }
    return false;
}

/**
 * Get the highest-priority lock currently held.
 */
TL_INLINE tl_lock_id_t tl_lock_highest_held(void) {
    tl_lock_tracker_t* t = &tl__lock_tracker;
    if (t->depth == 0) return TL_LOCK_NONE;
    return t->held[0]; /* First acquired = highest priority */
}

/* Macros for lock operations with tracking */
#define TL_LOCK(mu, id) do { \
    tl_lock_acquire_check(id); \
    tl_mutex_lock(mu); \
} while(0)

#define TL_UNLOCK(mu, id) do { \
    tl_mutex_unlock(mu); \
    tl_lock_release_check(id); \
} while(0)

#define TL_TRYLOCK(mu, id, result) do { \
    tl_lock_acquire_check(id); \
    (result) = tl_mutex_trylock(mu); \
    if (!(result)) { \
        tl_lock_release_check(id); \
    } \
} while(0)

#else /* !TL_DEBUG */

/* Release mode: no tracking overhead */
#define TL_LOCK(mu, id)           tl_mutex_lock(mu)
#define TL_UNLOCK(mu, id)         tl_mutex_unlock(mu)
#define TL_TRYLOCK(mu, id, result) ((result) = tl_mutex_trylock(mu))

#define tl_lock_acquire_check(id) ((void)0)
#define tl_lock_release_check(id) ((void)0)
#define tl_lock_is_held(id)       (false)
#define tl_lock_highest_held()    (TL_LOCK_NONE)

#endif /* TL_DEBUG */

/*===========================================================================
 * Named Lock Macros for Clarity
 *===========================================================================*/

/* Writer mutex - serializes manifest publication */
#define TL_LOCK_WRITER(tl)    TL_LOCK(&(tl)->writer_mu, TL_LOCK_WRITER_MU)
#define TL_UNLOCK_WRITER(tl)  TL_UNLOCK(&(tl)->writer_mu, TL_LOCK_WRITER_MU)

/* Flush mutex - single flusher at a time */
#define TL_LOCK_FLUSH(tl)     TL_LOCK(&(tl)->flush_mu, TL_LOCK_FLUSH_MU)
#define TL_UNLOCK_FLUSH(tl)   TL_UNLOCK(&(tl)->flush_mu, TL_LOCK_FLUSH_MU)

/* Maintenance mutex - protects maint state */
#define TL_LOCK_MAINT(tl)     TL_LOCK(&(tl)->maint_mu, TL_LOCK_MAINT_MU)
#define TL_UNLOCK_MAINT(tl)   TL_UNLOCK(&(tl)->maint_mu, TL_LOCK_MAINT_MU)

/* Memtable mutex - protects sealed queue */
#define TL_LOCK_MEMTABLE(tl)   TL_LOCK(&(tl)->memtable_mu, TL_LOCK_MEMTABLE_MU)
#define TL_UNLOCK_MEMTABLE(tl) TL_UNLOCK(&(tl)->memtable_mu, TL_LOCK_MEMTABLE_MU)

#endif /* TL_LOCKS_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_locks.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_log.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_LOG_H
#define TL_LOG_H

#include "tl_defs.h"
#include <stdarg.h>

/*===========================================================================
 * Log Context
 *
 * Uses tl_log_level_t from public API (timelog/timelog.h, included via tl_defs.h).
 * Internal code uses TL_LOG_* values directly.
 *===========================================================================*/

typedef struct tl_log_ctx {
    tl_log_fn       fn;
    void*           ctx;
    tl_log_level_t  max_level;
} tl_log_ctx_t;

/*===========================================================================
 * Initialization
 *===========================================================================*/

/**
 * Initialize log context from user configuration.
 * If fn is NULL, logging is disabled.
 * @param level Max log level to accept (use TL_LOG_NONE to disable all)
 */
void tl__log_init(tl_log_ctx_t* log, tl_log_fn fn, void* ctx, tl_log_level_t level);

/*===========================================================================
 * Logging Functions
 *===========================================================================*/

/**
 * Log a message at the specified level.
 * Thread-safe if the user's log function is thread-safe.
 */
void tl__log(tl_log_ctx_t* log, tl_log_level_t level,
             const char* fmt, ...);

void tl__log_v(tl_log_ctx_t* log, tl_log_level_t level,
               const char* fmt, va_list args);

/*===========================================================================
 * Convenience Macros
 *
 * Note: These macros use __VA_ARGS__ without the ## GCC extension for
 * MSVC portability. The format string is included in __VA_ARGS__.
 *===========================================================================*/

/* These require a `tl_log_ctx_t* log` in scope */

#define TL_LOG_ERROR(...) \
    tl__log(log, TL_LOG_ERROR, __VA_ARGS__)

#define TL_LOG_WARN(...) \
    tl__log(log, TL_LOG_WARN, __VA_ARGS__)

#define TL_LOG_INFO(...) \
    tl__log(log, TL_LOG_INFO, __VA_ARGS__)

#ifdef TL_DEBUG
    #define TL_LOG_DEBUG(...) \
        tl__log(log, TL_LOG_DEBUG, __VA_ARGS__)
    #define TL_LOG_TRACE(...) \
        tl__log(log, TL_LOG_TRACE, __VA_ARGS__)
#else
    #define TL_LOG_DEBUG(...) ((void)0)
    #define TL_LOG_TRACE(...) ((void)0)
#endif

/*===========================================================================
 * Global Log Macros (for use before instance is created)
 *===========================================================================*/

/* These use a static null log context - effectively disabled */
#define TL_LOG_STATIC_ERROR(...) ((void)0)
#define TL_LOG_STATIC_WARN(...)  ((void)0)

#endif /* TL_LOG_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_log.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_platform.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_PLATFORM_H
#define TL_PLATFORM_H

/*===========================================================================
 * Platform Detection
 *===========================================================================*/

#if defined(_WIN32) || defined(_WIN64)
    #define TL_PLATFORM_WINDOWS 1
#elif defined(__linux__)
    #define TL_PLATFORM_LINUX 1
#elif defined(__APPLE__)
    #define TL_PLATFORM_MACOS 1
#else
    #define TL_PLATFORM_UNKNOWN 1
#endif

/*===========================================================================
 * Compiler Detection
 *===========================================================================*/

#if defined(_MSC_VER)
    #define TL_COMPILER_MSVC 1
    #define TL_MSVC_VERSION _MSC_VER
#elif defined(__clang__)
    #define TL_COMPILER_CLANG 1
#elif defined(__GNUC__)
    #define TL_COMPILER_GCC 1
#endif

/*===========================================================================
 * Function Attributes
 *===========================================================================*/

#if defined(TL_COMPILER_MSVC)
    #if defined(__clang__)
        #define TL_INLINE        static inline __attribute__((always_inline))
    #else
        #define TL_INLINE        static __forceinline
    #endif
    #define TL_NOINLINE      __declspec(noinline)
    #define TL_RESTRICT      __restrict
    #define TL_LIKELY(x)     (x)
    #define TL_UNLIKELY(x)   (x)
    #define TL_ALIGNED(n)    __declspec(align(n))
    #define TL_ASSUME(x)     __assume(x)
    #define TL_UNREACHABLE() __assume(0)
    #define TL_THREAD_LOCAL  __declspec(thread)
#else
    #define TL_INLINE        static inline __attribute__((always_inline))
    #define TL_NOINLINE      __attribute__((noinline))
    #define TL_RESTRICT      __restrict__
    #define TL_LIKELY(x)     __builtin_expect(!!(x), 1)
    #define TL_UNLIKELY(x)   __builtin_expect(!!(x), 0)
    #define TL_ALIGNED(n)    __attribute__((aligned(n)))
    #define TL_ASSUME(x)     do { if (!(x)) __builtin_unreachable(); } while(0)
    #define TL_UNREACHABLE() __builtin_unreachable()
    #define TL_THREAD_LOCAL  _Thread_local
#endif

/*===========================================================================
 * Cache Line Size
 *===========================================================================*/

#ifndef TL_CACHE_LINE_SIZE
    #define TL_CACHE_LINE_SIZE 64
#endif

#define TL_CACHE_ALIGNED TL_ALIGNED(TL_CACHE_LINE_SIZE)

/*===========================================================================
 * Debug Assertions
 *
 * WARNING: TL_ASSERT maps to TL_ASSUME in release builds, which tells the
 * compiler the condition is always true. This is an optimization hint.
 *
 * NEVER use TL_ASSERT for:
 * - User input validation (use explicit checks + return TL_EINVAL)
 * - API contract enforcement on external data
 * - Anything that could be false due to caller error
 *
 * ONLY use TL_ASSERT for:
 * - Internal invariants provably true by construction
 * - Programmer errors that indicate bugs in timelog itself
 *===========================================================================*/

#ifdef TL_DEBUG
    #include <assert.h>
    #include <stdio.h>
    #include <stdlib.h>  /* for abort() */

    #ifdef TL_TEST_HOOKS
        /*
         * Test hook for intercepting assertions without aborting.
         * When tl__test_assert_hook is set, TL_ASSERT calls the hook
         * instead of aborting, allowing tests to verify assertion conditions.
         *
         * Usage in tests:
         *   tl__test_set_assert_hook(my_hook);
         *   // ... code that should trigger assertion ...
         *   tl__test_set_assert_hook(NULL);
         */
        typedef void (*tl_assert_hook_fn)(const char* file, int line, const char* expr);
        extern tl_assert_hook_fn tl__test_assert_hook;
        void tl__test_set_assert_hook(tl_assert_hook_fn hook);

        #define TL_ASSERT(cond) \
            do { \
                if (!(cond)) { \
                    if (tl__test_assert_hook) { \
                        tl__test_assert_hook(__FILE__, __LINE__, #cond); \
                    } else { \
                        fprintf(stderr, "ASSERT FAILED: %s at %s:%d\n", \
                                #cond, __FILE__, __LINE__); \
                        abort(); \
                    } \
                } \
            } while(0)

        #define TL_ASSERT_MSG(cond, msg) \
            do { \
                if (!(cond)) { \
                    if (tl__test_assert_hook) { \
                        tl__test_assert_hook(__FILE__, __LINE__, #cond ": " msg); \
                    } else { \
                        fprintf(stderr, "ASSERT FAILED: %s (%s) at %s:%d\n", \
                                #cond, msg, __FILE__, __LINE__); \
                        abort(); \
                    } \
                } \
            } while(0)
    #else
        #define TL_ASSERT(cond) assert(cond)
        #define TL_ASSERT_MSG(cond, msg) assert((cond) && (msg))
    #endif /* TL_TEST_HOOKS */
#else
    #define TL_ASSERT(cond) TL_ASSUME(cond)
    #define TL_ASSERT_MSG(cond, msg) TL_ASSUME(cond)
#endif

/*===========================================================================
 * Prefetch Hints
 *===========================================================================*/

#if defined(TL_COMPILER_MSVC)
    #include <intrin.h>
    #define TL_PREFETCH_READ(addr)  _mm_prefetch((const char*)(addr), _MM_HINT_T0)
    #define TL_PREFETCH_WRITE(addr) _mm_prefetch((const char*)(addr), _MM_HINT_T0)
#elif defined(TL_COMPILER_GCC) || defined(TL_COMPILER_CLANG)
    #define TL_PREFETCH_READ(addr)  __builtin_prefetch((addr), 0, 3)
    #define TL_PREFETCH_WRITE(addr) __builtin_prefetch((addr), 1, 3)
#else
    #define TL_PREFETCH_READ(addr)  ((void)(addr))
    #define TL_PREFETCH_WRITE(addr) ((void)(addr))
#endif

#endif /* TL_PLATFORM_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_platform.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_range.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_RANGE_H
#define TL_RANGE_H

#include "tl_defs.h"

/*===========================================================================
 * Unbounded Range Helpers
 *
 * These helpers ensure correct handling of unbounded ranges [t1, +inf).
 *
 * DESIGN PRINCIPLE:
 * Unbounded queries use a boolean flag (t2_unbounded) as the SOLE indicator
 * of infinity. INT64_MAX/TL_TS_MAX is a valid timestamp, NOT a sentinel.
 * When t2_unbounded is true:
 * - The t2 field is ignored (callers should pass 0 for clarity)
 * - All comparisons must check t2_unbounded FIRST before accessing t2
 *
 * Usage pattern:
 *   if (tl_ts_before_end(ts, t2, t2_unbounded)) { ... }
 *   if (tl_range_overlaps(min, max, t1, t2, t2_unbounded)) { ... }
 *
 * Reference: plan_phase5.md Section 5.0
 *===========================================================================*/

/**
 * Check if timestamp is before the end bound.
 *
 * Returns true if ts < t2 (bounded) or always true (unbounded).
 * This is the fundamental predicate for "is ts in range [t1, t2)?".
 *
 * @param ts           Timestamp to check
 * @param t2           End bound (ONLY read if !t2_unbounded)
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @return true if ts is before the end bound
 */
TL_INLINE bool tl_ts_before_end(tl_ts_t ts, tl_ts_t t2, bool t2_unbounded) {
    return t2_unbounded || ts < t2;
}

/**
 * Check if timestamp is at or after the end bound.
 *
 * Returns true if ts >= t2 (bounded) or always false (unbounded).
 * Useful for "stop iteration" checks.
 *
 * @param ts           Timestamp to check
 * @param t2           End bound (ONLY read if !t2_unbounded)
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @return true if ts is at or past the end bound
 */
TL_INLINE bool tl_ts_at_or_past_end(tl_ts_t ts, tl_ts_t t2, bool t2_unbounded) {
    return !t2_unbounded && ts >= t2;
}

/**
 * Check if interval [min_ts, max_ts] overlaps with range [t1, t2) or [t1, +inf).
 *
 * An interval [min_ts, max_ts] (inclusive bounds) overlaps a half-open range
 * [t1, t2) (or unbounded [t1, +inf)) when:
 * - max_ts >= t1 (interval ends at or after range start), AND
 * - min_ts < t2 (interval starts before range end) OR t2_unbounded
 *
 * Used for pruning segments and pages during query planning.
 *
 * @param min_ts       Interval minimum (inclusive)
 * @param max_ts       Interval maximum (inclusive)
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY read if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @return true if the interval overlaps the range
 */
TL_INLINE bool tl_range_overlaps(tl_ts_t min_ts, tl_ts_t max_ts,
                                  tl_ts_t t1, tl_ts_t t2,
                                  bool t2_unbounded) {
    return (max_ts >= t1) && (t2_unbounded || min_ts < t2);
}

/**
 * Check if range [t1, t2) or [t1, +inf) is empty.
 *
 * A bounded range is empty if t1 >= t2.
 * An unbounded range is never empty (assuming t1 is valid).
 *
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY read if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @return true if the range is empty
 */
TL_INLINE bool tl_range_is_empty(tl_ts_t t1, tl_ts_t t2, bool t2_unbounded) {
    return !t2_unbounded && t1 >= t2;
}

/**
 * Compute the overlap start between interval [min_ts, max_ts] and range [t1, t2).
 *
 * Returns max(min_ts, t1) - the first timestamp in the overlap.
 * Caller must first verify that an overlap exists using tl_range_overlaps().
 *
 * @param min_ts  Interval minimum (inclusive)
 * @param t1      Range start (inclusive)
 * @return Start of the overlap region
 */
TL_INLINE tl_ts_t tl_range_overlap_start(tl_ts_t min_ts, tl_ts_t t1) {
    return (min_ts > t1) ? min_ts : t1;
}

#endif /* TL_RANGE_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_range.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_recvec.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_RECVEC_H
#define TL_RECVEC_H

#include "tl_defs.h"
#include "tl_alloc.h"

/*===========================================================================
 * Record Vector
 *
 * A dynamic array of tl_record_t that provides:
 * - Amortized O(1) append for sorted and unsorted insertions
 * - Binary search helpers (lower_bound, upper_bound) for range queries
 * - Reserve/clear/destroy lifecycle
 *
 * Used by:
 * - tl_memtable_t.active_run (append-only sorted records)
 * - tl_memtable_t.active_ooo (sorted out-of-order records)
 * - tl_memrun_t.run and tl_memrun_t.ooo (sealed arrays)
 * - Page builder (sorted record stream)
 *
 * Thread Safety:
 * - Not thread-safe. Caller must provide synchronization.
 *===========================================================================*/

/**
 * Dynamic array of records.
 *
 * Design notes:
 * - The allocator pointer is borrowed; the caller owns the allocator lifetime.
 * - Capacity growth uses 2x strategy (amortized O(1) append).
 * - Zero-length vectors have data == NULL, len == 0, cap == 0.
 */
typedef struct tl_recvec {
    tl_record_t*    data;     /* Array of records */
    size_t          len;      /* Current number of records */
    size_t          cap;      /* Allocated capacity */
    tl_alloc_ctx_t* alloc;    /* Allocator context (borrowed, not owned) */
} tl_recvec_t;

/*---------------------------------------------------------------------------
 * Lifecycle
 *---------------------------------------------------------------------------*/

/**
 * Initialize an empty record vector.
 * @param rv    Vector to initialize
 * @param alloc Allocator context (must outlive the vector)
 */
void tl_recvec_init(tl_recvec_t* rv, tl_alloc_ctx_t* alloc);

/**
 * Destroy a record vector and free memory.
 * Idempotent: safe to call on already-destroyed or zero-initialized vectors.
 * After this call, rv is in a valid empty state (can be destroyed again or reused).
 */
void tl_recvec_destroy(tl_recvec_t* rv);

/**
 * Clear the vector (set len = 0) without freeing memory.
 * Useful for reuse without reallocation.
 */
void tl_recvec_clear(tl_recvec_t* rv);

/*---------------------------------------------------------------------------
 * Capacity Management
 *---------------------------------------------------------------------------*/

/**
 * Ensure capacity for at least min_cap records.
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_recvec_reserve(tl_recvec_t* rv, size_t min_cap);

/**
 * Shrink capacity to exactly fit current length.
 * If len == 0: frees backing storage and sets data=NULL, cap=0.
 * If len == cap: no-op.
 * Otherwise: realloc to len.
 * @return TL_OK on success, TL_ENOMEM if realloc fails (capacity unchanged)
 */
tl_status_t tl_recvec_shrink_to_fit(tl_recvec_t* rv);

/*---------------------------------------------------------------------------
 * Insertion
 *---------------------------------------------------------------------------*/

/**
 * Append a single record to the end.
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_recvec_push(tl_recvec_t* rv, tl_ts_t ts, tl_handle_t handle);

/**
 * Append multiple records to the end.
 * @param records Array of records to append
 * @param n       Number of records
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_recvec_push_n(tl_recvec_t* rv, const tl_record_t* records, size_t n);

/**
 * Insert a record at a specific index, shifting subsequent records.
 * @param idx Index to insert at (0 <= idx <= len)
 * @return TL_OK on success, TL_ENOMEM on allocation failure, TL_EINVAL if idx > len
 */
tl_status_t tl_recvec_insert(tl_recvec_t* rv, size_t idx, tl_ts_t ts, tl_handle_t handle);

/*---------------------------------------------------------------------------
 * Binary Search (for sorted vectors)
 *---------------------------------------------------------------------------*/

/**
 * Find the first index where rv->data[i].ts >= ts.
 * Returns rv->len if all records have ts < target.
 *
 * Precondition: rv is sorted by ts (non-decreasing).
 */
size_t tl_recvec_lower_bound(const tl_recvec_t* rv, tl_ts_t ts);

/**
 * Find the first index where rv->data[i].ts > ts.
 * Returns rv->len if all records have ts <= target.
 *
 * Precondition: rv is sorted by ts (non-decreasing).
 */
size_t tl_recvec_upper_bound(const tl_recvec_t* rv, tl_ts_t ts);

/**
 * Find the range [lo, hi) of indices where rv->data[i].ts is in [t1, t2).
 * @param lo Output: first index with ts >= t1
 * @param hi Output: first index with ts >= t2
 *
 * Precondition: rv is sorted by ts (non-decreasing).
 */
void tl_recvec_range_bounds(const tl_recvec_t* rv, tl_ts_t t1, tl_ts_t t2,
                            size_t* lo, size_t* hi);

/*---------------------------------------------------------------------------
 * Accessors
 *---------------------------------------------------------------------------*/

/**
 * Get pointer to record at index (no bounds check in release).
 */
TL_INLINE const tl_record_t* tl_recvec_get(const tl_recvec_t* rv, size_t idx) {
    TL_ASSERT(idx < rv->len);
    return &rv->data[idx];
}

/**
 * Get mutable pointer to record at index.
 */
TL_INLINE tl_record_t* tl_recvec_get_mut(tl_recvec_t* rv, size_t idx) {
    TL_ASSERT(idx < rv->len);
    return &rv->data[idx];
}

TL_INLINE size_t tl_recvec_len(const tl_recvec_t* rv) {
    return rv->len;
}

TL_INLINE bool tl_recvec_is_empty(const tl_recvec_t* rv) {
    return rv->len == 0;
}

/**
 * Get raw data pointer (for bulk operations).
 * May be NULL if len == 0.
 */
TL_INLINE const tl_record_t* tl_recvec_data(const tl_recvec_t* rv) {
    return rv->data;
}

/**
 * Take ownership of the internal array and reset vector to empty.
 * Caller is responsible for freeing the returned array via tl__free().
 * @param out_len Output: length of returned array
 * @return Array pointer (may be NULL if empty)
 */
tl_record_t* tl_recvec_take(tl_recvec_t* rv, size_t* out_len);

#endif /* TL_RECVEC_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_recvec.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_seqlock.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_SEQLOCK_H
#define TL_SEQLOCK_H

#include "tl_atomic.h"

/*===========================================================================
 * Seqlock for Snapshot Consistency
 *
 * Protocol from timelog_v1_c_software_design_spec.md Section 4.2:
 *
 * Writer (publication):
 *   1. Lock writer_mu
 *   2. view_seq++ (odd = publish in progress)
 *   3. Swap manifest pointer + update memtable state
 *   4. view_seq++ (even = publish complete)
 *   5. Unlock writer_mu
 *
 * Reader (snapshot acquisition):
 *   1. Lock writer_mu (required because we also capture memview)
 *   2. seq1 = load view_seq (must be even)
 *   3. Acquire manifest ref + capture memview
 *   4. seq2 = load view_seq
 *   5. Unlock writer_mu
 *   6. If seq1 != seq2 OR seq1 is odd: retry
 *
 * Note: Unlike a pure seqlock, we hold writer_mu during snapshot to ensure
 * the memview capture is consistent with manifest. The seqlock counter
 * provides an additional consistency check and enables future lock-free
 * optimizations.
 *===========================================================================*/

/*
 * Cache line size for padding calculations.
 * Use the platform definition if available, otherwise default to 64 bytes.
 * 64 bytes is correct for x86-64, ARM64, and most modern architectures.
 * Using padding instead of alignment attributes avoids overalignment UB
 * since malloc only guarantees 16-byte alignment (or 8 on some platforms).
 */
#ifndef TL_CACHE_LINE_SIZE
#define TL_CACHE_LINE_SIZE 64
#endif

/*
 * Verify that cache line size is large enough for padding calculation.
 * If TL_CACHE_LINE_SIZE is overridden to a small value, the padding
 * calculation would underflow. Minimum is sizeof(tl_atomic_u64) + 1.
 */
#if TL_CACHE_LINE_SIZE <= 8
#error "TL_CACHE_LINE_SIZE must be greater than sizeof(tl_atomic_u64) (8 bytes)"
#endif

typedef struct tl_seqlock {
    tl_atomic_u64 seq;
    /*
     * Padding to reduce false sharing with adjacent data.
     * Note: Without alignment, we cannot guarantee the seqlock starts at
     * a cache line boundary. The padding ensures the atomic counter
     * doesn't span cache lines and reduces (but doesn't eliminate) the
     * chance of sharing a line with unrelated data.
     */
    char _pad[TL_CACHE_LINE_SIZE - sizeof(tl_atomic_u64)];
} tl_seqlock_t;

/**
 * Initialize seqlock to even value (0 = idle).
 */
TL_INLINE void tl_seqlock_init(tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    tl_atomic_init_u64(&sl->seq, 0);
}

/**
 * Begin write (increment to odd).
 * Must be called under writer_mu.
 *
 * Uses ACQ_REL ordering:
 * - ACQUIRE: Ensures we see any prior writes before starting our write
 * - RELEASE: Ensures the odd counter is visible before we start modifying data
 * This creates a full barrier that prevents reordering in both directions.
 */
TL_INLINE void tl_seqlock_write_begin(tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    tl_atomic_fetch_add_u64(&sl->seq, 1, TL_MO_ACQ_REL);
#ifdef TL_DEBUG
    /* Verify we're now odd - only check in debug to avoid extra atomic load */
    TL_ASSERT((tl_atomic_load_relaxed_u64(&sl->seq) & 1) == 1);
#endif
}

/**
 * End write (increment to even).
 * Must be called under writer_mu.
 */
TL_INLINE void tl_seqlock_write_end(tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
#ifdef TL_DEBUG
    /* Verify we're currently odd - only check in debug to avoid extra atomic load */
    TL_ASSERT((tl_atomic_load_relaxed_u64(&sl->seq) & 1) == 1);
#endif
    tl_atomic_fetch_add_u64(&sl->seq, 1, TL_MO_RELEASE);
}

/**
 * Read seqlock value (for consistency check).
 * Returns the current sequence number.
 */
TL_INLINE uint64_t tl_seqlock_read(const tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    return tl_atomic_load_acquire_u64(&sl->seq);
}

/**
 * Check if sequence is even (no write in progress).
 */
TL_INLINE bool tl_seqlock_is_even(uint64_t seq) {
    return (seq & 1) == 0;
}

/**
 * Validate read consistency.
 * @param seq1 Value read before operation
 * @param seq2 Value read after operation
 * @return true if consistent (seq1 == seq2 and both even)
 */
TL_INLINE bool tl_seqlock_validate(uint64_t seq1, uint64_t seq2) {
    return (seq1 == seq2) && tl_seqlock_is_even(seq1);
}

/**
 * Get current sequence number (for debugging/metrics).
 */
TL_INLINE uint64_t tl_seqlock_current(const tl_seqlock_t* sl) {
    TL_ASSERT(sl != NULL);
    return tl_atomic_load_relaxed_u64(&sl->seq);
}

#endif /* TL_SEQLOCK_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_seqlock.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_sync.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_SYNC_H
#define TL_SYNC_H

#include "tl_defs.h"
#include "tl_atomic.h"

/*===========================================================================
 * Platform Includes
 *===========================================================================*/

#if defined(TL_PLATFORM_WINDOWS)
    #ifndef WIN32_LEAN_AND_MEAN
        #define WIN32_LEAN_AND_MEAN
    #endif
    #include <windows.h>
#else
    #include <pthread.h>
    #include <errno.h>
#endif

/*===========================================================================
 * Mutex
 *
 * Design: Use SRWLock on Windows (fast, slim) and pthread_mutex on POSIX.
 * Both are non-recursive by default, which matches our usage.
 *===========================================================================*/

#if defined(TL_PLATFORM_WINDOWS)

typedef struct tl_mutex {
    SRWLOCK lock;
#ifdef TL_DEBUG
    volatile DWORD owner;  /* Thread ID of owner, 0 if unlocked */
#endif
} tl_mutex_t;

#else /* POSIX */

typedef struct tl_mutex {
    pthread_mutex_t lock;
#ifdef TL_DEBUG
    /*
     * IMPORTANT: pthread_t is an opaque type - we cannot assign 0 to it.
     * We use 'locked' as the primary indicator and only read 'owner' when
     * 'locked' is true. The owner field is only valid when locked == 1.
     */
    pthread_t owner;    /* Valid only when locked == 1 */
    int locked;         /* 0 = unlocked, 1 = locked */
#endif
} tl_mutex_t;

#endif

/**
 * Initialize a mutex.
 * @return TL_OK on success, TL_EINTERNAL on failure
 */
tl_status_t tl_mutex_init(tl_mutex_t* mu);

/**
 * Destroy a mutex.
 * Mutex must be unlocked. Behavior undefined if locked.
 */
void tl_mutex_destroy(tl_mutex_t* mu);

/**
 * Acquire mutex (blocking).
 */
void tl_mutex_lock(tl_mutex_t* mu);

/**
 * Release mutex.
 * Must be called by the thread that locked it.
 */
void tl_mutex_unlock(tl_mutex_t* mu);

/**
 * Try to acquire mutex (non-blocking).
 * @return true if acquired, false if already locked
 */
bool tl_mutex_trylock(tl_mutex_t* mu);

#ifdef TL_DEBUG
/**
 * Check if current thread holds the mutex (debug only).
 */
bool tl_mutex_is_held(const tl_mutex_t* mu);
#endif

/*===========================================================================
 * Condition Variable
 *
 * Design: Use CONDITION_VARIABLE on Windows, pthread_cond on POSIX.
 *===========================================================================*/

#if defined(TL_PLATFORM_WINDOWS)

typedef struct tl_cond {
    CONDITION_VARIABLE cond;
} tl_cond_t;

#else /* POSIX */

typedef struct tl_cond {
    pthread_cond_t cond;
    bool use_monotonic;  /* true if using CLOCK_MONOTONIC, false for CLOCK_REALTIME */
} tl_cond_t;

#endif

/**
 * Initialize a condition variable.
 * @return TL_OK on success, TL_EINTERNAL on failure
 */
tl_status_t tl_cond_init(tl_cond_t* cv);

/**
 * Destroy a condition variable.
 */
void tl_cond_destroy(tl_cond_t* cv);

/**
 * Wait on condition variable.
 * Mutex must be held; it is released during wait and reacquired before return.
 */
void tl_cond_wait(tl_cond_t* cv, tl_mutex_t* mu);

/**
 * Wait on condition variable with timeout.
 * @param timeout_ms Maximum wait time in milliseconds
 * @return true if signaled, false if timed out
 */
bool tl_cond_timedwait(tl_cond_t* cv, tl_mutex_t* mu, uint32_t timeout_ms);

/**
 * Signal one waiting thread.
 */
void tl_cond_signal(tl_cond_t* cv);

/**
 * Signal all waiting threads.
 */
void tl_cond_broadcast(tl_cond_t* cv);

/*===========================================================================
 * Thread
 *
 * Design: Simple wrapper for background maintenance thread.
 *===========================================================================*/

typedef void* (*tl_thread_fn)(void* arg);

#if defined(TL_PLATFORM_WINDOWS)

typedef struct tl_thread {
    HANDLE handle;
    tl_thread_fn fn;
    void* arg;
    void* result;
} tl_thread_t;

#else /* POSIX */

typedef struct tl_thread {
    pthread_t handle;
    bool valid;
} tl_thread_t;

#endif

/**
 * Create and start a new thread.
 * @param thread Output thread handle
 * @param fn Thread function
 * @param arg Argument passed to fn
 * @return TL_OK on success, TL_EINTERNAL on failure
 */
tl_status_t tl_thread_create(tl_thread_t* thread, tl_thread_fn fn, void* arg);

/**
 * Wait for thread to complete and retrieve result.
 * @param thread Thread to join
 * @param result Optional output for thread return value
 * @return TL_OK on success
 */
tl_status_t tl_thread_join(tl_thread_t* thread, void** result);

/**
 * Get current thread ID (for debugging).
 */
uint64_t tl_thread_self_id(void);

#ifdef TL_DEBUG
/**
 * Set name for the current thread (debug only, for profilers/debuggers).
 *
 * Thread names appear in debuggers, profilers, and tools like htop.
 * This is useful for identifying maintenance worker threads.
 *
 * Platform support:
 * - Windows: SetThreadDescription (Windows 10 1607+, silently fails on older)
 * - Linux: pthread_setname_np (truncates to 15 chars)
 * - macOS: pthread_setname_np (truncates to 63 chars)
 *
 * @param name Thread name (null-terminated, may be truncated by platform)
 */
void tl_thread_set_name(const char* name);
#endif

/*===========================================================================
 * Yield and Sleep
 *===========================================================================*/

/**
 * Yield to other threads.
 */
void tl_thread_yield(void);

/**
 * Sleep for specified milliseconds.
 */
void tl_sleep_ms(uint32_t ms);

/*===========================================================================
 * Monotonic Time
 *===========================================================================*/

/**
 * Get current monotonic time in milliseconds.
 * Used for computing elapsed time in bounded waits.
 * The absolute value is meaningless; only differences are useful.
 */
uint64_t tl_monotonic_ms(void);

#endif /* TL_SYNC_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_sync.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_timelog_internal.h
/*   FROM: internal/
/*
/******************************************************************************/
#ifndef TL_TIMELOG_INTERNAL_H
#define TL_TIMELOG_INTERNAL_H

/*===========================================================================
 * Internal Timelog Structure Definition
 *
 * This header contains the SINGLE authoritative definition of struct tl_timelog.
 * It is included by:
 * - tl_timelog.c (main implementation)
 * - tl_snapshot.c (snapshot acquisition needs field access)
 * - Any future internal module that needs field access
 *
 * IMPORTANT: This is an INTERNAL header. External code must only use the
 * opaque tl_timelog_t pointer from timelog.h.
 *===========================================================================*/

#include "tl_defs.h"
#include "tl_alloc.h"
#include "tl_log.h"
#include "tl_sync.h"
#include "tl_seqlock.h"
#include "../delta/tl_memtable.h"
#include "../storage/tl_manifest.h"
#include "../maint/tl_adaptive.h"

/* Forward declaration to avoid heavy include dependencies. */
struct tl_memview_shared;
typedef struct tl_memview_shared tl_memview_shared_t;

/*===========================================================================
 * Maintenance Worker State Machine (Phase 7)
 *
 * Protected by maint_mu. State transitions:
 *   STOPPED  -> RUNNING  (tl_maint_start)
 *   RUNNING  -> STOPPING (tl_maint_stop initiated)
 *   STOPPING -> STOPPED  (tl_maint_stop completed)
 *
 * The 3-state machine prevents:
 * - Double-spawn: start during RUNNING returns TL_OK (idempotent)
 * - Double-join: start/stop during STOPPING returns TL_EBUSY/TL_OK
 *===========================================================================*/
typedef enum tl_worker_state {
    TL_WORKER_STOPPED  = 0,  /* No worker thread */
    TL_WORKER_RUNNING  = 1,  /* Worker thread active */
    TL_WORKER_STOPPING = 2   /* Stop requested, join in progress */
} tl_worker_state_t;

/**
 * Core timelog instance structure.
 *
 * Design notes:
 * - Cache-aligned to prevent false sharing in concurrent access
 * - Frequently accessed fields grouped together
 * - Immutable config stored inline (no indirection)
 */
struct tl_timelog {
    /*-----------------------------------------------------------------------
     * Configuration (immutable after init)
     *-----------------------------------------------------------------------*/
    tl_config_t     config;

    /* Computed/normalized config values */
    tl_ts_t         effective_window_size;
    size_t          effective_ooo_budget;

    /*-----------------------------------------------------------------------
     * Subsystem Contexts
     *-----------------------------------------------------------------------*/
    tl_alloc_ctx_t  alloc;
    tl_log_ctx_t    log;

    /*-----------------------------------------------------------------------
     * Synchronization (Phase 1)
     *
     * Lock ordering: maint_mu -> flush_mu -> writer_mu -> memtable_mu
     *-----------------------------------------------------------------------*/

    /* Writer mutex: serializes manifest publication and snapshot capture.
     * Held briefly during the publish phase of flush/compaction. */
    tl_mutex_t      writer_mu;

    /* Flush mutex: serializes flush build + publish (single flusher). */
    tl_mutex_t      flush_mu;

    /* Maintenance mutex: protects maint state flags and thread lifecycle. */
    tl_mutex_t      maint_mu;
    tl_cond_t       maint_cond;

    /* Memtable mutex: protects sealed memrun queue. */
    tl_mutex_t      memtable_mu;
    tl_cond_t       memtable_cond;  /* Backpressure: sealed queue has space */

    /* Seqlock for snapshot consistency. Even = idle, odd = publish in progress. */
    tl_seqlock_t    view_seq;

    /*-----------------------------------------------------------------------
     * Lifecycle Flag
     *
     * is_open is only modified at open/close boundaries when no other
     * threads should be accessing the instance.
     *-----------------------------------------------------------------------*/
    bool            is_open;

    /*-----------------------------------------------------------------------
     * Maintenance State (Phase 7)
     *
     * CRITICAL: All fields in this section are protected by maint_mu.
     * NO atomics are used. This eliminates the lost-work race condition
     * that exists with load-then-store patterns on atomic flags.
     *
     * The state machine + plain bools pattern from plan_phase7.md:
     * - State machine prevents double-spawn/double-join races
     * - Mutex-protected flags ensure work is never lost
     * - Flag set always happens (even if worker not RUNNING)
     * - Signal gated on state (only when RUNNING)
     *-----------------------------------------------------------------------*/
    tl_worker_state_t maint_state;      /* State machine: STOPPED/RUNNING/STOPPING */
    bool              maint_shutdown;   /* Signal worker to exit */
    bool              flush_pending;    /* Sealed memruns exist */
    bool              compact_pending;  /* Compaction requested */
    tl_thread_t       maint_thread;     /* Worker thread handle (valid when RUNNING) */

    /*-----------------------------------------------------------------------
     * Adaptive Segmentation State (V-Next)
     *
     * Protected by maint_mu. Single writer: maintenance thread only.
     * Tracks EWMA density and failure counters for window adaptation.
     * The authoritative window is `effective_window_size` (above).
     *-----------------------------------------------------------------------*/
    tl_adaptive_state_t adaptive;

    /*-----------------------------------------------------------------------
     * Delta Layer (Phase 4)
     *-----------------------------------------------------------------------*/

    /* Memtable: mutable write buffer for inserts and tombstones */
    tl_memtable_t   memtable;

    /* Snapshot memview cache (for reuse when memtable epoch unchanged) */
    tl_memview_shared_t* memview_cache;
    uint64_t             memview_cache_epoch;

    /*-----------------------------------------------------------------------
     * Storage Layer (Phase 5)
     *
     * The manifest is the atomic publication root for storage.
     * Swapped atomically under writer_mu + seqlock during flush/compaction.
     *-----------------------------------------------------------------------*/
    tl_manifest_t*  manifest;       /* Current manifest (atomic publication root) */
    uint32_t        next_gen;       /* Monotonic generation for new segments */

    /*-----------------------------------------------------------------------
     * Operational Counters (cumulative since open)
     *
     * These are atomic because they may be incremented by the writer thread
     * (seals, ooo_budget_hits, backpressure) or the maintenance thread
     * (flushes, compactions) while being read by stats queries.
     *-----------------------------------------------------------------------*/
    tl_atomic_u64   seals_total;        /* Memtable seals performed */
    tl_atomic_u64   ooo_budget_hits;    /* OOO budget exceeded (forced sort) */
    tl_atomic_u64   backpressure_waits; /* Writer blocked on sealed queue */
    tl_atomic_u64   flushes_total;      /* Flush operations completed */
    tl_atomic_u64   compactions_total;  /* Compaction operations completed */

#ifdef TL_DEBUG
    /*-----------------------------------------------------------------------
     * Debug-Only Snapshot Tracking
     *
     * Counts outstanding snapshots to detect leaks at close time.
     * Atomic because snapshots can be acquired/released from multiple threads.
     *-----------------------------------------------------------------------*/
    tl_atomic_u32   snapshot_count; /* Outstanding snapshot count */
#endif
};

#endif /* TL_TIMELOG_INTERNAL_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_timelog_internal.h
/------------------------------------------------------------------------------/
