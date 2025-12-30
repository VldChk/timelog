#ifndef TL_ATOMIC_H
#define TL_ATOMIC_H

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Atomic types using C11 atomics or compiler intrinsics.
 *
 * We provide both:
 * 1. Atomic pointer (for manifest publication)
 * 2. Atomic uint64 (for view sequence / seqlock)
 * 3. Atomic uint32 (for refcounts)
 */

#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L && !defined(__STDC_NO_ATOMICS__)
#include <stdatomic.h>
#define TL_USE_C11_ATOMICS 1
typedef _Atomic(void*)    tl_atomic_ptr_t;
typedef _Atomic(uint64_t) tl_atomic_u64_t;
typedef _Atomic(uint32_t) tl_atomic_u32_t;
#elif defined(_MSC_VER)
#include <intrin.h>
#define TL_USE_MSVC_INTRINSICS 1
typedef void* volatile    tl_atomic_ptr_t;
typedef uint64_t volatile tl_atomic_u64_t;
typedef uint32_t volatile tl_atomic_u32_t;
#elif defined(__GNUC__) || defined(__clang__)
#define TL_USE_GCC_BUILTINS 1
typedef void*    tl_atomic_ptr_t;
typedef uint64_t tl_atomic_u64_t;
typedef uint32_t tl_atomic_u32_t;
#else
#error "No atomic implementation available for this platform"
#endif

/*
 * Atomic pointer operations
 */
void* tl_atomic_ptr_load(const tl_atomic_ptr_t* ptr);
void  tl_atomic_ptr_store(tl_atomic_ptr_t* ptr, void* val);
void* tl_atomic_ptr_exchange(tl_atomic_ptr_t* ptr, void* val);
bool  tl_atomic_ptr_cas(tl_atomic_ptr_t* ptr, void** expected, void* desired);

/*
 * Atomic uint64 operations (for seqlock / view_seq)
 */
uint64_t tl_atomic_u64_load(const tl_atomic_u64_t* ptr);
void     tl_atomic_u64_store(tl_atomic_u64_t* ptr, uint64_t val);
uint64_t tl_atomic_u64_fetch_add(tl_atomic_u64_t* ptr, uint64_t val);

/*
 * Atomic uint32 operations (for refcounts)
 */
uint32_t tl_atomic_u32_load(const tl_atomic_u32_t* ptr);
void     tl_atomic_u32_store(tl_atomic_u32_t* ptr, uint32_t val);
uint32_t tl_atomic_u32_fetch_add(tl_atomic_u32_t* ptr, uint32_t val);
uint32_t tl_atomic_u32_fetch_sub(tl_atomic_u32_t* ptr, uint32_t val);

/*
 * Memory barriers
 */
void tl_atomic_thread_fence_acquire(void);
void tl_atomic_thread_fence_release(void);
void tl_atomic_thread_fence_seq_cst(void);

/*
 * Seqlock helper: check if sequence is even (stable)
 */
static inline bool tl_seqlock_is_stable(uint64_t seq) {
    return (seq & 1) == 0;
}

#ifdef __cplusplus
}
#endif

#endif /* TL_ATOMIC_H */
