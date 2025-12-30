#include "internal/tl_atomic.h"

#if defined(TL_USE_C11_ATOMICS)

void* tl_atomic_ptr_load(const tl_atomic_ptr_t* ptr) {
    return atomic_load_explicit((tl_atomic_ptr_t*)ptr, memory_order_acquire);
}

void tl_atomic_ptr_store(tl_atomic_ptr_t* ptr, void* val) {
    atomic_store_explicit(ptr, val, memory_order_release);
}

void* tl_atomic_ptr_exchange(tl_atomic_ptr_t* ptr, void* val) {
    return atomic_exchange_explicit(ptr, val, memory_order_acq_rel);
}

bool tl_atomic_ptr_cas(tl_atomic_ptr_t* ptr, void** expected, void* desired) {
    return atomic_compare_exchange_strong_explicit(
        ptr, expected, desired,
        memory_order_acq_rel, memory_order_acquire);
}

uint64_t tl_atomic_u64_load(const tl_atomic_u64_t* ptr) {
    return atomic_load_explicit((tl_atomic_u64_t*)ptr, memory_order_acquire);
}

void tl_atomic_u64_store(tl_atomic_u64_t* ptr, uint64_t val) {
    atomic_store_explicit(ptr, val, memory_order_release);
}

uint64_t tl_atomic_u64_fetch_add(tl_atomic_u64_t* ptr, uint64_t val) {
    return atomic_fetch_add_explicit(ptr, val, memory_order_acq_rel);
}

uint32_t tl_atomic_u32_load(const tl_atomic_u32_t* ptr) {
    return atomic_load_explicit((tl_atomic_u32_t*)ptr, memory_order_acquire);
}

void tl_atomic_u32_store(tl_atomic_u32_t* ptr, uint32_t val) {
    atomic_store_explicit(ptr, val, memory_order_release);
}

uint32_t tl_atomic_u32_fetch_add(tl_atomic_u32_t* ptr, uint32_t val) {
    return atomic_fetch_add_explicit(ptr, val, memory_order_acq_rel);
}

uint32_t tl_atomic_u32_fetch_sub(tl_atomic_u32_t* ptr, uint32_t val) {
    return atomic_fetch_sub_explicit(ptr, val, memory_order_acq_rel);
}

void tl_atomic_thread_fence_acquire(void) {
    atomic_thread_fence(memory_order_acquire);
}

void tl_atomic_thread_fence_release(void) {
    atomic_thread_fence(memory_order_release);
}

void tl_atomic_thread_fence_seq_cst(void) {
    atomic_thread_fence(memory_order_seq_cst);
}

#elif defined(TL_USE_MSVC_INTRINSICS)

/* MSVC implementation using Interlocked* functions */
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>

void* tl_atomic_ptr_load(const tl_atomic_ptr_t* ptr) {
    void* val = *ptr;
    MemoryBarrier();
    return val;
}

void tl_atomic_ptr_store(tl_atomic_ptr_t* ptr, void* val) {
    MemoryBarrier();
    *ptr = val;
    MemoryBarrier();
}

void* tl_atomic_ptr_exchange(tl_atomic_ptr_t* ptr, void* val) {
    return InterlockedExchangePointer(ptr, val);
}

bool tl_atomic_ptr_cas(tl_atomic_ptr_t* ptr, void** expected, void* desired) {
    void* old = InterlockedCompareExchangePointer(ptr, desired, *expected);
    if (old == *expected) {
        return true;
    }
    *expected = old;
    return false;
}

uint64_t tl_atomic_u64_load(const tl_atomic_u64_t* ptr) {
    /* Use InterlockedCompareExchange64 for atomic 64-bit load on x86 */
    return (uint64_t)InterlockedCompareExchange64((volatile LONG64*)ptr, 0, 0);
}

void tl_atomic_u64_store(tl_atomic_u64_t* ptr, uint64_t val) {
    InterlockedExchange64((volatile LONG64*)ptr, (LONG64)val);
}

uint64_t tl_atomic_u64_fetch_add(tl_atomic_u64_t* ptr, uint64_t val) {
    return (uint64_t)InterlockedExchangeAdd64((volatile LONG64*)ptr, (LONG64)val);
}

uint32_t tl_atomic_u32_load(const tl_atomic_u32_t* ptr) {
    uint32_t val = *ptr;
    MemoryBarrier();
    return val;
}

void tl_atomic_u32_store(tl_atomic_u32_t* ptr, uint32_t val) {
    MemoryBarrier();
    InterlockedExchange((volatile LONG*)ptr, (LONG)val);
}

uint32_t tl_atomic_u32_fetch_add(tl_atomic_u32_t* ptr, uint32_t val) {
    return (uint32_t)InterlockedExchangeAdd((volatile LONG*)ptr, (LONG)val);
}

uint32_t tl_atomic_u32_fetch_sub(tl_atomic_u32_t* ptr, uint32_t val) {
    return (uint32_t)InterlockedExchangeAdd((volatile LONG*)ptr, -(LONG)val);
}

void tl_atomic_thread_fence_acquire(void) { MemoryBarrier(); }
void tl_atomic_thread_fence_release(void) { MemoryBarrier(); }
void tl_atomic_thread_fence_seq_cst(void) { MemoryBarrier(); }

#elif defined(TL_USE_GCC_BUILTINS)

/* GCC/Clang implementation using __atomic builtins */
void* tl_atomic_ptr_load(const tl_atomic_ptr_t* ptr) {
    return __atomic_load_n(ptr, __ATOMIC_ACQUIRE);
}

void tl_atomic_ptr_store(tl_atomic_ptr_t* ptr, void* val) {
    __atomic_store_n(ptr, val, __ATOMIC_RELEASE);
}

void* tl_atomic_ptr_exchange(tl_atomic_ptr_t* ptr, void* val) {
    return __atomic_exchange_n(ptr, val, __ATOMIC_ACQ_REL);
}

bool tl_atomic_ptr_cas(tl_atomic_ptr_t* ptr, void** expected, void* desired) {
    return __atomic_compare_exchange_n(
        ptr, expected, desired, false,
        __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
}

uint64_t tl_atomic_u64_load(const tl_atomic_u64_t* ptr) {
    return __atomic_load_n(ptr, __ATOMIC_ACQUIRE);
}

void tl_atomic_u64_store(tl_atomic_u64_t* ptr, uint64_t val) {
    __atomic_store_n(ptr, val, __ATOMIC_RELEASE);
}

uint64_t tl_atomic_u64_fetch_add(tl_atomic_u64_t* ptr, uint64_t val) {
    return __atomic_fetch_add(ptr, val, __ATOMIC_ACQ_REL);
}

uint32_t tl_atomic_u32_load(const tl_atomic_u32_t* ptr) {
    return __atomic_load_n(ptr, __ATOMIC_ACQUIRE);
}

void tl_atomic_u32_store(tl_atomic_u32_t* ptr, uint32_t val) {
    __atomic_store_n(ptr, val, __ATOMIC_RELEASE);
}

uint32_t tl_atomic_u32_fetch_add(tl_atomic_u32_t* ptr, uint32_t val) {
    return __atomic_fetch_add(ptr, val, __ATOMIC_ACQ_REL);
}

uint32_t tl_atomic_u32_fetch_sub(tl_atomic_u32_t* ptr, uint32_t val) {
    return __atomic_fetch_sub(ptr, val, __ATOMIC_ACQ_REL);
}

void tl_atomic_thread_fence_acquire(void) { __atomic_thread_fence(__ATOMIC_ACQUIRE); }
void tl_atomic_thread_fence_release(void) { __atomic_thread_fence(__ATOMIC_RELEASE); }
void tl_atomic_thread_fence_seq_cst(void) { __atomic_thread_fence(__ATOMIC_SEQ_CST); }

#endif
