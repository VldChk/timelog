#include "internal/tl_alloc.h"
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* Libc wrappers that ignore ctx */
static void* libc_malloc(void* ctx, size_t size) {
    (void)ctx;
    return malloc(size);
}

static void* libc_calloc(void* ctx, size_t count, size_t size) {
    (void)ctx;
    return calloc(count, size);
}

static void* libc_realloc(void* ctx, void* ptr, size_t new_size) {
    (void)ctx;
    return realloc(ptr, new_size);
}

static void libc_free(void* ctx, void* ptr) {
    (void)ctx;
    free(ptr);
}

void tl_allocator_init_default(tl_allocator_t* alloc) {
    if (alloc == NULL) return;
    alloc->ctx = NULL;
    alloc->malloc_fn = libc_malloc;
    alloc->calloc_fn = libc_calloc;
    alloc->realloc_fn = libc_realloc;
    alloc->free_fn = libc_free;
}

void* tl__malloc(const tl_allocator_t* alloc, size_t size) {
    if (alloc == NULL || alloc->malloc_fn == NULL) {
        return malloc(size);
    }
    return alloc->malloc_fn(alloc->ctx, size);
}

void* tl__calloc(const tl_allocator_t* alloc, size_t count, size_t size) {
    if (alloc == NULL || alloc->calloc_fn == NULL) {
        return calloc(count, size);
    }
    return alloc->calloc_fn(alloc->ctx, count, size);
}

void* tl__realloc(const tl_allocator_t* alloc, void* ptr, size_t new_size) {
    if (alloc == NULL || alloc->realloc_fn == NULL) {
        return realloc(ptr, new_size);
    }
    return alloc->realloc_fn(alloc->ctx, ptr, new_size);
}

void tl__free(const tl_allocator_t* alloc, void* ptr) {
    if (ptr == NULL) return;
    if (alloc == NULL || alloc->free_fn == NULL) {
        free(ptr);
        return;
    }
    alloc->free_fn(alloc->ctx, ptr);
}

/*
 * Aligned allocation strategy:
 *
 * For custom allocators that don't provide aligned_alloc, we use the
 * "over-allocate and align" technique:
 * 1. Allocate (size + alignment + sizeof(void*))
 * 2. Store original pointer just before the aligned address
 * 3. Return aligned address
 *
 * For libc, use aligned_alloc where available (C11), else _aligned_malloc (MSVC).
 */

#if defined(_WIN32)
#include <malloc.h>
#define TL_HAS_ALIGNED_MALLOC 1
#elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
#define TL_HAS_ALIGNED_ALLOC 1
#endif

void* tl__aligned_alloc(const tl_allocator_t* alloc, size_t alignment, size_t size) {
    /* Alignment must be power of 2 and >= sizeof(void*) */
    if (alignment == 0 || (alignment & (alignment - 1)) != 0) {
        return NULL;
    }
    if (alignment < sizeof(void*)) {
        alignment = sizeof(void*);
    }

    /* Use platform-native for default allocator */
    if (alloc == NULL || alloc->malloc_fn == libc_malloc) {
#if defined(TL_HAS_ALIGNED_MALLOC)
        return _aligned_malloc(size, alignment);
#elif defined(TL_HAS_ALIGNED_ALLOC)
        /* aligned_alloc requires size to be multiple of alignment */
        size_t aligned_size = (size + alignment - 1) & ~(alignment - 1);
        return aligned_alloc(alignment, aligned_size);
#endif
    }

    /* Manual alignment for custom allocators */
    size_t total = size + alignment + sizeof(void*);
    void* raw = tl__malloc(alloc, total);
    if (raw == NULL) return NULL;

    /* Calculate aligned address */
    uintptr_t raw_addr = (uintptr_t)raw + sizeof(void*);
    uintptr_t aligned_addr = (raw_addr + alignment - 1) & ~(alignment - 1);

    /* Store original pointer for free */
    void** ptr_store = (void**)(aligned_addr - sizeof(void*));
    *ptr_store = raw;

    return (void*)aligned_addr;
}

void tl__aligned_free(const tl_allocator_t* alloc, void* ptr) {
    if (ptr == NULL) return;

    if (alloc == NULL || alloc->free_fn == libc_free) {
#if defined(TL_HAS_ALIGNED_MALLOC)
        _aligned_free(ptr);
        return;
#elif defined(TL_HAS_ALIGNED_ALLOC)
        free(ptr);
        return;
#endif
    }

    /* Retrieve original pointer */
    void** ptr_store = (void**)ptr - 1;
    tl__free(alloc, *ptr_store);
}
