#ifndef TL_ALLOC_H
#define TL_ALLOC_H

/*
 * Internal allocator header.
 * Re-exports tl_allocator_t from public header and adds internal functions.
 */
#include "../../include/timelog/timelog.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initialize allocator to use libc functions.
 */
void tl_allocator_init_default(tl_allocator_t* alloc);

/**
 * Internal allocation functions using the provided allocator.
 * These handle NULL function pointers by falling back to libc.
 */
void* tl__malloc(const tl_allocator_t* alloc, size_t size);
void* tl__calloc(const tl_allocator_t* alloc, size_t count, size_t size);
void* tl__realloc(const tl_allocator_t* alloc, void* ptr, size_t new_size);
void  tl__free(const tl_allocator_t* alloc, void* ptr);

/**
 * Aligned allocation (for cache-line alignment, SIMD, etc.)
 * Falls back to over-allocation + manual alignment if needed.
 */
void* tl__aligned_alloc(const tl_allocator_t* alloc, size_t alignment, size_t size);
void  tl__aligned_free(const tl_allocator_t* alloc, void* ptr);

#ifdef __cplusplus
}
#endif

#endif /* TL_ALLOC_H */
