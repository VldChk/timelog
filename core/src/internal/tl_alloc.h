#ifndef TL_ALLOC_H
#define TL_ALLOC_H

#include "tl_defs.h"
#include "tl_atomic.h"

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
    tl_atomic_u64  total_allocated;
    tl_atomic_u64  allocation_count;
    tl_atomic_u64  peak_allocated;
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
 * Allocation Safety Helpers
 *===========================================================================*/

/**
 * Check if allocation size would overflow size_t.
 *
 * Use this before multiplying count * elem_size for allocation.
 *
 * @param count     Number of elements
 * @param elem_size Size of each element in bytes
 * @return true if count * elem_size would overflow size_t
 */
TL_INLINE bool tl__alloc_would_overflow(size_t count, size_t elem_size) {
    return elem_size != 0 && count > SIZE_MAX / elem_size;
}

/**
 * Compute next capacity >= required using 2x growth.
 *
 * Growth strategy:
 * - If current == 0, start with min_cap
 * - Double until capacity >= required
 * - Return 0 on overflow (cannot satisfy request)
 *
 * @param current  Current capacity (may be 0 for first allocation)
 * @param required Minimum capacity needed (typically len + additional)
 * @param min_cap  Minimum initial capacity (e.g., 8 for heap, 16 for recvec)
 * @return New capacity >= required, or 0 if overflow would occur
 *
 * Usage:
 *   size_t new_cap = tl__grow_capacity(vec->cap, vec->len + 1, 16);
 *   if (new_cap == 0 || tl__alloc_would_overflow(new_cap, sizeof(elem_t))) {
 *       return TL_ENOMEM;
 *   }
 */
TL_INLINE size_t tl__grow_capacity(size_t current, size_t required, size_t min_cap) {
    TL_ASSERT(min_cap > 0);  /* Initial capacity must be positive */

    size_t new_cap = (current == 0) ? min_cap : current;

    while (new_cap < required) {
        if (new_cap > SIZE_MAX / 2) {
            return 0;  /* Cannot double without overflow */
        }
        new_cap *= 2;
    }

    return new_cap;
}

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
    do { tl__free((ctx), (void*)(ptr)); (ptr) = NULL; } while(0)

/*===========================================================================
 * Debug Statistics (Debug Builds Only)
 *===========================================================================*/

#ifdef TL_DEBUG
size_t tl__alloc_get_total(const tl_alloc_ctx_t* ctx);
size_t tl__alloc_get_count(const tl_alloc_ctx_t* ctx);
size_t tl__alloc_get_peak(const tl_alloc_ctx_t* ctx);
#endif

#endif /* TL_ALLOC_H */
