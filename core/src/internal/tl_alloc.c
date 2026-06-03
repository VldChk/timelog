#include "tl_alloc.h"
#include "tl_log.h"
#include <stdlib.h>
#include <stdio.h>

/*===========================================================================
 * Default Allocator (libc)
 *===========================================================================*/

static void* default_malloc(void* ctx, size_t size) {
    (void)ctx;
    return malloc(size);
}

static void* default_calloc(void* ctx, size_t count, size_t size) {
    (void)ctx;
    return calloc(count, size);
}

static void* default_realloc(void* ctx, void* ptr, size_t new_size) {
    (void)ctx;
    return realloc(ptr, new_size);
}

static void default_free(void* ctx, void* ptr) {
    (void)ctx;
    free(ptr);
}

/*===========================================================================
 * Initialization
 *===========================================================================*/

void tl__alloc_init(tl_alloc_ctx_t* ctx, const tl_allocator_t* user_alloc) {
    TL_ASSERT(ctx != NULL);

    memset(ctx, 0, sizeof(*ctx));

#ifdef TL_DEBUG
    tl_atomic_init_u64(&ctx->total_allocated, 0);
    tl_atomic_init_u64(&ctx->allocation_count, 0);
    tl_atomic_init_u64(&ctx->peak_allocated, 0);
#endif

    if (user_alloc == NULL ||
        user_alloc->malloc_fn == NULL ||
        user_alloc->free_fn == NULL) {
        /* Fall back to the libc allocator when the user supplied no hooks
         * or omitted the mandatory malloc/free pair. */
        ctx->alloc.ctx = NULL;
        ctx->alloc.malloc_fn  = default_malloc;
        ctx->alloc.calloc_fn  = default_calloc;
        ctx->alloc.realloc_fn = default_realloc;
        ctx->alloc.free_fn    = default_free;
        ctx->is_default = true;
    } else {
        ctx->alloc = *user_alloc;
        ctx->is_default = false;

        /* calloc_fn is optional; tl__calloc will emulate it with malloc +
         * memset when missing. realloc_fn is also optional but emulation is
         * impossible without the old allocation size, so tl__realloc will
         * fail-stop for resize operations rather than risk data corruption.
         * Callers that must grow buffers therefore have to supply it. */
    }
}

void tl__alloc_destroy(tl_alloc_ctx_t* ctx) {
    if (ctx == NULL) return;

#ifdef TL_DEBUG
    uint64_t count = tl_atomic_load_u64(&ctx->allocation_count, TL_MO_RELAXED);
    if (count != 0) {
        uint64_t total = tl_atomic_load_u64(&ctx->total_allocated, TL_MO_RELAXED);
        /* The allocator carries no log context, so this leak warning bypasses
         * the structured logging facility and writes straight to stderr. */
        fprintf(stderr, "[WARN] Memory leak detected: %zu allocations, %zu bytes\n",
                (size_t)count, (size_t)total);
    }
#endif

    memset(ctx, 0, sizeof(*ctx));
}

/*===========================================================================
 * Allocation Functions
 *===========================================================================*/

void* tl__malloc(tl_alloc_ctx_t* ctx, size_t size) {
    TL_ASSERT(ctx != NULL);
    TL_ASSERT(size > 0);

    void* ptr = ctx->alloc.malloc_fn(ctx->alloc.ctx, size);

#ifdef TL_DEBUG
    if (ptr != NULL) {
        uint64_t total = tl_atomic_fetch_add_u64(&ctx->total_allocated,
                                                 (uint64_t)size,
                                                 TL_MO_RELAXED) + (uint64_t)size;
        tl_atomic_fetch_add_u64(&ctx->allocation_count, 1, TL_MO_RELAXED);

        uint64_t peak = tl_atomic_load_u64(&ctx->peak_allocated, TL_MO_RELAXED);
        while (total > peak) {
            if (tl_atomic_cas_u64(&ctx->peak_allocated, &peak,
                                  total, TL_MO_RELAXED, TL_MO_RELAXED)) {
                break;
            }
        }
    }
#endif

    return ptr;
}

void* tl__calloc(tl_alloc_ctx_t* ctx, size_t count, size_t size) {
    TL_ASSERT(ctx != NULL);

    if (count == 0 || size == 0) {
        return NULL;
    }

    /* Overflow guard: rely on the round-trip identity (a*b)/a == b. */
    size_t total = count * size;
    if (total / count != size) {
        return NULL;
    }

    void* ptr;

    if (ctx->alloc.calloc_fn != NULL) {
        ptr = ctx->alloc.calloc_fn(ctx->alloc.ctx, count, size);
    } else {
        ptr = ctx->alloc.malloc_fn(ctx->alloc.ctx, total);
        if (ptr != NULL) {
            memset(ptr, 0, total);
        }
    }

#ifdef TL_DEBUG
    if (ptr != NULL) {
        uint64_t total_bytes = tl_atomic_fetch_add_u64(&ctx->total_allocated,
                                                       (uint64_t)total,
                                                       TL_MO_RELAXED) + (uint64_t)total;
        tl_atomic_fetch_add_u64(&ctx->allocation_count, 1, TL_MO_RELAXED);

        uint64_t peak = tl_atomic_load_u64(&ctx->peak_allocated, TL_MO_RELAXED);
        while (total_bytes > peak) {
            if (tl_atomic_cas_u64(&ctx->peak_allocated, &peak,
                                  total_bytes, TL_MO_RELAXED, TL_MO_RELAXED)) {
                break;
            }
        }
    }
#endif

    return ptr;
}

void* tl__mallocarray(tl_alloc_ctx_t* ctx, size_t count, size_t size) {
    TL_ASSERT(ctx != NULL);

    if (count == 0 || size == 0) {
        return NULL;
    }

    if (tl__alloc_would_overflow(count, size)) {
        return NULL;
    }

    return tl__malloc(ctx, count * size);
}

void* tl__reallocarray(tl_alloc_ctx_t* ctx, void* ptr, size_t count, size_t size) {
    TL_ASSERT(ctx != NULL);

    if (count == 0 || size == 0) {
        (void)tl__realloc(ctx, ptr, 0);
        return NULL;
    }

    if (tl__alloc_would_overflow(count, size)) {
        /* Match POSIX reallocarray semantics: on overflow the original
         * allocation is preserved so the caller keeps the only reference. */
        return NULL;
    }

    return tl__realloc(ctx, ptr, count * size);
}

void* tl__realloc(tl_alloc_ctx_t* ctx, void* ptr, size_t new_size) {
    TL_ASSERT(ctx != NULL);

    if (new_size == 0) {
        tl__free(ctx, ptr);
        return NULL;
    }

    if (ptr == NULL) {
        return tl__malloc(ctx, new_size);
    }

    /* Resize requires a user-supplied realloc_fn: without the original
     * allocation size we cannot safely malloc-copy-free, and silently
     * truncating would corrupt data. Fail rather than guess. */
    if (ctx->alloc.realloc_fn == NULL) {
        return NULL;
    }

    void* new_ptr = ctx->alloc.realloc_fn(ctx->alloc.ctx, ptr, new_size);

    /* Debug counters do not track resize deltas: we'd need a size-tracking
     * wrapper to compute the difference, which is more bookkeeping than
     * the diagnostic counters justify. */
    return new_ptr;
}

void tl__free(tl_alloc_ctx_t* ctx, void* ptr) {
    if (ctx == NULL || ptr == NULL) return;

#ifdef TL_DEBUG
    /* Debug-only allocation count: guard the CAS loop against underflow so
     * an accounting mismatch produces an assertion rather than wrapping to
     * UINT64_MAX and masking later bugs. */
    uint64_t expected = tl_atomic_load_u64(&ctx->allocation_count, TL_MO_RELAXED);
    for (;;) {
        TL_VERIFY(expected > 0);
        uint64_t desired = expected - 1;
        if (tl_atomic_cas_u64(&ctx->allocation_count, &expected, desired,
                              TL_MO_RELAXED, TL_MO_RELAXED)) {
            break;
        }
    }
#endif

    ctx->alloc.free_fn(ctx->alloc.ctx, ptr);
}

/*===========================================================================
 * Debug Statistics
 *===========================================================================*/

#ifdef TL_DEBUG
size_t tl__alloc_get_total(const tl_alloc_ctx_t* ctx) {
    return ctx ? (size_t)tl_atomic_load_u64(&ctx->total_allocated, TL_MO_RELAXED) : 0;
}

size_t tl__alloc_get_count(const tl_alloc_ctx_t* ctx) {
    return ctx ? (size_t)tl_atomic_load_u64(&ctx->allocation_count, TL_MO_RELAXED) : 0;
}

size_t tl__alloc_get_peak(const tl_alloc_ctx_t* ctx) {
    return ctx ? (size_t)tl_atomic_load_u64(&ctx->peak_allocated, TL_MO_RELAXED) : 0;
}
#endif
