/*
============================================================================

   COMBINED SOURCE FILE: internal.c

   Generated from: core/src/internal/
   Generated at:   2026-01-20 23:27:38

   This file combines all .c files from the internal/ subfolder.

   Files included:
 *   - tl_alloc.c
 *   - tl_heap.c
 *   - tl_intervals.c
 *   - tl_log.c
 *   - tl_recvec.c
 *   - tl_sync.c
 *   - tl_test_hooks.c

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: tl_alloc.c
/*   FROM: internal/
/*
/******************************************************************************/
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

    if (user_alloc == NULL ||
        user_alloc->malloc_fn == NULL ||
        user_alloc->free_fn == NULL) {
        /* Use default libc allocator */
        ctx->alloc.ctx = NULL;
        ctx->alloc.malloc_fn  = default_malloc;
        ctx->alloc.calloc_fn  = default_calloc;
        ctx->alloc.realloc_fn = default_realloc;
        ctx->alloc.free_fn    = default_free;
        ctx->is_default = true;
    } else {
        /* Use user-provided allocator */
        ctx->alloc = *user_alloc;
        ctx->is_default = false;

        /* Note: If calloc_fn is not provided (NULL), tl__calloc will emulate
         * it with malloc + memset. No action needed here.
         *
         * Note: realloc_fn is optional. If not provided, tl__realloc will
         * return NULL for resize operations (cannot emulate without old size).
         * Callers requiring realloc must provide realloc_fn. */
    }
}

void tl__alloc_destroy(tl_alloc_ctx_t* ctx) {
    if (ctx == NULL) return;

#ifdef TL_DEBUG
    if (ctx->allocation_count != 0) {
        /* Note: Cannot use TL_LOG_WARN here since we don't have access to
         * the log context from the allocator. Use stderr directly for this
         * critical leak warning. */
        fprintf(stderr, "[WARN] Memory leak detected: %zu allocations, %zu bytes\n",
                ctx->allocation_count, ctx->total_allocated);
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
        ctx->total_allocated += size;
        ctx->allocation_count++;
        if (ctx->total_allocated > ctx->peak_allocated) {
            ctx->peak_allocated = ctx->total_allocated;
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

    /* Check for overflow */
    size_t total = count * size;
    if (total / count != size) {
        return NULL; /* Overflow */
    }

    void* ptr;

    if (ctx->alloc.calloc_fn != NULL) {
        ptr = ctx->alloc.calloc_fn(ctx->alloc.ctx, count, size);
    } else {
        /* Emulate calloc with malloc + memset */
        ptr = ctx->alloc.malloc_fn(ctx->alloc.ctx, total);
        if (ptr != NULL) {
            memset(ptr, 0, total);
        }
    }

#ifdef TL_DEBUG
    if (ptr != NULL) {
        ctx->total_allocated += total;
        ctx->allocation_count++;
        if (ctx->total_allocated > ctx->peak_allocated) {
            ctx->peak_allocated = ctx->total_allocated;
        }
    }
#endif

    return ptr;
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

    /* realloc_fn is required for realloc operations.
     * We cannot safely emulate realloc without knowing the old size,
     * and silently corrupting data is unacceptable. */
    if (ctx->alloc.realloc_fn == NULL) {
        return NULL;
    }

    void* new_ptr = ctx->alloc.realloc_fn(ctx->alloc.ctx, ptr, new_size);

    /* Note: In debug builds, we can't accurately track size changes without
     * storing allocation sizes. For simplicity, we don't update counters here.
     * A full implementation would use a size-tracking wrapper. */

    return new_ptr;
}

void tl__free(tl_alloc_ctx_t* ctx, void* ptr) {
    if (ctx == NULL || ptr == NULL) return;

#ifdef TL_DEBUG
    /* Note: We can't accurately decrement without tracking sizes.
     * For debug, we just decrement count. */
    if (ctx->allocation_count > 0) {
        ctx->allocation_count--;
    }
#endif

    ctx->alloc.free_fn(ctx->alloc.ctx, ptr);
}

/*===========================================================================
 * Debug Statistics
 *===========================================================================*/

#ifdef TL_DEBUG
size_t tl__alloc_get_total(const tl_alloc_ctx_t* ctx) {
    return ctx ? ctx->total_allocated : 0;
}

size_t tl__alloc_get_count(const tl_alloc_ctx_t* ctx) {
    return ctx ? ctx->allocation_count : 0;
}

size_t tl__alloc_get_peak(const tl_alloc_ctx_t* ctx) {
    return ctx ? ctx->peak_allocated : 0;
}
#endif

/------------------------------------------------------------------------------/
/*   END OF: tl_alloc.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_heap.c
/*   FROM: internal/
/*
/******************************************************************************/
#include "tl_heap.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Check if allocation size would overflow.
 */
TL_INLINE bool alloc_would_overflow_heap(size_t count, size_t elem_size) {
    return elem_size != 0 && count > SIZE_MAX / elem_size;
}

/**
 * Compute next capacity >= required using 2x growth.
 */
static size_t next_capacity_heap(size_t current, size_t required) {
    static const size_t MIN_CAPACITY = 8;

    size_t new_cap = (current == 0) ? MIN_CAPACITY : current;

    while (new_cap < required) {
        if (new_cap > SIZE_MAX / 2) {
            return SIZE_MAX;
        }
        new_cap *= 2;
    }

    return new_cap;
}

/**
 * Compare two heap entries.
 * Entries are compared by (ts, component_id) for deterministic ordering.
 * @return true if a < b
 */
TL_INLINE bool heap_entry_less(const tl_heap_entry_t* a, const tl_heap_entry_t* b) {
    if (a->ts != b->ts) {
        return a->ts < b->ts;
    }
    return a->component_id < b->component_id;
}

/**
 * Swap two heap entries.
 */
TL_INLINE void heap_entry_swap(tl_heap_entry_t* a, tl_heap_entry_t* b) {
    tl_heap_entry_t tmp = *a;
    *a = *b;
    *b = tmp;
}

/**
 * Sift up: restore heap property after insertion at idx.
 */
static void sift_up(tl_heap_t* h, size_t idx) {
    while (idx > 0) {
        size_t parent = (idx - 1) / 2;

        if (!heap_entry_less(&h->data[idx], &h->data[parent])) {
            break; /* Heap property satisfied */
        }

        heap_entry_swap(&h->data[idx], &h->data[parent]);
        idx = parent;
    }
}

/**
 * Sift down: restore heap property after removal from root.
 */
static void sift_down(tl_heap_t* h, size_t idx) {
    while (true) {
        size_t left = 2 * idx + 1;
        size_t right = 2 * idx + 2;
        size_t smallest = idx;

        if (left < h->len && heap_entry_less(&h->data[left], &h->data[smallest])) {
            smallest = left;
        }

        if (right < h->len && heap_entry_less(&h->data[right], &h->data[smallest])) {
            smallest = right;
        }

        if (smallest == idx) {
            break; /* Heap property satisfied */
        }

        heap_entry_swap(&h->data[idx], &h->data[smallest]);
        idx = smallest;
    }
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_heap_init(tl_heap_t* h, tl_alloc_ctx_t* alloc) {
    TL_ASSERT(h != NULL);
    TL_ASSERT(alloc != NULL);

    h->data = NULL;
    h->len = 0;
    h->cap = 0;
    h->alloc = alloc;
}

void tl_heap_destroy(tl_heap_t* h) {
    if (h == NULL) {
        return;
    }

    /* State validation in debug builds.
     * If data is allocated, we need a valid allocator to free it.
     * If this fires, the heap was likely corrupted or double-destroyed. */
    TL_ASSERT(h->data == NULL || h->alloc != NULL);

    /* Invariant check: len cannot exceed cap */
    TL_ASSERT(h->len <= h->cap);

    if (h->data != NULL) {
        tl__free(h->alloc, h->data);
    }

    h->data = NULL;
    h->len = 0;
    h->cap = 0;
    /* Note: h->alloc is left as-is (not set to NULL) since destroy may be
     * called before full cleanup. Caller owns alloc lifetime. */
}

void tl_heap_clear(tl_heap_t* h) {
    TL_ASSERT(h != NULL);
    h->len = 0;
}

tl_status_t tl_heap_reserve(tl_heap_t* h, size_t min_cap) {
    TL_ASSERT(h != NULL);

    if (min_cap <= h->cap) {
        return TL_OK;
    }

    size_t new_cap = next_capacity_heap(h->cap, min_cap);

    if (alloc_would_overflow_heap(new_cap, sizeof(tl_heap_entry_t))) {
        return TL_ENOMEM;
    }

    tl_heap_entry_t* new_data = tl__realloc(h->alloc, h->data,
                                             new_cap * sizeof(tl_heap_entry_t));
    if (new_data == NULL) {
        return TL_ENOMEM;
    }

    h->data = new_data;
    h->cap = new_cap;
    return TL_OK;
}

/*===========================================================================
 * Heap Operations
 *===========================================================================*/

tl_status_t tl_heap_push(tl_heap_t* h, const tl_heap_entry_t* entry) {
    TL_ASSERT(h != NULL);
    TL_ASSERT(entry != NULL);

    if (h->len == SIZE_MAX) {
        return TL_ENOMEM;
    }

    tl_status_t s = tl_heap_reserve(h, h->len + 1);
    if (s != TL_OK) {
        return s;
    }

    /* Insert at end */
    h->data[h->len] = *entry;
    h->len++;

    /* Restore heap property */
    sift_up(h, h->len - 1);

    return TL_OK;
}

tl_status_t tl_heap_pop(tl_heap_t* h, tl_heap_entry_t* out) {
    TL_ASSERT(h != NULL);
    TL_ASSERT(out != NULL);

    if (h->len == 0) {
        return TL_EOF;
    }

    /* Return minimum (root) */
    *out = h->data[0];

    /* Move last element to root */
    h->len--;
    if (h->len > 0) {
        h->data[0] = h->data[h->len];
        sift_down(h, 0);
    }

    return TL_OK;
}

const tl_heap_entry_t* tl_heap_peek(const tl_heap_t* h) {
    TL_ASSERT(h != NULL);

    if (h->len == 0) {
        return NULL;
    }

    return &h->data[0];
}

tl_status_t tl_heap_build(tl_heap_t* h, const tl_heap_entry_t* entries, size_t n) {
    TL_ASSERT(h != NULL);

    tl_heap_clear(h);

    if (n == 0) {
        return TL_OK;
    }

    TL_ASSERT(entries != NULL);

    tl_status_t s = tl_heap_reserve(h, n);
    if (s != TL_OK) {
        return s;
    }

    /* Copy entries */
    memcpy(h->data, entries, n * sizeof(tl_heap_entry_t));
    h->len = n;

    /* Bottom-up heapify: O(n) */
    if (n > 1) {
        /* Start from last parent and work up to root */
        for (size_t i = n / 2; i > 0; i--) {
            sift_down(h, i - 1);
        }
    }

    return TL_OK;
}

void tl_heap_replace_top(tl_heap_t* h, const tl_heap_entry_t* new_entry) {
    TL_ASSERT(h != NULL);
    TL_ASSERT(h->len > 0);
    TL_ASSERT(new_entry != NULL);

    h->data[0] = *new_entry;
    sift_down(h, 0);
}

/------------------------------------------------------------------------------/
/*   END OF: tl_heap.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_intervals.c
/*   FROM: internal/
/*
/******************************************************************************/
#include "tl_intervals.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Check if allocation size would overflow.
 */
TL_INLINE bool alloc_would_overflow_iv(size_t count, size_t elem_size) {
    return elem_size != 0 && count > SIZE_MAX / elem_size;
}

/**
 * Compute next capacity >= required using 2x growth.
 */
static size_t next_capacity_iv(size_t current, size_t required) {
    static const size_t MIN_CAPACITY = 8;

    size_t new_cap = (current == 0) ? MIN_CAPACITY : current;

    while (new_cap < required) {
        if (new_cap > SIZE_MAX / 2) {
            return SIZE_MAX;
        }
        new_cap *= 2;
    }

    return new_cap;
}

/**
 * Reserve capacity for interval set.
 */
static tl_status_t intervals_reserve(tl_intervals_t* iv, size_t min_cap) {
    if (min_cap <= iv->cap) {
        return TL_OK;
    }

    size_t new_cap = next_capacity_iv(iv->cap, min_cap);

    if (alloc_would_overflow_iv(new_cap, sizeof(tl_interval_t))) {
        return TL_ENOMEM;
    }

    tl_interval_t* new_data = tl__realloc(iv->alloc, iv->data,
                                           new_cap * sizeof(tl_interval_t));
    if (new_data == NULL) {
        return TL_ENOMEM;
    }

    iv->data = new_data;
    iv->cap = new_cap;
    return TL_OK;
}

/**
 * Check if two intervals overlap or are adjacent (can be merged).
 * Handles unbounded intervals correctly.
 *
 * Precondition: a->start <= b->start (caller ensures sorted order)
 */
static bool intervals_can_merge(const tl_interval_t* a, const tl_interval_t* b) {
    if (a->end_unbounded) {
        return true; /* Unbounded covers everything after */
    }
    return a->end >= b->start; /* Adjacent or overlapping */
}

/**
 * Merge two overlapping/adjacent intervals into result.
 * Precondition: intervals_can_merge(a, b) is true.
 */
static void intervals_merge_into(tl_interval_t* result,
                                  const tl_interval_t* a,
                                  const tl_interval_t* b) {
    result->start = TL_MIN(a->start, b->start);

    /* Unboundedness propagates */
    if (a->end_unbounded || b->end_unbounded) {
        result->end_unbounded = true;
        result->end = 0; /* Undefined, set to 0 for safety */
    } else {
        result->end_unbounded = false;
        result->end = TL_MAX(a->end, b->end);
    }
}

/**
 * Find first interval with start >= ts using binary search.
 * Returns position where interval with this start would be inserted.
 */
static size_t intervals_lower_bound(const tl_intervals_t* iv, tl_ts_t ts) {
    size_t lo = 0;
    size_t hi = iv->len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (iv->data[mid].start < ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

/**
 * Push a single interval to the end (no coalescing).
 */
static tl_status_t intervals_push_interval(tl_intervals_t* iv, const tl_interval_t* interval) {
    if (iv->len == SIZE_MAX) {
        return TL_ENOMEM;
    }

    tl_status_t s = intervals_reserve(iv, iv->len + 1);
    if (s != TL_OK) {
        return s;
    }

    iv->data[iv->len] = *interval;
    iv->len++;
    return TL_OK;
}

/**
 * Replace a range [pos, end) with a single interval.
 * Shifts remaining elements.
 */
static tl_status_t intervals_replace_range(tl_intervals_t* iv, size_t pos, size_t end,
                                            const tl_interval_t* replacement) {
    size_t remove_count = end - pos;
    size_t tail_count = iv->len - end;

    if (remove_count == 0) {
        /* Insert new interval at pos */
        if (iv->len == SIZE_MAX) {
            return TL_ENOMEM;
        }

        tl_status_t s = intervals_reserve(iv, iv->len + 1);
        if (s != TL_OK) {
            return s;
        }

        /* Shift tail right by 1 */
        if (tail_count > 0) {
            memmove(&iv->data[pos + 1], &iv->data[pos],
                    tail_count * sizeof(tl_interval_t));
        }

        iv->data[pos] = *replacement;
        iv->len++;
    } else if (remove_count == 1) {
        /* Replace in place */
        iv->data[pos] = *replacement;
    } else {
        /* Replace first, shift tail left */
        iv->data[pos] = *replacement;

        if (tail_count > 0) {
            memmove(&iv->data[pos + 1], &iv->data[end],
                    tail_count * sizeof(tl_interval_t));
        }

        iv->len -= (remove_count - 1);
    }

    return TL_OK;
}

/**
 * Internal insert with full interval struct.
 * Handles both bounded and unbounded intervals.
 */
static tl_status_t intervals_insert_internal(tl_intervals_t* iv,
                                              const tl_interval_t* new_iv) {
    /* Handle empty case */
    if (iv->len == 0) {
        return intervals_push_interval(iv, new_iv);
    }

    /* Find insertion point */
    size_t pos = intervals_lower_bound(iv, new_iv->start);

    /* Working copy of merged interval */
    tl_interval_t merged = *new_iv;

    /* Check predecessor for merge */
    if (pos > 0) {
        const tl_interval_t* prev = &iv->data[pos - 1];
        if (intervals_can_merge(prev, &merged)) {
            pos--;
            intervals_merge_into(&merged, prev, &merged);
        }
    }

    /* Merge with successors */
    size_t merge_end = pos;
    while (merge_end < iv->len && !merged.end_unbounded) {
        const tl_interval_t* cur = &iv->data[merge_end];
        if (!intervals_can_merge(&merged, cur)) {
            break; /* No more overlap */
        }
        intervals_merge_into(&merged, &merged, cur);
        merge_end++;
    }

    /* If merged is unbounded, consume ALL remaining intervals */
    if (merged.end_unbounded) {
        merge_end = iv->len;
    }

    /* Replace [pos, merge_end) with single merged interval */
    return intervals_replace_range(iv, pos, merge_end, &merged);
}

/**
 * Append interval to end, coalescing with last if overlapping/adjacent.
 * This is O(1) per call - only compares with the last interval.
 *
 * Precondition: new_iv.start >= last interval's start (inputs arrive sorted).
 */
static tl_status_t intervals_append_coalescing(tl_intervals_t* out,
                                                const tl_interval_t* new_iv) {
    if (out->len == 0) {
        return intervals_push_interval(out, new_iv);
    }

    tl_interval_t* last = &out->data[out->len - 1];

    /* Check if we can merge with last */
    if (intervals_can_merge(last, new_iv)) {
        /* Merge in place - O(1) */
        intervals_merge_into(last, last, new_iv);
        return TL_OK;
    }

    /* No merge - append new interval */
    return intervals_push_interval(out, new_iv);
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_intervals_init(tl_intervals_t* iv, tl_alloc_ctx_t* alloc) {
    TL_ASSERT(iv != NULL);
    TL_ASSERT(alloc != NULL);

    iv->data = NULL;
    iv->len = 0;
    iv->cap = 0;
    iv->alloc = alloc;
}

void tl_intervals_destroy(tl_intervals_t* iv) {
    if (iv == NULL) {
        return;
    }

    if (iv->data != NULL) {
        tl__free(iv->alloc, iv->data);
    }

    iv->data = NULL;
    iv->len = 0;
    iv->cap = 0;
}

void tl_intervals_clear(tl_intervals_t* iv) {
    TL_ASSERT(iv != NULL);
    iv->len = 0;
}

/*===========================================================================
 * Insertion
 *===========================================================================*/

tl_status_t tl_intervals_insert(tl_intervals_t* iv, tl_ts_t t1, tl_ts_t t2) {
    TL_ASSERT(iv != NULL);

    /* Empty interval: no-op (Write Path LLD Section 3.8) */
    if (t1 == t2) {
        return TL_OK;
    }

    /* Invalid interval */
    if (t1 > t2) {
        return TL_EINVAL;
    }

    /* Create the new interval (bounded) */
    tl_interval_t new_iv;
    new_iv.start = t1;
    new_iv.end = t2;
    new_iv.end_unbounded = false;

    return intervals_insert_internal(iv, &new_iv);
}

tl_status_t tl_intervals_insert_unbounded(tl_intervals_t* iv, tl_ts_t t1) {
    TL_ASSERT(iv != NULL);

    tl_interval_t new_iv;
    new_iv.start = t1;
    new_iv.end = 0; /* Undefined for unbounded */
    new_iv.end_unbounded = true;

    return intervals_insert_internal(iv, &new_iv);
}

/*===========================================================================
 * Point Containment
 *===========================================================================*/

/**
 * Internal containment check on raw array.
 */
static bool intervals_contains_internal(const tl_interval_t* data, size_t len, tl_ts_t ts) {
    if (len == 0) {
        return false;
    }

    /* Binary search for first interval with start > ts */
    size_t lo = 0;
    size_t hi = len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (data[mid].start <= ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    /* Check if ts is in the interval before lo */
    if (lo == 0) {
        return false;
    }

    const tl_interval_t* cand = &data[lo - 1];
    return cand->end_unbounded || ts < cand->end;
}

bool tl_intervals_contains(const tl_intervals_t* iv, tl_ts_t ts) {
    TL_ASSERT(iv != NULL);
    return intervals_contains_internal(iv->data, iv->len, ts);
}

bool tl_intervals_imm_contains(tl_intervals_imm_t iv, tl_ts_t ts) {
    return intervals_contains_internal(iv.data, iv.len, ts);
}

/*===========================================================================
 * Set Operations
 *===========================================================================*/

tl_status_t tl_intervals_union(tl_intervals_t* out,
                               const tl_intervals_t* a,
                               const tl_intervals_t* b) {
    TL_ASSERT(out != NULL);
    TL_ASSERT(a != NULL);
    TL_ASSERT(b != NULL);

    /* Aliasing not supported: out must be distinct from inputs.
     * This is a runtime check (not TL_ASSERT) because caller error
     * should not become UB in release builds. */
    if (out == a || out == b) {
        return TL_EINVAL;
    }

    tl_intervals_clear(out);

    /* Check for length addition overflow before reserving */
    if (a->len > SIZE_MAX - b->len) {
        return TL_ENOMEM;
    }

    /* Reserve upfront to avoid reallocations during merge */
    tl_status_t s = intervals_reserve(out, a->len + b->len);
    if (s != TL_OK) {
        return s;
    }

    /* Two-pointer merge */
    size_t i = 0, j = 0;

    while (i < a->len || j < b->len) {
        const tl_interval_t* next;

        if (i >= a->len) {
            next = &b->data[j++];
        } else if (j >= b->len) {
            next = &a->data[i++];
        } else if (a->data[i].start <= b->data[j].start) {
            next = &a->data[i++];
        } else {
            next = &b->data[j++];
        }

        /* Append with coalescing - O(1) per interval */
        s = intervals_append_coalescing(out, next);
        if (s != TL_OK) {
            return s;
        }
    }

    return TL_OK;
}

tl_status_t tl_intervals_union_imm(tl_intervals_t* out,
                                   tl_intervals_imm_t a,
                                   tl_intervals_imm_t b) {
    TL_ASSERT(out != NULL);

    tl_intervals_clear(out);

    /* Check for length addition overflow before reserving */
    if (a.len > SIZE_MAX - b.len) {
        return TL_ENOMEM;
    }

    tl_status_t s = intervals_reserve(out, a.len + b.len);
    if (s != TL_OK) {
        return s;
    }

    size_t i = 0, j = 0;

    while (i < a.len || j < b.len) {
        const tl_interval_t* next;

        if (i >= a.len) {
            next = &b.data[j++];
        } else if (j >= b.len) {
            next = &a.data[i++];
        } else if (a.data[i].start <= b.data[j].start) {
            next = &a.data[i++];
        } else {
            next = &b.data[j++];
        }

        s = intervals_append_coalescing(out, next);
        if (s != TL_OK) {
            return s;
        }
    }

    return TL_OK;
}

void tl_intervals_clip(tl_intervals_t* iv, tl_ts_t t1, tl_ts_t t2) {
    TL_ASSERT(iv != NULL);
    TL_ASSERT(t1 < t2); /* Clip range must be valid */

    size_t write = 0;

    for (size_t read = 0; read < iv->len; read++) {
        tl_interval_t* cur = &iv->data[read];

        /* Compute clipped interval */
        tl_ts_t start = TL_MAX(cur->start, t1);
        tl_ts_t end;

        if (cur->end_unbounded) {
            /* Unbounded becomes bounded when clipped */
            end = t2;
        } else {
            end = TL_MIN(cur->end, t2);
        }

        /* Skip if empty after clipping */
        if (start >= end) {
            continue;
        }

        /* Write clipped interval (always bounded after clip) */
        iv->data[write].start = start;
        iv->data[write].end = end;
        iv->data[write].end_unbounded = false;
        write++;
    }

    iv->len = write;
}

void tl_intervals_clip_lower(tl_intervals_t* iv, tl_ts_t t1) {
    TL_ASSERT(iv != NULL);

    size_t write = 0;

    for (size_t read = 0; read < iv->len; read++) {
        tl_interval_t* cur = &iv->data[read];

        if (cur->end_unbounded) {
            /*
             * Unbounded interval [start, +inf).
             * Always kept (infinite intervals never "end before t1").
             * Truncate start if needed.
             */
            iv->data[write].start = TL_MAX(cur->start, t1);
            iv->data[write].end = 0; /* Undefined for unbounded */
            iv->data[write].end_unbounded = true;
            write++;
        } else {
            /*
             * Bounded interval [start, end).
             * Skip if interval ends at or before t1.
             */
            if (cur->end <= t1) {
                continue;
            }

            /* Truncate start if needed, preserve end */
            iv->data[write].start = TL_MAX(cur->start, t1);
            iv->data[write].end = cur->end;
            iv->data[write].end_unbounded = false;
            write++;
        }
    }

    iv->len = write;
}

/*===========================================================================
 * Accessors and Ownership
 *===========================================================================*/

tl_interval_t* tl_intervals_take(tl_intervals_t* iv, size_t* out_len) {
    TL_ASSERT(iv != NULL);
    TL_ASSERT(out_len != NULL);

    tl_interval_t* data = iv->data;
    *out_len = iv->len;

    iv->data = NULL;
    iv->len = 0;
    iv->cap = 0;

    return data;
}

tl_ts_t tl_intervals_covered_span(const tl_intervals_t* iv) {
    TL_ASSERT(iv != NULL);

    /*
     * Use unsigned arithmetic to avoid signed overflow UB.
     * For extreme ranges like [INT64_MIN, 0), (end - start) would overflow
     * signed arithmetic but is well-defined for unsigned.
     */
    uint64_t total = 0;

    for (size_t i = 0; i < iv->len; i++) {
        const tl_interval_t* cur = &iv->data[i];

        /* Unbounded => saturate to max */
        if (cur->end_unbounded) {
            return TL_TS_MAX;
        }

        /* Unsigned subtraction: always well-defined */
        uint64_t span = (uint64_t)cur->end - (uint64_t)cur->start;

        /* Saturating addition */
        if (span > UINT64_MAX - total) {
            return TL_TS_MAX;
        }
        total += span;

        /* Clamp to TL_TS_MAX */
        if (total > (uint64_t)TL_TS_MAX) {
            return TL_TS_MAX;
        }
    }

    return (tl_ts_t)total;
}

/*===========================================================================
 * Cursor Operations
 *===========================================================================*/

bool tl_intervals_cursor_is_deleted(tl_intervals_cursor_t* cur, tl_ts_t ts) {
    /* Advance past intervals that end before ts */
    while (cur->pos < cur->len) {
        const tl_interval_t* iv = &cur->data[cur->pos];

        /* Unbounded interval never ends - stay here forever */
        if (iv->end_unbounded) {
            return ts >= iv->start;
        }

        /* If ts < end, this interval might cover ts */
        if (ts < iv->end) {
            break;
        }

        /* ts >= end, advance to next interval */
        cur->pos++;
    }

    /* Check if current interval covers ts */
    if (cur->pos >= cur->len) {
        return false;
    }

    const tl_interval_t* iv = &cur->data[cur->pos];
    return ts >= iv->start && (iv->end_unbounded || ts < iv->end);
}

bool tl_intervals_cursor_skip_to(tl_intervals_cursor_t* cur, tl_ts_t ts,
                                  tl_ts_t* out) {
    TL_ASSERT(out != NULL);

    /*
     * Advance past intervals that are exhausted (ts >= end).
     * This mirrors cursor_is_deleted's advancement logic.
     */
    while (cur->pos < cur->len) {
        const tl_interval_t* iv = &cur->data[cur->pos];

        /* Unbounded interval never ends */
        if (iv->end_unbounded) {
            if (ts >= iv->start) {
                /* Covered by unbounded interval - no more uncovered timestamps */
                return false;
            }
            /* ts < start => not covered yet */
            *out = ts;
            return true;
        }

        /* If ts < end, this interval might still be relevant */
        if (ts < iv->end) {
            if (ts >= iv->start) {
                /* Covered => skip to end of interval */
                *out = iv->end;
                return true;
            }
            /* ts < start => not covered yet */
            *out = ts;
            return true;
        }

        /* ts >= end: interval exhausted, advance */
        cur->pos++;
    }

    /* No more intervals - ts is not covered */
    *out = ts;
    return true;
}

/*===========================================================================
 * Debug Validation
 *===========================================================================*/

#ifdef TL_DEBUG

/**
 * Shared raw array validator - core validation logic.
 *
 * Invariants checked:
 * 1. Each bounded interval has start < end
 * 2. Sorted by start timestamp (non-decreasing)
 * 3. Non-overlapping (prev->end <= cur->start for bounded prev)
 * 4. Non-adjacent / coalesced (prev->end != cur->start)
 * 5. No intervals after an unbounded interval
 */
bool tl_intervals_arr_validate(const tl_interval_t* data, size_t len) {
    /* Empty array is trivially valid */
    if (len == 0) {
        return true;
    }

    /* Non-empty array requires non-NULL data */
    if (data == NULL) {
        return false;
    }

    for (size_t i = 0; i < len; i++) {
        const tl_interval_t* cur = &data[i];

        /* Bounded intervals must have start < end */
        if (!cur->end_unbounded && cur->start >= cur->end) {
            return false;
        }

        /* Unbounded interval must be the last one (covers everything after) */
        if (cur->end_unbounded && i < len - 1) {
            return false;
        }

        /* Check sorted order and no overlap with predecessor */
        if (i > 0) {
            const tl_interval_t* prev = &data[i - 1];

            /* Must be sorted by start (non-decreasing) */
            if (cur->start < prev->start) {
                return false;
            }

            /* No overlap allowed (prev can't be unbounded here due to check above) */
            if (!prev->end_unbounded && prev->end > cur->start) {
                return false;
            }

            /* Adjacent intervals should have been coalesced */
            if (!prev->end_unbounded && prev->end == cur->start) {
                return false;
            }
        }
    }

    return true;
}

/**
 * Validate interval set by delegating to raw array validator.
 */
bool tl_intervals_validate(const tl_intervals_t* iv) {
    if (iv == NULL) {
        return false;
    }

    return tl_intervals_arr_validate(iv->data, iv->len);
}

#endif /* TL_DEBUG */

/------------------------------------------------------------------------------/
/*   END OF: tl_intervals.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_log.c
/*   FROM: internal/
/*
/******************************************************************************/
#include "tl_log.h"
#include <stdio.h>
#include <string.h>

/*===========================================================================
 * Configuration
 *===========================================================================*/

#define TL_LOG_MAX_MESSAGE_LEN 1024

/*===========================================================================
 * Initialization
 *===========================================================================*/

void tl__log_init(tl_log_ctx_t* log, tl_log_fn fn, void* ctx, tl_log_level_t level) {
    TL_ASSERT(log != NULL);

    log->fn = fn;
    log->ctx = ctx;
    log->max_level = level;
}

/*===========================================================================
 * Logging Implementation
 *===========================================================================*/

static const char* level_names[] = {
    "ERROR",
    "WARN",
    "INFO",
    "DEBUG",
    "TRACE"
};

void tl__log_v(tl_log_ctx_t* log, tl_log_level_t level,
               const char* fmt, va_list args) {
    if (log == NULL || log->fn == NULL) {
        return;
    }

    /* Validate level bounds before array access to prevent UB */
    if ((int)level < 0 || (int)level > (int)TL_LOG_TRACE) {
        return;
    }

    if (level > log->max_level) {
        return;
    }

    char buffer[TL_LOG_MAX_MESSAGE_LEN];
    int prefix_len;
    int msg_len;

    /* Format: "[LEVEL] message" */
    prefix_len = snprintf(buffer, sizeof(buffer), "[%s] ",
                          level_names[level]);

    if (prefix_len < 0 || (size_t)prefix_len >= sizeof(buffer)) {
        return;
    }

    msg_len = vsnprintf(buffer + prefix_len,
                        sizeof(buffer) - (size_t)prefix_len,
                        fmt, args);

    if (msg_len < 0) {
        /* Format error (encoding issue, etc.) - don't silently drop.
         * Log a placeholder so the user knows a log was attempted.
         * This helps catch format string bugs during development. */
        snprintf(buffer + prefix_len,
                 sizeof(buffer) - (size_t)prefix_len,
                 "<log format error>");
    }

    /* Call user's log function */
    log->fn(log->ctx, (int)level, buffer);
}

void tl__log(tl_log_ctx_t* log, tl_log_level_t level,
             const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    tl__log_v(log, level, fmt, args);
    va_end(args);
}

/------------------------------------------------------------------------------/
/*   END OF: tl_log.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_recvec.c
/*   FROM: internal/
/*
/******************************************************************************/
#include "tl_recvec.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Check if allocation size would overflow.
 * @param count Number of elements
 * @param elem_size Size of each element
 * @return true if count * elem_size would overflow size_t
 */
TL_INLINE bool alloc_would_overflow(size_t count, size_t elem_size) {
    return elem_size != 0 && count > SIZE_MAX / elem_size;
}

/**
 * Compute next capacity >= required using 2x growth.
 * Returns SIZE_MAX on overflow (will fail allocation).
 *
 * Overflow handling:
 * - Check before multiply to avoid UB
 * - SIZE_MAX / 2 is the largest value that can safely double
 */
static size_t next_capacity(size_t current, size_t required) {
    /* Minimum initial capacity */
    static const size_t MIN_CAPACITY = 16;

    /* Start with minimum capacity or current */
    size_t new_cap = (current == 0) ? MIN_CAPACITY : current;

    while (new_cap < required) {
        /* Check for overflow BEFORE multiplying */
        if (new_cap > SIZE_MAX / 2) {
            return SIZE_MAX; /* Overflow sentinel - will fail allocation */
        }
        new_cap *= 2;
    }

    return new_cap;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_recvec_init(tl_recvec_t* rv, tl_alloc_ctx_t* alloc) {
    TL_ASSERT(rv != NULL);
    TL_ASSERT(alloc != NULL);

    rv->data = NULL;
    rv->len = 0;
    rv->cap = 0;
    rv->alloc = alloc;
}

void tl_recvec_destroy(tl_recvec_t* rv) {
    if (rv == NULL) {
        return;
    }

    if (rv->data != NULL) {
        tl__free(rv->alloc, rv->data);
    }

    /* Leave in valid empty state for idempotent destroy */
    rv->data = NULL;
    rv->len = 0;
    rv->cap = 0;
    /* Note: alloc pointer is borrowed, not cleared */
}

void tl_recvec_clear(tl_recvec_t* rv) {
    TL_ASSERT(rv != NULL);
    rv->len = 0;
}

/*===========================================================================
 * Capacity Management
 *===========================================================================*/

tl_status_t tl_recvec_reserve(tl_recvec_t* rv, size_t min_cap) {
    TL_ASSERT(rv != NULL);

    if (min_cap <= rv->cap) {
        return TL_OK; /* Already have enough capacity */
    }

    size_t new_cap = next_capacity(rv->cap, min_cap);

    /* Check for byte-size overflow */
    if (alloc_would_overflow(new_cap, sizeof(tl_record_t))) {
        return TL_ENOMEM;
    }

    tl_record_t* new_data = tl__realloc(rv->alloc, rv->data,
                                         new_cap * sizeof(tl_record_t));
    if (new_data == NULL) {
        return TL_ENOMEM;
    }

    rv->data = new_data;
    rv->cap = new_cap;
    return TL_OK;
}

tl_status_t tl_recvec_shrink_to_fit(tl_recvec_t* rv) {
    TL_ASSERT(rv != NULL);

    if (rv->len == rv->cap) {
        return TL_OK; /* Already exact fit */
    }

    if (rv->len == 0) {
        /* Free backing storage entirely */
        if (rv->data != NULL) {
            tl__free(rv->alloc, rv->data);
            rv->data = NULL;
        }
        rv->cap = 0;
        return TL_OK;
    }

    /* Reallocate to exact size */
    tl_record_t* new_data = tl__realloc(rv->alloc, rv->data,
                                         rv->len * sizeof(tl_record_t));
    if (new_data == NULL) {
        /* Realloc failed, capacity unchanged (data is still valid) */
        return TL_ENOMEM;
    }

    rv->data = new_data;
    rv->cap = rv->len;
    return TL_OK;
}

/*===========================================================================
 * Insertion
 *===========================================================================*/

tl_status_t tl_recvec_push(tl_recvec_t* rv, tl_ts_t ts, tl_handle_t handle) {
    TL_ASSERT(rv != NULL);

    /* Check for len overflow */
    if (rv->len == SIZE_MAX) {
        return TL_ENOMEM;
    }

    tl_status_t s = tl_recvec_reserve(rv, rv->len + 1);
    if (s != TL_OK) {
        return s;
    }

    rv->data[rv->len].ts = ts;
    rv->data[rv->len].handle = handle;
    rv->len++;
    return TL_OK;
}

tl_status_t tl_recvec_push_n(tl_recvec_t* rv, const tl_record_t* records, size_t n) {
    TL_ASSERT(rv != NULL);

    if (n == 0) {
        return TL_OK; /* No-op for n=0 */
    }

    TL_ASSERT(records != NULL);

    /* Check for len + n overflow */
    if (n > SIZE_MAX - rv->len) {
        return TL_ENOMEM;
    }

    tl_status_t s = tl_recvec_reserve(rv, rv->len + n);
    if (s != TL_OK) {
        return s;
    }

    memcpy(&rv->data[rv->len], records, n * sizeof(tl_record_t));
    rv->len += n;
    return TL_OK;
}

tl_status_t tl_recvec_insert(tl_recvec_t* rv, size_t idx, tl_ts_t ts, tl_handle_t handle) {
    TL_ASSERT(rv != NULL);

    if (idx > rv->len) {
        return TL_EINVAL;
    }

    /* Check for len overflow */
    if (rv->len == SIZE_MAX) {
        return TL_ENOMEM;
    }

    tl_status_t s = tl_recvec_reserve(rv, rv->len + 1);
    if (s != TL_OK) {
        return s;
    }

    /* Shift elements to make room */
    if (idx < rv->len) {
        memmove(&rv->data[idx + 1], &rv->data[idx],
                (rv->len - idx) * sizeof(tl_record_t));
    }

    rv->data[idx].ts = ts;
    rv->data[idx].handle = handle;
    rv->len++;
    return TL_OK;
}

/*===========================================================================
 * Binary Search
 *===========================================================================*/

size_t tl_recvec_lower_bound(const tl_recvec_t* rv, tl_ts_t ts) {
    TL_ASSERT(rv != NULL);

    size_t lo = 0;
    size_t hi = rv->len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (rv->data[mid].ts < ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

size_t tl_recvec_upper_bound(const tl_recvec_t* rv, tl_ts_t ts) {
    TL_ASSERT(rv != NULL);

    size_t lo = 0;
    size_t hi = rv->len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (rv->data[mid].ts <= ts) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

void tl_recvec_range_bounds(const tl_recvec_t* rv, tl_ts_t t1, tl_ts_t t2,
                            size_t* lo, size_t* hi) {
    TL_ASSERT(rv != NULL);
    TL_ASSERT(lo != NULL);
    TL_ASSERT(hi != NULL);

    *lo = tl_recvec_lower_bound(rv, t1);
    *hi = tl_recvec_lower_bound(rv, t2);
}

/*===========================================================================
 * Ownership Transfer
 *===========================================================================*/

tl_record_t* tl_recvec_take(tl_recvec_t* rv, size_t* out_len) {
    TL_ASSERT(rv != NULL);
    TL_ASSERT(out_len != NULL);

    tl_record_t* data = rv->data;
    *out_len = rv->len;

    /* Reset vector to empty state */
    rv->data = NULL;
    rv->len = 0;
    rv->cap = 0;

    return data;
}

/------------------------------------------------------------------------------/
/*   END OF: tl_recvec.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_sync.c
/*   FROM: internal/
/*
/******************************************************************************/
#include "tl_sync.h"
#include "tl_locks.h"
#include "tl_log.h"

/*===========================================================================
 * Thread-Local Lock Tracker (Debug Mode Only)
 *===========================================================================*/

#ifdef TL_DEBUG
TL_THREAD_LOCAL tl_lock_tracker_t tl__lock_tracker = {0};
#endif

/*===========================================================================
 * Windows Implementation
 *===========================================================================*/

#if defined(TL_PLATFORM_WINDOWS)

/*---------------------------------------------------------------------------
 * Mutex
 *---------------------------------------------------------------------------*/

tl_status_t tl_mutex_init(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
    InitializeSRWLock(&mu->lock);
#ifdef TL_DEBUG
    mu->owner = 0;
#endif
    return TL_OK;
}

void tl_mutex_destroy(tl_mutex_t* mu) {
    if (mu == NULL) return;
    /* SRWLock doesn't require explicit destruction */
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner == 0);
#endif
}

void tl_mutex_lock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner != GetCurrentThreadId()); /* Detect recursive lock */
#endif
    AcquireSRWLockExclusive(&mu->lock);
#ifdef TL_DEBUG
    mu->owner = GetCurrentThreadId();
#endif
}

void tl_mutex_unlock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner == GetCurrentThreadId());
    mu->owner = 0;
#endif
    ReleaseSRWLockExclusive(&mu->lock);
}

bool tl_mutex_trylock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner != GetCurrentThreadId()); /* Detect recursive lock */
#endif
    if (TryAcquireSRWLockExclusive(&mu->lock)) {
#ifdef TL_DEBUG
        mu->owner = GetCurrentThreadId();
#endif
        return true;
    }
    return false;
}

#ifdef TL_DEBUG
bool tl_mutex_is_held(const tl_mutex_t* mu) {
    return mu && mu->owner == GetCurrentThreadId();
}
#endif

/*---------------------------------------------------------------------------
 * Condition Variable
 *---------------------------------------------------------------------------*/

tl_status_t tl_cond_init(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    InitializeConditionVariable(&cv->cond);
    return TL_OK;
}

void tl_cond_destroy(tl_cond_t* cv) {
    /* CONDITION_VARIABLE doesn't require explicit destruction */
    (void)cv;
}

void tl_cond_wait(tl_cond_t* cv, tl_mutex_t* mu) {
    TL_ASSERT(cv != NULL);
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner == GetCurrentThreadId());
    mu->owner = 0;
#endif
    SleepConditionVariableSRW(&cv->cond, &mu->lock, INFINITE, 0);
#ifdef TL_DEBUG
    mu->owner = GetCurrentThreadId();
#endif
}

bool tl_cond_timedwait(tl_cond_t* cv, tl_mutex_t* mu, uint32_t timeout_ms) {
    TL_ASSERT(cv != NULL);
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->owner == GetCurrentThreadId());
    mu->owner = 0;
#endif
    BOOL result = SleepConditionVariableSRW(&cv->cond, &mu->lock, timeout_ms, 0);
#ifdef TL_DEBUG
    mu->owner = GetCurrentThreadId();
#endif
    return result != 0;
}

void tl_cond_signal(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    WakeConditionVariable(&cv->cond);
}

void tl_cond_broadcast(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    WakeAllConditionVariable(&cv->cond);
}

/*---------------------------------------------------------------------------
 * Thread
 *
 * IMPORTANT: We use _beginthreadex instead of CreateThread.
 * CreateThread does not initialize CRT per-thread data, which causes:
 * - Memory leaks if the thread uses CRT functions
 * - Potential crashes with errno, strerror, etc.
 * _beginthreadex properly initializes the CRT and is the recommended API.
 *---------------------------------------------------------------------------*/

#include <process.h>  /* For _beginthreadex */

/* Windows thread wrapper - uses unsigned __stdcall for _beginthreadex */
static unsigned __stdcall win32_thread_wrapper(void* arg) {
    tl_thread_t* t = (tl_thread_t*)arg;
    t->result = t->fn(t->arg);
    return 0;
}

tl_status_t tl_thread_create(tl_thread_t* thread, tl_thread_fn fn, void* arg) {
    TL_ASSERT(thread != NULL);
    TL_ASSERT(fn != NULL);

    thread->fn = fn;
    thread->arg = arg;
    thread->result = NULL;

    /* _beginthreadex returns handle or 0 on error (not INVALID_HANDLE_VALUE) */
    uintptr_t h = _beginthreadex(
        NULL,                   /* default security attributes */
        0,                      /* default stack size */
        win32_thread_wrapper,
        thread,
        0,                      /* run immediately */
        NULL                    /* don't need thread ID */
    );

    if (h == 0) {
        return TL_EINTERNAL;
    }
    thread->handle = (HANDLE)h;
    return TL_OK;
}

tl_status_t tl_thread_join(tl_thread_t* thread, void** result) {
    TL_ASSERT(thread != NULL);
    TL_ASSERT(thread->handle != NULL);

    DWORD wait_result = WaitForSingleObject(thread->handle, INFINITE);
    if (wait_result != WAIT_OBJECT_0) {
        /* Close handle even on error to prevent resource leak */
        CloseHandle(thread->handle);
        thread->handle = NULL;
        return TL_EINTERNAL;
    }

    CloseHandle(thread->handle);
    thread->handle = NULL;

    if (result != NULL) {
        *result = thread->result;
    }
    return TL_OK;
}

uint64_t tl_thread_self_id(void) {
    return (uint64_t)GetCurrentThreadId();
}

#ifdef TL_DEBUG
/*
 * Thread-safe one-time initialization for SetThreadDescription.
 * Uses InitOnceExecuteOnce to avoid data races when multiple threads
 * call tl_thread_set_name() concurrently at startup.
 */
typedef HRESULT (WINAPI *SetThreadDescriptionFn)(HANDLE, PCWSTR);

static INIT_ONCE g_thread_name_init_once = INIT_ONCE_STATIC_INIT;
static SetThreadDescriptionFn g_set_thread_desc_fn = NULL;

static BOOL CALLBACK thread_name_init_callback(
    PINIT_ONCE init_once,
    PVOID parameter,
    PVOID* context)
{
    (void)init_once;
    (void)parameter;
    (void)context;

    HMODULE kernel32 = GetModuleHandleW(L"kernel32.dll");
    if (kernel32) {
        g_set_thread_desc_fn = (SetThreadDescriptionFn)GetProcAddress(
            kernel32, "SetThreadDescription");
    }
    return TRUE;
}

void tl_thread_set_name(const char* name) {
    if (name == NULL) return;

    /*
     * SetThreadDescription requires Windows 10 1607+.
     * We dynamically load it to avoid breaking older systems.
     * InitOnceExecuteOnce ensures thread-safe one-time initialization.
     */
    InitOnceExecuteOnce(&g_thread_name_init_once, thread_name_init_callback, NULL, NULL);

    if (g_set_thread_desc_fn) {
        /* Convert to wide string (simple ASCII conversion sufficient for thread names) */
        wchar_t wname[64];
        int i = 0;
        while (i < 63 && name[i]) {  /* Check bounds before array access */
            wname[i] = (wchar_t)(unsigned char)name[i];
            i++;
        }
        wname[i] = L'\0';
        g_set_thread_desc_fn(GetCurrentThread(), wname);
    }
}
#endif

void tl_thread_yield(void) {
    SwitchToThread();
}

void tl_sleep_ms(uint32_t ms) {
    Sleep(ms);
}

uint64_t tl_monotonic_ms(void) {
    /* GetTickCount64 returns milliseconds since system start.
     * Available on Windows Vista and later (our minimum target).
     * Never wraps (64-bit), monotonic, ~15ms resolution typical. */
    return GetTickCount64();
}

/*===========================================================================
 * POSIX Implementation
 *===========================================================================*/

#else /* POSIX */

#include <time.h>
#include <sys/time.h>
#include <sched.h>
#include <unistd.h>
#include <string.h>

/*---------------------------------------------------------------------------
 * POSIX Capability Detection
 *
 * pthread_condattr_setclock() is required to use CLOCK_MONOTONIC with
 * condition variables. It's available when:
 * - _POSIX_CLOCK_SELECTION is defined and > 0
 * - CLOCK_MONOTONIC is defined
 * - _POSIX_MONOTONIC_CLOCK is defined
 *
 * On systems where setclock isn't available (e.g., older macOS), we fall
 * back to CLOCK_REALTIME which can have issues with time jumps.
 *---------------------------------------------------------------------------*/
#if defined(_POSIX_CLOCK_SELECTION) && (_POSIX_CLOCK_SELECTION > 0) && \
    defined(CLOCK_MONOTONIC) && defined(_POSIX_MONOTONIC_CLOCK)
    #define TL_HAS_PTHREAD_CONDATTR_SETCLOCK 1
#else
    #define TL_HAS_PTHREAD_CONDATTR_SETCLOCK 0
#endif

/*---------------------------------------------------------------------------
 * Mutex
 *---------------------------------------------------------------------------*/

tl_status_t tl_mutex_init(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);

#ifdef TL_DEBUG
    /* Use ERRORCHECK in debug mode for deadlock detection */
    pthread_mutexattr_t attr;
    pthread_mutexattr_init(&attr);
    pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_ERRORCHECK);

    int rc = pthread_mutex_init(&mu->lock, &attr);
    pthread_mutexattr_destroy(&attr);
#else
    /* Use default (faster) mutex in release mode */
    int rc = pthread_mutex_init(&mu->lock, NULL);
#endif

    if (rc != 0) {
        return TL_EINTERNAL;
    }

#ifdef TL_DEBUG
    /* Note: We don't initialize owner since it's only valid when locked == 1 */
    mu->locked = 0;
#endif
    return TL_OK;
}

void tl_mutex_destroy(tl_mutex_t* mu) {
    if (mu == NULL) return;
#ifdef TL_DEBUG
    TL_ASSERT(!mu->locked);
#endif
    pthread_mutex_destroy(&mu->lock);
}

void tl_mutex_lock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
    int rc = pthread_mutex_lock(&mu->lock);
    TL_ASSERT(rc == 0);
    (void)rc;
#ifdef TL_DEBUG
    mu->owner = pthread_self();
    mu->locked = 1;
#endif
}

void tl_mutex_unlock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->locked);
    TL_ASSERT(pthread_equal(mu->owner, pthread_self()));
    /* Clear locked flag first - owner is now invalid */
    mu->locked = 0;
    /* Note: We don't clear owner since pthread_t is opaque */
#endif
    int rc = pthread_mutex_unlock(&mu->lock);
    TL_ASSERT(rc == 0);
    (void)rc;
}

bool tl_mutex_trylock(tl_mutex_t* mu) {
    TL_ASSERT(mu != NULL);
    int rc = pthread_mutex_trylock(&mu->lock);
    if (rc == 0) {
#ifdef TL_DEBUG
        mu->owner = pthread_self();
        mu->locked = 1;
#endif
        return true;
    }
    return false;
}

#ifdef TL_DEBUG
bool tl_mutex_is_held(const tl_mutex_t* mu) {
    return mu && mu->locked && pthread_equal(mu->owner, pthread_self());
}
#endif

/*---------------------------------------------------------------------------
 * Condition Variable
 *---------------------------------------------------------------------------*/

tl_status_t tl_cond_init(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);

#if TL_HAS_PTHREAD_CONDATTR_SETCLOCK
    /* Use CLOCK_MONOTONIC for reliable timeouts */
    pthread_condattr_t attr;
    int attr_rc = pthread_condattr_init(&attr);
    int rc;

    if (attr_rc == 0) {
        int setclock_rc = pthread_condattr_setclock(&attr, CLOCK_MONOTONIC);
        if (setclock_rc == 0) {
            rc = pthread_cond_init(&cv->cond, &attr);
            cv->use_monotonic = true;
        } else {
            /* setclock failed, fall back to default (CLOCK_REALTIME) */
            rc = pthread_cond_init(&cv->cond, NULL);
            cv->use_monotonic = false;
        }
        pthread_condattr_destroy(&attr);
    } else {
        /* attr init failed, fall back to default */
        rc = pthread_cond_init(&cv->cond, NULL);
        cv->use_monotonic = false;
    }
#else
    int rc = pthread_cond_init(&cv->cond, NULL);
    cv->use_monotonic = false;
#endif

    if (rc != 0) {
        return TL_EINTERNAL;
    }
    return TL_OK;
}

void tl_cond_destroy(tl_cond_t* cv) {
    if (cv == NULL) return;
    pthread_cond_destroy(&cv->cond);
}

void tl_cond_wait(tl_cond_t* cv, tl_mutex_t* mu) {
    TL_ASSERT(cv != NULL);
    TL_ASSERT(mu != NULL);
#ifdef TL_DEBUG
    TL_ASSERT(mu->locked);
    /* Mark as unlocked before wait (mutex will be released during wait) */
    mu->locked = 0;
#endif
    int rc = pthread_cond_wait(&cv->cond, &mu->lock);
    TL_ASSERT(rc == 0);
    (void)rc;
#ifdef TL_DEBUG
    /* Mutex is reacquired after wait */
    mu->owner = pthread_self();
    mu->locked = 1;
#endif
}

bool tl_cond_timedwait(tl_cond_t* cv, tl_mutex_t* mu, uint32_t timeout_ms) {
    TL_ASSERT(cv != NULL);
    TL_ASSERT(mu != NULL);

    struct timespec ts;

    /*
     * Use the same clock that was configured in tl_cond_init().
     * The condvar and timeout calculation MUST use the same clock,
     * otherwise timeouts will be wrong (possibly very long or immediate).
     */
#if TL_HAS_PTHREAD_CONDATTR_SETCLOCK
    if (cv->use_monotonic) {
        clock_gettime(CLOCK_MONOTONIC, &ts);
    } else {
        clock_gettime(CLOCK_REALTIME, &ts);
    }
#else
    /* CLOCK_MONOTONIC not available for condvars, use REALTIME */
    clock_gettime(CLOCK_REALTIME, &ts);
#endif

    /* Add timeout */
    ts.tv_sec += timeout_ms / 1000;
    ts.tv_nsec += (timeout_ms % 1000) * 1000000L;
    /* Handle nanosecond overflow */
    if (ts.tv_nsec >= 1000000000L) {
        ts.tv_sec += 1;
        ts.tv_nsec -= 1000000000L;
    }

#ifdef TL_DEBUG
    TL_ASSERT(mu->locked);
    /* Mark as unlocked before wait */
    mu->locked = 0;
#endif
    int rc = pthread_cond_timedwait(&cv->cond, &mu->lock, &ts);
#ifdef TL_DEBUG
    /* Mutex is reacquired after wait */
    mu->owner = pthread_self();
    mu->locked = 1;
#endif

    if (rc == 0) {
        return true;  /* Signaled */
    }
    if (rc == ETIMEDOUT) {
        return false; /* Timed out */
    }
    TL_ASSERT(0); /* Unexpected error */
    return false;
}

void tl_cond_signal(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    pthread_cond_signal(&cv->cond);
}

void tl_cond_broadcast(tl_cond_t* cv) {
    TL_ASSERT(cv != NULL);
    pthread_cond_broadcast(&cv->cond);
}

/*---------------------------------------------------------------------------
 * Thread
 *---------------------------------------------------------------------------*/

tl_status_t tl_thread_create(tl_thread_t* thread, tl_thread_fn fn, void* arg) {
    TL_ASSERT(thread != NULL);
    TL_ASSERT(fn != NULL);

    int rc = pthread_create(&thread->handle, NULL, fn, arg);
    if (rc != 0) {
        thread->valid = false;
        return TL_EINTERNAL;
    }
    thread->valid = true;
    return TL_OK;
}

tl_status_t tl_thread_join(tl_thread_t* thread, void** result) {
    TL_ASSERT(thread != NULL);
    TL_ASSERT(thread->valid);

    void* ret = NULL;
    int rc = pthread_join(thread->handle, &ret);
    if (rc != 0) {
        return TL_EINTERNAL;
    }

    thread->valid = false;

    if (result != NULL) {
        *result = ret;
    }
    return TL_OK;
}

uint64_t tl_thread_self_id(void) {
    /*
     * pthread_t is an opaque type that may not be integer-convertible.
     * We use memcpy to safely extract a numeric ID for debugging purposes.
     * This ID is only used for debug output and lock tracking, not for
     * thread comparison (use pthread_equal() for that).
     */
    pthread_t self = pthread_self();
    uint64_t id = 0;
    size_t copy_size = sizeof(self) < sizeof(id) ? sizeof(self) : sizeof(id);
    memcpy(&id, &self, copy_size);
    return id;
}

#ifdef TL_DEBUG
void tl_thread_set_name(const char* name) {
    if (name == NULL) return;

#if defined(__APPLE__)
    /* macOS: pthread_setname_np takes only the name (current thread implicit) */
    pthread_setname_np(name);
#elif defined(__linux__)
    /* Linux: pthread_setname_np takes thread handle and name (max 15 chars + NUL) */
    pthread_setname_np(pthread_self(), name);
#else
    /* Other POSIX: best-effort no-op */
    (void)name;
#endif
}
#endif

void tl_thread_yield(void) {
    sched_yield();
}

void tl_sleep_ms(uint32_t ms) {
    /*
     * Use nanosleep instead of usleep:
     * - usleep is obsolete in POSIX.1-2008
     * - nanosleep handles interrupts properly (EINTR)
     * - nanosleep provides remaining time on interrupt
     */
    struct timespec ts;
    ts.tv_sec = ms / 1000;
    ts.tv_nsec = (ms % 1000) * 1000000L;

    while (nanosleep(&ts, &ts) == -1 && errno == EINTR) {
        /* Retry with remaining time if interrupted */
    }
}

uint64_t tl_monotonic_ms(void) {
    struct timespec ts;
#if defined(CLOCK_MONOTONIC)
    clock_gettime(CLOCK_MONOTONIC, &ts);
#else
    /* Fallback to realtime if monotonic unavailable (rare) */
    clock_gettime(CLOCK_REALTIME, &ts);
#endif
    return (uint64_t)ts.tv_sec * 1000 + (uint64_t)ts.tv_nsec / 1000000;
}

#endif /* Platform selection */

/------------------------------------------------------------------------------/
/*   END OF: tl_sync.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_test_hooks.c
/*   FROM: internal/
/*
/******************************************************************************/
/*===========================================================================
 * tl_test_hooks.c - Test hook implementations
 *
 * This file contains implementations for test-only hooks that allow
 * intercepting internal behavior for testing purposes.
 *
 * Only compiled when TL_TEST_HOOKS is defined.
 *===========================================================================*/

#include "tl_platform.h"

#ifdef TL_TEST_HOOKS

/*===========================================================================
 * Assert Hook
 *
 * Global hook for intercepting TL_ASSERT without aborting.
 * Used by tests to verify assertion conditions.
 *===========================================================================*/

#ifdef TL_DEBUG

/* Global hook pointer - NULL by default (normal assert behavior) */
tl_assert_hook_fn tl__test_assert_hook = NULL;

void tl__test_set_assert_hook(tl_assert_hook_fn hook) {
    tl__test_assert_hook = hook;
}

#endif /* TL_DEBUG */

#endif /* TL_TEST_HOOKS */

/------------------------------------------------------------------------------/
/*   END OF: tl_test_hooks.c
/------------------------------------------------------------------------------/
