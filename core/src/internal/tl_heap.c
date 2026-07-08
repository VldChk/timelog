#include "tl_heap.h"

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/* Starting capacity: K-way merges typically have only a handful of sources,
 * so a small initial buffer avoids over-allocation for the common case. */
static const size_t HEAP_MIN_CAPACITY = 8;

/**
 * Strict less-than for the heap order. The tie-breaker on equal timestamps
 * is mandatory: it gives the merge a stable, deterministic output across
 * runs, which downstream consumers rely on for reproducible results.
 */
TL_INLINE bool heap_entry_less(const tl_heap_entry_t* a, const tl_heap_entry_t* b) {
    if (a->ts != b->ts) {
        return a->ts < b->ts;
    }
    return a->tie_break_key < b->tie_break_key;
}

TL_INLINE void heap_entry_swap(tl_heap_entry_t* a, tl_heap_entry_t* b) {
    tl_heap_entry_t tmp = *a;
    *a = *b;
    *b = tmp;
}

/* Restore the heap property after an insertion at idx. */
static void sift_up(tl_heap_t* h, size_t idx) {
    while (idx > 0) {
        size_t parent = (idx - 1) / 2;

        if (!heap_entry_less(&h->data[idx], &h->data[parent])) {
            break;
        }

        heap_entry_swap(&h->data[idx], &h->data[parent]);
        idx = parent;
    }
}

/* Restore the heap property after replacing the root. */
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
            break;
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

    /* Allocator must outlive the heap data: if we own a buffer we must
     * still be able to free it. A NULL allocator here usually indicates a
     * use-after-destroy or memcpy'd heap struct. */
    TL_ASSERT(h->data == NULL || h->alloc != NULL);

    TL_ASSERT(h->len <= h->cap);

    if (h->data != NULL) {
        tl__free(h->alloc, h->data);
    }

    h->data = NULL;
    h->len = 0;
    h->cap = 0;
    /* h->alloc is intentionally not cleared: the allocator outlives the
     * heap and may be reused if init is called again on the same struct. */
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

    size_t new_cap = tl__grow_capacity(h->cap, min_cap, HEAP_MIN_CAPACITY);
    if (new_cap == 0 || tl__alloc_would_overflow(new_cap, sizeof(tl_heap_entry_t))) {
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

    h->data[h->len] = *entry;
    h->len++;
    sift_up(h, h->len - 1);

    return TL_OK;
}

tl_status_t tl_heap_pop(tl_heap_t* h, tl_heap_entry_t* out) {
    TL_ASSERT(h != NULL);
    TL_ASSERT(out != NULL);

    if (h->len == 0) {
        return TL_EOF;
    }

    *out = h->data[0];

    /* Standard binary-heap pop: move the last element to the root and
     * sift it down to restore the heap order. */
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

void tl_heap_replace_top(tl_heap_t* h, const tl_heap_entry_t* new_entry) {
    TL_ASSERT(h != NULL);
    TL_ASSERT(h->len > 0);
    TL_ASSERT(new_entry != NULL);

    h->data[0] = *new_entry;
    sift_down(h, 0);
}
