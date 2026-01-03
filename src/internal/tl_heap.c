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

    if (h->data != NULL) {
        tl__free(h->alloc, h->data);
    }

    h->data = NULL;
    h->len = 0;
    h->cap = 0;
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
