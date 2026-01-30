#ifndef TL_HEAP_H
#define TL_HEAP_H

#include "tl_defs.h"
#include "tl_alloc.h"

/*===========================================================================
 * Min-Heap
 *
 * Provides efficient K-way merge for the read path. Stores
 * (timestamp, tie_break_key) pairs and supports:
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
    tl_ts_t       ts;            /* Sort key (timestamp) */
    uint32_t      tie_break_key; /* M-14: Secondary sort key for equal timestamps */
    tl_handle_t   handle;        /* Current record handle */
    void*         iter;          /* Opaque pointer to component iterator */
} tl_heap_entry_t;

/**
 * Min-heap for K-way merge.
 * Entries are ordered by (ts, tie_break_key).
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
