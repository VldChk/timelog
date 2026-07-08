#ifndef TL_HEAP_H
#define TL_HEAP_H

#include "tl_defs.h"
#include "tl_alloc.h"

/*===========================================================================
 * Min-Heap
 *
 * Backs the K-way merge used on the read path. Entries are ordered by
 * (timestamp, tie_break_key); equal timestamps are broken by tie_break_key
 * so the merge output remains deterministic. Push, pop, and peek run in
 * O(log K).
 *
 * Used by the segment merge iterator and the memview iterator (the latter
 * merges the active run, OOO runs, and sealed memruns).
 *
 * Not thread-safe; callers serialise access externally.
 *===========================================================================*/

/**
 * One slot per active component iterator. The fields hold the iterator's
 * current record so the heap can order without dereferencing iter on every
 * comparison; iter is followed only when the entry is popped to advance the
 * source.
 */
typedef struct tl_heap_entry {
    tl_ts_t       ts;            /* Primary sort key. */
    uint32_t      tie_break_key; /* Disambiguates equal timestamps. */
    tl_handle_t   handle;
    tl_seq_t      watermark;     /* Tombstone watermark of the source. */
    void*         iter;          /* Opaque component iterator. */
} tl_heap_entry_t;

/** Min-heap ordered by (ts, tie_break_key). */
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
 * Release heap storage and reset to a valid empty state. Idempotent on
 * already-destroyed or zero-initialised heaps so it can be used in cleanup
 * paths regardless of how far initialisation progressed.
 */
void tl_heap_destroy(tl_heap_t* h);

void tl_heap_clear(tl_heap_t* h);

/** Grow the backing array so it can hold at least min_cap entries. */
tl_status_t tl_heap_reserve(tl_heap_t* h, size_t min_cap);

/*---------------------------------------------------------------------------
 * Heap Operations
 *---------------------------------------------------------------------------*/

/**
 * @return TL_OK on success, TL_ENOMEM on allocation failure.
 */
tl_status_t tl_heap_push(tl_heap_t* h, const tl_heap_entry_t* entry);

/**
 * @param out Receives the popped minimum entry.
 * @return TL_OK on success, TL_EOF if the heap is empty.
 */
tl_status_t tl_heap_pop(tl_heap_t* h, tl_heap_entry_t* out);

/** @return Pointer to the minimum entry, or NULL when empty. */
const tl_heap_entry_t* tl_heap_peek(const tl_heap_t* h);

/**
 * Replace the top entry with new_entry and sift down. Equivalent to
 * pop+push without the extra log K work of restoring the heap twice.
 * Precondition: the heap is not empty.
 */
void tl_heap_replace_top(tl_heap_t* h, const tl_heap_entry_t* new_entry);

/*---------------------------------------------------------------------------
 * Accessors
 *---------------------------------------------------------------------------*/

TL_INLINE bool tl_heap_is_empty(const tl_heap_t* h) {
    return h->len == 0;
}

#endif /* TL_HEAP_H */
