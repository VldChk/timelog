#ifndef TL_KMERGE_ITER_H
#define TL_KMERGE_ITER_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_heap.h"
#include "tl_plan.h"

/*===========================================================================
 * K-way Merge Iterator
 *
 * K-way merge over all component iterators (segments, memruns, active).
 * Uses a min-heap to efficiently produce records in sorted order.
 *
 * NOTE: This is distinct from tl_merge_iter_t in tl_flush.h, which is
 * a simple two-way merge used during flush. This is a K-way merge for
 * the read path query execution.
 *
 * The merge iterator takes a query plan as input. The plan contains
 * initialized iterators for all sources that overlap the query range.
 *
 * Algorithm:
 * 1. Initialize: prime each source iterator with next(), push onto heap
 * 2. On next(): pop minimum, output record, advance source, push replacement
 * 3. Continue until heap is empty
 *
 * Tie-Breaking (implementation detail, not a public guarantee):
 * - On timestamp ties, sources are ordered by tie_break_key (priority assigned
 *   by the query plan, not necessarily the iterator array index)
 * - This provides deterministic results for testing, but clients must not
 *   depend on tie-break ordering - it may change in future versions
 *
 * Thread Safety:
 * - Not thread-safe (each thread needs its own iterator)
 * - Plan must remain valid for the lifetime of the iterator
 *
 * Reference: Read Path LLD Section 6
 *===========================================================================*/

typedef struct tl_kmerge_iter {
    /* Min-heap for K-way merge */
    tl_heap_t       heap;

    /* Source plan (borrowed, must remain valid) */
    tl_plan_t*      plan;

    /* State */
    bool            done;
    tl_status_t     error;

    /* Allocator (borrowed) */
    tl_alloc_ctx_t* alloc;
} tl_kmerge_iter_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Initialize K-way merge iterator from query plan.
 *
 * Primes all component iterators and builds the initial heap.
 * If no sources have data, the iterator starts exhausted.
 *
 * @param it     Iterator to initialize
 * @param plan   Query plan (must remain valid; owned by caller)
 * @param alloc  Allocator for heap data
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_kmerge_iter_init(tl_kmerge_iter_t* it,
                                 tl_plan_t* plan,
                                 tl_alloc_ctx_t* alloc);

/**
 * Destroy K-way merge iterator.
 *
 * Frees heap data but does NOT destroy the plan.
 * Safe to call on zero-initialized or partially initialized iterator.
 */
void tl_kmerge_iter_destroy(tl_kmerge_iter_t* it);

/*===========================================================================
 * Iteration
 *===========================================================================*/

/**
 * Get next record from merged stream.
 *
 * Returns records in non-decreasing timestamp order.
 * Duplicates (same timestamp from different sources) are preserved.
 *
 * @param it   Iterator
 * @param out  Output record
 * @return TL_OK if record available, TL_EOF if exhausted
 */
tl_status_t tl_kmerge_iter_next(tl_kmerge_iter_t* it, tl_record_t* out);

/**
 * Seek all sources to first record with ts >= target.
 *
 * Used for skip-ahead optimization when filtering tombstones.
 * After seek, the iterator is repositioned so that the next call to
 * tl_kmerge_iter_next() returns the first record with ts >= target.
 *
 * Semantics:
 * - Forward-only: if target <= current position, this is a no-op
 * - Entries in the heap with ts >= target are preserved (not re-fetched)
 * - Only sources with buffered ts < target are re-sought
 * - If all sources are exhausted after seek, iterator becomes done
 *
 * Implementation note: The heap contains prefetched records. Source iterators
 * use forward-only seek and cannot recover records they've already returned.
 * Therefore, heap entries with ts >= target must be preserved in place.
 *
 * @param it     Iterator
 * @param target Target timestamp to seek to
 */
void tl_kmerge_iter_seek(tl_kmerge_iter_t* it, tl_ts_t target);

/*===========================================================================
 * State Queries
 *===========================================================================*/

/**
 * Check if iterator is exhausted.
 */
TL_INLINE bool tl_kmerge_iter_done(const tl_kmerge_iter_t* it) {
    TL_ASSERT(it != NULL);
    return it->done || (it->error != TL_OK);
}

/**
 * Peek at minimum timestamp without advancing.
 *
 * Useful for skip-ahead optimization.
 *
 * @param it  Iterator
 * @return Pointer to minimum timestamp, or NULL if exhausted
 */
TL_INLINE const tl_ts_t* tl_kmerge_iter_peek_ts(const tl_kmerge_iter_t* it) {
    TL_ASSERT(it != NULL);
    if (it->done || it->error != TL_OK) return NULL;
    const tl_heap_entry_t* entry = tl_heap_peek(&it->heap);
    return entry != NULL ? &entry->ts : NULL;
}

#endif /* TL_KMERGE_ITER_H */
