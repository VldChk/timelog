#ifndef TL_KMERGE_ITER_H
#define TL_KMERGE_ITER_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_heap.h"
#include "tl_plan.h"

/*===========================================================================
 * K-way Merge Iterator
 *
 * Min-heap K-way merge over all component iterators referenced by a
 * query plan (segment iterators, memrun iterators, the active memview
 * iterator). Each next() pops the minimum-timestamp entry, advances the
 * source it came from, and pushes the replacement entry.
 *
 * Distinct from the flush build's internal k-way merge (tl_flush.c), which
 * merges memrun sources directly over tl_heap without an iterator layer.
 *
 * Tie-Breaking (implementation detail, not a public guarantee):
 * - On timestamp ties, sources are ordered by tie_break_key (priority
 *   assigned by the query plan, not the iterator array index).
 * - This is deterministic for tests but may change between versions;
 *   clients must not depend on the ordering.
 *
 * Thread Safety:
 * - Not thread-safe (each thread needs its own iterator).
 * - Plan must remain valid for the lifetime of the iterator.
 *===========================================================================*/

typedef struct tl_kmerge_iter {
    /* Min-heap for K-way merge */
    tl_heap_t       heap;

    /* Source plan (borrowed, must remain valid) */
    tl_plan_t*      plan;

    /* State */
    bool            done;
    tl_status_t     error;

    /* Skip-ahead optimization state */
    tl_seq_t        max_watermark;
    bool            has_variable_watermark;
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
tl_status_t tl_kmerge_iter_next(tl_kmerge_iter_t* it, tl_record_t* out,
                                 tl_seq_t* out_watermark);

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

/**
 * Check if skip-ahead is safe for a tombstone seq.
 *
 * Safe when all sources have constant watermarks and tomb_seq is newer
 * than every source watermark.
 */
TL_INLINE bool tl_kmerge_iter_can_skip(const tl_kmerge_iter_t* it,
                                       tl_seq_t tomb_seq) {
    return !it->has_variable_watermark && tomb_seq > it->max_watermark;
}

/*===========================================================================
 * State Queries
 *===========================================================================*/

/** Check if iterator is exhausted. */
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
