#include "tl_merge_iter.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/* Disable C4702 (unreachable code) for defensive fallback code.
 * LTCG proves these are unreachable, but we keep them for safety. */
#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable: 4702)
#endif

/**
 * Advance a source iterator and get the next record.
 *
 * @param src    Source to advance
 * @param out    Output record
 * @return TL_OK if record available, TL_EOF if exhausted
 */
static tl_status_t source_next(tl_iter_source_t* src, tl_record_t* out) {
    if (src->kind == TL_ITER_SEGMENT) {
        return tl_segment_iter_next(&src->iter.segment, out);
    }
    if (src->kind == TL_ITER_MEMRUN) {
        return tl_memrun_iter_next(&src->iter.memrun, out);
    }
    if (src->kind == TL_ITER_ACTIVE) {
        return tl_active_iter_next(&src->iter.active, out);
    }
    /* Should never reach here - all enum values handled above */
    TL_ASSERT(false && "Invalid source kind");
    return TL_EINVAL;
}

/**
 * Check if a source is done.
 */
static bool source_done(const tl_iter_source_t* src) {
    if (src->kind == TL_ITER_SEGMENT) {
        return tl_segment_iter_done(&src->iter.segment);
    }
    if (src->kind == TL_ITER_MEMRUN) {
        return tl_memrun_iter_done(&src->iter.memrun);
    }
    if (src->kind == TL_ITER_ACTIVE) {
        return tl_active_iter_done(&src->iter.active);
    }
    /* Should never reach here - all enum values handled above */
    TL_ASSERT(false && "Invalid source kind");
    return true;
}

#ifdef _MSC_VER
#pragma warning(pop)
#endif

/**
 * Push initial entry for a source onto the heap.
 *
 * Primes the source iterator with next() and pushes if successful.
 *
 * @param h    Heap to push onto
 * @param src  Source to prime (priority field used for tie-breaking)
 * @return TL_OK on success (whether pushed or source was empty),
 *         TL_ENOMEM on heap allocation failure
 */
static tl_status_t push_initial_entry(tl_heap_t* h,
                                       tl_iter_source_t* src) {
    /* Check if already exhausted (from init pruning) */
    if (source_done(src)) {
        return TL_OK;
    }

    /* Prime the iterator */
    tl_record_t rec;
    tl_status_t st = source_next(src, &rec);

    if (st == TL_EOF) {
        /* Source was empty */
        return TL_OK;
    }
    if (st != TL_OK) {
        return st;
    }

    /* Push entry onto heap.
     *
     * Use source priority for tie-breaking. Higher priority sources
     * (newer data) will appear after lower priority on timestamp ties.
     * This is an implementation detail, not a public guarantee.
     */
    tl_heap_entry_t entry = {
        .ts = rec.ts,
        .component_id = src->priority,
        .handle = rec.handle,
        .iter = src
    };

    return tl_heap_push(h, &entry);
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_kmerge_iter_init(tl_kmerge_iter_t* it,
                                 tl_plan_t* plan,
                                 tl_alloc_ctx_t* alloc) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(plan != NULL);
    TL_ASSERT(alloc != NULL);

    memset(it, 0, sizeof(*it));
    it->plan = plan;
    it->alloc = alloc;

    tl_heap_init(&it->heap, alloc);

    /* Handle empty plan */
    if (plan->source_count == 0) {
        it->done = true;
        return TL_OK;
    }

    /* Reserve heap capacity */
    tl_status_t st = tl_heap_reserve(&it->heap, plan->source_count);
    if (st != TL_OK) {
        return st;
    }

    /* Prime each source and push initial entries */
    for (size_t i = 0; i < plan->source_count; i++) {
        tl_iter_source_t* src = tl_plan_source(plan, i);
        st = push_initial_entry(&it->heap, src);
        if (st != TL_OK) {
            tl_heap_destroy(&it->heap);
            return st;
        }
    }

    /* Check if all sources were empty */
    if (tl_heap_is_empty(&it->heap)) {
        it->done = true;
    }

    return TL_OK;
}

void tl_kmerge_iter_destroy(tl_kmerge_iter_t* it) {
    if (it == NULL) {
        return;
    }

    tl_heap_destroy(&it->heap);
    it->plan = NULL;
    it->done = true;
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_kmerge_iter_next(tl_kmerge_iter_t* it, tl_record_t* out) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(out != NULL);

    if (it->done) {
        return TL_EOF;
    }

    /*
     * Use peek + replace_top pattern to eliminate allocation failure window.
     *
     * Previous code used pop + push, which had a failure window: if push
     * failed after pop, the next record from that source would be lost.
     * Since init() reserves capacity for source_count entries, push "should"
     * never allocate, but relying on that is fragile.
     *
     * New pattern:
     * 1. Peek minimum (no modification)
     * 2. Output the record
     * 3. Advance source
     * 4. If source has more: replace_top (cannot fail - no allocation)
     * 5. If source exhausted: pop (cannot fail - just removes)
     *
     * This guarantees no data loss regardless of allocation behavior.
     */

    /* Step 1: Peek minimum (heap unchanged) */
    const tl_heap_entry_t* peek = tl_heap_peek(&it->heap);
    if (peek == NULL) {
        it->done = true;
        return TL_EOF;
    }

    /* Step 2: Output the record */
    out->ts = peek->ts;
    out->handle = peek->handle;

    /* Get source pointer and component_id while peek is still valid */
    tl_iter_source_t* src = (tl_iter_source_t*)peek->iter;
    uint32_t component_id = peek->component_id;

    /* Step 3: Advance the source that produced this record */
    tl_record_t next_rec;
    tl_status_t st = source_next(src, &next_rec);

    if (st == TL_OK) {
        /* Step 4: Source has more - replace top entry (no allocation) */
        tl_heap_entry_t new_entry = {
            .ts = next_rec.ts,
            .component_id = component_id,
            .handle = next_rec.handle,
            .iter = src
        };
        tl_heap_replace_top(&it->heap, &new_entry);
    } else {
        /* Step 5: Source exhausted - remove entry from heap (no allocation) */
        tl_heap_entry_t discard;
        (void)tl_heap_pop(&it->heap, &discard);
    }

    /* Check if heap is now empty */
    if (tl_heap_is_empty(&it->heap)) {
        it->done = true;
    }

    return TL_OK;
}
