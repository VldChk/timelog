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

    /* Pop minimum from heap */
    tl_heap_entry_t entry;
    tl_status_t st = tl_heap_pop(&it->heap, &entry);

    if (st == TL_EOF) {
        it->done = true;
        return TL_EOF;
    }
    TL_ASSERT(st == TL_OK);

    /* Output the record */
    out->ts = entry.ts;
    out->handle = entry.handle;

    /* Advance the source that produced this record */
    tl_iter_source_t* src = (tl_iter_source_t*)entry.iter;

    tl_record_t next_rec;
    st = source_next(src, &next_rec);

    if (st == TL_OK) {
        /* Push replacement entry */
        tl_heap_entry_t new_entry = {
            .ts = next_rec.ts,
            .component_id = entry.component_id,
            .handle = next_rec.handle,
            .iter = src
        };

        st = tl_heap_push(&it->heap, &new_entry);
        if (st != TL_OK) {
            /* Heap push failed - iterator is in inconsistent state.
             * Mark as done to prevent further use. */
            it->done = true;
            return st;
        }
    }
    /* If TL_EOF, source is exhausted - don't push replacement */

    /* Check if heap is now empty */
    if (tl_heap_is_empty(&it->heap)) {
        it->done = true;
    }

    return TL_OK;
}
