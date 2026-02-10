#include "tl_merge_iter.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/* Test hook: force kmerge source_next to return TL_EINTERNAL */
#ifdef TL_TEST_HOOKS
volatile int tl_test_kmerge_force_error_count = 0;
#endif

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
static tl_status_t source_next(tl_iter_source_t* src, tl_record_t* out,
                               tl_seq_t* out_watermark) {
#ifdef TL_TEST_HOOKS
    if (tl_test_kmerge_force_error_count > 0) {
        tl_test_kmerge_force_error_count--;
        return TL_EINTERNAL;
    }
#endif
    if (src->kind == TL_ITER_SEGMENT) {
        tl_status_t st = tl_segment_iter_next(&src->iter.segment, out);
        if (st == TL_OK && out_watermark != NULL) {
            *out_watermark = src->watermark;
        }
        return st;
    }
    if (src->kind == TL_ITER_MEMRUN) {
        return tl_memrun_iter_next(&src->iter.memrun, out, out_watermark);
    }
    if (src->kind == TL_ITER_ACTIVE) {
        return tl_active_iter_next(&src->iter.active, out, out_watermark);
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

/**
 * Seek a source iterator to target timestamp.
 * After seek, caller should call source_next to get the first record >= target.
 */
static void source_seek(tl_iter_source_t* src, tl_ts_t target) {
    if (src->kind == TL_ITER_SEGMENT) {
        tl_segment_iter_seek(&src->iter.segment, target);
        return;
    }
    if (src->kind == TL_ITER_MEMRUN) {
        tl_memrun_iter_seek(&src->iter.memrun, target);
        return;
    }
    if (src->kind == TL_ITER_ACTIVE) {
        tl_active_iter_seek(&src->iter.active, target);
        return;
    }
    /* Should never reach here - all enum values handled above */
    TL_ASSERT(false && "Invalid source kind");
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
    tl_seq_t watermark = 0;
    tl_status_t st = source_next(src, &rec, &watermark);

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
        .tie_break_key = src->priority,
        .handle = rec.handle,
        .watermark = watermark,
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
    it->error = TL_OK;

    tl_heap_init(&it->heap, alloc);

    /* Handle empty plan */
    if (plan->source_count == 0) {
        it->done = true;
        return TL_OK;
    }

    /* Compute skip-ahead metadata */
    it->max_watermark = 0;
    it->has_variable_watermark = false;
    for (size_t i = 0; i < plan->source_count; i++) {
        const tl_iter_source_t* src = tl_plan_source(plan, i);
        if (src->kind == TL_ITER_ACTIVE) {
            it->has_variable_watermark = true;
            continue;
        }
        if (src->watermark > it->max_watermark) {
            it->max_watermark = src->watermark;
        }
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
    it->error = TL_OK;
    it->max_watermark = 0;
    it->has_variable_watermark = false;
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_kmerge_iter_next(tl_kmerge_iter_t* it, tl_record_t* out,
                                 tl_seq_t* out_watermark) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(out != NULL);

    if (it->error != TL_OK) {
        return it->error;
    }
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
    if (out_watermark != NULL) {
        *out_watermark = peek->watermark;
    }

    /* Get source pointer and tie_break_key while peek is still valid */
    tl_iter_source_t* src = (tl_iter_source_t*)peek->iter;
    uint32_t tie_id = peek->tie_break_key;

    /* Step 3: Advance the source that produced this record */
    tl_record_t next_rec;
    tl_seq_t next_watermark = 0;
    tl_status_t st = source_next(src, &next_rec, &next_watermark);

    if (st == TL_OK) {
        /* Step 4: Source has more - replace top entry (no allocation) */
        tl_heap_entry_t new_entry = {
            .ts = next_rec.ts,
            .tie_break_key = tie_id,
            .handle = next_rec.handle,
            .watermark = next_watermark,
            .iter = src
        };
        tl_heap_replace_top(&it->heap, &new_entry);
    } else if (st == TL_EOF) {
        /* Source exhausted - remove entry from heap (no allocation).
         * Source iterators are expected to return TL_OK or TL_EOF only. */
        tl_heap_entry_t discard;
        (void)tl_heap_pop(&it->heap, &discard);
    } else {
        /* Error - clear heap to avoid stale refs */
        it->error = st;
        it->done = true;
        tl_heap_clear(&it->heap);
        return st;
    }

    /* Check if heap is now empty */
    if (tl_heap_is_empty(&it->heap)) {
        it->done = true;
    }

    return TL_OK;
}

/*===========================================================================
 * Seek
 *===========================================================================*/

void tl_kmerge_iter_seek(tl_kmerge_iter_t* it, tl_ts_t target) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(it->plan != NULL);

    if (it->error != TL_OK) {
        return;
    }
    if (it->done) {
        return;
    }

    /*
     * Optimization: Check if target is at or before current minimum.
     * If so, this is a no-op (forward-only seek).
     */
    const tl_ts_t* current_min = tl_kmerge_iter_peek_ts(it);
    if (current_min != NULL && target <= *current_min) {
        return;
    }

    /*
     * FIXED seek algorithm (C-02 / QUERY-1.1):
     *
     * The heap contains PREFETCHED records. Each heap entry has a timestamp (ts)
     * and an iterator pointer (iter). The source iterator has already advanced
     * past the record stored in the heap entry via previous next() calls.
     *
     * Source iterators use FORWARD-ONLY seek: seek(target) advances to the first
     * record >= target, but cannot go backwards. If we clear the entire heap and
     * re-seek all sources, we lose records that were:
     * - Already fetched (in heap) with ts >= target
     * - Not recoverable because the source has already advanced past them
     *
     * Correct algorithm:
     * 1. Pop entries with ts < target (these sources need to advance)
     * 2. For each popped entry, seek that source and push new entry if available
     * 3. Preserve entries with ts >= target (already correct, no action needed)
     *
     * The min-heap property guarantees: if peek()->ts >= target, then ALL entries
     * in the heap have ts >= target, so we can stop the loop.
     *
     * Complexity: O(P * (log K + seek_cost)) where P = popped entries, K = heap size.
     * Worst case P = K (all entries < target), but typically P << K when seeking
     * past tombstone ranges where most sources are already positioned ahead.
     */

    /* Pop all entries with ts < target and re-seek those sources */
    while (!tl_heap_is_empty(&it->heap)) {
        const tl_heap_entry_t* min = tl_heap_peek(&it->heap);
        if (min->ts >= target) {
            /* Min-heap property: if minimum >= target, all entries >= target.
             * These prefetched records are already valid; preserve them. */
            break;
        }

        /* Pop entry for source that needs to advance */
        tl_heap_entry_t popped;
        (void)tl_heap_pop(&it->heap, &popped);

        tl_iter_source_t* src = (tl_iter_source_t*)popped.iter;

        /* Seek this source to target */
        source_seek(src, target);

        /* Check if source is exhausted after seek */
        if (source_done(src)) {
            continue;
        }

        /* Prime the iterator with next record */
        tl_record_t rec;
        tl_seq_t watermark = 0;
        tl_status_t st = source_next(src, &rec, &watermark);

        if (st == TL_EOF) {
            continue;
        }

        if (st != TL_OK) {
            /* Error - mark as done and return.
             * Existing behavior: errors become EOF (see H-16 for error state). */
            it->error = st;
            it->done = true;
            tl_heap_clear(&it->heap);
            return;
        }

        /* Push onto heap.
         * Use popped.tie_break_key to preserve original tie-break semantics
         * (Codex review: safer than re-reading src->priority). */
        tl_heap_entry_t entry = {
            .ts = rec.ts,
            .tie_break_key = popped.tie_break_key,
            .handle = rec.handle,
            .watermark = watermark,
            .iter = src
        };

        tl_status_t push_st = tl_heap_push(&it->heap, &entry);
        if (push_st != TL_OK) {
            /* Allocation failure during seek invalidates the iterator.
             * Subsequent operations will return EOF. */
            it->error = push_st;
            it->done = true;
            tl_heap_clear(&it->heap);
            return;
        }
    }

    /* Check if all sources exhausted */
    if (tl_heap_is_empty(&it->heap)) {
        it->done = true;
    }
}
