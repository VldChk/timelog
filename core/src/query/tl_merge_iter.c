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

/** Advance a source iterator and get the next record. */
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

/** Check if a source is done. */
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

/** Seek a source to target timestamp (forward-only). */
static tl_status_t source_seek(tl_iter_source_t* src, tl_ts_t target) {
    if (src->kind == TL_ITER_SEGMENT) {
        tl_segment_iter_seek(&src->iter.segment, target);
        return TL_OK;
    }
    if (src->kind == TL_ITER_MEMRUN) {
        return tl_memrun_iter_seek(&src->iter.memrun, target);
    }
    if (src->kind == TL_ITER_ACTIVE) {
        return tl_active_iter_seek(&src->iter.active, target);
    }
    /* Should never reach here - all enum values handled above */
    TL_ASSERT(false && "Invalid source kind");
    return TL_EINVAL;
}

#ifdef _MSC_VER
#pragma warning(pop)
#endif

/** Prime a source with next() and push initial entry onto heap. */
static tl_status_t push_initial_entry(tl_heap_t* h,
                                       tl_iter_source_t* src) {
    if (source_done(src)) {
        return TL_OK;
    }

    tl_record_t rec;
    tl_seq_t watermark = 0;
    tl_status_t st = source_next(src, &rec, &watermark);

    if (st == TL_EOF) {
        return TL_OK;
    }
    if (st != TL_OK) {
        return st;
    }

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
     * Peek + replace_top pattern: avoids the data-loss window of
     * pop + push (where push failure would lose a record).
     */
    const tl_heap_entry_t* peek = tl_heap_peek(&it->heap);
    if (peek == NULL) {
        it->done = true;
        return TL_EOF;
    }

    out->ts = peek->ts;
    out->handle = peek->handle;
    if (out_watermark != NULL) {
        *out_watermark = peek->watermark;
    }

    tl_iter_source_t* src = (tl_iter_source_t*)peek->iter;
    uint32_t tie_id = peek->tie_break_key;

    tl_record_t next_rec;
    tl_seq_t next_watermark = 0;
    tl_status_t st = source_next(src, &next_rec, &next_watermark);

    if (st == TL_OK) {
        /* Replace top (no allocation needed) */
        tl_heap_entry_t new_entry = {
            .ts = next_rec.ts,
            .tie_break_key = tie_id,
            .handle = next_rec.handle,
            .watermark = next_watermark,
            .iter = src
        };
        tl_heap_replace_top(&it->heap, &new_entry);
    } else if (st == TL_EOF) {
        tl_heap_entry_t discard;
        (void)tl_heap_pop(&it->heap, &discard);
    } else {
        it->error = st;
        it->done = true;
        tl_heap_clear(&it->heap);
        return st;
    }

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

    /* Forward-only: no-op if target <= current min */
    const tl_ts_t* current_min = tl_kmerge_iter_peek_ts(it);
    if (current_min != NULL && target <= *current_min) {
        return;
    }

    /*
     * Pop entries with ts < target, re-seek those sources, push replacements.
     * Entries with ts >= target are preserved (source already advanced past them,
     * so they cannot be re-fetched). Min-heap property lets us stop when
     * peek()->ts >= target.
     */
    while (!tl_heap_is_empty(&it->heap)) {
        const tl_heap_entry_t* min = tl_heap_peek(&it->heap);
        if (min->ts >= target) {
            break;
        }

        tl_heap_entry_t popped;
        (void)tl_heap_pop(&it->heap, &popped);

        tl_iter_source_t* src = (tl_iter_source_t*)popped.iter;

        tl_status_t seek_st = source_seek(src, target);
        if (seek_st != TL_OK) {
            it->error = seek_st;
            it->done = true;
            tl_heap_clear(&it->heap);
            return;
        }

        if (source_done(src)) {
            continue;
        }

        tl_record_t rec;
        tl_seq_t watermark = 0;
        tl_status_t st = source_next(src, &rec, &watermark);

        if (st == TL_EOF) {
            continue;
        }

        if (st != TL_OK) {
            it->error = st;
            it->done = true;
            tl_heap_clear(&it->heap);
            return;
        }

        tl_heap_entry_t entry = {
            .ts = rec.ts,
            .tie_break_key = popped.tie_break_key,
            .handle = rec.handle,
            .watermark = watermark,
            .iter = src
        };

        tl_status_t push_st = tl_heap_push(&it->heap, &entry);
        if (push_st != TL_OK) {
            it->error = push_st;
            it->done = true;
            tl_heap_clear(&it->heap);
            return;
        }
    }

    if (tl_heap_is_empty(&it->heap)) {
        it->done = true;
    }
}
