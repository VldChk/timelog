/*
============================================================================

   COMBINED SOURCE FILE: query.c

   Generated from: core\src\query
   Generated at:   2026-01-30 00:27:14

   This file combines all .c files from the query/ subfolder.

   Files included:
 *   - tl_active_iter.c
 *   - tl_filter.c
 *   - tl_iter_build.c
 *   - tl_memrun_iter.c
 *   - tl_merge_iter.c
 *   - tl_pagespan_iter.c
 *   - tl_plan.c
 *   - tl_point.c
 *   - tl_segment_iter.c
 *   - tl_snapshot.c
 *   - tl_submerge.c

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: tl_active_iter.c
/*   FROM: query/
/*
/******************************************************************************/
#include "tl_active_iter.h"
#include "tl_submerge.h"
#include "tl_iter_build.h"
#include "../internal/tl_range.h"
#include <string.h>

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_active_iter_init(tl_active_iter_t* it,
                                 const tl_memview_t* mv,
                                 tl_ts_t t1, tl_ts_t t2,
                                 bool t2_unbounded,
                                 tl_alloc_ctx_t* alloc) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(mv != NULL);
    TL_ASSERT(alloc != NULL);

    memset(it, 0, sizeof(*it));
    it->mv = mv;
    it->t1 = t1;
    it->t2 = t2;
    it->t2_unbounded = t2_unbounded;
    it->done = false;

    size_t run_len = tl_memview_run_len(mv);
    size_t head_len = tl_memview_ooo_head_len(mv);
    const tl_ooorunset_t* runs = tl_memview_ooo_runs(mv);

    tl_status_t st = tl_iter_build_submerge(&it->merge,
                                            alloc,
                                            tl_memview_run_data(mv),
                                            run_len,
                                            runs,
                                            tl_memview_ooo_head_data(mv),
                                            head_len,
                                            t1,
                                            t2,
                                            t2_unbounded);
    if (st != TL_OK) {
        return st;
    }

    if (tl_submerge_done(&it->merge)) {
        it->done = true;
    }

    return TL_OK;
}

void tl_active_iter_destroy(tl_active_iter_t* it) {
    if (it == NULL) {
        return;
    }

    tl_submerge_destroy(&it->merge);
    it->mv = NULL;
    it->done = true;
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_active_iter_next(tl_active_iter_t* it, tl_record_t* out) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return TL_EOF;
    }

    tl_record_t rec;
    tl_status_t st = tl_submerge_next(&it->merge, &rec);
    if (st != TL_OK) {
        it->done = true;
        return TL_EOF;
    }

    if (out != NULL) {
        *out = rec;
    }

    return TL_OK;
}

void tl_active_iter_seek(tl_active_iter_t* it, tl_ts_t target) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return;
    }

    if (target <= it->t1) {
        return;
    }

    if (!it->t2_unbounded && target >= it->t2) {
        it->done = true;
        return;
    }

    tl_submerge_seek(&it->merge, target);
    it->done = tl_submerge_done(&it->merge);
}

/------------------------------------------------------------------------------/
/*   END OF: tl_active_iter.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_filter.c
/*   FROM: query/
/*
/******************************************************************************/
#include "tl_filter.h"

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_filter_iter_init(tl_filter_iter_t* it,
                          tl_kmerge_iter_t* merge,
                          tl_intervals_imm_t tombs) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(merge != NULL);

    it->merge = merge;
    tl_intervals_cursor_init(&it->tomb_cursor, tombs);
    it->done = tl_kmerge_iter_done(merge);
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_filter_iter_next(tl_filter_iter_t* it, tl_record_t* out) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(out != NULL);

    if (it->done) {
        return TL_EOF;
    }

    /* Loop until we find a visible record or exhaust the merge iterator */
    for (;;) {
        /*
         * Skip-ahead optimization (Read Path LLD Section 7.2):
         *
         * Before fetching the next record, check if we can skip ahead
         * past a tombstone range. This avoids fetching records one-by-one
         * only to discard them immediately.
         *
         * If the merge iterator's current minimum is inside a tombstone,
         * we seek directly to the tombstone's end timestamp.
         */
        const tl_ts_t* peek_ts = tl_kmerge_iter_peek_ts(it->merge);
        if (peek_ts != NULL) {
            tl_ts_t skip_target;
            if (!tl_intervals_cursor_skip_to(&it->tomb_cursor, *peek_ts, &skip_target)) {
                /*
                 * False return means all remaining timestamps are covered
                 * by an unbounded tombstone. No more visible records exist.
                 */
                it->done = true;
                return TL_EOF;
            }

            /*
             * If skip_target > current timestamp, seek the merge iterator
             * to skip past the tombstone range efficiently.
             */
            if (skip_target > *peek_ts) {
                tl_kmerge_iter_seek(it->merge, skip_target);

                /* After seek, iterator may be exhausted */
                if (tl_kmerge_iter_done(it->merge)) {
                    it->done = true;
                    return TL_EOF;
                }
            }
        }

        /* Fetch next record from merge iterator */
        tl_record_t rec;
        tl_status_t st = tl_kmerge_iter_next(it->merge, &rec);

        if (st == TL_EOF) {
            it->done = true;
            return TL_EOF;
        }

        if (st != TL_OK) {
            /* Propagate any error */
            it->done = true;
            return st;
        }

        /* Check if this record is deleted by a tombstone.
         *
         * The cursor is efficient because both the merge output and
         * tombstone intervals are sorted. The cursor advances forward
         * monotonically, giving amortized O(1) per record.
         *
         * Edge cases handled by cursor:
         * - Empty tombstone set: pos >= len, returns false (not deleted)
         * - Single tombstone [a,b): deleted iff a <= ts < b
         * - Unbounded tombstone [a, +inf): deleted iff ts >= a
         * - Gaps between tombstones: correctly returns false in gaps
         * - Boundary values: half-open [start, end) semantics
         *
         * IMPORTANT: cursor_is_deleted assumes monotonically increasing ts.
         * Out-of-order timestamps would require cursor reset (not supported).
         * The k-way merge guarantees sorted output, so this is safe.
         *
         * Note: After the skip-ahead optimization above, most records that
         * reach this point should NOT be deleted. The check here handles
         * edge cases where skip_target == *peek_ts (record at tombstone boundary).
         */
        if (tl_intervals_cursor_is_deleted(&it->tomb_cursor, rec.ts)) {
            /* Record is deleted - skip it */
            continue;
        }

        /* Record is visible - return it */
        *out = rec;
        return TL_OK;
    }
}

/------------------------------------------------------------------------------/
/*   END OF: tl_filter.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_iter_build.c
/*   FROM: query/
/*
/******************************************************************************/
#include "tl_iter_build.h"

static size_t count_sources(const tl_record_t* run_data,
                            size_t run_len,
                            const tl_ooorunset_t* runs,
                            const tl_record_t* head_data,
                            size_t head_len) {
    size_t count = 0;
    if (run_len > 0 && run_data != NULL) {
        count++;
    }
    if (head_len > 0 && head_data != NULL) {
        count++;
    }
    if (runs != NULL) {
        for (size_t i = 0; i < runs->count; i++) {
            const tl_ooorun_t* run = runs->runs[i];
            if (run != NULL && run->len > 0) {
                count++;
            }
        }
    }
    return count;
}

tl_status_t tl_iter_build_submerge(tl_submerge_t* merge,
                                    tl_alloc_ctx_t* alloc,
                                    const tl_record_t* run_data,
                                    size_t run_len,
                                    const tl_ooorunset_t* runs,
                                    const tl_record_t* head_data,
                                    size_t head_len,
                                    tl_ts_t t1,
                                    tl_ts_t t2,
                                    bool t2_unbounded) {
    TL_ASSERT(merge != NULL);
    TL_ASSERT(alloc != NULL);

    size_t run_count = runs != NULL ? runs->count : 0;
    if (run_count > UINT32_MAX - 1) {
        return TL_EOVERFLOW;
    }

    size_t src_count = count_sources(run_data, run_len, runs, head_data, head_len);

    tl_status_t st = tl_submerge_init(merge, alloc, src_count);
    if (st != TL_OK) {
        return st;
    }

    size_t idx = 0;
    if (run_len > 0 && run_data != NULL) {
        tl_submerge_src_init(&merge->srcs[idx++],
                             run_data, run_len,
                             t1, t2, t2_unbounded,
                             0);
    }

    if (runs != NULL) {
        for (size_t i = 0; i < runs->count; i++) {
            const tl_ooorun_t* run = runs->runs[i];
            if (run == NULL || run->len == 0) {
                continue;
            }
            tl_submerge_src_init(&merge->srcs[idx++],
                                 run->records, run->len,
                                 t1, t2, t2_unbounded,
                                 (uint32_t)(1 + i));
        }
    }

    if (head_len > 0 && head_data != NULL) {
        tl_submerge_src_init(&merge->srcs[idx++],
                             head_data, head_len,
                             t1, t2, t2_unbounded,
                             (uint32_t)(1 + run_count));
    }

    merge->src_count = idx;

    st = tl_submerge_build(merge);
    if (st != TL_OK) {
        tl_submerge_destroy(merge);
        return st;
    }

    return TL_OK;
}

/------------------------------------------------------------------------------/
/*   END OF: tl_iter_build.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memrun_iter.c
/*   FROM: query/
/*
/******************************************************************************/
#include "tl_memrun_iter.h"
#include "tl_submerge.h"
#include "tl_iter_build.h"
#include "../internal/tl_range.h"
#include <string.h>

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_memrun_iter_init(tl_memrun_iter_t* it,
                                 const tl_memrun_t* mr,
                                 tl_ts_t t1, tl_ts_t t2,
                                 bool t2_unbounded,
                                 tl_alloc_ctx_t* alloc) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(mr != NULL);
    TL_ASSERT(alloc != NULL);

    memset(it, 0, sizeof(*it));
    it->mr = mr;
    it->t1 = t1;
    it->t2 = t2;
    it->t2_unbounded = t2_unbounded;
    it->done = false;

    if (!tl_memrun_has_records(mr)) {
        it->done = true;
        return TL_OK;
    }

    if (!tl_range_overlaps(tl_memrun_min_ts(mr), tl_memrun_max_ts(mr),
                           t1, t2, t2_unbounded)) {
        it->done = true;
        return TL_OK;
    }

    size_t run_len = tl_memrun_run_len(mr);

    const tl_ooorunset_t* runs = tl_memrun_ooo_runs(mr);

    tl_status_t st = tl_iter_build_submerge(&it->merge,
                                            alloc,
                                            tl_memrun_run_data(mr),
                                            run_len,
                                            runs,
                                            NULL,
                                            0,
                                            t1,
                                            t2,
                                            t2_unbounded);
    if (st != TL_OK) {
        return st;
    }

    if (tl_submerge_done(&it->merge)) {
        it->done = true;
    }

    return TL_OK;
}

void tl_memrun_iter_destroy(tl_memrun_iter_t* it) {
    if (it == NULL) {
        return;
    }

    tl_submerge_destroy(&it->merge);
    it->mr = NULL;
    it->done = true;
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_memrun_iter_next(tl_memrun_iter_t* it, tl_record_t* out) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return TL_EOF;
    }

    tl_record_t rec;
    tl_status_t st = tl_submerge_next(&it->merge, &rec);
    if (st != TL_OK) {
        it->done = true;
        return TL_EOF;
    }

    if (out != NULL) {
        *out = rec;
    }

    return TL_OK;
}

void tl_memrun_iter_seek(tl_memrun_iter_t* it, tl_ts_t target) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return;
    }

    if (target <= it->t1) {
        return;
    }

    if (!it->t2_unbounded && target >= it->t2) {
        it->done = true;
        return;
    }

    tl_submerge_seek(&it->merge, target);
    it->done = tl_submerge_done(&it->merge);
}

/------------------------------------------------------------------------------/
/*   END OF: tl_memrun_iter.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_merge_iter.c
/*   FROM: query/
/*
/******************************************************************************/
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
static tl_status_t source_next(tl_iter_source_t* src, tl_record_t* out) {
#ifdef TL_TEST_HOOKS
    if (tl_test_kmerge_force_error_count > 0) {
        tl_test_kmerge_force_error_count--;
        return TL_EINTERNAL;
    }
#endif
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
        .tie_break_key = src->priority,
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
    it->error = TL_OK;

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
    it->error = TL_OK;
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_kmerge_iter_next(tl_kmerge_iter_t* it, tl_record_t* out) {
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

    /* Get source pointer and tie_break_key while peek is still valid */
    tl_iter_source_t* src = (tl_iter_source_t*)peek->iter;
    uint32_t tie_id = peek->tie_break_key;

    /* Step 3: Advance the source that produced this record */
    tl_record_t next_rec;
    tl_status_t st = source_next(src, &next_rec);

    if (st == TL_OK) {
        /* Step 4: Source has more - replace top entry (no allocation) */
        tl_heap_entry_t new_entry = {
            .ts = next_rec.ts,
            .tie_break_key = tie_id,
            .handle = next_rec.handle,
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
        tl_status_t st = source_next(src, &rec);

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

/------------------------------------------------------------------------------/
/*   END OF: tl_merge_iter.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_pagespan_iter.c
/*   FROM: query/
/*
/******************************************************************************/
/*===========================================================================
 * tl_pagespan_iter.c - PageSpan Iterator Implementation
 *
 * Streaming iterator over page spans for a time range.
 * Moves span enumeration logic from bindings into core, eliminating
 * algorithm duplication and layout coupling.
 *
 * Key design decisions:
 * - Streaming (no pre-allocation of span array)
 * - Each view owns a reference to the owner
 * - Owner refcount is plain uint32_t (caller serialization required)
 * - Free owner before calling release hook (allocator lifetime safety)
 *
 * Reference: docs/timelog_v2_lld_pagespan_core_api_unification.md
 *===========================================================================*/

#include "tl_pagespan_iter.h"
#include "tl_snapshot.h"
#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_range.h"
#include "tl_segment_range.h"
#include "../internal/tl_timelog_internal.h"
#include "../storage/tl_page.h"
#include "../storage/tl_segment.h"
#include "../storage/tl_manifest.h"

#include <string.h>

/* Test hook: force iter allocation failure after owner creation */
#ifdef TL_TEST_HOOKS
volatile int tl_test_pagespan_fail_iter_alloc = 0;
#endif

/*===========================================================================
 * Internal Types
 *===========================================================================*/

/**
 * Owner structure - pins snapshot resources backing spans.
 *
 * CONCURRENCY CONSTRAINT:
 * The refcount is plain uint32_t, NOT atomic. All incref/decref operations
 * MUST be serialized by the caller (GIL for CPython bindings).
 */
struct tl_pagespan_owner {
    uint32_t                    refcnt;     /* NOT atomic - see constraint above */
    tl_snapshot_t*              snapshot;   /* Owned reference */
    tl_alloc_ctx_t*             alloc;      /* Borrowed from timelog */
    tl_pagespan_owner_hooks_t   hooks;      /* Copied from iter_open */
    bool                        hook_armed; /* Hook runs only after successful open */
};

/**
 * Iterator phase state machine.
 * L1 segments are enumerated before L0 (matches B4 behavior).
 */
typedef enum {
    PHASE_L1   = 0,     /* Iterating L1 segments */
    PHASE_L0   = 1,     /* Iterating L0 segments */
    PHASE_DONE = 2      /* All segments exhausted */
} iter_phase_t;

/**
 * Iterator structure - streaming iteration over page spans.
 */
struct tl_pagespan_iter {
    tl_pagespan_owner_t*    owner;      /* Owned reference (released on close) */
    tl_alloc_ctx_t*         alloc;      /* Allocator (for iter cleanup) */
    const tl_manifest_t*    manifest;   /* Borrowed from snapshot */
    tl_ts_t                 t1;         /* Range start (inclusive) */
    tl_ts_t                 t2;         /* Range end (exclusive) */
    uint32_t                flags;      /* TL_PAGESPAN_* flags */

    iter_phase_t            phase;      /* Current phase */
    uint32_t                seg_idx;    /* Current segment index in phase */

    const tl_segment_t*     current_seg;    /* Current segment (NULL if none) */
    uint32_t                page_idx;       /* Current page index in segment */
    uint32_t                page_end;       /* End page index (exclusive) */

    bool                    closed;     /* True after close() called */
};

/*===========================================================================
 * Owner Lifecycle
 *===========================================================================*/

/**
 * Create a new owner with the given snapshot.
 * Initial refcount is 1 (caller owns the reference).
 */
static tl_status_t owner_create(
    tl_snapshot_t* snapshot,
    tl_alloc_ctx_t* alloc,
    const tl_pagespan_owner_hooks_t* hooks,
    tl_pagespan_owner_t** out)
{
    TL_ASSERT(snapshot != NULL);
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    tl_pagespan_owner_t* owner = tl__malloc(alloc, sizeof(tl_pagespan_owner_t));
    if (owner == NULL) {
        return TL_ENOMEM;
    }

    owner->refcnt = 1;
    owner->snapshot = snapshot;
    owner->alloc = alloc;
    owner->hook_armed = false;

    /* Copy hooks (NULL-safe) */
    if (hooks != NULL) {
        owner->hooks = *hooks;
    } else {
        memset(&owner->hooks, 0, sizeof(owner->hooks));
    }

    *out = owner;
    return TL_OK;
}

/**
 * Destroy owner and release all resources.
 *
 * DESTRUCTION ORDER (CRITICAL - allocator lifetime safety):
 * 1. Copy out hooks from owner struct
 * 2. Release snapshot (no binding code runs)
 * 3. Free owner struct BEFORE calling hook
 * 4. Call release hook if non-NULL
 *
 * Rationale: The hook may Py_DECREF the timelog, which owns the allocator.
 * Freeing owner after the hook could use a freed allocator (UAF).
 */
static void owner_destroy(tl_pagespan_owner_t* owner) {
    TL_ASSERT(owner != NULL);
    TL_ASSERT(owner->refcnt == 0);

    /* Step 1: Copy out hooks before freeing owner */
    tl_snapshot_t* snap = owner->snapshot;
    tl_alloc_ctx_t* alloc = owner->alloc;
    tl_pagespan_owner_hooks_t hooks = owner->hooks;
    bool hook_armed = owner->hook_armed;

    /* Step 2: Release snapshot (no binding code runs here) */
    if (snap != NULL) {
        tl_snapshot_release(snap);
    }

    /* Step 3: Free owner struct BEFORE calling hook */
    tl__free(alloc, owner);

    /* Step 4: Call release hook (may run binding code, e.g., Py_DECREF) */
    if (hook_armed && hooks.on_release != NULL) {
        hooks.on_release(hooks.user);
    }
}

void tl_pagespan_owner_incref(tl_pagespan_owner_t* owner) {
    TL_ASSERT(owner != NULL);
    TL_ASSERT(owner->refcnt > 0);       /* Must not be dead */
    TL_ASSERT(owner->refcnt < UINT32_MAX);  /* Overflow check */
    owner->refcnt++;
}

void tl_pagespan_owner_decref(tl_pagespan_owner_t* owner) {
    TL_ASSERT(owner != NULL);
    TL_ASSERT(owner->refcnt > 0);  /* Must not be dead */

    owner->refcnt--;
    if (owner->refcnt == 0) {
        owner_destroy(owner);
    }
}

/*===========================================================================
 * Segment Cursor Initialization
 *
 * Canonical algorithm from tl_segment_iter_init (Section 5.3 of plan).
 * Finds the page range [first, last) that overlaps with [t1, t2).
 *===========================================================================*/

/**
 * Initialize cursor for a segment.
 * Returns true if segment has pages overlapping [t1, t2), false otherwise.
 */
static bool init_segment_cursor(tl_pagespan_iter_t* it, const tl_segment_t* seg) {
    TL_ASSERT(it != NULL);

    /* Null segment or no pages */
    if (seg == NULL || seg->page_count == 0) {
        return false;
    }

    /* Check segment-level bounds overlap with half-open [t1, t2) */
    /* Note: B4 does not support unbounded ranges (t2_unbounded = false) */
    if (!tl_range_overlaps(seg->min_ts, seg->max_ts, it->t1, it->t2, false)) {
        return false;
    }

    size_t first = 0;
    size_t last = 0;
    if (!tl_segment_page_range(seg, it->t1, it->t2, false, &first, &last)) {
        return false;
    }

    /* Validate cast to uint32_t (page counts are bounded by segment build) */
    TL_ASSERT(first <= UINT32_MAX);
    TL_ASSERT(last <= UINT32_MAX);

    it->current_seg = seg;
    it->page_idx = (uint32_t)first;
    it->page_end = (uint32_t)last;

    return true;
}

/*===========================================================================
 * Segment Advancement
 *
 * State machine: PHASE_L1 -> PHASE_L0 -> PHASE_DONE
 * Within each phase, iterate segment indices in order.
 *===========================================================================*/

/**
 * Advance to the next segment in the current phase or transition to next phase.
 * Returns true if a new segment was found, false if exhausted.
 */
static bool advance_to_next_segment(tl_pagespan_iter_t* it) {
    TL_ASSERT(it != NULL);

    const tl_manifest_t* m = it->manifest;

    for (;;) {
        switch (it->phase) {
        case PHASE_L1:
            /* Check if L1 is enabled */
            if (!(it->flags & TL_PAGESPAN_INCLUDE_L1)) {
                it->phase = PHASE_L0;
                it->seg_idx = 0;
                continue;
            }

            /* Try next L1 segment */
            bool early_stop = false;
            size_t l1_count = tl_manifest_l1_count(m);
            while (it->seg_idx < l1_count) {
                const tl_segment_t* seg = tl_manifest_l1_get(m, it->seg_idx);
                /*
                 * Early terminate L1 scan for bounded ranges.
                 *
                 * Correctness proof: L1 segments have strictly increasing min_ts.
                 * Invariants: (1) L1 sorted by window_start
                 *             (2) Non-overlapping: window_start[i] >= window_end[i-1]
                 *             (3) Records in bounds: min_ts >= window_start (H-12)
                 * Chain: min_ts[i] >= window_start[i] >= window_end[i-1] > max_ts[i-1]
                 *
                 * Therefore if min_ts >= t2, all later segments also have min_ts >= t2.
                 */
                if (seg->min_ts >= it->t2) {
                    early_stop = true;
                    break;
                }
                it->seg_idx++;

                if (init_segment_cursor(it, seg)) {
                    return true;
                }
            }

            /* L1 exhausted, move to L0 */
            if (early_stop || it->seg_idx >= l1_count) {
                it->phase = PHASE_L0;
                it->seg_idx = 0;
            }
            break;

        case PHASE_L0:
            /* Check if L0 is enabled */
            if (!(it->flags & TL_PAGESPAN_INCLUDE_L0)) {
                it->phase = PHASE_DONE;
                return false;
            }

            /* Try next L0 segment */
            while (it->seg_idx < tl_manifest_l0_count(m)) {
                const tl_segment_t* seg = tl_manifest_l0_get(m, it->seg_idx);
                it->seg_idx++;

                if (init_segment_cursor(it, seg)) {
                    return true;
                }
            }

            /* L0 exhausted */
            it->phase = PHASE_DONE;
            return false;

        case PHASE_DONE:
            return false;
        }
    }
}

/*===========================================================================
 * Iterator API Implementation
 *===========================================================================*/

tl_status_t tl_pagespan_iter_open(
    tl_timelog_t* tl,
    tl_ts_t t1,
    tl_ts_t t2,
    uint32_t flags,
    const tl_pagespan_owner_hooks_t* hooks,
    tl_pagespan_iter_t** out)
{
    /* Step 1: Validate required args */
    if (tl == NULL || out == NULL) {
        return TL_EINVAL;
    }

    *out = NULL;

    /* Step 2: Normalize flags (0 -> DEFAULT) */
    if (flags == 0) {
        flags = TL_PAGESPAN_DEFAULT;
    }

    /* Step 3: Validate B4 flag requirements */
    /* SEGMENTS_ONLY is required */
    if (!(flags & TL_PAGESPAN_SEGMENTS_ONLY)) {
        return TL_EINVAL;
    }

    /* VISIBLE_ONLY is reserved (return EINVAL if set) */
    if (flags & TL_PAGESPAN_VISIBLE_ONLY) {
        return TL_EINVAL;
    }

    /* Verify timelog is open */
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    /* Get allocator from timelog */
    tl_alloc_ctx_t* alloc = &tl->alloc;

    /* Step 4: Detect empty range (t1 >= t2) */
    bool empty_range = tl_range_is_empty(t1, t2, false);

    /*
     * Step 5: Acquire snapshot - ALWAYS, even for empty range.
     *
     * RATIONALE (hook symmetry for bindings):
     * Bindings call pins_enter() before iter_open() and rely on the release
     * hook to call pins_exit(). If we skip owner creation for empty ranges,
     * the hook never runs and pins leak. Always creating an owner ensures
     * symmetric lifecycle: if iter_open succeeds, the hook WILL be called
     * when all views are released and the iterator is closed.
     */
    tl_snapshot_t* snap = NULL;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    if (st != TL_OK) {
        return st;
    }

    /* Step 6: Create owner (refcnt=1, holds snapshot and hooks) */
    tl_pagespan_owner_t* owner = NULL;
    st = owner_create(snap, alloc, hooks, &owner);
    if (st != TL_OK) {
        tl_snapshot_release(snap);
        return st;
    }

    /* Test hook: force iterator allocation failure after owner creation */
#ifdef TL_TEST_HOOKS
    if (tl_test_pagespan_fail_iter_alloc > 0) {
        tl_test_pagespan_fail_iter_alloc--;
        tl_pagespan_owner_decref(owner);
        return TL_ENOMEM;
    }
#endif

    /* Step 7: Create iterator */
    tl_pagespan_iter_t* it = tl__malloc(alloc, sizeof(tl_pagespan_iter_t));
    if (it == NULL) {
        /* Owner has refcnt=1 from owner_create; decref triggers destroy */
        tl_pagespan_owner_decref(owner);
        return TL_ENOMEM;
    }

    memset(it, 0, sizeof(*it));
    it->owner = owner;
    it->alloc = alloc;
    it->t1 = t1;
    it->t2 = t2;
    it->flags = flags;
    it->closed = false;
    it->manifest = tl_snapshot_manifest(snap);

    if (empty_range) {
        /* Empty range: go directly to PHASE_DONE, first next() returns EOF */
        it->phase = PHASE_DONE;
    } else {
        /* Normal case: setup for iteration */
        if (flags & TL_PAGESPAN_INCLUDE_L1) {
            it->phase = PHASE_L1;
        } else if (flags & TL_PAGESPAN_INCLUDE_L0) {
            it->phase = PHASE_L0;
        } else {
            /* Neither L1 nor L0 enabled - will return EOF immediately */
            it->phase = PHASE_DONE;
        }
    }
    it->seg_idx = 0;
    it->current_seg = NULL;

    /* Arm release hook only after successful open */
    owner->hook_armed = true;

    *out = it;
    return TL_OK;
}

tl_status_t tl_pagespan_iter_next(
    tl_pagespan_iter_t* it,
    tl_pagespan_view_t* out_view)
{
    /* Defensive NULL checks (match iter_open pattern) */
    if (it == NULL || out_view == NULL) {
        return TL_EINVAL;
    }

    /* Clear output */
    memset(out_view, 0, sizeof(*out_view));

    /* Check if closed or done */
    if (it->closed || it->phase == PHASE_DONE) {
        return TL_EOF;
    }

    /* Owner is always valid (created even for empty range for hook symmetry) */
    TL_ASSERT(it->owner != NULL);

    for (;;) {
        /* If no current segment, advance to next */
        if (it->current_seg == NULL) {
            if (!advance_to_next_segment(it)) {
                return TL_EOF;
            }
        }

        /* Scan pages in current segment */
        const tl_page_catalog_t* cat = tl_segment_catalog(it->current_seg);

        while (it->page_idx < it->page_end) {
            const tl_page_meta_t* meta = tl_page_catalog_get(cat, it->page_idx);
            const tl_page_t* page = meta->page;

            /*
             * Page flag validation (B4/V1 constraint):
             *
             * V1/B4 only supports TL_PAGE_FULLY_LIVE. Any other state indicates
             * corruption or a bug. We error out loudly rather than silently
             * skipping, which could hide data loss.
             *
             * If V2 introduces PARTIAL_DELETED pages with row bitmaps, this
             * code must be updated to handle visibility splitting.
             */
            if (page->flags != TL_PAGE_FULLY_LIVE) {
                /* Corruption or unsupported page state - internal error */
                return TL_EINTERNAL;
            }

            /* Compute row bounds within page */
            size_t row_start = tl_page_lower_bound(page, it->t1);
            size_t row_end = tl_page_lower_bound(page, it->t2);

            /* If no rows in range, skip page */
            if (row_start >= row_end) {
                it->page_idx++;
                continue;
            }

            /* Validate row bounds */
            TL_ASSERT(row_start < page->count);
            TL_ASSERT(row_end <= page->count);
            TL_ASSERT(row_end - row_start <= UINT32_MAX);

            /* Build view */
            uint32_t len = (uint32_t)(row_end - row_start);

            out_view->owner = it->owner;
            out_view->ts = &page->ts[row_start];
            out_view->h = &page->h[row_start];
            out_view->len = len;
            out_view->first_ts = page->ts[row_start];
            out_view->last_ts = page->ts[row_end - 1];

            /* Increment owner refcount for this view */
            tl_pagespan_owner_incref(it->owner);

            /* Advance to next page for next call */
            it->page_idx++;

            return TL_OK;
        }

        /* Current segment exhausted, move to next */
        it->current_seg = NULL;
    }
}

void tl_pagespan_iter_close(tl_pagespan_iter_t* it) {
    if (it == NULL || it->closed) {
        return;
    }

    it->closed = true;

    /*
     * CRITICAL: Free iterator BEFORE releasing owner reference (C-03 fix).
     *
     * The owner's release hook may Py_DECREF the timelog, which owns the
     * allocator. If owner decref triggers destroy -> hook -> allocator freed,
     * then calling tl__free(alloc, it) would be use-after-free.
     *
     * Correct order:
     * 1. Cache owner pointer
     * 2. Free iterator using allocator (while allocator is still valid)
     * 3. Release owner reference (may trigger destroy and hook)
     *
     * This mirrors the pattern in owner_destroy() which frees the owner
     * struct before calling the release hook.
     */
    tl_pagespan_owner_t* owner = it->owner;
    tl_alloc_ctx_t* alloc = it->alloc;

    /* Step 1: Free iterator struct while allocator is valid */
    tl__free(alloc, it);

    /* Step 2: Release owner reference (may trigger destroy and hook) */
    if (owner != NULL) {
        tl_pagespan_owner_decref(owner);
    }
}

/------------------------------------------------------------------------------/
/*   END OF: tl_pagespan_iter.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_plan.c
/*   FROM: query/
/*
/******************************************************************************/
#include "tl_plan.h"
#include "../internal/tl_range.h"
#include "../internal/tl_intervals.h"
#include "../storage/tl_manifest.h"
#include <string.h>
#include <stdlib.h>

/*===========================================================================
 * Constants
 *===========================================================================*/

/* Initial capacity for source array */
#define TL_PLAN_INIT_SOURCES 8

/* Initial capacity for tombstone array */
#define TL_PLAN_INIT_TOMBS 16

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Ensure source array has capacity for one more entry.
 */
static tl_status_t ensure_source_capacity(tl_plan_t* plan) {
    if (plan->source_count < plan->source_capacity) {
        return TL_OK;
    }

    size_t new_cap;
    if (plan->source_capacity == 0) {
        new_cap = TL_PLAN_INIT_SOURCES;
    } else {
        /* Overflow guard for capacity doubling */
        if (plan->source_capacity > SIZE_MAX / 2) {
            return TL_ENOMEM;
        }
        new_cap = plan->source_capacity * 2;
    }

    /* Overflow guard for allocation size */
    if (new_cap > SIZE_MAX / sizeof(tl_iter_source_t)) {
        return TL_ENOMEM;
    }

    tl_iter_source_t* new_arr = tl__malloc(plan->alloc,
                                            new_cap * sizeof(tl_iter_source_t));
    if (new_arr == NULL) {
        return TL_ENOMEM;
    }

    if (plan->sources != NULL) {
        memcpy(new_arr, plan->sources,
               plan->source_count * sizeof(tl_iter_source_t));
        tl__free(plan->alloc, plan->sources);
    }

    plan->sources = new_arr;
    plan->source_capacity = new_cap;
    return TL_OK;
}

/**
 * Ensure tombstone array has capacity for more entries.
 */
static tl_status_t ensure_tomb_capacity(tl_plan_t* plan, size_t additional) {
    /* Overflow guard for addition */
    if (additional > SIZE_MAX - plan->tomb_count) {
        return TL_ENOMEM;
    }
    size_t needed = plan->tomb_count + additional;
    if (needed <= plan->tomb_capacity) {
        return TL_OK;
    }

    size_t new_cap = (plan->tomb_capacity == 0)
                         ? TL_PLAN_INIT_TOMBS
                         : plan->tomb_capacity;
    while (new_cap < needed) {
        /* Overflow guard for capacity doubling */
        if (new_cap > SIZE_MAX / 2) {
            return TL_ENOMEM;
        }
        new_cap *= 2;
    }

    /* Overflow guard for allocation size */
    if (new_cap > SIZE_MAX / sizeof(tl_interval_t)) {
        return TL_ENOMEM;
    }

    tl_interval_t* new_arr = tl__malloc(plan->alloc,
                                         new_cap * sizeof(tl_interval_t));
    if (new_arr == NULL) {
        return TL_ENOMEM;
    }

    if (plan->tombstones != NULL) {
        memcpy(new_arr, plan->tombstones,
               plan->tomb_count * sizeof(tl_interval_t));
        tl__free(plan->alloc, plan->tombstones);
    }

    plan->tombstones = new_arr;
    plan->tomb_capacity = new_cap;
    return TL_OK;
}

/**
 * Add a segment source to the plan.
 */
static tl_status_t add_segment_source(tl_plan_t* plan,
                                       const tl_segment_t* seg,
                                       uint32_t priority) {
    tl_status_t st = ensure_source_capacity(plan);
    if (st != TL_OK) {
        return st;
    }

    tl_iter_source_t* src = &plan->sources[plan->source_count];
    src->kind = TL_ITER_SEGMENT;
    src->priority = priority;

    tl_segment_iter_init(&src->iter.segment, seg,
                         plan->t1, plan->t2, plan->t2_unbounded);

    /* Only add if not immediately exhausted */
    if (!tl_segment_iter_done(&src->iter.segment)) {
        plan->source_count++;
    }

    return TL_OK;
}

/**
 * Add a memrun source to the plan.
 */
static tl_status_t add_memrun_source(tl_plan_t* plan,
                                      const tl_memrun_t* mr,
                                      uint32_t priority) {
    tl_status_t st = ensure_source_capacity(plan);
    if (st != TL_OK) {
        return st;
    }

    tl_iter_source_t* src = &plan->sources[plan->source_count];
    src->kind = TL_ITER_MEMRUN;
    src->priority = priority;

    tl_status_t init_st = tl_memrun_iter_init(&src->iter.memrun, mr,
                                              plan->t1, plan->t2, plan->t2_unbounded,
                                              plan->alloc);
    if (init_st != TL_OK) {
        tl_memrun_iter_destroy(&src->iter.memrun);
        return init_st;
    }

    /* Only add if not immediately exhausted */
    if (!tl_memrun_iter_done(&src->iter.memrun)) {
        plan->source_count++;
    } else {
        tl_memrun_iter_destroy(&src->iter.memrun);
    }

    return TL_OK;
}

/**
 * Add the active memview source to the plan.
 */
static tl_status_t add_active_source(tl_plan_t* plan,
                                      const tl_memview_t* mv) {
    tl_status_t st = ensure_source_capacity(plan);
    if (st != TL_OK) {
        return st;
    }

    tl_iter_source_t* src = &plan->sources[plan->source_count];
    src->kind = TL_ITER_ACTIVE;
    src->priority = UINT32_MAX;  /* Active is always highest priority */

    tl_status_t init_st = tl_active_iter_init(&src->iter.active, mv,
                                              plan->t1, plan->t2, plan->t2_unbounded,
                                              plan->alloc);
    if (init_st != TL_OK) {
        tl_active_iter_destroy(&src->iter.active);
        return init_st;
    }

    /* Only add if not immediately exhausted */
    if (!tl_active_iter_done(&src->iter.active)) {
        plan->source_count++;
    } else {
        tl_active_iter_destroy(&src->iter.active);
    }

    return TL_OK;
}

/**
 * Clip a single interval's lower bound to t1.
 * Modifies interval in place, returns true if interval is still valid.
 */
static bool clip_interval_lower(tl_interval_t* interval, tl_ts_t t1) {
    /* If bounded and ends at or before t1, remove it */
    if (!interval->end_unbounded && interval->end <= t1) {
        return false;
    }

    /* Clip start to t1 if needed */
    if (interval->start < t1) {
        interval->start = t1;
    }

    return true;
}

/**
 * Add tombstone intervals from a segment to the plan.
 * Clips intervals to [t1, ...) range.
 */
static tl_status_t add_segment_tombstones(tl_plan_t* plan,
                                           const tl_segment_t* seg) {
    tl_intervals_imm_t tombs = tl_segment_tombstones_imm(seg);
    if (tombs.len == 0) {
        return TL_OK;
    }

    tl_status_t st = ensure_tomb_capacity(plan, tombs.len);
    if (st != TL_OK) {
        return st;
    }

    for (size_t i = 0; i < tombs.len; i++) {
        tl_interval_t interval = tombs.data[i];

        /* Skip if interval doesn't overlap query range */
        tl_ts_t int_max = interval.end_unbounded ? TL_TS_MAX : interval.end - 1;
        if (!tl_range_overlaps(interval.start, int_max,
                               plan->t1, plan->t2, plan->t2_unbounded)) {
            continue;
        }

        /* Clip to lower bound and add if still valid */
        if (clip_interval_lower(&interval, plan->t1)) {
            plan->tombstones[plan->tomb_count++] = interval;
        }
    }

    return TL_OK;
}

/**
 * Add tombstone intervals from a memrun to the plan.
 */
static tl_status_t add_memrun_tombstones(tl_plan_t* plan,
                                          const tl_memrun_t* mr) {
    size_t tomb_count = tl_memrun_tombs_len(mr);
    if (tomb_count == 0) {
        return TL_OK;
    }

    tl_status_t st = ensure_tomb_capacity(plan, tomb_count);
    if (st != TL_OK) {
        return st;
    }

    const tl_interval_t* tombs = tl_memrun_tombs_data(mr);

    for (size_t i = 0; i < tomb_count; i++) {
        tl_interval_t interval = tombs[i];

        /* Skip if interval doesn't overlap query range */
        tl_ts_t int_max = interval.end_unbounded ? TL_TS_MAX : interval.end - 1;
        if (!tl_range_overlaps(interval.start, int_max,
                               plan->t1, plan->t2, plan->t2_unbounded)) {
            continue;
        }

        /* Clip to lower bound and add if still valid */
        if (clip_interval_lower(&interval, plan->t1)) {
            plan->tombstones[plan->tomb_count++] = interval;
        }
    }

    return TL_OK;
}

/**
 * Add tombstone intervals from active memview to the plan.
 */
static tl_status_t add_active_tombstones(tl_plan_t* plan,
                                          const tl_memview_t* mv) {
    size_t tomb_count = tl_memview_tomb_len(mv);
    if (tomb_count == 0) {
        return TL_OK;
    }

    tl_status_t st = ensure_tomb_capacity(plan, tomb_count);
    if (st != TL_OK) {
        return st;
    }

    const tl_interval_t* tombs = tl_memview_tomb_data(mv);

    for (size_t i = 0; i < tomb_count; i++) {
        tl_interval_t interval = tombs[i];

        /* Skip if interval doesn't overlap query range */
        tl_ts_t int_max = interval.end_unbounded ? TL_TS_MAX : interval.end - 1;
        if (!tl_range_overlaps(interval.start, int_max,
                               plan->t1, plan->t2, plan->t2_unbounded)) {
            continue;
        }

        /* Clip to lower bound and add if still valid */
        if (clip_interval_lower(&interval, plan->t1)) {
            plan->tombstones[plan->tomb_count++] = interval;
        }
    }

    return TL_OK;
}

/**
 * Compare intervals by start timestamp for sorting.
 *
 * M-16 fix: Add secondary/tertiary comparisons for qsort stability.
 * Primary: start timestamp (ascending)
 * Secondary: end_unbounded (bounded < unbounded)
 * Tertiary: end (ascending, for bounded intervals)
 *
 * This ensures deterministic ordering even when intervals have equal starts.
 */
static int tomb_cmp(const void* a, const void* b) {
    const tl_interval_t* ia = (const tl_interval_t*)a;
    const tl_interval_t* ib = (const tl_interval_t*)b;

    /* Primary: by start timestamp */
    if (ia->start < ib->start) return -1;
    if (ia->start > ib->start) return 1;

    /* Secondary: bounded < unbounded */
    if (!ia->end_unbounded && ib->end_unbounded) return -1;
    if (ia->end_unbounded && !ib->end_unbounded) return 1;

    /* Tertiary: by end for bounded intervals */
    if (!ia->end_unbounded && !ib->end_unbounded) {
        if (ia->end < ib->end) return -1;
        if (ia->end > ib->end) return 1;
    }

    return 0;
}

/**
 * Sort tombstone intervals by start timestamp.
 */
static void sort_tombstones(tl_plan_t* plan) {
    if (plan->tomb_count <= 1) {
        return;
    }

    qsort(plan->tombstones, plan->tomb_count,
          sizeof(tl_interval_t), tomb_cmp);
}

/**
 * Clip tombstone intervals to upper bound (t2) for bounded queries.
 *
 * For bounded queries [t1, t2):
 * - If tombstone end > t2, clip end to t2
 * - If tombstone is unbounded [x, +inf), it becomes [max(x, t1), t2)
 * - Removes intervals that start at or past t2
 *
 * For unbounded queries, this is a no-op.
 *
 * Precondition: tombstones are already clipped to lower bound.
 */
static void clip_tombstones_upper(tl_plan_t* plan) {
    if (plan->t2_unbounded || plan->tomb_count == 0) {
        return;  /* Nothing to clip for unbounded queries */
    }

    size_t write = 0;
    for (size_t read = 0; read < plan->tomb_count; read++) {
        tl_interval_t* interval = &plan->tombstones[read];

        /* Remove intervals that start at or past t2 */
        if (interval->start >= plan->t2) {
            continue;
        }

        /* Clip unbounded intervals to t2 */
        if (interval->end_unbounded) {
            interval->end_unbounded = false;
            interval->end = plan->t2;
        } else if (interval->end > plan->t2) {
            /* Clip bounded intervals that extend past t2 */
            interval->end = plan->t2;
        }

        /* Copy to output position if needed */
        if (write != read) {
            plan->tombstones[write] = *interval;
        }
        write++;
    }

    plan->tomb_count = write;
}

/**
 * Coalesce overlapping/adjacent tombstone intervals in-place.
 *
 * Precondition: tombstones are sorted by start timestamp.
 * Result: disjoint intervals with gaps between them.
 *
 * Algorithm (LLD Section 4.4):
 * - Merge intervals that overlap or are adjacent
 * - Unbounded interval absorbs all subsequent intervals
 */
static void coalesce_tombstones(tl_plan_t* plan) {
    if (plan->tomb_count <= 1) {
        return;
    }

    size_t write = 0;  /* Write position for coalesced output */

    for (size_t read = 1; read < plan->tomb_count; read++) {
        tl_interval_t* cur = &plan->tombstones[write];
        const tl_interval_t* next = &plan->tombstones[read];

        /* If current is unbounded, it absorbs everything */
        if (cur->end_unbounded) {
            break;
        }

        /* Check if next overlaps or is adjacent to current:
         * Overlap: next.start < cur.end
         * Adjacent: next.start == cur.end
         * Combined: next.start <= cur.end */
        if (next->start <= cur->end) {
            /* Merge: extend current to cover next */
            if (next->end_unbounded) {
                cur->end_unbounded = true;
                /* No need to update end - unbounded means infinite */
            } else if (next->end > cur->end) {
                cur->end = next->end;
            }
            /* Continue to potentially merge more */
        } else {
            /* Gap between intervals - emit current, start new */
            write++;
            plan->tombstones[write] = *next;
        }
    }

    /* Update count to number of coalesced intervals */
    plan->tomb_count = write + 1;
}

/*===========================================================================
 * Lifecycle
 *
 * Allocation and cleanup semantics:
 * - tl_plan_build() initializes plan with memset(0) first, so partial
 *   allocations on failure leave plan in a safe state (NULL pointers)
 * - On any allocation failure, build() calls tl_plan_destroy() internally
 *   before returning error, so caller does NOT need to clean up on failure
 * - tl_plan_destroy() safely handles NULL arrays (checks before free)
 * - Caller MUST call tl_plan_destroy() on success to free sources/tombstones
 *===========================================================================*/

tl_status_t tl_plan_build(tl_plan_t* plan,
                           tl_snapshot_t* snapshot,
                           tl_alloc_ctx_t* alloc,
                           tl_ts_t t1, tl_ts_t t2,
                           bool t2_unbounded) {
    TL_ASSERT(plan != NULL);
    TL_ASSERT(snapshot != NULL);
    TL_ASSERT(alloc != NULL);

    memset(plan, 0, sizeof(*plan));
    plan->alloc = alloc;
    plan->t1 = t1;
    plan->t2 = t2;
    plan->t2_unbounded = t2_unbounded;
    plan->snapshot = snapshot;

    tl_status_t st;
    const tl_manifest_t* manifest = snapshot->manifest;
    const tl_memview_t* mv = tl_snapshot_memview(snapshot);

    /*
     * Check if range is empty (bounded only).
     * Unbounded ranges are never empty.
     */
    if (tl_range_is_empty(t1, t2, t2_unbounded)) {
        return TL_OK;
    }

    /*
     * Step 1: Add L1 segment sources.
     * Use binary search to find first potentially overlapping segment.
     */
    size_t l1_start = tl_manifest_l1_find_first_overlap(manifest, t1);
    for (size_t i = l1_start; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);

        /* Stop early if segment starts past range end */
        if (!t2_unbounded && seg->min_ts >= t2) {
            plan->segments_pruned += (tl_manifest_l1_count(manifest) - i);
            break;
        }

        /* Check overlap */
        if (!tl_range_overlaps(seg->min_ts, seg->max_ts, t1, t2, t2_unbounded)) {
            plan->segments_pruned++;
            continue;
        }

        st = add_segment_source(plan, seg, seg->generation);
        if (st != TL_OK) goto fail;

        /* Defensive: include L1 tombstones if present (should be empty in V1). */
        st = add_segment_tombstones(plan, seg);
        if (st != TL_OK) goto fail;
    }

    /* Count pruned segments from before l1_start */
    plan->segments_pruned += l1_start;

    /*
     * Step 2: Add L0 segment sources.
     * L0 segments may overlap and are in flush order.
     * Assign priorities based on position (later = higher priority).
     */
    for (size_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);

        /* Check overlap using record/tombstone bounds independently. */
        bool overlaps = false;
        if (tl_segment_has_records(seg)) {
            overlaps |= tl_range_overlaps(seg->record_min_ts, seg->record_max_ts,
                                          t1, t2, t2_unbounded);
        }
        if (tl_segment_has_tombstones(seg)) {
            overlaps |= tl_range_overlaps(seg->tomb_min_ts, seg->tomb_max_ts,
                                          t1, t2, t2_unbounded);
        }
        if (!overlaps) {
            plan->segments_pruned++;
            continue;
        }

        /* L0 priority: use generation (newer flushes have higher gen) */
        st = add_segment_source(plan, seg, seg->generation);
        if (st != TL_OK) goto fail;

        st = add_segment_tombstones(plan, seg);
        if (st != TL_OK) goto fail;
    }

    /*
     * Step 3: Add sealed memrun sources.
     * Memruns are in FIFO order (oldest first).
     * Assign priorities: higher index = newer = higher priority.
     */
    size_t sealed_len = tl_memview_sealed_len(mv);
    for (size_t i = 0; i < sealed_len; i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(mv, i);

        /* Check if memrun has any data */
        if (!tl_memrun_has_records(mr) && !tl_memrun_has_tombstones(mr)) {
            plan->memruns_pruned++;
            continue;
        }

        /* Check overlap */
        if (!tl_range_overlaps(tl_memrun_min_ts(mr), tl_memrun_max_ts(mr),
                               t1, t2, t2_unbounded)) {
            plan->memruns_pruned++;
            continue;
        }

        /* Priority for memruns: base at segment max gen + index */
        uint32_t base_priority = 0;
        if (tl_manifest_l0_count(manifest) > 0) {
            base_priority = tl_manifest_l0_get(manifest,
                                tl_manifest_l0_count(manifest) - 1)->generation + 1;
        }

        /*
         * M-15 fix: Overflow-safe priority assignment with saturation.
         * If base_priority + i would exceed UINT32_MAX, saturate to UINT32_MAX.
         * This preserves relative ordering within the valid range.
         */
        uint32_t priority;
        if (base_priority > UINT32_MAX - (uint32_t)i) {
            priority = UINT32_MAX;  /* Saturate on overflow */
        } else {
            priority = base_priority + (uint32_t)i;
        }

        st = add_memrun_source(plan, mr, priority);
        if (st != TL_OK) goto fail;

        st = add_memrun_tombstones(plan, mr);
        if (st != TL_OK) goto fail;
    }

    /*
     * Step 4: Add active memview source.
     * Active data is the newest and has highest priority.
     */
    if (mv->has_data && tl_memview_overlaps(mv, t1, t2, t2_unbounded)) {
        size_t active_run_len = tl_memview_run_len(mv);
        size_t active_ooo_len = tl_memview_ooo_total_len(mv);

        if (active_run_len > 0 || active_ooo_len > 0) {
            st = add_active_source(plan, mv);
            if (st != TL_OK) goto fail;
        }

        st = add_active_tombstones(plan, mv);
        if (st != TL_OK) goto fail;
    }

    /*
     * Step 5: Sort, coalesce, and clip tombstones (LLD Section 4.4).
     * - Sort by start timestamp
     * - Merge overlapping/adjacent intervals
     * - Clip to upper bound [t1, t2) for bounded queries
     * This ensures efficient filtering during merge.
     */
    sort_tombstones(plan);
    coalesce_tombstones(plan);
    clip_tombstones_upper(plan);

    return TL_OK;

fail:
    tl_plan_destroy(plan);
    return st;
}

void tl_plan_destroy(tl_plan_t* plan) {
    if (plan == NULL) {
        return;
    }

    if (plan->sources != NULL) {
        for (size_t i = 0; i < plan->source_count; i++) {
            tl_iter_source_t* src = &plan->sources[i];
            if (src->kind == TL_ITER_ACTIVE) {
                tl_active_iter_destroy(&src->iter.active);
            } else if (src->kind == TL_ITER_MEMRUN) {
                tl_memrun_iter_destroy(&src->iter.memrun);
            }
        }
        tl__free(plan->alloc, plan->sources);
        plan->sources = NULL;
    }
    plan->source_count = 0;
    plan->source_capacity = 0;

    if (plan->tombstones != NULL) {
        tl__free(plan->alloc, plan->tombstones);
        plan->tombstones = NULL;
    }
    plan->tomb_count = 0;
    plan->tomb_capacity = 0;
}

/------------------------------------------------------------------------------/
/*   END OF: tl_plan.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_point.c
/*   FROM: query/
/*
/******************************************************************************/
#include "tl_point.h"
#include "tl_snapshot.h"
#include "../internal/tl_intervals.h"
#include "../internal/tl_search.h"
#include "../storage/tl_manifest.h"
#include "../storage/tl_segment.h"
#include "../storage/tl_page.h"
#include "../delta/tl_memview.h"
#include "../delta/tl_memrun.h"
#include <string.h>

/*===========================================================================
 * Constants
 *===========================================================================*/

#define TL_POINT_INIT_CAP 8

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Ensure result has capacity for additional records.
 */
static tl_status_t ensure_capacity(tl_point_result_t* result, size_t additional) {
    size_t needed = result->count + additional;
    if (needed <= result->capacity) {
        return TL_OK;
    }

    size_t new_cap = (result->capacity == 0) ? TL_POINT_INIT_CAP : result->capacity;
    while (new_cap < needed) {
        /* Overflow guard */
        if (new_cap > SIZE_MAX / 2) {
            return TL_ENOMEM;
        }
        new_cap *= 2;
    }

    tl_record_t* new_arr = tl__mallocarray(result->alloc, new_cap, sizeof(tl_record_t));
    if (new_arr == NULL) {
        return TL_ENOMEM;
    }

    if (result->records != NULL) {
        memcpy(new_arr, result->records, result->count * sizeof(tl_record_t));
        tl__free(result->alloc, result->records);
    }

    result->records = new_arr;
    result->capacity = new_cap;
    return TL_OK;
}

/**
 * Add a record to the result.
 */
static tl_status_t add_record(tl_point_result_t* result, tl_ts_t ts, tl_handle_t handle) {
    tl_status_t st = ensure_capacity(result, 1);
    if (st != TL_OK) {
        return st;
    }

    result->records[result->count].ts = ts;
    result->records[result->count].handle = handle;
    result->count++;
    return TL_OK;
}


/**
 * Collect all records with exact timestamp from a sorted array.
 */
static tl_status_t collect_from_sorted(tl_point_result_t* result,
                                        const tl_record_t* data, size_t len,
                                        tl_ts_t ts) {
    if (len == 0 || data == NULL) {
        return TL_OK;
    }

    /* Binary search to find first occurrence */
    size_t idx = tl_record_lower_bound(data, len, ts);

    /* Collect all matching records */
    while (idx < len && data[idx].ts == ts) {
        tl_status_t st = add_record(result, data[idx].ts, data[idx].handle);
        if (st != TL_OK) {
            return st;
        }
        idx++;
    }

    return TL_OK;
}

/**
 * Collect matching records from a page.
 */
static tl_status_t collect_from_page(tl_point_result_t* result,
                                      const tl_page_t* page,
                                      tl_ts_t ts) {
    /* Binary search to find first occurrence */
    size_t idx = tl_page_lower_bound(page, ts);

    /* Collect all matching records */
    tl_record_t rec;
    while (idx < page->count) {
        if (tl_page_row_is_deleted(page, idx)) {
            idx++;
            continue;
        }

        tl_page_get_record(page, idx, &rec);
        if (rec.ts != ts) {
            break;
        }
        tl_status_t st = add_record(result, rec.ts, rec.handle);
        if (st != TL_OK) {
            return st;
        }
        idx++;
    }

    return TL_OK;
}

/**
 * Collect matching records from a segment.
 */
static tl_status_t collect_from_segment(tl_point_result_t* result,
                                         const tl_segment_t* seg,
                                         tl_ts_t ts) {
    /* Check if segment contains ts */
    if (ts < seg->min_ts || ts > seg->max_ts) {
        return TL_OK;
    }

    /* Handle tombstone-only segments */
    if (seg->page_count == 0) {
        return TL_OK;
    }

    const tl_page_catalog_t* cat = tl_segment_catalog(seg);

    /* Binary search catalog to find pages that might contain ts */
    size_t page_idx = tl_page_catalog_find_first_ge(cat, ts);

    /* Search pages that could contain ts */
    while (page_idx < tl_page_catalog_count(cat)) {
        const tl_page_meta_t* meta = tl_page_catalog_get(cat, page_idx);

        /* Stop if page starts after ts */
        if (meta->min_ts > ts) {
            break;
        }

        /* Skip if page ends before ts (shouldn't happen after find_first_ge) */
        if (meta->max_ts < ts) {
            page_idx++;
            continue;
        }

        /* Skip fully deleted pages (bitmask test for future flag compatibility) */
        if ((meta->flags & TL_PAGE_FULLY_DELETED) != 0) {
            page_idx++;
            continue;
        }

        /* Collect from this page */
        tl_status_t st = collect_from_page(result, meta->page, ts);
        if (st != TL_OK) {
            return st;
        }

        page_idx++;
    }

    return TL_OK;
}

/**
 * Collect matching records from a memrun.
 */
static tl_status_t collect_from_memrun(tl_point_result_t* result,
                                        const tl_memrun_t* mr,
                                        tl_ts_t ts) {
    /* Check if memrun contains ts */
    if (!tl_memrun_has_records(mr)) {
        return TL_OK;
    }

    tl_ts_t min_ts = tl_memrun_min_ts(mr);
    tl_ts_t max_ts = tl_memrun_max_ts(mr);
    if (ts < min_ts || ts > max_ts) {
        return TL_OK;
    }

    tl_status_t st;

    /* Collect from run (sorted) */
    st = collect_from_sorted(result,
                             tl_memrun_run_data(mr),
                             tl_memrun_run_len(mr),
                             ts);
    if (st != TL_OK) {
        return st;
    }

    /* Collect from OOO runs (sorted) */
    size_t run_count = tl_memrun_ooo_run_count(mr);
    for (size_t i = 0; i < run_count; i++) {
        const tl_ooorun_t* run = tl_memrun_ooo_run_at(mr, i);
        if (run == NULL || run->len == 0) {
            continue;
        }
        st = collect_from_sorted(result, run->records, run->len, ts);
        if (st != TL_OK) {
            return st;
        }
    }

    return TL_OK;
}

/**
 * Collect matching records from memview active buffers.
 */
static tl_status_t collect_from_memview(tl_point_result_t* result,
                                         const tl_memview_t* mv,
                                         tl_ts_t ts) {
    tl_status_t st;

    /* Collect from active_run (sorted) */
    st = collect_from_sorted(result,
                             tl_memview_run_data(mv),
                             tl_memview_run_len(mv),
                             ts);
    if (st != TL_OK) {
        return st;
    }

    /* Collect from active OOO head (sorted) */
    st = collect_from_sorted(result,
                             tl_memview_ooo_head_data(mv),
                             tl_memview_ooo_head_len(mv),
                             ts);
    if (st != TL_OK) {
        return st;
    }

    /* Collect from active OOO runs (sorted) */
    const tl_ooorunset_t* runs = tl_memview_ooo_runs(mv);
    if (runs != NULL) {
        for (size_t i = 0; i < runs->count; i++) {
            const tl_ooorun_t* run = runs->runs[i];
            if (run == NULL || run->len == 0) {
                continue;
            }
            st = collect_from_sorted(result, run->records, run->len, ts);
            if (st != TL_OK) {
                return st;
            }
        }
    }

    return TL_OK;
}

/**
 * Check if ts is covered by any tombstone in the snapshot.
 *
 * M-18 fix: Added bounds pruning before scanning tombstones.
 * If ts is outside a source's bounds, skip tombstone check entirely.
 * This avoids O(log T) binary search in tl_intervals_imm_contains
 * when bounds make it impossible for the tombstone to cover ts.
 */
static bool is_deleted(const tl_snapshot_t* snap, tl_ts_t ts) {
    const tl_manifest_t* manifest = snap->manifest;
    const tl_memview_t* mv = tl_snapshot_memview(snap);

    /* Check memview tombstones (no bounds check - memview tombs cover full range) */
    tl_intervals_imm_t mv_tombs = tl_memview_tombs_imm(mv);
    if (tl_intervals_imm_contains(mv_tombs, ts)) {
        return true;
    }

    /* Check sealed memrun tombstones */
    for (size_t i = 0; i < tl_memview_sealed_len(mv); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(mv, i);

        /* M-18: Skip if ts outside memrun bounds */
        if (ts < tl_memrun_min_ts(mr) || ts > tl_memrun_max_ts(mr)) {
            continue;
        }

        tl_intervals_imm_t mr_tombs = tl_memrun_tombs_imm(mr);
        if (tl_intervals_imm_contains(mr_tombs, ts)) {
            return true;
        }
    }

    /* Check L0 segment tombstones */
    for (size_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);

        /* M-18: Skip if ts outside segment bounds */
        if (ts < seg->min_ts || ts > seg->max_ts) {
            continue;
        }

        tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
        if (tl_intervals_imm_contains(seg_tombs, ts)) {
            return true;
        }
    }

    /* Defensive: check L1 tombstones if present (should be empty in V1). */
    for (size_t i = 0; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);

        /* M-18: Skip if ts outside segment bounds */
        if (ts < seg->min_ts || ts > seg->max_ts) {
            continue;
        }

        tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
        if (tl_intervals_imm_contains(seg_tombs, ts)) {
            return true;
        }
    }

    return false;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_point_lookup(tl_point_result_t* result,
                             const tl_snapshot_t* snap,
                             tl_ts_t ts,
                             tl_alloc_ctx_t* alloc) {
    TL_ASSERT(result != NULL);
    TL_ASSERT(snap != NULL);
    TL_ASSERT(alloc != NULL);

    /* Initialize result */
    memset(result, 0, sizeof(*result));
    result->alloc = alloc;

    /* Fast path: no data in snapshot */
    if (!snap->has_data) {
        return TL_OK;
    }

    /* Step 1: Tombstone check first (LLD Section 8) */
    if (is_deleted(snap, ts)) {
        return TL_OK;  /* Deleted - return empty result */
    }

    tl_status_t st;
    const tl_manifest_t* manifest = snap->manifest;
    const tl_memview_t* mv = tl_snapshot_memview(snap);

    /* Step 2: L1 lookup (non-overlapping windows) */
    size_t l1_start = tl_manifest_l1_find_first_overlap(manifest, ts);
    for (size_t i = l1_start; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);

        /* L1 segments are sorted, stop if past ts */
        if (seg->min_ts > ts) {
            break;
        }

        st = collect_from_segment(result, seg, ts);
        if (st != TL_OK) {
            goto fail;
        }
    }

    /* Step 3: L0 lookup (overlapping segments) */
    for (size_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);

        st = collect_from_segment(result, seg, ts);
        if (st != TL_OK) {
            goto fail;
        }
    }

    /* Step 4: Memview lookup */

    /* Sealed memruns */
    for (size_t i = 0; i < tl_memview_sealed_len(mv); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(mv, i);

        st = collect_from_memrun(result, mr, ts);
        if (st != TL_OK) {
            goto fail;
        }
    }

    /* Active buffers */
    st = collect_from_memview(result, mv, ts);
    if (st != TL_OK) {
        goto fail;
    }

    return TL_OK;

fail:
    tl_point_result_destroy(result);
    return st;
}

void tl_point_result_destroy(tl_point_result_t* result) {
    if (result == NULL) {
        return;
    }

    if (result->records != NULL) {
        tl__free(result->alloc, result->records);
    }

    memset(result, 0, sizeof(*result));
}

/------------------------------------------------------------------------------/
/*   END OF: tl_point.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_segment_iter.c
/*   FROM: query/
/*
/******************************************************************************/
#include "tl_segment_iter.h"
#include "../internal/tl_range.h"
#include "tl_segment_range.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Initialize row bounds for current page.
 * Uses binary search to find the range of rows that overlap [t1, t2).
 */
static void init_page_bounds(tl_segment_iter_t* it) {
    const tl_page_catalog_t* cat = tl_segment_catalog(it->seg);
    const tl_page_meta_t* meta = tl_page_catalog_get(cat, it->page_idx);
    const tl_page_t* page = meta->page;

    /* Skip FULLY_DELETED pages (bitmask test for future flag compatibility) */
    if ((meta->flags & TL_PAGE_FULLY_DELETED) != 0) {
        it->row_idx = 0;
        it->row_end = 0;  /* Empty range, will advance to next page */
        return;
    }

    /* Binary search for row boundaries within this page */
    it->row_idx = tl_page_lower_bound(page, it->t1);

    if (it->t2_unbounded) {
        it->row_end = page->count;
    } else {
        it->row_end = tl_page_lower_bound(page, it->t2);
    }
}

/**
 * Advance to next page that has rows in range.
 * Returns true if found a valid page, false if exhausted.
 */
static bool advance_to_next_page(tl_segment_iter_t* it) {
    it->page_idx++;

    while (it->page_idx < it->page_end) {
        init_page_bounds(it);

        /* Check if this page has any rows in range */
        if (it->row_idx < it->row_end) {
            return true;
        }

        /* No rows in range, try next page */
        it->page_idx++;
    }

    /* Exhausted all pages */
    return false;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_segment_iter_init(tl_segment_iter_t* it,
                           const tl_segment_t* seg,
                           tl_ts_t t1, tl_ts_t t2,
                           bool t2_unbounded) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(seg != NULL);

    memset(it, 0, sizeof(*it));
    it->seg = seg;
    it->t1 = t1;
    it->t2 = t2;
    it->t2_unbounded = t2_unbounded;
    it->done = false;

    /*
     * Check segment bounds first (pruning).
     * Use tl_range_overlaps for correct unbounded handling.
     */
    if (!tl_range_overlaps(seg->min_ts, seg->max_ts, t1, t2, t2_unbounded)) {
        it->done = true;
        return;
    }

    /* Handle tombstone-only segments (no pages to iterate) */
    if (seg->page_count == 0) {
        it->done = true;
        return;
    }

    size_t first = 0;
    size_t last = 0;
    if (!tl_segment_page_range(seg, t1, t2, t2_unbounded, &first, &last)) {
        it->done = true;
        return;
    }

    it->page_idx = first;
    it->page_end = last;

    /* Initialize first page bounds */
    init_page_bounds(it);

    /* If first page has no rows in range, advance to next page */
    if (it->row_idx >= it->row_end) {
        if (!advance_to_next_page(it)) {
            it->done = true;
        }
    }
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_segment_iter_next(tl_segment_iter_t* it, tl_record_t* out) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return TL_EOF;
    }

    for (;;) {
        /* Ensure current page bounds are valid */
        if (it->row_idx >= it->row_end) {
            if (!advance_to_next_page(it)) {
                it->done = true;
                return TL_EOF;
            }
        }

        const tl_page_catalog_t* cat = tl_segment_catalog(it->seg);
        const tl_page_meta_t* meta = tl_page_catalog_get(cat, it->page_idx);
        const tl_page_t* page = meta->page;

        /* Skip deleted rows on PARTIAL_DELETED pages */
        if (tl_page_row_is_deleted(page, it->row_idx)) {
            it->row_idx++;
            continue;
        }

        /* Load current record */
        tl_record_t rec;
        tl_page_get_record(page, it->row_idx, &rec);

        /* Output the record if requested */
        if (out != NULL) {
            *out = rec;
        }

        /* Advance to next row */
        it->row_idx++;

        /* Check if we've exhausted the current page */
        if (it->row_idx >= it->row_end) {
            /* Try to advance to next page */
            if (!advance_to_next_page(it)) {
                it->done = true;
            }
        }

        return TL_OK;
    }
}

void tl_segment_iter_seek(tl_segment_iter_t* it, tl_ts_t target) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return;
    }

    /*
     * If target is before or at current position, do nothing.
     * We can only seek forward.
     */
    if (target <= it->t1) {
        return;
    }

    /*
     * Check if target is past the query range end.
     */
    if (!it->t2_unbounded && target >= it->t2) {
        it->done = true;
        return;
    }

    /*
     * Check if target is past the segment's max_ts.
     */
    if (target > it->seg->max_ts) {
        it->done = true;
        return;
    }

    /*
     * Save current position for monotonicity clamping.
     * Seek must NEVER go backwards - this is a critical invariant.
     */
    size_t old_page_idx = it->page_idx;
    size_t old_row_idx = it->row_idx;

    const tl_page_catalog_t* cat = tl_segment_catalog(it->seg);

    /*
     * Find the first page that might contain target.
     * This is the page with max_ts >= target.
     */
    size_t new_page_idx = tl_page_catalog_find_first_ge(cat, target);

    /* Make sure we don't go backwards or past the end */
    if (new_page_idx < it->page_idx) {
        new_page_idx = it->page_idx;
    }

    if (new_page_idx >= it->page_end) {
        it->done = true;
        return;
    }

    /* Update position */
    it->page_idx = new_page_idx;

    /* Reinitialize page bounds with new t1 = target */
    const tl_page_meta_t* meta = tl_page_catalog_get(cat, it->page_idx);
    const tl_page_t* page = meta->page;

    /* Skip FULLY_DELETED pages (bitmask test for future flag compatibility) */
    if ((meta->flags & TL_PAGE_FULLY_DELETED) != 0) {
        it->row_idx = 0;
        it->row_end = 0;
    } else {
        /* Binary search for row >= target */
        size_t new_row_idx = tl_page_lower_bound(page, target);

        /*
         * CRITICAL: Clamp row_idx to maintain monotonicity.
         * When staying on the same page, never go backwards.
         */
        if (it->page_idx == old_page_idx && new_row_idx < old_row_idx) {
            new_row_idx = old_row_idx;
        }

        it->row_idx = new_row_idx;

        if (it->t2_unbounded) {
            it->row_end = page->count;
        } else {
            it->row_end = tl_page_lower_bound(page, it->t2);
        }
    }

    /* If this page has no rows in range, advance to next page */
    if (it->row_idx >= it->row_end) {
        if (!advance_to_next_page(it)) {
            it->done = true;
        }
    }

}

/------------------------------------------------------------------------------/
/*   END OF: tl_segment_iter.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_snapshot.c
/*   FROM: query/
/*
/******************************************************************************/
#include "tl_snapshot.h"
#include "../internal/tl_timelog_internal.h"
#include "../internal/tl_locks.h"
#include "../internal/tl_range.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Compute global bounds from manifest and memview.
 */
static void snap_compute_bounds(tl_snapshot_t* snap) {
    snap->has_data = false;
    snap->min_ts = 0;
    snap->max_ts = 0;

    /* Bounds from manifest */
    const tl_manifest_t* m = snap->manifest;
    if (m->has_bounds) {
        snap->min_ts = m->min_ts;
        snap->max_ts = m->max_ts;
        snap->has_data = true;
    }

    /* Bounds from memview */
    const tl_memview_t* mv = tl_memview_shared_view(snap->memview);
    if (mv != NULL && mv->has_data) {
        if (!snap->has_data) {
            snap->min_ts = mv->min_ts;
            snap->max_ts = mv->max_ts;
            snap->has_data = true;
        } else {
            if (mv->min_ts < snap->min_ts) {
                snap->min_ts = mv->min_ts;
            }
            if (mv->max_ts > snap->max_ts) {
                snap->max_ts = mv->max_ts;
            }
        }
    }
}

/*===========================================================================
 * Debug Iterator Tracking
 *===========================================================================*/

#ifdef TL_DEBUG
void tl_snapshot_iter_created(tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    snap->iter_count++;
}

void tl_snapshot_iter_destroyed(tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(snap->iter_count > 0);
    snap->iter_count--;
}
#endif

/*===========================================================================
 * Snapshot Acquisition
 *===========================================================================*/

tl_status_t tl_snapshot_acquire_internal(struct tl_timelog* tl,
                                          tl_alloc_ctx_t* alloc,
                                          tl_snapshot_t** out) {
    TL_ASSERT(tl != NULL);
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    /* Allocate snapshot structure */
    tl_snapshot_t* snap = TL_NEW(alloc, tl_snapshot_t);
    if (snap == NULL) {
        return TL_ENOMEM;
    }

    /* Zero-initialize all fields for defensive safety */
    memset(snap, 0, sizeof(*snap));
    snap->alloc = alloc;

    /*
     * Snapshot consistency is guaranteed by writer_mu:
     * - Writers hold writer_mu during publish (manifest swap + memtable pop)
     * - Snapshots hold writer_mu during capture
     * Therefore, we do not need a seqlock retry loop here.
     */
    tl_manifest_t* manifest = NULL;
    tl_memview_shared_t* mv = NULL;
    bool used_cache = false;

    TL_LOCK_WRITER(tl);

    /* Acquire manifest reference under writer_mu to prevent UAF */
    manifest = tl_manifest_acquire(tl->manifest);

    /* Capture or reuse memview (locks memtable_mu internally) */
    uint64_t epoch = tl_memtable_epoch(&tl->memtable);
    if (tl->memview_cache != NULL && tl->memview_cache_epoch == epoch) {
        mv = tl_memview_shared_acquire(tl->memview_cache);
        used_cache = true;
    } else {
        tl_status_t st = tl_memview_shared_capture(&mv,
                                                    &tl->memtable,
                                                    &tl->memtable_mu,
                                                    alloc,
                                                    epoch);
        if (st != TL_OK) {
            tl_manifest_release(manifest);
            TL_UNLOCK_WRITER(tl);
            tl__free(alloc, snap);
            return st;
        }
    }

    TL_UNLOCK_WRITER(tl);

    /* Sort OOO head off writer_mu for fresh captures. */
    if (!used_cache) {
        tl_memview_sort_head(&mv->view);

        /* Update cache if epoch unchanged (two-phase capture). */
        TL_LOCK_WRITER(tl);
        if (tl_memtable_epoch(&tl->memtable) == epoch) {
            if (tl->memview_cache == NULL ||
                tl->memview_cache_epoch != epoch) {
                if (tl->memview_cache != NULL) {
                    tl_memview_shared_release(tl->memview_cache);
                }
                tl->memview_cache = tl_memview_shared_acquire(mv);
                tl->memview_cache_epoch = epoch;
            }
        }
        TL_UNLOCK_WRITER(tl);
    }

    snap->manifest = manifest;
    snap->memview = mv;

    /* Compute global bounds from manifest + memview */
    snap_compute_bounds(snap);

    snap->parent = tl;

#ifdef TL_DEBUG
    snap->iter_count = 0;
    /* Increment outstanding snapshot count for leak detection at close */
    tl_atomic_fetch_add_u32(&tl->snapshot_count, 1, TL_MO_RELAXED);
#endif

    *out = snap;
    return TL_OK;
}

void tl_snapshot_release_internal(tl_snapshot_t* snap) {
    if (snap == NULL) {
        return;
    }

#ifdef TL_DEBUG
    TL_ASSERT(snap->iter_count == 0 && "Outstanding iterators on snapshot release");
    /* Decrement outstanding snapshot count (cast away const for atomic update) */
    if (snap->parent != NULL) {
        tl_atomic_fetch_sub_u32(&((struct tl_timelog*)snap->parent)->snapshot_count, 1, TL_MO_RELAXED);
    }
#endif

    /* Release memview (shared, refcounted) */
    tl_memview_shared_release(snap->memview);

    /* Release manifest reference */
    if (snap->manifest != NULL) {
        tl_manifest_release(snap->manifest);
    }

    /* Free snapshot structure */
    tl__free(snap->alloc, snap);
}

/------------------------------------------------------------------------------/
/*   END OF: tl_snapshot.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_submerge.c
/*   FROM: query/
/*
/******************************************************************************/
#include "tl_submerge.h"
#include <string.h>

tl_status_t tl_submerge_init(tl_submerge_t* sm,
                              tl_alloc_ctx_t* alloc,
                              size_t src_count) {
    TL_ASSERT(sm != NULL);
    TL_ASSERT(alloc != NULL);

    memset(sm, 0, sizeof(*sm));
    sm->alloc = alloc;
    tl_heap_init(&sm->heap, alloc);

    if (src_count == 0) {
        return TL_OK;
    }

    if (src_count > SIZE_MAX / sizeof(tl_subsrc_t)) {
        return TL_EOVERFLOW;
    }

    sm->srcs = tl__malloc(alloc, src_count * sizeof(tl_subsrc_t));
    if (sm->srcs == NULL) {
        tl_heap_destroy(&sm->heap);
        return TL_ENOMEM;
    }

    memset(sm->srcs, 0, src_count * sizeof(tl_subsrc_t));
    sm->src_count = src_count;
    return TL_OK;
}

void tl_submerge_destroy(tl_submerge_t* sm) {
    if (sm == NULL) {
        return;
    }

    if (sm->srcs != NULL) {
        tl__free(sm->alloc, sm->srcs);
        sm->srcs = NULL;
    }
    sm->src_count = 0;

    tl_heap_destroy(&sm->heap);
    sm->alloc = NULL;
}

tl_status_t tl_submerge_build(tl_submerge_t* sm) {
    TL_ASSERT(sm != NULL);

    tl_heap_clear(&sm->heap);

    if (sm->src_count == 0) {
        return TL_OK;
    }

    tl_status_t st = tl_heap_reserve(&sm->heap, sm->src_count);
    if (st != TL_OK) {
        return st;
    }

    for (size_t i = 0; i < sm->src_count; i++) {
        tl_subsrc_t* src = &sm->srcs[i];
        if (src->len > 0 && src->data == NULL) {
            return TL_EINVAL;
        }
        if (src->pos >= src->end) {
            continue;
        }

        const tl_record_t* rec = &src->data[src->pos++];
        tl_heap_entry_t entry = {
            .ts = rec->ts,
            .tie_break_key = src->tie_id,
            .handle = rec->handle,
            .iter = src
        };
        st = tl_heap_push(&sm->heap, &entry);
        if (st != TL_OK) {
            tl_heap_clear(&sm->heap);
            return st;
        }
    }

    return TL_OK;
}

tl_status_t tl_submerge_next(tl_submerge_t* sm, tl_record_t* out) {
    TL_ASSERT(sm != NULL);

    const tl_heap_entry_t* peek = tl_heap_peek(&sm->heap);
    if (peek == NULL) {
        return TL_EOF;
    }

    if (out != NULL) {
        out->ts = peek->ts;
        out->handle = peek->handle;
    }

    tl_subsrc_t* src = (tl_subsrc_t*)peek->iter;
    uint32_t tie_id = peek->tie_break_key;

    if (src->pos < src->end) {
        const tl_record_t* rec = &src->data[src->pos++];
        tl_heap_entry_t entry = {
            .ts = rec->ts,
            .tie_break_key = tie_id,
            .handle = rec->handle,
            .iter = src
        };
        tl_heap_replace_top(&sm->heap, &entry);
    } else {
        tl_heap_entry_t discard;
        (void)tl_heap_pop(&sm->heap, &discard);
    }

    return TL_OK;
}

void tl_submerge_seek(tl_submerge_t* sm, tl_ts_t target) {
    TL_ASSERT(sm != NULL);

    if (tl_heap_is_empty(&sm->heap)) {
        return;
    }

    const tl_heap_entry_t* min = tl_heap_peek(&sm->heap);
    if (min != NULL && min->ts >= target) {
        return;
    }

    while (!tl_heap_is_empty(&sm->heap)) {
        const tl_heap_entry_t* entry = tl_heap_peek(&sm->heap);
        if (entry->ts >= target) {
            break;
        }

        tl_heap_entry_t popped;
        (void)tl_heap_pop(&sm->heap, &popped);

        tl_subsrc_t* src = (tl_subsrc_t*)popped.iter;
        size_t new_pos = tl_record_lower_bound(src->data, src->end, target);
        if (new_pos > src->pos) {
            src->pos = new_pos;
        }

        if (src->pos >= src->end) {
            continue;
        }

        const tl_record_t* rec = &src->data[src->pos++];
        tl_heap_entry_t new_entry = {
            .ts = rec->ts,
            .tie_break_key = popped.tie_break_key,
            .handle = rec->handle,
            .iter = src
        };
        tl_status_t st = tl_heap_push(&sm->heap, &new_entry);
        TL_ASSERT(st == TL_OK);
    }
}

/------------------------------------------------------------------------------/
/*   END OF: tl_submerge.c
/------------------------------------------------------------------------------/
