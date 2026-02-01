/*
============================================================================

   COMBINED SOURCE FILE: delta.c

   Generated from: core\src\delta
   Generated at:   2026-01-30 00:27:14

   This file combines all .c files from the delta/ subfolder.

   Files included:
 *   - tl_flush.c
 *   - tl_memrun.c
 *   - tl_memtable.c
 *   - tl_memview.c
 *   - tl_ooorun.c

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: tl_flush.c
/*   FROM: delta/
/*
/******************************************************************************/
#include "tl_flush.h"
#include "../internal/tl_heap.h"

/*===========================================================================
 * Merge Iterator Implementation
 *===========================================================================*/

void tl_merge_iter_init(tl_merge_iter_t* it,
                         const tl_record_t* a, size_t a_len,
                         const tl_record_t* b, size_t b_len) {
    TL_ASSERT(it != NULL);

    it->a = a;
    it->a_len = a_len;
    it->a_pos = 0;

    it->b = b;
    it->b_len = b_len;
    it->b_pos = 0;
}

const tl_record_t* tl_merge_iter_peek(const tl_merge_iter_t* it) {
    TL_ASSERT(it != NULL);

    /* If 'a' is exhausted, peek from 'b' */
    if (it->a_pos >= it->a_len) {
        if (it->b_pos >= it->b_len) {
            return NULL; /* Both exhausted */
        }
        return &it->b[it->b_pos];
    }

    /* If 'b' is exhausted, peek from 'a' */
    if (it->b_pos >= it->b_len) {
        return &it->a[it->a_pos];
    }

    /*
     * Both have elements: compare timestamps.
     * Stable merge: prefer 'a' on equal timestamps.
     */
    if (it->a[it->a_pos].ts <= it->b[it->b_pos].ts) {
        return &it->a[it->a_pos];
    }
    return &it->b[it->b_pos];
}

const tl_record_t* tl_merge_iter_next(tl_merge_iter_t* it) {
    TL_ASSERT(it != NULL);

    /* If 'a' is exhausted, take from 'b' */
    if (it->a_pos >= it->a_len) {
        if (it->b_pos >= it->b_len) {
            return NULL; /* Both exhausted */
        }
        return &it->b[it->b_pos++];
    }

    /* If 'b' is exhausted, take from 'a' */
    if (it->b_pos >= it->b_len) {
        return &it->a[it->a_pos++];
    }

    /*
     * Both have elements: compare timestamps.
     * Stable merge: prefer 'a' (run) on equal timestamps.
     * This preserves insertion order: in-order records before OOO records
     * with the same timestamp.
     */
    if (it->a[it->a_pos].ts <= it->b[it->b_pos].ts) {
        return &it->a[it->a_pos++];
    } else {
        return &it->b[it->b_pos++];
    }
}

/*===========================================================================
 * Flush Build Implementation
 *===========================================================================*/

tl_status_t tl_flush_build(const tl_flush_ctx_t* ctx,
                            const tl_memrun_t* mr,
                            tl_segment_t** out_seg) {
    TL_ASSERT(ctx != NULL);
    TL_ASSERT(ctx->alloc != NULL);
    TL_ASSERT(mr != NULL);
    TL_ASSERT(out_seg != NULL);

    *out_seg = NULL;

    /*
     * Step 1: Addition overflow check FIRST.
     * If run_len + ooo_len would overflow size_t, reject early.
     */
    if (mr->run_len > SIZE_MAX - mr->ooo_total_len) {
        return TL_EOVERFLOW;
    }

    size_t total_records = mr->run_len + mr->ooo_total_len;

    /*
     * Step 2: Handle tombstone-only case.
     * If no records but tombstones exist, build tombstone-only L0 segment.
     */
    if (total_records == 0) {
        if (mr->tombs_len > 0) {
            /* Tombstone-only segment */
            return tl_segment_build_l0(ctx->alloc,
                                        NULL, 0,
                                        mr->tombs, mr->tombs_len,
                                        ctx->target_page_bytes,
                                        ctx->generation,
                                        out_seg);
        } else {
            /* Empty memrun should never reach here (invariant violation) */
            return TL_EINVAL;
        }
    }

    /*
     * Step 3: Multiplication overflow check.
     * total_records * sizeof(tl_record_t) must not overflow.
     */
    if (total_records > SIZE_MAX / sizeof(tl_record_t)) {
        return TL_EOVERFLOW;
    }

    /*
     * Step 4: Allocate merged buffer.
     */
    size_t merged_size = total_records * sizeof(tl_record_t);
    tl_record_t* merged = tl__malloc(ctx->alloc, merged_size);
    if (merged == NULL) {
        return TL_ENOMEM;
    }

    /*
     * Step 5: K-way merge run + OOO runs into merged[].
     * Stable tie-break: run first, then OOO runs by gen order.
     */
    size_t run_count = mr->ooo_run_count;
    if (run_count > UINT32_MAX - 1) {
        tl__free(ctx->alloc, merged);
        return TL_EOVERFLOW;
    }
    size_t src_count = (mr->run_len > 0 ? 1 : 0) + run_count;
    if (src_count == 0) {
        tl__free(ctx->alloc, merged);
        return TL_EINTERNAL;
    }

    typedef struct flush_src {
        const tl_record_t* data;
        size_t             pos;
        size_t             end;
        uint32_t           tie_id;
    } flush_src_t;

    if (src_count > SIZE_MAX / sizeof(flush_src_t)) {
        tl__free(ctx->alloc, merged);
        return TL_EOVERFLOW;
    }

    flush_src_t* srcs = tl__malloc(ctx->alloc, src_count * sizeof(flush_src_t));
    if (srcs == NULL) {
        tl__free(ctx->alloc, merged);
        return TL_ENOMEM;
    }

    size_t src_idx = 0;
    if (mr->run_len > 0) {
        srcs[src_idx].data = mr->run;
        srcs[src_idx].pos = 0;
        srcs[src_idx].end = mr->run_len;
        srcs[src_idx].tie_id = 0;
        src_idx++;
    }

    if (run_count > 0) {
        TL_ASSERT(mr->ooo_runs != NULL);
        for (size_t i = 0; i < run_count; i++) {
            const tl_ooorun_t* run = mr->ooo_runs->runs[i];
            if (run == NULL || run->len == 0) {
                continue;
            }
            srcs[src_idx].data = run->records;
            srcs[src_idx].pos = 0;
            srcs[src_idx].end = run->len;
            srcs[src_idx].tie_id = (uint32_t)(1 + i);
            src_idx++;
        }
    }

    if (src_idx == 0) {
        tl__free(ctx->alloc, srcs);
        tl__free(ctx->alloc, merged);
        return TL_EINTERNAL;
    }

    tl_heap_t heap;
    tl_heap_init(&heap, ctx->alloc);
    tl_status_t st = tl_heap_reserve(&heap, src_idx);
    if (st != TL_OK) {
        tl_heap_destroy(&heap);
        tl__free(ctx->alloc, srcs);
        tl__free(ctx->alloc, merged);
        return st;
    }

    for (size_t i = 0; i < src_idx; i++) {
        if (srcs[i].pos >= srcs[i].end) {
            continue;
        }
        const tl_record_t* rec = &srcs[i].data[srcs[i].pos++];
        tl_heap_entry_t entry = {
            .ts = rec->ts,
            .tie_break_key = srcs[i].tie_id,
            .handle = rec->handle,
            .iter = &srcs[i]
        };
        st = tl_heap_push(&heap, &entry);
        if (st != TL_OK) {
            tl_heap_destroy(&heap);
            tl__free(ctx->alloc, srcs);
            tl__free(ctx->alloc, merged);
            return st;
        }
    }

    size_t i = 0;
    while (!tl_heap_is_empty(&heap)) {
        const tl_heap_entry_t* top = tl_heap_peek(&heap);
        TL_ASSERT(top != NULL);
        merged[i].ts = top->ts;
        merged[i].handle = top->handle;
        i++;

        flush_src_t* src = (flush_src_t*)top->iter;
        uint32_t tie_id = top->tie_break_key;
        if (src->pos < src->end) {
            const tl_record_t* rec = &src->data[src->pos++];
            tl_heap_entry_t entry = {
                .ts = rec->ts,
                .tie_break_key = tie_id,
                .handle = rec->handle,
                .iter = src
            };
            tl_heap_replace_top(&heap, &entry);
        } else {
            tl_heap_entry_t discard;
            (void)tl_heap_pop(&heap, &discard);
        }
    }

    tl_heap_destroy(&heap);
    tl__free(ctx->alloc, srcs);

    TL_ASSERT(i == total_records);

    /*
     * Step 6: Build L0 segment from merged records and tombstones.
     */
    st = tl_segment_build_l0(ctx->alloc,
                             merged, total_records,
                             mr->tombs, mr->tombs_len,
                             ctx->target_page_bytes,
                             ctx->generation,
                             out_seg);

    /*
     * Step 7: Free merged buffer regardless of build result.
     */
    tl__free(ctx->alloc, merged);

    return st;
}

/------------------------------------------------------------------------------/
/*   END OF: tl_flush.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memrun.c
/*   FROM: delta/
/*
/******************************************************************************/
#include "tl_memrun.h"

/*===========================================================================
 * Bounds Computation (M-11: Public for reuse)
 *
 * CRITICAL: Bounds MUST include tombstones, not just records.
 * This ensures tombstones outside record bounds are NOT pruned during
 * read-path overlap checks (which would cause missed deletes).
 *===========================================================================*/

void tl__memrun_compute_bounds(tl_memrun_t* mr) {
    /* Start with invalid bounds */
    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;

    /* Record bounds from run (sorted, so first/last are min/max) */
    if (mr->run_len > 0) {
        min_ts = TL_MIN(min_ts, mr->run[0].ts);
        max_ts = TL_MAX(max_ts, mr->run[mr->run_len - 1].ts);
    }

    /* Record bounds from OOO runs (precomputed min/max) */
    if (mr->ooo_total_len > 0) {
        min_ts = TL_MIN(min_ts, mr->ooo_min_ts);
        max_ts = TL_MAX(max_ts, mr->ooo_max_ts);
    }

    /* Tombstone bounds (CRITICAL for read-path correctness) */
    for (size_t i = 0; i < mr->tombs_len; i++) {
        const tl_interval_t* tomb = &mr->tombs[i];
        min_ts = TL_MIN(min_ts, tomb->start);

        if (tomb->end_unbounded) {
            /* Unbounded tombstone [start, +inf) => max_ts = TL_TS_MAX */
            max_ts = TL_TS_MAX;
        } else {
            /* Bounded tombstone [start, end) => max covered ts is end-1 */
            max_ts = TL_MAX(max_ts, tomb->end - 1);
        }
    }

    mr->min_ts = min_ts;
    mr->max_ts = max_ts;
}

/*===========================================================================
 * Creation
 *===========================================================================*/

/**
 * Initialize a pre-allocated memrun in-place.
 *
 * Takes ownership of the provided arrays (run, ooo, tombs).
 * Caller must ensure at least one array is non-empty.
 * Sets refcnt to 1.
 */
tl_status_t tl_memrun_init(tl_memrun_t* mr,
                            tl_alloc_ctx_t* alloc,
                            tl_record_t* run, size_t run_len,
                            tl_ooorunset_t* ooo_runs,
                            tl_interval_t* tombs, size_t tombs_len) {
    if (mr == NULL || alloc == NULL) {
        return TL_EINVAL;
    }
    if (run_len == 0 && ooo_runs == NULL && tombs_len == 0) {
        return TL_EINVAL;
    }
    if (run_len > 0 && run == NULL) {
        return TL_EINVAL;
    }
    if (ooo_runs != NULL && ooo_runs->count == 0) {
        return TL_EINVAL;
    }
    if (tombs_len > 0 && tombs == NULL) {
        return TL_EINVAL;
    }

    /* Take ownership of arrays */
    mr->run = run;
    mr->run_len = run_len;
    mr->ooo_runs = ooo_runs;
    mr->ooo_total_len = (ooo_runs == NULL) ? 0 : ooo_runs->total_len;
    mr->ooo_run_count = (ooo_runs == NULL) ? 0 : ooo_runs->count;
    mr->ooo_min_ts = TL_TS_MAX;
    mr->ooo_max_ts = TL_TS_MIN;
    mr->tombs = tombs;
    mr->tombs_len = tombs_len;

    /* Store allocator */
    mr->alloc = alloc;

    /* Initialize reference count to 1 (caller owns) */
    tl_atomic_init_u32(&mr->refcnt, 1);

    if (mr->ooo_total_len > 0) {
        for (size_t i = 0; i < mr->ooo_run_count; i++) {
            const tl_ooorun_t* run_ptr = mr->ooo_runs->runs[i];
            mr->ooo_min_ts = TL_MIN(mr->ooo_min_ts, run_ptr->min_ts);
            mr->ooo_max_ts = TL_MAX(mr->ooo_max_ts, run_ptr->max_ts);
        }
    }

    /* Compute bounds (includes tombstones) */
    tl__memrun_compute_bounds(mr);
    return TL_OK;
}

tl_status_t tl_memrun_create(tl_alloc_ctx_t* alloc,
                              tl_record_t* run, size_t run_len,
                              tl_ooorunset_t* ooo_runs,
                              tl_interval_t* tombs, size_t tombs_len,
                              tl_memrun_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    /* All empty is invalid */
    if (run_len == 0 && ooo_runs == NULL && tombs_len == 0) {
        return TL_EINVAL;
    }
    if (run_len > 0 && run == NULL) {
        return TL_EINVAL;
    }
    if (ooo_runs != NULL && ooo_runs->count == 0) {
        return TL_EINVAL;
    }
    if (tombs_len > 0 && tombs == NULL) {
        return TL_EINVAL;
    }

    tl_memrun_t* mr = NULL;
    tl_status_t st = tl_memrun_alloc(alloc, &mr);
    if (st != TL_OK) {
        return st;
    }

    st = tl_memrun_init(mr, alloc, run, run_len, ooo_runs, tombs, tombs_len);
    if (st != TL_OK) {
        tl__free(alloc, mr);
        return st;
    }

    *out = mr;
    return TL_OK;
}

tl_status_t tl_memrun_alloc(tl_alloc_ctx_t* alloc, tl_memrun_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    tl_memrun_t* mr = TL_NEW(alloc, tl_memrun_t);
    if (mr == NULL) {
        return TL_ENOMEM;
    }

    *out = mr;
    return TL_OK;
}

/*===========================================================================
 * Reference Counting
 *===========================================================================*/

tl_memrun_t* tl_memrun_acquire(tl_memrun_t* mr) {
    if (mr == NULL) {
        return NULL;
    }

    /* Relaxed: we already have a reference, so no ordering needed for increment */
    tl_atomic_fetch_add_u32(&mr->refcnt, 1, TL_MO_RELAXED);
    return mr;
}

void tl_memrun_release(tl_memrun_t* mr) {
    if (mr == NULL) {
        return;
    }

    /* Release ordering: ensure all prior writes are visible before potential destruction */
    uint32_t old = tl_atomic_fetch_sub_u32(&mr->refcnt, 1, TL_MO_RELEASE);

    if (old == 1) {
        /* Acquire fence: synchronize with all releasers before destruction */
        tl_atomic_fence(TL_MO_ACQUIRE);

        /* Free owned arrays */
        if (mr->run != NULL) {
            tl__free(mr->alloc, mr->run);
        }
        if (mr->ooo_runs != NULL) {
            tl_ooorunset_release(mr->ooo_runs);
        }
        if (mr->tombs != NULL) {
            tl__free(mr->alloc, mr->tombs);
        }

        /* Free memrun struct */
        tl__free(mr->alloc, mr);
    }
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/**
 * Check if record array is sorted by timestamp (non-decreasing).
 */
static bool is_records_sorted_ts(const tl_record_t* arr, size_t len) {
    if (len <= 1) {
        return true;
    }
    for (size_t i = 0; i < len - 1; i++) {
        if (arr[i].ts > arr[i + 1].ts) {
            return false;
        }
    }
    return true;
}

static bool is_records_sorted_ts_handle(const tl_record_t* arr, size_t len) {
    if (len <= 1) {
        return true;
    }
    for (size_t i = 0; i < len - 1; i++) {
        if (arr[i].ts > arr[i + 1].ts) {
            return false;
        }
        if (arr[i].ts == arr[i + 1].ts &&
            arr[i].handle > arr[i + 1].handle) {
            return false;
        }
    }
    return true;
}

/**
 * Check if tombstone array is sorted, non-overlapping, and coalesced.
 */
static bool is_tombs_valid(const tl_interval_t* arr, size_t len) {
    if (len <= 1) {
        return true;
    }
    for (size_t i = 0; i < len - 1; i++) {
        const tl_interval_t* curr = &arr[i];
        const tl_interval_t* next = &arr[i + 1];

        /* Must be sorted by start */
        if (curr->start > next->start) {
            return false;
        }

        /* If current is unbounded, nothing should follow */
        if (curr->end_unbounded) {
            return false;
        }

        /* Must not overlap: curr->end <= next->start */
        if (curr->end > next->start) {
            return false;
        }

        /* Must not be adjacent (should be coalesced): curr->end < next->start */
        if (curr->end == next->start) {
            return false;
        }
    }
    return true;
}

bool tl_memrun_validate(const tl_memrun_t* mr) {
    if (mr == NULL) {
        return false;
    }

    /* Reference count must be positive */
    if (tl_memrun_refcnt(mr) == 0) {
        return false;
    }

    /* At least one component must be non-empty */
    if (mr->run_len == 0 && mr->ooo_total_len == 0 && mr->tombs_len == 0) {
        return false;
    }

    /* Check run sorted by ts (handle order is unspecified for in-order path) */
    if (!is_records_sorted_ts(mr->run, mr->run_len)) {
        return false;
    }

    /* Check OOO runset */
    if (mr->ooo_total_len > 0) {
        if (mr->ooo_runs == NULL || mr->ooo_run_count == 0) {
            return false;
        }
        if (mr->ooo_run_count != mr->ooo_runs->count) {
            return false;
        }
        size_t total = 0;
        uint64_t last_gen = 0;
        bool have_gen = false;
        tl_ts_t min_ts = TL_TS_MAX;
        tl_ts_t max_ts = TL_TS_MIN;

        for (size_t i = 0; i < mr->ooo_run_count; i++) {
            const tl_ooorun_t* run = mr->ooo_runs->runs[i];
            if (run == NULL) {
                return false;
            }
            if (!is_records_sorted_ts_handle(run->records, run->len)) {
                return false;
            }
            if (have_gen && run->gen < last_gen) {
                return false;
            }
            have_gen = true;
            last_gen = run->gen;

            if (run->len > SIZE_MAX - total) {
                return false;
            }
            total += run->len;

            min_ts = TL_MIN(min_ts, run->min_ts);
            max_ts = TL_MAX(max_ts, run->max_ts);
        }

        if (total != mr->ooo_total_len) {
            return false;
        }
        if (min_ts != mr->ooo_min_ts || max_ts != mr->ooo_max_ts) {
            return false;
        }
    } else if (mr->ooo_runs != NULL || mr->ooo_run_count != 0) {
        return false;
    }

    /* Check tombs valid */
    if (!is_tombs_valid(mr->tombs, mr->tombs_len)) {
        return false;
    }

    /* Verify min_ts */
    tl_ts_t expected_min = TL_TS_MAX;
    if (mr->run_len > 0) {
        expected_min = TL_MIN(expected_min, mr->run[0].ts);
    }
    if (mr->ooo_total_len > 0) {
        expected_min = TL_MIN(expected_min, mr->ooo_min_ts);
    }
    for (size_t i = 0; i < mr->tombs_len; i++) {
        expected_min = TL_MIN(expected_min, mr->tombs[i].start);
    }
    if (mr->min_ts != expected_min) {
        return false;
    }

    /* Verify max_ts */
    tl_ts_t expected_max = TL_TS_MIN;
    if (mr->run_len > 0) {
        expected_max = TL_MAX(expected_max, mr->run[mr->run_len - 1].ts);
    }
    if (mr->ooo_total_len > 0) {
        expected_max = TL_MAX(expected_max, mr->ooo_max_ts);
    }
    for (size_t i = 0; i < mr->tombs_len; i++) {
        const tl_interval_t* tomb = &mr->tombs[i];
        if (tomb->end_unbounded) {
            expected_max = TL_TS_MAX;
        } else {
            expected_max = TL_MAX(expected_max, tomb->end - 1);
        }
    }
    if (mr->max_ts != expected_max) {
        return false;
    }

    return true;
}

#endif /* TL_DEBUG */

/------------------------------------------------------------------------------/
/*   END OF: tl_memrun.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memtable.c
/*   FROM: delta/
/*
/******************************************************************************/
#include "tl_memtable.h"
#include "../internal/tl_locks.h"
#include <stdlib.h>
#include <string.h>

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_memtable_init(tl_memtable_t* mt,
                              tl_alloc_ctx_t* alloc,
                              size_t memtable_max_bytes,
                              size_t ooo_budget_bytes,
                              size_t sealed_max_runs) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(sealed_max_runs > 0);

    memset(mt, 0, sizeof(*mt));

    /* Store allocator */
    mt->alloc = alloc;

    /* Initialize active buffers */
    tl_recvec_init(&mt->active_run, alloc);
    tl_recvec_init(&mt->ooo_head, alloc);
    tl_intervals_init(&mt->active_tombs, alloc);

    /* Preallocate sealed queue (CRITICAL: no realloc on seal path) */
    mt->sealed = TL_NEW_ARRAY(alloc, tl_memrun_t*, sealed_max_runs);
    if (mt->sealed == NULL) {
        tl_recvec_destroy(&mt->active_run);
        tl_recvec_destroy(&mt->ooo_head);
        tl_intervals_destroy(&mt->active_tombs);
        return TL_ENOMEM;
    }
    mt->sealed_head = 0;
    mt->sealed_len = 0;
    mt->sealed_max_runs = sealed_max_runs;
    mt->sealed_epoch = 0;

    /* Store configuration */
    mt->memtable_max_bytes = memtable_max_bytes;
    mt->ooo_budget_bytes = ooo_budget_bytes;
    mt->ooo_chunk_records = 0;  /* Derived below */
    mt->ooo_run_limit = TL_DEFAULT_OOO_RUN_LIMIT;

    /* Initialize metadata */
    mt->last_inorder_ts = TL_TS_MIN;
    mt->active_bytes_est = 0;
    mt->epoch = 0;

    mt->ooo_runs = NULL;
    mt->ooo_head_sorted = true;
    mt->ooo_head_last_ts = TL_TS_MIN;
    mt->ooo_head_last_handle = 0;
    mt->ooo_next_gen = 0;

    /* Derive OOO chunk size from budget (bounded) */
    size_t budget_records = (ooo_budget_bytes / TL_RECORD_SIZE);
    size_t chunk = budget_records / TL_OOO_TARGET_RUNS;
    if (chunk < TL_OOO_CHUNK_MIN_RECORDS) {
        chunk = TL_OOO_CHUNK_MIN_RECORDS;
    }
    if (chunk > TL_OOO_CHUNK_MAX_RECORDS) {
        chunk = TL_OOO_CHUNK_MAX_RECORDS;
    }
    if (chunk == 0) {
        chunk = TL_OOO_CHUNK_MIN_RECORDS;
    }
    mt->ooo_chunk_records = chunk;

    return TL_OK;
}

void tl_memtable_destroy(tl_memtable_t* mt) {
    if (mt == NULL) {
        return;
    }

    /* Release all sealed memruns */
    for (size_t i = 0; i < mt->sealed_len; i++) {
        size_t idx = tl_memtable_sealed_index(mt, i);
        if (mt->sealed[idx] != NULL) {
            tl_memrun_release(mt->sealed[idx]);
        }
    }

    /* Free sealed queue array */
    if (mt->sealed != NULL) {
        tl__free(mt->alloc, (void*)mt->sealed);
        mt->sealed = NULL;
    }
    mt->sealed_len = 0;
    mt->sealed_head = 0;
    mt->sealed_epoch = 0;

    /* Destroy active buffers */
    tl_recvec_destroy(&mt->active_run);
    tl_recvec_destroy(&mt->ooo_head);
    tl_intervals_destroy(&mt->active_tombs);
    if (mt->ooo_runs != NULL) {
        tl_ooorunset_release(mt->ooo_runs);
        mt->ooo_runs = NULL;
    }
}

/*===========================================================================
 * Insert Operations
 *===========================================================================*/

/**
 * Comparison function for qsort.
 * Sorts records by (ts, handle) in non-decreasing order.
 */
static int cmp_record_ts_head(const void* a, const void* b) {
    const tl_record_t* ra = (const tl_record_t*)a;
    const tl_record_t* rb = (const tl_record_t*)b;

    if (ra->ts < rb->ts) return -1;
    if (ra->ts > rb->ts) return 1;
    if (ra->handle < rb->handle) return -1;
    if (ra->handle > rb->handle) return 1;
    return 0;
}

static void memtable_add_bytes(tl_memtable_t* mt, size_t add) {
    if (add == 0) {
        return;
    }
    if (mt->active_bytes_est > SIZE_MAX - add) {
        mt->active_bytes_est = SIZE_MAX;
        return;
    }
    mt->active_bytes_est += add;
}

static void memtable_add_record_bytes(tl_memtable_t* mt, size_t count) {
    if (count == 0) {
        return;
    }
    if (tl__alloc_would_overflow(count, TL_RECORD_SIZE)) {
        mt->active_bytes_est = SIZE_MAX;
        return;
    }
    memtable_add_bytes(mt, count * TL_RECORD_SIZE);
}

static void memtable_adjust_tomb_bytes(tl_memtable_t* mt,
                                       size_t before_len,
                                       size_t after_len) {
    if (before_len == after_len) {
        return;
    }

    size_t diff = (after_len > before_len)
                    ? (after_len - before_len)
                    : (before_len - after_len);

    if (tl__alloc_would_overflow(diff, sizeof(tl_interval_t))) {
        /* Saturate conservatively on overflow. */
        if (after_len > before_len) {
            mt->active_bytes_est = SIZE_MAX;
        } else {
            mt->active_bytes_est = 0;
        }
        return;
    }

    size_t bytes = diff * sizeof(tl_interval_t);

    if (after_len > before_len) {
        memtable_add_bytes(mt, bytes);
    } else {
        if (mt->active_bytes_est < bytes) {
            mt->active_bytes_est = 0;
        } else {
            mt->active_bytes_est -= bytes;
        }
    }
}

static size_t memtable_ooo_bytes_est(const tl_memtable_t* mt) {
    size_t total_len = tl_memtable_ooo_total_len(mt);
    if (tl__alloc_would_overflow(total_len, TL_RECORD_SIZE)) {
        return SIZE_MAX;
    }
    return total_len * TL_RECORD_SIZE;
}

static void ooo_head_note_append(tl_memtable_t* mt, tl_ts_t ts, tl_handle_t handle) {
    size_t head_len = tl_recvec_len(&mt->ooo_head);
    if (head_len <= 1) {
        mt->ooo_head_sorted = true;
        mt->ooo_head_last_ts = ts;
        mt->ooo_head_last_handle = handle;
        return;
    }

    if (mt->ooo_head_sorted) {
        if (ts < mt->ooo_head_last_ts ||
            (ts == mt->ooo_head_last_ts && handle < mt->ooo_head_last_handle)) {
            mt->ooo_head_sorted = false;
        }
    }

    mt->ooo_head_last_ts = ts;
    mt->ooo_head_last_handle = handle;
}

static tl_status_t memtable_flush_ooo_head(tl_memtable_t* mt, bool required) {
    size_t head_len = tl_recvec_len(&mt->ooo_head);
    if (head_len == 0) {
        return TL_OK;
    }

    if (!required && mt->ooo_run_limit > 0 &&
        tl_ooorunset_count(mt->ooo_runs) >= mt->ooo_run_limit) {
        return TL_EBUSY;
    }

    if (head_len > SIZE_MAX / sizeof(tl_record_t)) {
        return TL_EOVERFLOW;
    }

    size_t bytes = head_len * sizeof(tl_record_t);
    tl_record_t* copy = tl__malloc(mt->alloc, bytes);
    if (copy == NULL) {
        return TL_ENOMEM;
    }
    memcpy(copy, tl_recvec_data(&mt->ooo_head), bytes);

    if (!mt->ooo_head_sorted && head_len > 1) {
        qsort(copy, head_len, sizeof(tl_record_t), cmp_record_ts_head);
    }

    uint64_t gen = ++mt->ooo_next_gen;
    tl_ooorun_t* run = NULL;
    tl_status_t st = tl_ooorun_create(mt->alloc, copy, head_len, gen, &run);
    if (st != TL_OK) {
        tl__free(mt->alloc, copy);
        return st;
    }

    tl_ooorunset_t* new_set = NULL;
    st = tl_ooorunset_append(mt->alloc, mt->ooo_runs, run, &new_set);
    if (st != TL_OK) {
        tl_ooorun_release(run);
        return st;
    }

    tl_ooorunset_t* old_set = mt->ooo_runs;
    mt->ooo_runs = new_set;
    if (old_set != NULL) {
        tl_ooorunset_release(old_set);
    }
    tl_ooorun_release(run); /* Runset now owns a reference */

    tl_recvec_clear(&mt->ooo_head);
    mt->ooo_head_sorted = true;
    mt->ooo_head_last_ts = TL_TS_MIN;
    mt->ooo_head_last_handle = 0;

    mt->epoch++;

    return TL_OK;
}

tl_status_t tl_memtable_insert(tl_memtable_t* mt, tl_ts_t ts, tl_handle_t handle) {
    TL_ASSERT(mt != NULL);

    tl_status_t st;

    /* Route to appropriate buffer based on timestamp ordering */
    if (tl_recvec_len(&mt->active_run) == 0 ||
        ts >= mt->last_inorder_ts) {
        /* In-order: fast path to run */
        st = tl_recvec_push(&mt->active_run, ts, handle);
        if (st != TL_OK) {
            return st;
        }
        mt->last_inorder_ts = ts;
    } else {
        /* Out-of-order: append to OOO head (sorted on flush/seal). */
        st = tl_recvec_push(&mt->ooo_head, ts, handle);
        if (st != TL_OK) {
            return st;
        }
        ooo_head_note_append(mt, ts, handle);
    }

    /* Update metadata AFTER successful insert */
    mt->epoch++;
    memtable_add_record_bytes(mt, 1);

    /* Best-effort head flush when threshold reached */
    if (tl_recvec_len(&mt->ooo_head) >= mt->ooo_chunk_records) {
        tl_status_t flush_st = memtable_flush_ooo_head(mt, false);
        if (flush_st != TL_OK) {
            return TL_EBUSY; /* Insert succeeded, flush failed */
        }
    }

    return TL_OK;
}

/**
 * Check if entire batch is sorted (non-decreasing by timestamp).
 * Returns true if batch is sorted, false otherwise.
 * FULL CHECK, NO SAMPLING - sampling could miss unsorted sections.
 */
static bool batch_is_sorted(const tl_record_t* records, size_t n) {
    if (n <= 1) {
        return true;
    }
    for (size_t i = 0; i < n - 1; i++) {
        if (records[i].ts > records[i + 1].ts) {
            return false;
        }
    }
    return true;
}

tl_status_t tl_memtable_insert_batch(tl_memtable_t* mt,
                                      const tl_record_t* records, size_t n,
                                      uint32_t flags) {
    TL_ASSERT(mt != NULL);
    (void)flags; /* Hint only - we verify sortedness regardless */

    if (n == 0) {
        return TL_OK;
    }

    TL_ASSERT(records != NULL);

    tl_status_t st;
    size_t inserted = 0;

    /* Determine if we can use fast path (bulk append to run) */
    bool use_fast_path = false;
    bool first_fits = (tl_recvec_len(&mt->active_run) == 0) ||
                      (records[0].ts >= mt->last_inorder_ts);

    if (first_fits) {
        /* Verify batch is sorted: FULL CHECK, NO SAMPLING */
        if (batch_is_sorted(records, n)) {
            use_fast_path = true;
        }
    }

    if (use_fast_path) {
        /* Fast path: bulk append to active_run */
        size_t len = tl_recvec_len(&mt->active_run);

        /* Check for addition overflow before computing new capacity */
        if (n > SIZE_MAX - len) {
            return TL_EOVERFLOW;
        }

        /* Pre-reserve to make this all-or-nothing (no partial state on failure) */
        size_t new_cap = len + n;
        st = tl_recvec_reserve(&mt->active_run, new_cap);
        if (st != TL_OK) {
            /* No records inserted, clean failure */
            return st;
        }

        /* Copy all records (cannot fail after reserve).
         *
         * ATOMICITY: push_n is a memcpy-based operation that cannot partially
         * fail after successful reserve. If it returns error (shouldn't happen),
         * no records were inserted (memcpy is all-or-nothing). Therefore we
         * return without updating metadata - this maintains consistency.
         *
         * If push_n ever changed to allow partial writes, this would need
         * to handle partial metadata updates like the slow path does. */
        st = tl_recvec_push_n(&mt->active_run, records, n);
        if (st != TL_OK) {
            /* Reserve succeeded but push_n failed - should never happen.
             * No records were inserted, return without metadata update. */
            return st;
        }

        mt->last_inorder_ts = records[n - 1].ts;
        inserted = n;
    } else {
        /* Slow path: per-record insert
         *
         * C-08 fix: Pre-reserve both vectors to guarantee all-or-nothing semantics.
         * This ensures that if any allocation would fail, we fail BEFORE inserting
         * any records. Callers can then safely rollback INCREF on all input handles.
         *
         * TRADEOFF: We reserve up to 2N slots total (worst case: all go to run OR
         * all go to ooo). This may fail earlier under memory pressure than actual
         * inserts would, but guarantees atomicity which is more important for API
         * correctness. Memory is virtual, so over-reservation doesn't waste physical
         * RAM immediately.
         */
        size_t run_len = tl_recvec_len(&mt->active_run);
        size_t ooo_len = tl_recvec_len(&mt->ooo_head);

        /* Overflow checks before computing sums */
        if (n > SIZE_MAX - run_len || n > SIZE_MAX - ooo_len) {
            return TL_EOVERFLOW;
        }

        /* Pre-reserve to guarantee all-or-nothing semantics */
        st = tl_recvec_reserve(&mt->active_run, run_len + n);
        if (st != TL_OK) {
            return st;  /* No records inserted, clean failure */
        }

        st = tl_recvec_reserve(&mt->ooo_head, ooo_len + n);
        if (st != TL_OK) {
            return st;  /* No records inserted, clean failure */
        }

        /* Loop: push/insert cannot fail on allocation after pre-reserve */
        for (size_t i = 0; i < n; i++) {
            tl_ts_t ts = records[i].ts;
            tl_handle_t handle = records[i].handle;

            if (tl_recvec_len(&mt->active_run) == 0 || ts >= mt->last_inorder_ts) {
                st = tl_recvec_push(&mt->active_run, ts, handle);
                /* Capacity guaranteed, can only fail on programming error */
                TL_ASSERT(st == TL_OK);
                mt->last_inorder_ts = ts;
            } else {
                /* OOO head append (sorted on flush/seal) */
                st = tl_recvec_push(&mt->ooo_head, ts, handle);
                /* Capacity guaranteed, can only fail on programming error */
                TL_ASSERT(st == TL_OK);
                ooo_head_note_append(mt, ts, handle);
            }
            inserted++;
        }
    }

    /* Update metadata ONCE at end (all records inserted successfully) */
    mt->epoch++;
    memtable_add_record_bytes(mt, inserted);

    /* Best-effort head flush when threshold reached */
    if (tl_recvec_len(&mt->ooo_head) >= mt->ooo_chunk_records) {
        tl_status_t flush_st = memtable_flush_ooo_head(mt, false);
        if (flush_st != TL_OK) {
            return TL_EBUSY; /* Inserted all records, flush failed */
        }
    }

    return TL_OK;
}

tl_status_t tl_memtable_insert_tombstone(tl_memtable_t* mt, tl_ts_t t1, tl_ts_t t2) {
    TL_ASSERT(mt != NULL);

    /* Delegate to tl_intervals which handles validation and coalescing */
    size_t before_len = tl_intervals_len(&mt->active_tombs);
    tl_status_t st = tl_intervals_insert(&mt->active_tombs, t1, t2);

    if (st == TL_OK && t1 < t2) {
        /* Only update metadata if actual insert happened (not empty interval) */
        mt->epoch++;
        size_t after_len = tl_intervals_len(&mt->active_tombs);
        memtable_adjust_tomb_bytes(mt, before_len, after_len);
    }

    return st;
}

tl_status_t tl_memtable_insert_tombstone_unbounded(tl_memtable_t* mt, tl_ts_t t1) {
    TL_ASSERT(mt != NULL);

    size_t before_len = tl_intervals_len(&mt->active_tombs);
    tl_status_t st = tl_intervals_insert_unbounded(&mt->active_tombs, t1);

    if (st == TL_OK) {
        mt->epoch++;
        size_t after_len = tl_intervals_len(&mt->active_tombs);
        memtable_adjust_tomb_bytes(mt, before_len, after_len);
    }

    return st;
}

/*===========================================================================
 * Seal Operations
 *===========================================================================*/

bool tl_memtable_should_seal(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);

    /* Check total active bytes */
    if (mt->active_bytes_est >= mt->memtable_max_bytes) {
        return true;
    }

    /* Check OOO bytes specifically (skip if budget is 0 = unlimited) */
    if (mt->ooo_budget_bytes > 0) {
        size_t ooo_bytes = memtable_ooo_bytes_est(mt);
        if (ooo_bytes >= mt->ooo_budget_bytes) {
            return true;
        }
    }

    if (mt->ooo_run_limit > 0 &&
        tl_ooorunset_count(mt->ooo_runs) >= mt->ooo_run_limit) {
        return true;
    }

    return false;
}

bool tl_memtable_ooo_budget_exceeded(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);

    if (mt->ooo_budget_bytes == 0) {
        return false;  /* Unlimited budget */
    }

    size_t ooo_bytes = memtable_ooo_bytes_est(mt);
    return ooo_bytes >= mt->ooo_budget_bytes;
}

bool tl_memtable_is_active_empty(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);
    return tl_recvec_is_empty(&mt->active_run) &&
           tl_recvec_is_empty(&mt->ooo_head) &&
           tl_ooorunset_total_len(mt->ooo_runs) == 0 &&
           tl_intervals_is_empty(&mt->active_tombs);
}

tl_status_t tl_memtable_seal(tl_memtable_t* mt, tl_mutex_t* mu, tl_cond_t* cond) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(mu != NULL);

    /* Step 1: Check if anything to seal (no lock needed - under writer_mu) */
    if (tl_memtable_is_active_empty(mt)) {
        return TL_OK; /* Nothing to seal */
    }

    /* Step 2: Check queue capacity FIRST (under memtable_mu) */
    TL_LOCK(mu, TL_LOCK_MEMTABLE_MU);
    if (mt->sealed_len >= mt->sealed_max_runs) {
        TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);
        return TL_EBUSY; /* Active state PRESERVED */
    }
    TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);

    /*
     * Step 3: Take ownership of active arrays FIRST.
     * We do this before allocating memrun so that if tl_memrun_create
     * fails, we can restore the arrays to the memtable.
     * However, tl_recvec_take and tl_intervals_take reset the vectors,
     * so we need to be careful about rollback.
     *
     * DESIGN: The plan says "check capacity, allocate memrun, then take".
     * But tl_memrun_create handles allocation internally. We must
     * try tl_memrun_create first (which allocates internally), and if
     * it fails due to TL_ENOMEM, we've already detached the arrays.
     *
     * SOLUTION: Take arrays, try create. If create fails:
     * - For TL_EINVAL: shouldn't happen (checked non-empty above)
     * - For TL_ENOMEM: arrays were taken but memrun alloc failed.
     *   We must restore them. But tl_recvec has no "restore" API.
     *
     * REVISED SOLUTION: We know we're non-empty. Take the arrays,
     * and tl_memrun_create will succeed unless OOM. On OOM, we lose
     * the arrays (they're freed in cleanup). This violates "preserve
     * active state on ENOMEM".
     *
     * CORRECT SOLUTION: Attempt a dummy allocation first to test if
     * memory is available, OR accept that on OOM during seal, data
     * may be lost. The plan says "active preserved on ENOMEM".
     *
     * IMPLEMENTATION: Pre-allocate the memrun struct (just the struct,
     * not with tl_memrun_create). Then take arrays, initialize manually,
     * compute bounds. This matches the plan exactly.
     */

    /* Step 3: Pre-allocate memrun struct BEFORE detaching arrays */
    tl_memrun_t* mr = NULL;
    tl_status_t alloc_st = tl_memrun_alloc(mt->alloc, &mr);
    if (alloc_st != TL_OK) {
        return TL_ENOMEM; /* Active state PRESERVED */
    }

    /* Step 4: Flush OOO head (required at seal) */
    tl_status_t flush_st = memtable_flush_ooo_head(mt, true);
    if (flush_st != TL_OK) {
        tl__free(mt->alloc, mr);
        return flush_st; /* Active state PRESERVED */
    }

    /* Step 5: Take ownership of active arrays and runset */
    size_t run_len = 0;
    size_t tombs_len = 0;

    tl_record_t* run = tl_recvec_take(&mt->active_run, &run_len);
    tl_interval_t* tombs = tl_intervals_take(&mt->active_tombs, &tombs_len);
    tl_ooorunset_t* ooo_runs = mt->ooo_runs;
    mt->ooo_runs = NULL;

    /* Step 6: Initialize memrun in-place (no allocations) */
    tl_status_t init_st = tl_memrun_init(mr, mt->alloc,
                                         run, run_len,
                                         ooo_runs,
                                         tombs, tombs_len);
    if (init_st != TL_OK) {
        /* Internal invariant violation - avoid leaks, but data is lost */
        if (run != NULL) tl__free(mt->alloc, run);
        if (ooo_runs != NULL) tl_ooorunset_release(ooo_runs);
        if (tombs != NULL) tl__free(mt->alloc, tombs);
        tl__free(mt->alloc, mr);
        return TL_EINTERNAL;
    }

    /* Step 7: Push to sealed queue (under memtable_mu) */
    TL_LOCK(mu, TL_LOCK_MEMTABLE_MU);
    /*
     * M-10 fix: Runtime check for queue capacity (defensive).
     * Single writer means this should never fail, but we check defensively
     * in case of future code changes. On failure, release memrun and return
     * TL_EBUSY without corrupting the queue.
     */
    if (mt->sealed_len >= mt->sealed_max_runs) {
        TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);
        tl_memrun_release(mr);
        return TL_EBUSY;
    }
    TL_ASSERT(mt->sealed_len < mt->sealed_max_runs);
    size_t idx = tl_memtable_sealed_index(mt, mt->sealed_len);
    mt->sealed[idx] = mr;
    mt->sealed_len++;
    mt->sealed_epoch++;
    TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);

    /* Step 8: Reset active metadata AFTER successful enqueue */
    mt->last_inorder_ts = TL_TS_MIN;
    mt->active_bytes_est = 0;
    mt->epoch++;  /* Memtable state changed (active -> sealed) */
    tl_recvec_clear(&mt->ooo_head);
    mt->ooo_head_sorted = true;
    mt->ooo_head_last_ts = TL_TS_MIN;
    mt->ooo_head_last_handle = 0;
    mt->ooo_next_gen = 0;

    /* Signal waiters if provided */
    if (cond != NULL) {
        tl_cond_signal(cond);
    }

    return TL_OK;
}

/*===========================================================================
 * Sealed Queue Operations
 *===========================================================================*/

bool tl_memtable_has_sealed(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);
    return mt->sealed_len > 0;
}

bool tl_memtable_is_sealed_full(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);
    return mt->sealed_len >= mt->sealed_max_runs;
}

tl_status_t tl_memtable_peek_oldest(const tl_memtable_t* mt, tl_memrun_t** out) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(out != NULL);

    if (mt->sealed_len == 0) {
        *out = NULL;
        return TL_OK;
    }

    /* Peek oldest (FIFO: sealed_head) and acquire reference */
    tl_memrun_t* mr = tl_memtable_sealed_at(mt, 0);
    *out = tl_memrun_acquire(mr);
    return TL_OK;
}

void tl_memtable_pop_oldest(tl_memtable_t* mt, tl_cond_t* cond) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(mt->sealed_len > 0);

    /* Get oldest (FIFO: sealed_head) */
    size_t idx = tl_memtable_sealed_index(mt, 0);
    tl_memrun_t* mr = mt->sealed[idx];
    mt->sealed[idx] = NULL;

    /* Advance head */
    mt->sealed_head++;
    if (mt->sealed_head == mt->sealed_max_runs) {
        mt->sealed_head = 0;
    }
    mt->sealed_len--;
    if (mt->sealed_len == 0) {
        mt->sealed_head = 0;
    }
    mt->sealed_epoch++;

    /* Release queue's reference */
    tl_memrun_release(mr);

    /* Sealed queue changed (flush removed a memrun) */
    mt->epoch++;

    /* Signal waiters (backpressure) */
    if (cond != NULL) {
        tl_cond_signal(cond);
    }
}

size_t tl_memtable_sealed_len(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);
    return mt->sealed_len;
}

/*===========================================================================
 * Backpressure
 *===========================================================================*/

bool tl_memtable_wait_for_space(const tl_memtable_t* mt, tl_mutex_t* mu,
                                 tl_cond_t* cond, uint32_t timeout_ms) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(mu != NULL);
    TL_ASSERT(cond != NULL);

    /*
     * Loop to handle spurious wakeups properly.
     * memtable_cond is dedicated to sealed queue space signaling.
     * Use monotonic time to track actual elapsed time across wakeups.
     */
    uint64_t start_ms = tl_monotonic_ms();
    uint64_t deadline_ms = start_ms + timeout_ms;

    while (mt->sealed_len >= mt->sealed_max_runs) {
        uint64_t now_ms = tl_monotonic_ms();

        /* Check if deadline passed (handles wraparound via unsigned math) */
        if (now_ms >= deadline_ms) {
            /* Timeout expired */
            break;
        }

        /* Compute remaining time (safe: now_ms < deadline_ms) */
        uint64_t remaining = deadline_ms - now_ms;
        uint32_t wait_ms = (remaining > UINT32_MAX) ? UINT32_MAX : (uint32_t)remaining;

        /* Wait with remaining timeout */
        bool signaled = tl_cond_timedwait(cond, mu, wait_ms);
        if (!signaled) {
            /* Timed out - but re-check condition before returning */
            break;
        }

        /* Signaled (possibly spuriously) - loop will re-check condition */
    }

    return (mt->sealed_len < mt->sealed_max_runs);
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/**
 * Check if record array is sorted.
 */
static bool debug_records_sorted(const tl_record_t* arr, size_t len) {
    if (len <= 1) return true;
    for (size_t i = 0; i < len - 1; i++) {
        if (arr[i].ts > arr[i + 1].ts) return false;
    }
    return true;
}

bool tl_memtable_validate(const tl_memtable_t* mt) {
    if (mt == NULL) {
        return false;
    }

    /* Check active_run is sorted */
    if (!debug_records_sorted(tl_recvec_data(&mt->active_run),
                              tl_recvec_len(&mt->active_run))) {
        return false;
    }

    /* OOO head is unsorted during append; do NOT check sortedness here.
     * Sortedness is enforced on head flush or seal. */

    /* Check active_tombs is valid */
    if (!tl_intervals_validate(&mt->active_tombs)) {
        return false;
    }

    /* Check sealed queue bounds */
    if (mt->sealed_len > mt->sealed_max_runs) {
        return false;
    }
    if (mt->sealed_head >= mt->sealed_max_runs) {
        return false;
    }

    /* Check sealed entries are non-NULL */
    for (size_t i = 0; i < mt->sealed_len; i++) {
        if (tl_memtable_sealed_at(mt, i) == NULL) {
            return false;
        }
    }

    return true;
}

#endif /* TL_DEBUG */

/------------------------------------------------------------------------------/
/*   END OF: tl_memtable.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memview.c
/*   FROM: delta/
/*
/******************************************************************************/
#include "tl_memview.h"
#include "../internal/tl_range.h"
#include "../internal/tl_locks.h"
#include "../internal/tl_records.h"
#include <stdlib.h>  /* qsort */
#include <string.h>

/* Test hooks for memview capture retry behavior */
#ifdef TL_TEST_HOOKS
volatile int tl_test_memview_force_retry_count = 0;
volatile int tl_test_memview_used_fallback = 0;
#endif

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Comparison function for qsort.
 * Sorts records by (ts, handle) in non-decreasing order.
 */
static int cmp_record_ts_mv(const void* a, const void* b) {
    const tl_record_t* ra = (const tl_record_t*)a;
    const tl_record_t* rb = (const tl_record_t*)b;

    /* Use explicit comparison to avoid integer overflow in subtraction. */
    if (ra->ts < rb->ts) return -1;
    if (ra->ts > rb->ts) return 1;
    if (ra->handle < rb->handle) return -1;
    if (ra->handle > rb->handle) return 1;
    return 0;
}

/**
 * Update bounds with a record array.
 * Assumes records are sorted by (ts, handle).
 */
static void update_bounds_from_records(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                        bool* has_data,
                                        const tl_record_t* data, size_t len) {
    if (len == 0) {
        return;
    }

    tl_ts_t rec_min = data[0].ts;
    tl_ts_t rec_max = data[len - 1].ts;

    if (!*has_data) {
        *min_ts = rec_min;
        *max_ts = rec_max;
        *has_data = true;
    } else {
        if (rec_min < *min_ts) *min_ts = rec_min;
        if (rec_max > *max_ts) *max_ts = rec_max;
    }
}

/**
 * Update bounds with an unsorted record array (scan).
 */
static void update_bounds_from_records_unsorted(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                                 bool* has_data,
                                                 const tl_record_t* data, size_t len) {
    if (len == 0) {
        return;
    }

    tl_ts_t rec_min = data[0].ts;
    tl_ts_t rec_max = rec_min;
    for (size_t i = 1; i < len; i++) {
        rec_min = TL_MIN(rec_min, data[i].ts);
        rec_max = TL_MAX(rec_max, data[i].ts);
    }

    if (!*has_data) {
        *min_ts = rec_min;
        *max_ts = rec_max;
        *has_data = true;
    } else {
        if (rec_min < *min_ts) *min_ts = rec_min;
        if (rec_max > *max_ts) *max_ts = rec_max;
    }
}

/**
 * Update bounds with OOO runs (using per-run min/max).
 */
static void update_bounds_from_runs(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                     bool* has_data,
                                     const tl_ooorunset_t* runs) {
    if (runs == NULL || runs->total_len == 0) {
        return;
    }

    tl_ts_t rec_min = TL_TS_MAX;
    tl_ts_t rec_max = TL_TS_MIN;
    for (size_t i = 0; i < runs->count; i++) {
        const tl_ooorun_t* run = runs->runs[i];
        rec_min = TL_MIN(rec_min, run->min_ts);
        rec_max = TL_MAX(rec_max, run->max_ts);
    }

    if (!*has_data) {
        *min_ts = rec_min;
        *max_ts = rec_max;
        *has_data = true;
    } else {
        if (rec_min < *min_ts) *min_ts = rec_min;
        if (rec_max > *max_ts) *max_ts = rec_max;
    }
}

/**
 * Update bounds with tombstone intervals.
 * Tombstones contribute to bounds per read-path overlap rules.
 */
static void update_bounds_from_tombs(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                      bool* has_data,
                                      const tl_interval_t* data, size_t len) {
    if (len == 0) {
        return;
    }

    /* Min is first interval's start (intervals are sorted by start) */
    tl_ts_t tomb_min = data[0].start;

    /* Max is determined by last interval's end (or TL_TS_MAX if unbounded) */
    const tl_interval_t* last = &data[len - 1];
    tl_ts_t tomb_max;
    if (last->end_unbounded) {
        tomb_max = TL_TS_MAX;
    } else {
        /*
         * Tombstone [start, end) covers timestamps up to end-1.
         * For overlap checking, we use end-1 as the max bound.
         * However, we must be careful: if end == TL_TS_MIN (impossible
         * for a valid interval), subtracting would underflow.
         * Valid intervals have start < end, so end > TL_TS_MIN.
         */
        tomb_max = last->end - 1;
    }

    if (!*has_data) {
        *min_ts = tomb_min;
        *max_ts = tomb_max;
        *has_data = true;
    } else {
        if (tomb_min < *min_ts) *min_ts = tomb_min;
        if (tomb_max > *max_ts) *max_ts = tomb_max;
    }
}

/**
 * Update bounds from a memrun.
 */
static void update_bounds_from_memrun(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                       bool* has_data,
                                       const tl_memrun_t* mr) {
    /*
     * Memrun has precomputed bounds that already include tombstones.
     * However, we need to check if it has data first.
     */
    bool mr_has_records = tl_memrun_has_records(mr);
    bool mr_has_tombs = tl_memrun_has_tombstones(mr);

    if (!mr_has_records && !mr_has_tombs) {
        return;
    }

    tl_ts_t mr_min = tl_memrun_min_ts(mr);
    tl_ts_t mr_max = tl_memrun_max_ts(mr);

    if (!*has_data) {
        *min_ts = mr_min;
        *max_ts = mr_max;
        *has_data = true;
    } else {
        if (mr_min < *min_ts) *min_ts = mr_min;
        if (mr_max > *max_ts) *max_ts = mr_max;
    }
}

/**
 * Deep-copy a record array.
 *
 * C-07 fix: Changed to return status for distinguishing errors.
 *
 * @param alloc   Allocator context
 * @param src     Source record array (may be NULL if len == 0)
 * @param len     Number of records
 * @param out     Output: copied array (set to NULL on error or len==0)
 * @return TL_OK on success (including len==0),
 *         TL_EINVAL if len > 0 but src == NULL,
 *         TL_EOVERFLOW if len * sizeof(tl_record_t) would overflow,
 *         TL_ENOMEM on allocation failure
 */
/**
 * Deep-copy an interval array.
 *
 * C-07 fix: Changed to return status for distinguishing errors.
 *
 * @param alloc   Allocator context
 * @param src     Source interval array (may be NULL if len == 0)
 * @param len     Number of intervals
 * @param out     Output: copied array (set to NULL on error or len==0)
 * @return TL_OK on success (including len==0),
 *         TL_EINVAL if len > 0 but src == NULL,
 *         TL_EOVERFLOW if len * sizeof(tl_interval_t) would overflow,
 *         TL_ENOMEM on allocation failure
 */
static tl_status_t copy_intervals(tl_alloc_ctx_t* alloc,
                                   const tl_interval_t* src, size_t len,
                                   tl_interval_t** out) {
    *out = NULL;

    if (len == 0) {
        return TL_OK;  /* Success, no allocation needed */
    }

    if (src == NULL) {
        return TL_EINVAL;  /* Error: non-zero len but NULL src */
    }

    /* C-07 fix: Check for size overflow before multiplication */
    if (tl__alloc_would_overflow(len, sizeof(tl_interval_t))) {
        return TL_EOVERFLOW;
    }

    size_t bytes = len * sizeof(tl_interval_t);
    tl_interval_t* dst = tl__malloc(alloc, bytes);
    if (dst == NULL) {
        return TL_ENOMEM;
    }

    memcpy(dst, src, bytes);
    *out = dst;
    return TL_OK;
}

/**
 * Allocate and populate sealed memrun array.
 * Acquires references to each memrun.
 * On failure, releases any already-acquired references.
 */
static tl_status_t copy_sealed_memruns(tl_memview_t* mv,
                                        const tl_memtable_t* mt,
                                        tl_mutex_t* memtable_mu) {
    const int max_retries = 3;

    for (int attempt = 0; attempt < max_retries; attempt++) {
        size_t len = 0;
        size_t head = 0;
        uint64_t epoch = 0;

        /* Phase 1: snapshot sealed queue metadata under lock */
        TL_LOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        len = mt->sealed_len;
        head = mt->sealed_head;
        epoch = mt->sealed_epoch;
        if (len == 0) {
            mv->sealed = NULL;
            mv->sealed_len = 0;
            TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
            return TL_OK;
        }
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);

        /* C-07 fix: Check for size overflow before multiplication */
        if (tl__alloc_would_overflow(len, sizeof(tl_memrun_t*))) {
            return TL_EOVERFLOW;
        }

        /* Phase 2: allocate outside lock */
        tl_memrun_t** sealed = (tl_memrun_t**)tl__malloc(mv->alloc,
                                                          len * sizeof(tl_memrun_t*));
        if (sealed == NULL) {
            return TL_ENOMEM;
        }

        /* Phase 3: re-lock and verify queue unchanged */
        TL_LOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        if (mt->sealed_len != len ||
            mt->sealed_head != head ||
            mt->sealed_epoch != epoch) {
            TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
            tl__free(mv->alloc, (void*)sealed);
            continue; /* retry */
        }

#ifdef TL_TEST_HOOKS
        if (tl_test_memview_force_retry_count > 0) {
            tl_test_memview_force_retry_count--;
            TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
            tl__free(mv->alloc, sealed);
            continue; /* forced retry */
        }
#endif

        /* Copy pointers and acquire each memrun */
        for (size_t i = 0; i < len; i++) {
            tl_memrun_t* mr = tl_memtable_sealed_at(mt, i);
            sealed[i] = tl_memrun_acquire(mr);
        }
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);

        mv->sealed = sealed;
        mv->sealed_len = len;
        return TL_OK;
    }

    /*
     * Fallback: allocate and acquire under lock to avoid livelock.
     * This is the pre-existing behavior.
     */
#ifdef TL_TEST_HOOKS
    tl_test_memview_used_fallback = 1;
#endif
    TL_LOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);

    size_t len = mt->sealed_len;
    if (len == 0) {
        mv->sealed = NULL;
        mv->sealed_len = 0;
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        return TL_OK;
    }

    if (tl__alloc_would_overflow(len, sizeof(tl_memrun_t*))) {
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        return TL_EOVERFLOW;
    }

    tl_memrun_t** sealed = (tl_memrun_t**)tl__malloc(mv->alloc,
                                                      len * sizeof(tl_memrun_t*));
    if (sealed == NULL) {
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        return TL_ENOMEM;
    }

    for (size_t i = 0; i < len; i++) {
        tl_memrun_t* mr = tl_memtable_sealed_at(mt, i);
        sealed[i] = tl_memrun_acquire(mr);
    }

    mv->sealed = sealed;
    mv->sealed_len = len;
    TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
    return TL_OK;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_memview_capture(tl_memview_t* mv,
                                const tl_memtable_t* mt,
                                tl_mutex_t* memtable_mu,
                                tl_alloc_ctx_t* alloc) {
    TL_ASSERT(mv != NULL);
    TL_ASSERT(mt != NULL);
    TL_ASSERT(memtable_mu != NULL);
    TL_ASSERT(alloc != NULL);

    /* Initialize to empty state */
    memset(mv, 0, sizeof(*mv));
    mv->alloc = alloc;
    mv->has_data = false;

    tl_status_t status;

    /*
     * Step 1: Copy active buffers.
     * Caller holds writer_mu which protects active state.
     *
     * C-07 fix: Use new signatures that return status and preserve
     * distinct error codes (TL_EOVERFLOW, TL_ENOMEM, TL_EINVAL).
     */

    /* Copy active_run */
    size_t run_len = tl_memtable_run_len(mt);
    status = tl_records_copy(alloc, tl_memtable_run_data(mt), run_len, &mv->active_run);
    if (status != TL_OK) {
        goto fail;
    }
    mv->active_run_len = run_len;

    /* Copy OOO head */
    size_t ooo_head_len = tl_memtable_ooo_head_len(mt);
    status = tl_records_copy(alloc, tl_memtable_ooo_head_data(mt), ooo_head_len,
                              &mv->active_ooo_head);
    if (status != TL_OK) {
        goto fail;
    }
    mv->active_ooo_head_len = ooo_head_len;
    mv->active_ooo_head_sorted = mt->ooo_head_sorted;

    /* Pin OOO runs */
    mv->active_ooo_runs = tl_ooorunset_acquire(
                            (tl_ooorunset_t*)tl_memtable_ooo_runs(mt));
    mv->active_ooo_total_len = ooo_head_len +
                               tl_ooorunset_total_len(mv->active_ooo_runs);

    /* Copy active_tombs */
    tl_intervals_imm_t tombs_imm = tl_memtable_tombs_imm(mt);
    status = copy_intervals(alloc, tombs_imm.data, tombs_imm.len, &mv->active_tombs);
    if (status != TL_OK) {
        goto fail;
    }
    mv->active_tombs_len = tombs_imm.len;

    /*
     * Step 2: Pin sealed memruns.
     * This function locks memtable_mu internally.
     */
    status = copy_sealed_memruns(mv, mt, memtable_mu);
    if (status != TL_OK) {
        goto fail;
    }

    /*
     * Step 3: Compute bounds.
     * Include records AND tombstones per read-path overlap rules.
     */
    update_bounds_from_records(&mv->min_ts, &mv->max_ts, &mv->has_data,
                               mv->active_run, mv->active_run_len);
    update_bounds_from_records_unsorted(&mv->min_ts, &mv->max_ts, &mv->has_data,
                                        mv->active_ooo_head, mv->active_ooo_head_len);
    update_bounds_from_runs(&mv->min_ts, &mv->max_ts, &mv->has_data,
                            mv->active_ooo_runs);
    update_bounds_from_tombs(&mv->min_ts, &mv->max_ts, &mv->has_data,
                             mv->active_tombs, mv->active_tombs_len);

    for (size_t i = 0; i < mv->sealed_len; i++) {
        update_bounds_from_memrun(&mv->min_ts, &mv->max_ts, &mv->has_data,
                                  mv->sealed[i]);
    }

    return TL_OK;

fail:
    tl_memview_destroy(mv);
    return status;
}

void tl_memview_sort_head(tl_memview_t* mv) {
    if (mv == NULL) {
        return;
    }

    if (mv->active_ooo_head_sorted) {
        return;
    }

    if (mv->active_ooo_head_len > 1) {
        qsort(mv->active_ooo_head,
              mv->active_ooo_head_len,
              sizeof(tl_record_t),
              cmp_record_ts_mv);
    }

    mv->active_ooo_head_sorted = true;
}

void tl_memview_destroy(tl_memview_t* mv) {
    if (mv == NULL) {
        return;
    }

    /* Free copied active buffers */
    if (mv->active_run != NULL) {
        tl__free(mv->alloc, mv->active_run);
        mv->active_run = NULL;
    }
    mv->active_run_len = 0;

    if (mv->active_ooo_head != NULL) {
        tl__free(mv->alloc, mv->active_ooo_head);
        mv->active_ooo_head = NULL;
    }
    mv->active_ooo_head_len = 0;
    mv->active_ooo_head_sorted = false;

    if (mv->active_ooo_runs != NULL) {
        tl_ooorunset_release(mv->active_ooo_runs);
        mv->active_ooo_runs = NULL;
    }
    mv->active_ooo_total_len = 0;

    if (mv->active_tombs != NULL) {
        tl__free(mv->alloc, mv->active_tombs);
        mv->active_tombs = NULL;
    }
    mv->active_tombs_len = 0;

    /* Release pinned sealed memruns */
    if (mv->sealed != NULL) {
        for (size_t i = 0; i < mv->sealed_len; i++) {
            if (mv->sealed[i] != NULL) {
                tl_memrun_release(mv->sealed[i]);
            }
        }
        tl__free(mv->alloc, (void*)mv->sealed);
        mv->sealed = NULL;
    }
    mv->sealed_len = 0;

    /* Reset bounds */
    mv->min_ts = 0;
    mv->max_ts = 0;
    mv->has_data = false;
}

/*===========================================================================
 * Shared Memview (Snapshot Cache)
 *===========================================================================*/

tl_status_t tl_memview_shared_capture(tl_memview_shared_t** out,
                                       const tl_memtable_t* mt,
                                       tl_mutex_t* memtable_mu,
                                       tl_alloc_ctx_t* alloc,
                                       uint64_t epoch) {
    TL_ASSERT(out != NULL);
    TL_ASSERT(mt != NULL);
    TL_ASSERT(memtable_mu != NULL);
    TL_ASSERT(alloc != NULL);

    *out = NULL;

    tl_memview_shared_t* mv = TL_NEW(alloc, tl_memview_shared_t);
    if (mv == NULL) {
        return TL_ENOMEM;
    }

    memset(mv, 0, sizeof(*mv));
    mv->epoch = epoch;
    tl_atomic_init_u32(&mv->refcnt, 1);

    tl_status_t st = tl_memview_capture(&mv->view, mt, memtable_mu, alloc);
    if (st != TL_OK) {
        tl__free(alloc, mv);
        return st;
    }

    *out = mv;
    return TL_OK;
}

tl_memview_shared_t* tl_memview_shared_acquire(tl_memview_shared_t* mv) {
    if (mv == NULL) {
        return NULL;
    }

    tl_atomic_fetch_add_u32(&mv->refcnt, 1, TL_MO_RELAXED);
    return mv;
}

void tl_memview_shared_release(tl_memview_shared_t* mv) {
    if (mv == NULL) {
        return;
    }

    uint32_t old = tl_atomic_fetch_sub_u32(&mv->refcnt, 1, TL_MO_RELEASE);
    TL_ASSERT(old >= 1);

    if (old == 1) {
        tl_atomic_fence(TL_MO_ACQUIRE);
        tl_memview_destroy(&mv->view);
        tl__free(mv->view.alloc, mv);
    }
}

/*===========================================================================
 * Query Support
 *===========================================================================*/

bool tl_memview_overlaps(const tl_memview_t* mv, tl_ts_t t1, tl_ts_t t2,
                         bool t2_unbounded) {
    TL_ASSERT(mv != NULL);

    if (!mv->has_data) {
        return false;
    }

    /*
     * Use tl_range_overlaps from tl_range.h.
     * Memview bounds are [min_ts, max_ts] (inclusive).
     * Query range is [t1, t2) or [t1, +inf).
     */
    return tl_range_overlaps(mv->min_ts, mv->max_ts, t1, t2, t2_unbounded);
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/* Include for tl_intervals_arr_validate */
#include "../internal/tl_intervals.h"
#include "../internal/tl_recvec.h"

/**
 * Validate memview invariants.
 *
 * Invariants:
 * 1. active_run is sorted (non-decreasing timestamps)
 * 2. active_ooo_head is sorted (ts, handle)
 * 3. active_ooo_runs are valid and gen-ordered
 * 4. active_tombs is valid (sorted, non-overlapping, coalesced)
 * 5. sealed memrun pointers non-NULL
 * 6. has_data consistent with actual content
 */
bool tl_memview_validate(const tl_memview_t* mv) {
    if (mv == NULL) {
        return false;
    }

    /*
     * Invariant 1: active_run is sorted (non-decreasing timestamps)
     *
     * Use accessor functions for encapsulation.
     */
    const tl_record_t* run = tl_memview_run_data(mv);
    size_t run_len = tl_memview_run_len(mv);
    for (size_t i = 1; i < run_len; i++) {
        if (run[i].ts < run[i - 1].ts) {
            return false;
        }
    }
    if (!tl_records_validate_bounds(run, run_len, mv->min_ts, mv->max_ts)) {
        return false;
    }

    /*
     * Invariant 2: active_ooo_head is sorted (ts, handle) iff marked sorted.
     * During two-phase capture, head may be unsorted until post-lock sort.
     */
    const tl_record_t* ooo_head = tl_memview_ooo_head_data(mv);
    size_t ooo_head_len = tl_memview_ooo_head_len(mv);
    if (mv->active_ooo_head_sorted) {
        for (size_t i = 1; i < ooo_head_len; i++) {
            if (ooo_head[i].ts < ooo_head[i - 1].ts) {
                return false;
            }
            if (ooo_head[i].ts == ooo_head[i - 1].ts &&
                ooo_head[i].handle < ooo_head[i - 1].handle) {
                return false;
            }
        }
    }
    if (!tl_records_validate_bounds(ooo_head, ooo_head_len, mv->min_ts, mv->max_ts)) {
        return false;
    }

    /*
     * Invariant 3: active_ooo_runs are valid and gen-ordered
     */
    const tl_ooorunset_t* runs = tl_memview_ooo_runs(mv);
    if (runs != NULL) {
        size_t total = 0;
        uint64_t last_gen = 0;
        bool have_gen = false;
        for (size_t i = 0; i < runs->count; i++) {
            const tl_ooorun_t* run_ptr = runs->runs[i];
            if (run_ptr == NULL) {
                return false;
            }
            for (size_t j = 1; j < run_ptr->len; j++) {
                if (run_ptr->records[j].ts < run_ptr->records[j - 1].ts) {
                    return false;
                }
                if (run_ptr->records[j].ts == run_ptr->records[j - 1].ts &&
                    run_ptr->records[j].handle < run_ptr->records[j - 1].handle) {
                    return false;
                }
            }
            if (have_gen && run_ptr->gen < last_gen) {
                return false;
            }
            have_gen = true;
            last_gen = run_ptr->gen;
            if (run_ptr->len > SIZE_MAX - total) {
                return false;
            }
            total += run_ptr->len;
            if (!tl_records_validate_bounds(run_ptr->records, run_ptr->len,
                                            mv->min_ts, mv->max_ts)) {
                return false;
            }
        }
        if (total + ooo_head_len != mv->active_ooo_total_len) {
            return false;
        }
    } else if (ooo_head_len != mv->active_ooo_total_len) {
        return false;
    }

    /*
     * Invariant 4: active_tombs is valid
     *
     * Uses the shared tl_intervals_arr_validate() function.
     */
    const tl_interval_t* tombs = tl_memview_tomb_data(mv);
    size_t tombs_len = tl_memview_tomb_len(mv);
    if (!tl_intervals_arr_validate(tombs, tombs_len)) {
        return false;
    }

    /*
     * Invariant 5: sealed memrun pointers non-NULL
     */
    size_t sealed_len = tl_memview_sealed_len(mv);
    for (size_t i = 0; i < sealed_len; i++) {
        if (tl_memview_sealed_get(mv, i) == NULL) {
            return false;
        }
    }

    /*
     * Invariant 6: has_data consistency
     *
     * If has_data is true, there must be some content.
     * Content can be: records in run, records in OOO head/runs,
     * tombstones, or sealed memruns.
     */
    if (tl_memview_has_data(mv)) {
        bool has_content = (run_len > 0 || mv->active_ooo_total_len > 0 ||
                           tombs_len > 0 || sealed_len > 0);
        if (!has_content) {
            return false;  /* has_data true but no content */
        }
    }

    return true;
}

#endif /* TL_DEBUG */

/------------------------------------------------------------------------------/
/*   END OF: tl_memview.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_ooorun.c
/*   FROM: delta/
/*
/******************************************************************************/
#include "tl_ooorun.h"

/*===========================================================================
 * Run Lifecycle
 *===========================================================================*/

tl_status_t tl_ooorun_create(tl_alloc_ctx_t* alloc,
                              tl_record_t* records, size_t len,
                              uint64_t gen,
                              tl_ooorun_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    if (len == 0 || records == NULL) {
        return TL_EINVAL;
    }

#ifdef TL_DEBUG
    /* Verify records are sorted by (ts, handle) */
    for (size_t i = 1; i < len; i++) {
        TL_ASSERT(records[i - 1].ts < records[i].ts ||
                  (records[i - 1].ts == records[i].ts &&
                   records[i - 1].handle <= records[i].handle));
    }
#endif

    tl_ooorun_t* run = TL_NEW(alloc, tl_ooorun_t);
    if (run == NULL) {
        return TL_ENOMEM;
    }

    run->alloc = alloc;
    run->records = records;
    run->len = len;
    run->gen = gen;

    run->min_ts = records[0].ts;
    run->max_ts = records[len - 1].ts;

    tl_atomic_init_u32(&run->refcnt, 1);

    *out = run;
    return TL_OK;
}

tl_ooorun_t* tl_ooorun_acquire(tl_ooorun_t* run) {
    if (run == NULL) {
        return NULL;
    }

    tl_atomic_fetch_add_u32(&run->refcnt, 1, TL_MO_RELAXED);
    return run;
}

void tl_ooorun_release(tl_ooorun_t* run) {
    if (run == NULL) {
        return;
    }

    uint32_t old = tl_atomic_fetch_sub_u32(&run->refcnt, 1, TL_MO_RELEASE);
    TL_ASSERT(old >= 1);

    if (old == 1) {
        tl_atomic_fence(TL_MO_ACQUIRE);
        tl__free(run->alloc, run->records);
        tl__free(run->alloc, run);
    }
}

/*===========================================================================
 * Runset Lifecycle
 *===========================================================================*/

tl_status_t tl_ooorunset_create(tl_alloc_ctx_t* alloc,
                                 tl_ooorun_t* const* runs,
                                 size_t count,
                                 tl_ooorunset_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    if (count == 0 || runs == NULL) {
        return TL_EINVAL;
    }

    if (count > (SIZE_MAX - sizeof(tl_ooorunset_t)) / sizeof(tl_ooorun_t*)) {
        return TL_EOVERFLOW;
    }

    size_t bytes = sizeof(tl_ooorunset_t) + count * sizeof(tl_ooorun_t*);
    tl_ooorunset_t* set = tl__malloc(alloc, bytes);
    if (set == NULL) {
        return TL_ENOMEM;
    }

    tl_atomic_init_u32(&set->refcnt, 1);
    set->alloc = alloc;
    set->count = count;
    set->total_len = 0;

    for (size_t i = 0; i < count; i++) {
        if (runs[i] == NULL) {
            /* NULL run in array - unwind and fail */
            for (size_t j = 0; j < i; j++) {
                tl_ooorun_release(set->runs[j]);
            }
            tl__free(alloc, set);
            return TL_EINVAL;
        }
        set->runs[i] = tl_ooorun_acquire(runs[i]);
        if (runs[i]->len > SIZE_MAX - set->total_len) {
            /* Overflow - unwind */
            for (size_t j = 0; j <= i; j++) {
                tl_ooorun_release(set->runs[j]);
            }
            tl__free(alloc, set);
            return TL_EOVERFLOW;
        }
        set->total_len += runs[i]->len;
    }

    *out = set;
    return TL_OK;
}

tl_status_t tl_ooorunset_append(tl_alloc_ctx_t* alloc,
                                 tl_ooorunset_t* old_set,
                                 tl_ooorun_t* run,
                                 tl_ooorunset_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(run != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    size_t old_count = (old_set == NULL) ? 0 : old_set->count;
    size_t new_count = old_count + 1;

    if (new_count > (SIZE_MAX - sizeof(tl_ooorunset_t)) / sizeof(tl_ooorun_t*)) {
        return TL_EOVERFLOW;
    }

    size_t bytes = sizeof(tl_ooorunset_t) + new_count * sizeof(tl_ooorun_t*);
    tl_ooorunset_t* set = tl__malloc(alloc, bytes);
    if (set == NULL) {
        return TL_ENOMEM;
    }

    tl_atomic_init_u32(&set->refcnt, 1);
    set->alloc = alloc;
    set->count = new_count;
    set->total_len = 0;

    for (size_t i = 0; i < old_count; i++) {
        TL_ASSERT(old_set->runs[i] != NULL);  /* Invariant: valid runsets have no NULL runs */
        set->runs[i] = tl_ooorun_acquire(old_set->runs[i]);
        if (old_set->runs[i]->len > SIZE_MAX - set->total_len) {
            for (size_t j = 0; j <= i; j++) {
                tl_ooorun_release(set->runs[j]);
            }
            tl__free(alloc, set);
            return TL_EOVERFLOW;
        }
        set->total_len += old_set->runs[i]->len;
    }

    set->runs[old_count] = tl_ooorun_acquire(run);
    if (run->len > SIZE_MAX - set->total_len) {
        for (size_t j = 0; j < new_count; j++) {
            tl_ooorun_release(set->runs[j]);
        }
        tl__free(alloc, set);
        return TL_EOVERFLOW;
    }
    set->total_len += run->len;

    *out = set;
    return TL_OK;
}

tl_ooorunset_t* tl_ooorunset_acquire(tl_ooorunset_t* set) {
    if (set == NULL) {
        return NULL;
    }

    tl_atomic_fetch_add_u32(&set->refcnt, 1, TL_MO_RELAXED);
    return set;
}

void tl_ooorunset_release(tl_ooorunset_t* set) {
    if (set == NULL) {
        return;
    }

    uint32_t old = tl_atomic_fetch_sub_u32(&set->refcnt, 1, TL_MO_RELEASE);
    TL_ASSERT(old >= 1);

    if (old == 1) {
        tl_atomic_fence(TL_MO_ACQUIRE);
        for (size_t i = 0; i < set->count; i++) {
            tl_ooorun_release(set->runs[i]);
        }
        tl__free(set->alloc, set);
    }
}

/------------------------------------------------------------------------------/
/*   END OF: tl_ooorun.c
/------------------------------------------------------------------------------/
