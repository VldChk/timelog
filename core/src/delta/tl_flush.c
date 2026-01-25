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
            .component_id = srcs[i].tie_id,
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
        uint32_t component_id = top->component_id;
        if (src->pos < src->end) {
            const tl_record_t* rec = &src->data[src->pos++];
            tl_heap_entry_t entry = {
                .ts = rec->ts,
                .component_id = component_id,
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
