#include "tl_flush.h"
#include "../internal/tl_heap.h"
#include "../internal/tl_intervals.h"
#include "../internal/tl_formal_trace.h"

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
                            tl_segment_t** out_seg,
                            tl_record_t** out_dropped,
                            size_t* out_dropped_len) {
    TL_ASSERT(ctx != NULL);
    TL_ASSERT(ctx->alloc != NULL);
    TL_ASSERT(mr != NULL);
    TL_ASSERT(out_seg != NULL);
    TL_ASSERT(out_dropped != NULL);
    TL_ASSERT(out_dropped_len != NULL);
    TL_ASSERT(ctx->applied_seq > 0);

    if (ctx->applied_seq == 0) {
        return TL_EINVAL;
    }
    for (size_t i = 0; i < ctx->tombs.len; i++) {
        if (ctx->tombs.data[i].max_seq > ctx->applied_seq) {
            return TL_EINVAL;
        }
    }

    *out_seg = NULL;
    *out_dropped = NULL;
    *out_dropped_len = 0;

    tl_formal_trace_emit(&(tl_formal_trace_event_t){
        .ev = "flush_build",
        .seq = ctx->applied_seq,
        .t1 = tl_memrun_min_ts(mr),
        .t2 = tl_memrun_max_ts(mr),
        .src0 = (uint64_t)mr->run_len,
        .src1 = (uint64_t)mr->ooo_total_len,
        .wm0 = (uint64_t)ctx->applied_seq,
        .wm1 = (uint64_t)mr->applied_seq,
        .status = TL_OK
    });

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
                                        ctx->applied_seq,
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

    tl_record_t* dropped = NULL;
    size_t dropped_len = 0;
    size_t dropped_cap = 0;

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
        tl_seq_t           watermark;
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
        srcs[src_idx].watermark = mr->applied_seq;
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
            srcs[src_idx].watermark = run->applied_seq;
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
            .watermark = srcs[i].watermark,
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

    tl_intervals_cursor_t tomb_cursor;
    tl_intervals_cursor_init(&tomb_cursor, ctx->tombs);

    size_t i = 0;
    while (!tl_heap_is_empty(&heap)) {
        const tl_heap_entry_t* top = tl_heap_peek(&heap);
        TL_ASSERT(top != NULL);
        tl_seq_t tomb_seq = 0;
        if (ctx->tombs.len > 0) {
            tomb_seq = tl_intervals_cursor_max_seq(&tomb_cursor, top->ts);
        }
        /* Tie semantics: tomb_seq == watermark → record kept (strict >).
         * The tombstone was already applied at build time and this record survived. */
        if (tomb_seq <= top->watermark) {
            merged[i].ts = top->ts;
            merged[i].handle = top->handle;
            i++;
        } else if (ctx->collect_drops) {
            if (dropped_len >= dropped_cap) {
                size_t new_cap = (dropped_cap == 0) ? 64 : dropped_cap * 2;
                if (tl__alloc_would_overflow(new_cap, sizeof(tl_record_t))) {
                    tl_heap_destroy(&heap);
                    tl__free(ctx->alloc, srcs);
                    tl__free(ctx->alloc, merged);
                    tl__free(ctx->alloc, dropped);
                    return TL_EOVERFLOW;
                }
                tl_record_t* new_arr = tl__realloc(ctx->alloc, dropped,
                                                   new_cap * sizeof(tl_record_t));
                if (new_arr == NULL) {
                    tl_heap_destroy(&heap);
                    tl__free(ctx->alloc, srcs);
                    tl__free(ctx->alloc, merged);
                    tl__free(ctx->alloc, dropped);
                    return TL_ENOMEM;
                }
                dropped = new_arr;
                dropped_cap = new_cap;
            }
            dropped[dropped_len].ts = top->ts;
            dropped[dropped_len].handle = top->handle;
            dropped_len++;
        }

        flush_src_t* src = (flush_src_t*)top->iter;
        uint32_t tie_id = top->tie_break_key;
        if (src->pos < src->end) {
            const tl_record_t* rec = &src->data[src->pos++];
            tl_heap_entry_t entry = {
                .ts = rec->ts,
                .tie_break_key = tie_id,
                .handle = rec->handle,
                .watermark = src->watermark,
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

    size_t kept = i;

    /*
     * Step 6: Build L0 segment from merged records and tombstones.
     */
    if (kept == 0) {
        if (mr->tombs_len > 0) {
            st = tl_segment_build_l0(ctx->alloc,
                                     NULL, 0,
                                     mr->tombs, mr->tombs_len,
                                     ctx->target_page_bytes,
                                     ctx->generation,
                                     ctx->applied_seq,
                                     out_seg);
        } else {
            st = TL_OK;
            *out_seg = NULL;
        }
    } else {
        st = tl_segment_build_l0(ctx->alloc,
                                 merged, kept,
                                 mr->tombs, mr->tombs_len,
                                 ctx->target_page_bytes,
                                 ctx->generation,
                                 ctx->applied_seq,
                                 out_seg);
    }

    /*
     * Step 7: Free merged buffer regardless of build result.
     */
    tl__free(ctx->alloc, merged);

    if (st != TL_OK) {
        tl__free(ctx->alloc, dropped);
        return st;
    }

    *out_dropped = dropped;
    *out_dropped_len = dropped_len;

    tl_formal_trace_emit(&(tl_formal_trace_event_t){
        .ev = "flush_build_done",
        .seq = ctx->applied_seq,
        .t1 = tl_memrun_min_ts(mr),
        .t2 = tl_memrun_max_ts(mr),
        .src0 = (uint64_t)kept,
        .src1 = (uint64_t)dropped_len,
        .wm0 = (uint64_t)ctx->applied_seq,
        .status = TL_OK
    });

    return TL_OK;
}
