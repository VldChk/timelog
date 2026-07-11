#include "tl_flush.h"
#include "../internal/tl_heap.h"
#include "../internal/tl_intervals.h"
#include "../internal/tl_recvec.h"

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

    /* Reject before allocating: the combined record count must fit in size_t,
     * otherwise the merge buffer sizing below would silently wrap. */
    if (mr->run_len > SIZE_MAX - mr->ooo_total_len) {
        return TL_EOVERFLOW;
    }

    size_t total_records = mr->run_len + mr->ooo_total_len;

    if (total_records == 0) {
        if (mr->tombs_len > 0) {
            /* No records survived but tombstones still need to be published so the
             * read path can suppress matching records from older segments. */
            return tl_segment_build_l0(ctx->alloc,
                                        NULL, 0,
                                        mr->tombs, mr->tombs_len,
                                        ctx->target_page_bytes,
                                        ctx->generation,
                                        ctx->applied_seq,
                                        out_seg);
        } else {
            return TL_EINVAL;
        }
    }

    if (total_records > SIZE_MAX / sizeof(tl_record_t)) {
        return TL_EOVERFLOW;
    }

    size_t merged_size = total_records * sizeof(tl_record_t);
    tl_record_t* merged = tl__malloc(ctx->alloc, merged_size);
    if (merged == NULL) {
        return TL_ENOMEM;
    }

    tl_recvec_t dropped_vec;
    tl_recvec_init(&dropped_vec, ctx->alloc);

    /* Stable k-way merge across the in-order run and every OOO run. Tie-break
     * key is the source's tie_id (active_run=0, OOO runs=1..N in generation
     * order), guaranteeing equal-timestamp records keep their relative order. */
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
        /* Strict greater-than: a tombstone with seq equal to the source's
         * watermark was already applied at build time, so the record was
         * deliberately retained and must survive the merge. */
        if (tomb_seq <= top->watermark) {
            merged[i].ts = top->ts;
            merged[i].handle = top->handle;
            i++;
        } else if (ctx->collect_drops) {
            st = tl_recvec_push(&dropped_vec, top->ts, top->handle);
            if (st != TL_OK) {
                tl_heap_destroy(&heap);
                tl__free(ctx->alloc, srcs);
                tl__free(ctx->alloc, merged);
                tl_recvec_destroy(&dropped_vec);
                return st;
            }
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

    tl__free(ctx->alloc, merged);

    if (st != TL_OK) {
        tl_recvec_destroy(&dropped_vec);
        return st;
    }

    size_t dropped_len = 0;
    tl_record_t* dropped = tl_recvec_take(&dropped_vec, &dropped_len);
    if (dropped_len == 0 && dropped != NULL) {
        /* Normalize a reserved-but-empty take so out_dropped is NULL exactly
         * when nothing was dropped. */
        tl__free(ctx->alloc, dropped);
        dropped = NULL;
    }
    *out_dropped = dropped;
    *out_dropped_len = dropped_len;

    return TL_OK;
}
