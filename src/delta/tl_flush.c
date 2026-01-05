#include "tl_flush.h"

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
    if (mr->run_len > SIZE_MAX - mr->ooo_len) {
        return TL_EOVERFLOW;
    }

    size_t total_records = mr->run_len + mr->ooo_len;

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
     * Step 5: Merge run + ooo into merged[] using two-way merge iterator.
     * The iterator produces records in sorted order (stable: prefers run on ties).
     */
    tl_merge_iter_t it;
    tl_merge_iter_init(&it, mr->run, mr->run_len, mr->ooo, mr->ooo_len);

    size_t i = 0;
    while (!tl_merge_iter_done(&it)) {
        const tl_record_t* rec = tl_merge_iter_next(&it);
        TL_ASSERT(rec != NULL); /* Should not be NULL if not done */
        merged[i++] = *rec;
    }

    TL_ASSERT(i == total_records);

    /*
     * Step 6: Build L0 segment from merged records and tombstones.
     */
    tl_status_t st = tl_segment_build_l0(ctx->alloc,
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
