#include "tl_iter_build.h"

tl_status_t tl_iter_build_submerge(tl_submerge_t* merge,
                                    tl_alloc_ctx_t* alloc,
                                    const tl_record_t* run_data,
                                    const tl_seq_t* run_seqs,
                                    size_t run_len,
                                    tl_seq_t run_watermark,
                                    const tl_ooorunset_t* runs,
                                    const tl_record_t* head_data,
                                    const tl_seq_t* head_seqs,
                                    size_t head_len,
                                    tl_ts_t t1,
                                    tl_ts_t t2,
                                    bool t2_unbounded) {
    TL_ASSERT(merge != NULL);
    TL_ASSERT(alloc != NULL);

    size_t run_count = runs != NULL ? runs->count : 0;
    /* Bounds the tie_id casts below AND keeps the 2 + run_count
     * allocation from wrapping size_t on 32-bit targets. */
    if (run_count > UINT32_MAX - 3) {
        return TL_EOVERFLOW;
    }

    /* Over-allocate: run + head + one slot per OOO run. Spare slots for
     * empty sources are zeroed by tl_submerge_init and never visited
     * (src_count is set to the fill index below). */
    tl_status_t st = tl_submerge_init(merge, alloc, 2 + run_count);
    if (st != TL_OK) {
        return st;
    }

    size_t idx = 0;
    if (run_len > 0 && run_data != NULL) {
        tl_submerge_src_init(&merge->srcs[idx++],
                             run_data, run_seqs, run_len,
                             t1, t2, t2_unbounded,
                             0,
                             run_seqs != NULL ? 0 : run_watermark);
    }

    if (runs != NULL) {
        for (size_t i = 0; i < runs->count; i++) {
            const tl_ooorun_t* run = runs->runs[i];
            if (run == NULL || run->len == 0) {
                continue;
            }
            tl_submerge_src_init(&merge->srcs[idx++],
                                 run->records, NULL, run->len,
                                 t1, t2, t2_unbounded,
                                 (uint32_t)(1 + i),
                                 run->applied_seq);
        }
    }

    if (head_len > 0 && head_data != NULL) {
        tl_submerge_src_init(&merge->srcs[idx++],
                             head_data, head_seqs, head_len,
                             t1, t2, t2_unbounded,
                             (uint32_t)(1 + run_count),
                             0);
    }

    merge->src_count = idx;

    st = tl_submerge_build(merge);
    if (st != TL_OK) {
        tl_submerge_destroy(merge);
        return st;
    }

    return TL_OK;
}
