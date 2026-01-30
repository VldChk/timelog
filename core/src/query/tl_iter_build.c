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
