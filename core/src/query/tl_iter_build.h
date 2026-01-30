#ifndef TL_ITER_BUILD_H
#define TL_ITER_BUILD_H

#include "tl_submerge.h"
#include "../delta/tl_ooorun.h"

/**
 * Build sub-merge sources for (run + OOO runs + optional head).
 *
 * Ordering:
 * - run: tie_id = 0
 * - OOO runs: tie_id = 1 + index
 * - head (if present): tie_id = 1 + run_count (last)
 */
tl_status_t tl_iter_build_submerge(tl_submerge_t* merge,
                                    tl_alloc_ctx_t* alloc,
                                    const tl_record_t* run_data,
                                    size_t run_len,
                                    const tl_ooorunset_t* runs,
                                    const tl_record_t* head_data,
                                    size_t head_len,
                                    tl_ts_t t1,
                                    tl_ts_t t2,
                                    bool t2_unbounded);

#endif /* TL_ITER_BUILD_H */
