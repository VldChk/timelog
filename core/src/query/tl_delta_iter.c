#include "tl_delta_iter.h"
#include "tl_submerge.h"
#include "tl_iter_build.h"
#include "../internal/tl_range.h"
#include <string.h>

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_delta_iter_init_memrun(tl_delta_iter_t* it,
                                      const tl_memrun_t* mr,
                                      tl_ts_t t1, tl_ts_t t2,
                                      bool t2_unbounded,
                                      tl_alloc_ctx_t* alloc) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(mr != NULL);
    TL_ASSERT(alloc != NULL);

    memset(it, 0, sizeof(*it));
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

    /* Memruns carry a single applied_seq watermark, no per-record seqs. */
    tl_status_t st = tl_iter_build_submerge(&it->merge,
                                            alloc,
                                            tl_memrun_run_data(mr),
                                            NULL,
                                            tl_memrun_run_len(mr),
                                            tl_memrun_applied_seq(mr),
                                            tl_memrun_ooo_runs(mr),
                                            NULL,
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

tl_status_t tl_delta_iter_init_memview(tl_delta_iter_t* it,
                                       const tl_memview_t* mv,
                                       tl_ts_t t1, tl_ts_t t2,
                                       bool t2_unbounded,
                                       tl_alloc_ctx_t* alloc) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(mv != NULL);
    TL_ASSERT(alloc != NULL);
    /* OOO head must be sorted before iteration. */
    TL_ASSERT(mv->active_ooo_head_sorted);

    memset(it, 0, sizeof(*it));
    it->t1 = t1;
    it->t2 = t2;
    it->t2_unbounded = t2_unbounded;
    it->done = false;

    tl_status_t st = tl_iter_build_submerge(&it->merge,
                                            alloc,
                                            tl_memview_run_data(mv),
                                            tl_memview_run_seqs(mv),
                                            tl_memview_run_len(mv),
                                            0,
                                            tl_memview_ooo_runs(mv),
                                            tl_memview_ooo_head_data(mv),
                                            tl_memview_ooo_head_seqs(mv),
                                            tl_memview_ooo_head_len(mv),
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

void tl_delta_iter_destroy(tl_delta_iter_t* it) {
    if (it == NULL) {
        return;
    }

    tl_submerge_destroy(&it->merge);
    it->done = true;
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_delta_iter_next(tl_delta_iter_t* it,
                               tl_record_t* out,
                               tl_seq_t* out_watermark) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return TL_EOF;
    }

    tl_record_t rec;
    tl_seq_t watermark = 0;
    tl_status_t st = tl_submerge_next(&it->merge, &rec, &watermark);
    if (st == TL_EOF) {
        it->done = true;
        return TL_EOF;
    }
    if (st != TL_OK) {
        it->done = true;
        return st;
    }

    if (out != NULL) {
        *out = rec;
    }
    if (out_watermark != NULL) {
        *out_watermark = watermark;
    }

    return TL_OK;
}

tl_status_t tl_delta_iter_seek(tl_delta_iter_t* it, tl_ts_t target) {
    TL_ASSERT(it != NULL);

    if (it->done) {
        return TL_OK;
    }

    if (target <= it->t1) {
        return TL_OK;
    }

    if (!it->t2_unbounded && target >= it->t2) {
        it->done = true;
        return TL_OK;
    }

    tl_status_t st = tl_submerge_seek(&it->merge, target);
    if (st != TL_OK) {
        it->done = true;
        return st;
    }
    it->done = tl_submerge_done(&it->merge);
    return TL_OK;
}
