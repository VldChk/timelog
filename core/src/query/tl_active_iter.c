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
