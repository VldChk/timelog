#include "tl_active_iter.h"
#include "tl_submerge.h"
#include "../internal/tl_range.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

static void init_src(tl_subsrc_t* src,
                      const tl_record_t* data,
                      size_t len,
                      tl_ts_t t1,
                      tl_ts_t t2,
                      bool t2_unbounded,
                      uint32_t tie_id) {
    src->data = data;
    src->len = len;
    src->tie_id = tie_id;

    src->pos = tl_submerge_lower_bound(data, len, t1);
    if (t2_unbounded) {
        src->end = len;
    } else {
        src->end = tl_submerge_lower_bound(data, len, t2);
    }

    if (src->pos > src->end) {
        src->pos = src->end;
    }
}

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
    it->has_current = false;

    size_t run_len = tl_memview_run_len(mv);
    size_t head_len = tl_memview_ooo_head_len(mv);
    const tl_ooorunset_t* runs = tl_memview_ooo_runs(mv);
    size_t run_count = runs != NULL ? runs->count : 0;

    if (run_len == 0 && head_len == 0 && run_count == 0) {
        it->done = true;
        return TL_OK;
    }

    if (run_count > UINT32_MAX - 1) {
        return TL_EOVERFLOW;
    }

    size_t src_count = 0;
    if (run_len > 0) {
        src_count++;
    }
    if (head_len > 0) {
        src_count++;
    }
    if (runs != NULL) {
        for (size_t i = 0; i < runs->count; i++) {
            if (runs->runs[i] != NULL && runs->runs[i]->len > 0) {
                src_count++;
            }
        }
    }

    tl_status_t st = tl_submerge_init(&it->merge, alloc, src_count);
    if (st != TL_OK) {
        return st;
    }

    size_t idx = 0;
    if (run_len > 0) {
        init_src(&it->merge.srcs[idx++],
                 tl_memview_run_data(mv), run_len,
                 t1, t2, t2_unbounded, 0);
    }

    if (runs != NULL) {
        for (size_t i = 0; i < runs->count; i++) {
            const tl_ooorun_t* run = runs->runs[i];
            if (run == NULL || run->len == 0) {
                continue;
            }
            init_src(&it->merge.srcs[idx++],
                     run->records, run->len,
                     t1, t2, t2_unbounded,
                     (uint32_t)(1 + i));
        }
    }

    if (head_len > 0) {
        init_src(&it->merge.srcs[idx++],
                 tl_memview_ooo_head_data(mv), head_len,
                 t1, t2, t2_unbounded,
                 (uint32_t)(1 + run_count));
    }

    it->merge.src_count = idx;

    st = tl_submerge_build(&it->merge);
    if (st != TL_OK) {
        tl_submerge_destroy(&it->merge);
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
    it->has_current = false;
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
        it->has_current = false;
        return TL_EOF;
    }

    it->current = rec;
    it->has_current = true;
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
        it->has_current = false;
        return;
    }

    tl_submerge_seek(&it->merge, target);
    it->done = tl_submerge_done(&it->merge);
    it->has_current = false;
}
