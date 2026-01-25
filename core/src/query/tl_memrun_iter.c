#include "tl_memrun_iter.h"
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

tl_status_t tl_memrun_iter_init(tl_memrun_iter_t* it,
                                 const tl_memrun_t* mr,
                                 tl_ts_t t1, tl_ts_t t2,
                                 bool t2_unbounded,
                                 tl_alloc_ctx_t* alloc) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(mr != NULL);
    TL_ASSERT(alloc != NULL);

    memset(it, 0, sizeof(*it));
    it->mr = mr;
    it->t1 = t1;
    it->t2 = t2;
    it->t2_unbounded = t2_unbounded;
    it->done = false;
    it->has_current = false;

    if (!tl_memrun_has_records(mr)) {
        it->done = true;
        return TL_OK;
    }

    if (!tl_range_overlaps(tl_memrun_min_ts(mr), tl_memrun_max_ts(mr),
                           t1, t2, t2_unbounded)) {
        it->done = true;
        return TL_OK;
    }

    size_t run_len = tl_memrun_run_len(mr);
    size_t run_count = tl_memrun_ooo_run_count(mr);

    if (run_count > UINT32_MAX - 1) {
        return TL_EOVERFLOW;
    }

    size_t src_count = 0;
    if (run_len > 0) {
        src_count++;
    }
    for (size_t i = 0; i < run_count; i++) {
        const tl_ooorun_t* run = tl_memrun_ooo_run_at(mr, i);
        if (run != NULL && run->len > 0) {
            src_count++;
        }
    }

    tl_status_t st = tl_submerge_init(&it->merge, alloc, src_count);
    if (st != TL_OK) {
        return st;
    }

    size_t idx = 0;
    if (run_len > 0) {
        init_src(&it->merge.srcs[idx++],
                 tl_memrun_run_data(mr), run_len,
                 t1, t2, t2_unbounded, 0);
    }

    for (size_t i = 0; i < run_count; i++) {
        const tl_ooorun_t* run = tl_memrun_ooo_run_at(mr, i);
        if (run == NULL || run->len == 0) {
            continue;
        }
        init_src(&it->merge.srcs[idx++],
                 run->records, run->len,
                 t1, t2, t2_unbounded,
                 (uint32_t)(1 + i));
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

void tl_memrun_iter_destroy(tl_memrun_iter_t* it) {
    if (it == NULL) {
        return;
    }

    tl_submerge_destroy(&it->merge);
    it->mr = NULL;
    it->done = true;
    it->has_current = false;
}

/*===========================================================================
 * Iteration
 *===========================================================================*/

tl_status_t tl_memrun_iter_next(tl_memrun_iter_t* it, tl_record_t* out) {
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

void tl_memrun_iter_seek(tl_memrun_iter_t* it, tl_ts_t target) {
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
