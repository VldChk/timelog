#include "../internal/tl_flush.h"
#include "../internal/tl_tombstones.h"
#include <string.h>

/*
 * Compute records per page based on target bytes.
 *
 * Layout: page header + ts[] + handle[]
 * Minimum 128 records per page.
 */
static uint32_t compute_page_capacity(size_t target_bytes) {
    /* Rough header estimate */
    size_t header_size = 64;  /* Conservative */
    size_t record_size = sizeof(tl_ts_t) + sizeof(tl_handle_t);

    if (target_bytes <= header_size) {
        return 128;  /* Minimum */
    }

    uint32_t capacity = (uint32_t)((target_bytes - header_size) / record_size);
    if (capacity < 128) capacity = 128;

    return capacity;
}

/*
 * 2-way merge iterator state.
 */
typedef struct {
    const tl_record_t* run;
    size_t             run_len;
    size_t             run_idx;

    const tl_record_t* ooo;
    size_t             ooo_len;
    size_t             ooo_idx;
} merge_iter_t;

static void merge_iter_init(merge_iter_t* it, const tl_memrun_t* mr) {
    it->run = mr->run;
    it->run_len = mr->run_len;
    it->run_idx = 0;

    it->ooo = mr->ooo;
    it->ooo_len = mr->ooo_len;
    it->ooo_idx = 0;
}

static bool merge_iter_has_next(const merge_iter_t* it) {
    return it->run_idx < it->run_len || it->ooo_idx < it->ooo_len;
}

static const tl_record_t* merge_iter_next(merge_iter_t* it) {
    /* Both exhausted */
    if (it->run_idx >= it->run_len && it->ooo_idx >= it->ooo_len) {
        return NULL;
    }

    /* OOO exhausted */
    if (it->ooo_idx >= it->ooo_len) {
        return &it->run[it->run_idx++];
    }

    /* Run exhausted */
    if (it->run_idx >= it->run_len) {
        return &it->ooo[it->ooo_idx++];
    }

    /* Both have data: pick smaller timestamp */
    if (it->run[it->run_idx].ts <= it->ooo[it->ooo_idx].ts) {
        return &it->run[it->run_idx++];
    } else {
        return &it->ooo[it->ooo_idx++];
    }
}

tl_status_t tl_flush_memrun(const tl_allocator_t* alloc,
                             const tl_memrun_t* mr,
                             size_t target_page_bytes,
                             uint32_t generation,
                             tl_segment_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    if (mr == NULL) return TL_EINVAL;

    /* Handle empty memrun */
    bool has_records = (mr->run_len > 0 || mr->ooo_len > 0);
    bool has_tombs = (mr->tombs_len > 0);

    if (!has_records && !has_tombs) {
        return TL_EOF;  /* Nothing to flush */
    }

    tl_status_t st;

    /* Create tombstones from memrun tombstones */
    tl_tombstones_t* tombstones = NULL;
    if (has_tombs) {
        /* Create intervals_t wrapper for tombstones_create */
        tl_intervals_t temp_iset;
        temp_iset.data = mr->tombs;
        temp_iset.len = mr->tombs_len;
        temp_iset.cap = mr->tombs_len;
        temp_iset.alloc = alloc;

        st = tl_tombstones_create(alloc, &temp_iset, &tombstones);
        if (st != TL_OK) return st;

        /* Note: temp_iset.data is not freed (we don't own it) */
    }

    /* Handle tombstone-only memrun */
    if (!has_records) {
        st = tl_segment_create_tombstone_only(alloc, tombstones,
                                               TL_SEG_DELTA, generation, out);
        if (st != TL_OK && tombstones != NULL) {
            tl_tombstones_destroy(alloc, tombstones);
        }
        return st;
    }

    /* Build segment from records */
    uint32_t page_capacity = compute_page_capacity(target_page_bytes);

    tl_segment_builder_t builder;
    st = tl_segment_builder_init(&builder, alloc, page_capacity,
                                  TL_SEG_DELTA, generation);
    if (st != TL_OK) {
        if (tombstones != NULL) tl_tombstones_destroy(alloc, tombstones);
        return st;
    }

    /* 2-way merge run + ooo into segment builder */
    merge_iter_t iter;
    merge_iter_init(&iter, mr);

    while (merge_iter_has_next(&iter)) {
        const tl_record_t* rec = merge_iter_next(&iter);
        st = tl_segment_builder_add(&builder, rec->ts, rec->handle);
        if (st != TL_OK) {
            tl_segment_builder_destroy(&builder);
            if (tombstones != NULL) tl_tombstones_destroy(alloc, tombstones);
            return st;
        }
    }

    /* Set tombstones */
    if (tombstones != NULL) {
        tl_segment_builder_set_tombstones(&builder, tombstones);
        tombstones = NULL;  /* Ownership transferred */
    }

    /* Finish building segment */
    st = tl_segment_builder_finish(&builder, out);
    tl_segment_builder_destroy(&builder);

    return st;
}
