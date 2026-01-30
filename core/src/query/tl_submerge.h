#ifndef TL_SUBMERGE_H
#define TL_SUBMERGE_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_heap.h"
#include "../internal/tl_search.h"

/*===========================================================================
 * Sub-merge helper for active/memrun iterators.
 *
 * Provides a small K-way merge over sorted record arrays using tl_heap.
 * Sources are arrays sorted by (ts, handle). Tie-break across sources is
 * driven by tie_id (lower wins), which encodes run-before-OOO ordering.
 *===========================================================================*/

typedef struct tl_subsrc {
    const tl_record_t* data;
    size_t             len;
    size_t             pos;
    size_t             end;
    uint32_t           tie_id;
} tl_subsrc_t;

typedef struct tl_submerge {
    tl_subsrc_t*   srcs;
    size_t         src_count;
    tl_heap_t      heap;
    tl_alloc_ctx_t* alloc;
} tl_submerge_t;

/**
 * Initialize sub-merge source bounds for a sorted record array.
 */
TL_INLINE void tl_submerge_src_init(tl_subsrc_t* src,
                                     const tl_record_t* data,
                                     size_t len,
                                     tl_ts_t t1,
                                     tl_ts_t t2,
                                     bool t2_unbounded,
                                     uint32_t tie_id) {
    src->data = data;
    src->len = len;
    src->tie_id = tie_id;

    src->pos = tl_record_lower_bound(data, len, t1);
    if (t2_unbounded) {
        src->end = len;
    } else {
        src->end = tl_record_lower_bound(data, len, t2);
    }

    if (src->pos > src->end) {
        src->pos = src->end;
    }
}

/**
 * Initialize sub-merge with a fixed number of sources.
 * Allocates source array and initializes heap.
 */
tl_status_t tl_submerge_init(tl_submerge_t* sm,
                              tl_alloc_ctx_t* alloc,
                              size_t src_count);

/**
 * Destroy sub-merge and free internal resources.
 */
void tl_submerge_destroy(tl_submerge_t* sm);

/**
 * Build heap from configured sources.
 * Caller must populate sm->srcs and sm->src_count before calling.
 */
tl_status_t tl_submerge_build(tl_submerge_t* sm);

/**
 * Advance to next record.
 * @return TL_OK if record available, TL_EOF if exhausted
 */
tl_status_t tl_submerge_next(tl_submerge_t* sm, tl_record_t* out);

/**
 * Seek to first record with ts >= target (forward-only).
 */
void tl_submerge_seek(tl_submerge_t* sm, tl_ts_t target);

/**
 * Check if merge is exhausted.
 */
TL_INLINE bool tl_submerge_done(const tl_submerge_t* sm) {
    return sm == NULL || tl_heap_is_empty(&sm->heap);
}

#endif /* TL_SUBMERGE_H */
