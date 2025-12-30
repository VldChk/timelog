#ifndef TL_MERGE_H
#define TL_MERGE_H

#include "tl_defs.h"
#include "tl_status.h"
#include "tl_alloc.h"
#include "tl_plan.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Heap node for k-way merge.
 */
typedef struct tl_merge_node {
    tl_record_t         record;       /* Current record from this component */
    tl_component_iter_t* iter;        /* Pointer to component iterator */
    uint32_t            component_id; /* For deterministic tie-breaking */
} tl_merge_node_t;

/**
 * K-way merge iterator using min-heap.
 *
 * Merges all component iterators from a query plan into a single
 * sorted stream.
 *
 * Properties:
 * - Output is non-decreasing by timestamp
 * - Ties are broken by component_id (deterministic but unspecified to users)
 * - O(log k) per record emitted
 */
typedef struct tl_merge_iter {
    /* Heap storage */
    tl_merge_node_t*   heap;
    uint32_t           heap_size;
    uint32_t           heap_cap;

    /* Query plan (not owned) */
    tl_qplan_t*        plan;

    /* Current state */
    tl_record_t        current;
    tl_iter_state_t    state;

    /* Allocator */
    const tl_allocator_t* alloc;
} tl_merge_iter_t;

/**
 * Create a merge iterator from a query plan.
 *
 * The plan is NOT consumed; caller retains ownership.
 * Component iterators are borrowed from plan.
 *
 * @param alloc Allocator
 * @param plan  Query plan with component iterators
 * @param out   Output iterator
 * @return TL_OK on success
 */
tl_status_t tl_merge_iter_create(const tl_allocator_t* alloc,
                                  tl_qplan_t* plan,
                                  tl_merge_iter_t** out);

/**
 * Destroy merge iterator.
 * Does NOT destroy the underlying plan.
 */
void tl_merge_iter_destroy(tl_merge_iter_t* it);

/**
 * Get current record.
 * Returns NULL if not in READY state.
 */
const tl_record_t* tl_merge_iter_peek(tl_merge_iter_t* it);

/**
 * Advance to next record.
 * @return TL_OK if advanced, TL_EOF if exhausted
 */
tl_status_t tl_merge_iter_advance(tl_merge_iter_t* it);

/**
 * Get current state.
 */
tl_iter_state_t tl_merge_iter_state(tl_merge_iter_t* it);

/**
 * Seek all component iterators to >= ts.
 * Rebuilds heap after seeking.
 *
 * @return TL_OK if positioned, TL_EOF if all exhausted
 */
tl_status_t tl_merge_iter_seek(tl_merge_iter_t* it, tl_ts_t ts);

#ifdef __cplusplus
}
#endif

#endif /* TL_MERGE_H */
