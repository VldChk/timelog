#ifndef TL_PLAN_H
#define TL_PLAN_H

#include "tl_defs.h"
#include "tl_status.h"
#include "tl_alloc.h"
#include "tl_snapshot.h"
#include "tl_iter.h"
#include "tl_tombstones.h"
#include "tl_intervals.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Query plan: collection of component iterators + effective tombstones.
 *
 * Built from a snapshot for a specific range [t1, t2).
 *
 * Contains:
 * - Component iterators for all overlapping segments
 * - Iterators for memview (active + sealed memruns)
 * - Effective tombstones (union of all visible tombstones, clipped to range)
 *
 * The plan is built once per query and provides:
 * - All data sources that overlap the query range
 * - Pre-computed tombstone union for efficient filtering
 */
typedef struct tl_qplan {
    /* Query range */
    tl_ts_t              t1;
    tl_ts_t              t2;

    /* Component iterators */
    tl_component_iter_t* iters;
    uint32_t             n_iters;
    uint32_t             iters_cap;

    /* Effective tombstones (union of all sources, clipped to [t1, t2)) */
    tl_tombstones_t*     eff_tombs;

    /* Allocator */
    const tl_allocator_t* alloc;
} tl_qplan_t;

/**
 * Build a query plan for range [t1, t2).
 *
 * This function:
 * 1. Selects candidate segments overlapping [t1, t2)
 * 2. Creates segment iterators for each candidate
 * 3. Creates memview iterators for active + sealed memruns
 * 4. Computes effective tombstones by union + clip
 *
 * @param alloc Allocator
 * @param snap  Snapshot to query
 * @param t1    Range start (inclusive)
 * @param t2    Range end (exclusive)
 * @param out   Output plan
 * @return TL_OK on success, TL_EINVAL if t2 < t1
 */
tl_status_t tl_qplan_build(const tl_allocator_t* alloc,
                            const tl_snapshot_t* snap,
                            tl_ts_t t1,
                            tl_ts_t t2,
                            tl_qplan_t** out);

/**
 * Destroy a query plan and all owned resources.
 */
void tl_qplan_destroy(tl_qplan_t* plan);

/**
 * Get number of component iterators in plan.
 */
TL_INLINE uint32_t tl_qplan_iter_count(const tl_qplan_t* plan) {
    return plan ? plan->n_iters : 0;
}

/**
 * Check if plan has any iterators.
 */
TL_INLINE bool tl_qplan_empty(const tl_qplan_t* plan) {
    return plan == NULL || plan->n_iters == 0;
}

/**
 * Check if plan has effective tombstones.
 */
TL_INLINE bool tl_qplan_has_tombstones(const tl_qplan_t* plan) {
    return plan != NULL && plan->eff_tombs != NULL &&
           !tl_tombstones_empty(plan->eff_tombs);
}

#ifdef __cplusplus
}
#endif

#endif /* TL_PLAN_H */
