#include "tl_plan.h"
#include "../internal/tl_range.h"
#include "../internal/tl_intervals.h"
#include "../internal/tl_tombstone_utils.h"
#include "../storage/tl_manifest.h"
#include <string.h>
#include <stdlib.h>

/*===========================================================================
 * Constants
 *===========================================================================*/

/* Initial capacity for source array */
#define TL_PLAN_INIT_SOURCES 8

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/** Grow source array if at capacity. */
static tl_status_t ensure_source_capacity(tl_plan_t* plan) {
    if (plan->source_count < plan->source_capacity) {
        return TL_OK;
    }

    size_t new_cap;
    if (plan->source_capacity == 0) {
        new_cap = TL_PLAN_INIT_SOURCES;
    } else {
        /* Overflow guard for capacity doubling */
        if (plan->source_capacity > SIZE_MAX / 2) {
            return TL_ENOMEM;
        }
        new_cap = plan->source_capacity * 2;
    }

    /* Overflow guard for allocation size */
    if (new_cap > SIZE_MAX / sizeof(tl_iter_source_t)) {
        return TL_ENOMEM;
    }

    tl_iter_source_t* new_arr = tl__malloc(plan->alloc,
                                            new_cap * sizeof(tl_iter_source_t));
    if (new_arr == NULL) {
        return TL_ENOMEM;
    }

    if (plan->sources != NULL) {
        memcpy(new_arr, plan->sources,
               plan->source_count * sizeof(tl_iter_source_t));
        tl__free(plan->alloc, plan->sources);
    }

    plan->sources = new_arr;
    plan->source_capacity = new_cap;
    return TL_OK;
}

/** Add a segment source to the plan. */
static tl_status_t add_segment_source(tl_plan_t* plan,
                                       const tl_segment_t* seg,
                                       uint32_t priority) {
    tl_status_t st = ensure_source_capacity(plan);
    if (st != TL_OK) {
        return st;
    }

    tl_iter_source_t* src = &plan->sources[plan->source_count];
    src->kind = TL_ITER_SEGMENT;
    src->priority = priority;
    src->watermark = tl_segment_applied_seq(seg);

    tl_segment_iter_init(&src->iter.segment, seg,
                         plan->t1, plan->t2, plan->t2_unbounded);

    /* Only add if not immediately exhausted */
    if (!tl_segment_iter_done(&src->iter.segment)) {
        plan->source_count++;
    }

    return TL_OK;
}

/** Add a memrun source to the plan. */
static tl_status_t add_memrun_source(tl_plan_t* plan,
                                      const tl_memrun_t* mr,
                                      uint32_t priority) {
    tl_status_t st = ensure_source_capacity(plan);
    if (st != TL_OK) {
        return st;
    }

    tl_iter_source_t* src = &plan->sources[plan->source_count];
    src->kind = TL_ITER_MEMRUN;
    src->priority = priority;
    src->watermark = tl_memrun_applied_seq(mr);

    tl_status_t init_st = tl_memrun_iter_init(&src->iter.memrun, mr,
                                              plan->t1, plan->t2, plan->t2_unbounded,
                                              plan->alloc);
    if (init_st != TL_OK) {
        tl_memrun_iter_destroy(&src->iter.memrun);
        return init_st;
    }

    /* Only add if not immediately exhausted */
    if (!tl_memrun_iter_done(&src->iter.memrun)) {
        plan->source_count++;
    } else {
        tl_memrun_iter_destroy(&src->iter.memrun);
    }

    return TL_OK;
}

/** Add the active memview source to the plan. */
static tl_status_t add_active_source(tl_plan_t* plan,
                                      const tl_memview_t* mv) {
    tl_status_t st = ensure_source_capacity(plan);
    if (st != TL_OK) {
        return st;
    }

    tl_iter_source_t* src = &plan->sources[plan->source_count];
    src->kind = TL_ITER_ACTIVE;
    src->priority = UINT32_MAX;  /* Active is always highest priority */
    src->watermark = 0;

    tl_status_t init_st = tl_active_iter_init(&src->iter.active, mv,
                                              plan->t1, plan->t2, plan->t2_unbounded,
                                              plan->alloc);
    if (init_st != TL_OK) {
        tl_active_iter_destroy(&src->iter.active);
        return init_st;
    }

    /* Only add if not immediately exhausted */
    if (!tl_active_iter_done(&src->iter.active)) {
        plan->source_count++;
    } else {
        tl_active_iter_destroy(&src->iter.active);
    }

    return TL_OK;
}

static tl_status_t add_segment_tombstones(tl_intervals_t* accum,
                                           const tl_segment_t* seg,
                                           tl_ts_t t1, tl_ts_t t2,
                                           bool t2_unbounded) {
    tl_intervals_imm_t tombs = tl_segment_tombstones_imm(seg);
    return tl_tombstones_add_intervals(accum, tombs, t1, t2, t2_unbounded);
}

static tl_status_t add_memrun_tombstones(tl_intervals_t* accum,
                                          const tl_memrun_t* mr,
                                          tl_ts_t t1, tl_ts_t t2,
                                          bool t2_unbounded) {
    tl_intervals_imm_t tombs = tl_memrun_tombs_imm(mr);
    return tl_tombstones_add_intervals(accum, tombs, t1, t2, t2_unbounded);
}

static tl_status_t add_active_tombstones(tl_intervals_t* accum,
                                          const tl_memview_t* mv,
                                          tl_ts_t t1, tl_ts_t t2,
                                          bool t2_unbounded) {
    tl_intervals_imm_t tombs = tl_memview_tombs_imm(mv);
    return tl_tombstones_add_intervals(accum, tombs, t1, t2, t2_unbounded);
}

/*===========================================================================
 * Lifecycle
 *
 * Allocation and cleanup semantics:
 * - tl_plan_build() initializes plan with memset(0) first, so partial
 *   allocations on failure leave plan in a safe state (NULL pointers)
 * - On any allocation failure, build() calls tl_plan_destroy() internally
 *   before returning error, so caller does NOT need to clean up on failure
 * - tl_plan_destroy() safely handles NULL arrays (checks before free)
 * - Caller MUST call tl_plan_destroy() on success to free sources/tombstones
 *===========================================================================*/

tl_status_t tl_plan_build(tl_plan_t* plan,
                           tl_snapshot_t* snapshot,
                           tl_alloc_ctx_t* alloc,
                           tl_ts_t t1, tl_ts_t t2,
                           bool t2_unbounded) {
    TL_ASSERT(plan != NULL);
    TL_ASSERT(snapshot != NULL);
    TL_ASSERT(alloc != NULL);

    memset(plan, 0, sizeof(*plan));
    plan->alloc = alloc;
    plan->t1 = t1;
    plan->t2 = t2;
    plan->t2_unbounded = t2_unbounded;
    plan->snapshot = snapshot;

    const tl_manifest_t* manifest = snapshot->manifest;
    const tl_memview_t* mv = tl_snapshot_memview(snapshot);
    tl_intervals_t tombs;
    tl_intervals_init(&tombs, alloc);
    tl_status_t st;

    /* Empty range short-circuit (unbounded ranges are never empty) */
    if (tl_range_is_empty(t1, t2, t2_unbounded)) {
        return TL_OK;
    }

    /* Step 1: L1 segments (binary search to first overlap) */
    size_t l1_start = tl_manifest_l1_find_first_overlap(manifest, t1);
    for (size_t i = l1_start; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);

        if (!t2_unbounded && seg->min_ts >= t2) {
            plan->segments_pruned += (tl_manifest_l1_count(manifest) - i);
            break;
        }

        if (!tl_range_overlaps(seg->min_ts, seg->max_ts, t1, t2, t2_unbounded)) {
            plan->segments_pruned++;
            continue;
        }

        st = add_segment_source(plan, seg, seg->generation);
        if (st != TL_OK) goto fail;

        /* Defensive: include any L1 tombstones if present. */
        st = add_segment_tombstones(&tombs, seg, t1, t2, t2_unbounded);
        if (st != TL_OK) goto fail;
    }

    /* Count pruned segments from before l1_start */
    plan->segments_pruned += l1_start;

    /* Step 2: L0 segments (may overlap; priority by generation) */
    for (size_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);

        bool overlaps = false;
        if (tl_segment_has_records(seg)) {
            overlaps |= tl_range_overlaps(seg->record_min_ts, seg->record_max_ts,
                                          t1, t2, t2_unbounded);
        }
        if (tl_segment_has_tombstones(seg)) {
            overlaps |= tl_range_overlaps(seg->tomb_min_ts, seg->tomb_max_ts,
                                          t1, t2, t2_unbounded);
        }
        if (!overlaps) {
            plan->segments_pruned++;
            continue;
        }

        /* L0 priority: use generation (newer flushes have higher gen) */
        st = add_segment_source(plan, seg, seg->generation);
        if (st != TL_OK) goto fail;

        st = add_segment_tombstones(&tombs, seg, t1, t2, t2_unbounded);
        if (st != TL_OK) goto fail;
    }

    /* Step 3: Sealed memruns (FIFO; higher index = newer = higher priority) */
    size_t sealed_len = tl_memview_sealed_len(mv);
    for (size_t i = 0; i < sealed_len; i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(mv, i);

        if (!tl_memrun_has_records(mr) && !tl_memrun_has_tombstones(mr)) {
            plan->memruns_pruned++;
            continue;
        }

        if (!tl_range_overlaps(tl_memrun_min_ts(mr), tl_memrun_max_ts(mr),
                               t1, t2, t2_unbounded)) {
            plan->memruns_pruned++;
            continue;
        }

        /* Priority for memruns: base at segment max gen + index */
        uint32_t base_priority = 0;
        if (tl_manifest_l0_count(manifest) > 0) {
            uint32_t newest_gen = tl_manifest_l0_get(
                manifest, tl_manifest_l0_count(manifest) - 1)->generation;
            base_priority = (newest_gen == UINT32_MAX) ? UINT32_MAX : (newest_gen + 1);
        }

        /*
         * Overflow-safe priority assignment with saturation.
         * If base_priority + i would exceed UINT32_MAX, saturate to UINT32_MAX.
         * This preserves relative ordering within the valid range.
         */
        uint32_t priority;
        if (i > UINT32_MAX) {
            priority = UINT32_MAX;
        } else if (base_priority > UINT32_MAX - (uint32_t)i) {
            priority = UINT32_MAX;  /* Saturate on overflow */
        } else {
            priority = base_priority + (uint32_t)i;
        }

        st = add_memrun_source(plan, mr, priority);
        if (st != TL_OK) goto fail;

        st = add_memrun_tombstones(&tombs, mr, t1, t2, t2_unbounded);
        if (st != TL_OK) goto fail;
    }

    /* Step 4: Active memview (highest priority) */
    if (mv->has_data && tl_memview_overlaps(mv, t1, t2, t2_unbounded)) {
        size_t active_run_len = tl_memview_run_len(mv);
        size_t active_ooo_len = tl_memview_ooo_total_len(mv);

        if (active_run_len > 0 || active_ooo_len > 0) {
            st = add_active_source(plan, mv);
            if (st != TL_OK) goto fail;
        }

        st = add_active_tombstones(&tombs, mv, t1, t2, t2_unbounded);
        if (st != TL_OK) goto fail;
    }

    /* Step 5: Clip tombstones to query range */
    if (!tl_intervals_is_empty(&tombs)) {
        if (t2_unbounded) {
            tl_intervals_clip_lower(&tombs, t1);
        } else {
            tl_intervals_clip(&tombs, t1, t2);
        }
    }

    plan->tombstones = tl_intervals_take(&tombs, &plan->tomb_count);
    plan->tomb_capacity = plan->tomb_count;

    tl_intervals_destroy(&tombs);

    return TL_OK;

fail:
    tl_intervals_destroy(&tombs);
    tl_plan_destroy(plan);
    return st;
}

void tl_plan_destroy(tl_plan_t* plan) {
    if (plan == NULL) {
        return;
    }

    if (plan->sources != NULL) {
        for (size_t i = 0; i < plan->source_count; i++) {
            tl_iter_source_t* src = &plan->sources[i];
            if (src->kind == TL_ITER_ACTIVE) {
                tl_active_iter_destroy(&src->iter.active);
            } else if (src->kind == TL_ITER_MEMRUN) {
                tl_memrun_iter_destroy(&src->iter.memrun);
            }
        }
        tl__free(plan->alloc, plan->sources);
        plan->sources = NULL;
    }
    plan->source_count = 0;
    plan->source_capacity = 0;

    if (plan->tombstones != NULL) {
        tl__free(plan->alloc, plan->tombstones);
        plan->tombstones = NULL;
    }
    plan->tomb_count = 0;
    plan->tomb_capacity = 0;
}
