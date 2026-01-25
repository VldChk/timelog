#include "tl_plan.h"
#include "../internal/tl_range.h"
#include "../internal/tl_intervals.h"
#include "../storage/tl_manifest.h"
#include <string.h>
#include <stdlib.h>

/*===========================================================================
 * Constants
 *===========================================================================*/

/* Initial capacity for source array */
#define TL_PLAN_INIT_SOURCES 8

/* Initial capacity for tombstone array */
#define TL_PLAN_INIT_TOMBS 16

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Ensure source array has capacity for one more entry.
 */
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

/**
 * Ensure tombstone array has capacity for more entries.
 */
static tl_status_t ensure_tomb_capacity(tl_plan_t* plan, size_t additional) {
    /* Overflow guard for addition */
    if (additional > SIZE_MAX - plan->tomb_count) {
        return TL_ENOMEM;
    }
    size_t needed = plan->tomb_count + additional;
    if (needed <= plan->tomb_capacity) {
        return TL_OK;
    }

    size_t new_cap = (plan->tomb_capacity == 0)
                         ? TL_PLAN_INIT_TOMBS
                         : plan->tomb_capacity;
    while (new_cap < needed) {
        /* Overflow guard for capacity doubling */
        if (new_cap > SIZE_MAX / 2) {
            return TL_ENOMEM;
        }
        new_cap *= 2;
    }

    /* Overflow guard for allocation size */
    if (new_cap > SIZE_MAX / sizeof(tl_interval_t)) {
        return TL_ENOMEM;
    }

    tl_interval_t* new_arr = tl__malloc(plan->alloc,
                                         new_cap * sizeof(tl_interval_t));
    if (new_arr == NULL) {
        return TL_ENOMEM;
    }

    if (plan->tombstones != NULL) {
        memcpy(new_arr, plan->tombstones,
               plan->tomb_count * sizeof(tl_interval_t));
        tl__free(plan->alloc, plan->tombstones);
    }

    plan->tombstones = new_arr;
    plan->tomb_capacity = new_cap;
    return TL_OK;
}

/**
 * Add a segment source to the plan.
 */
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

    tl_segment_iter_init(&src->iter.segment, seg,
                         plan->t1, plan->t2, plan->t2_unbounded);

    /* Only add if not immediately exhausted */
    if (!tl_segment_iter_done(&src->iter.segment)) {
        plan->source_count++;
    }

    return TL_OK;
}

/**
 * Add a memrun source to the plan.
 */
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

/**
 * Add the active memview source to the plan.
 */
static tl_status_t add_active_source(tl_plan_t* plan,
                                      const tl_memview_t* mv) {
    tl_status_t st = ensure_source_capacity(plan);
    if (st != TL_OK) {
        return st;
    }

    tl_iter_source_t* src = &plan->sources[plan->source_count];
    src->kind = TL_ITER_ACTIVE;
    src->priority = UINT32_MAX;  /* Active is always highest priority */

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

/**
 * Clip a single interval's lower bound to t1.
 * Modifies interval in place, returns true if interval is still valid.
 */
static bool clip_interval_lower(tl_interval_t* interval, tl_ts_t t1) {
    /* If bounded and ends at or before t1, remove it */
    if (!interval->end_unbounded && interval->end <= t1) {
        return false;
    }

    /* Clip start to t1 if needed */
    if (interval->start < t1) {
        interval->start = t1;
    }

    return true;
}

/**
 * Add tombstone intervals from a segment to the plan.
 * Clips intervals to [t1, ...) range.
 */
static tl_status_t add_segment_tombstones(tl_plan_t* plan,
                                           const tl_segment_t* seg) {
    tl_intervals_imm_t tombs = tl_segment_tombstones_imm(seg);
    if (tombs.len == 0) {
        return TL_OK;
    }

    tl_status_t st = ensure_tomb_capacity(plan, tombs.len);
    if (st != TL_OK) {
        return st;
    }

    for (size_t i = 0; i < tombs.len; i++) {
        tl_interval_t interval = tombs.data[i];

        /* Skip if interval doesn't overlap query range */
        tl_ts_t int_max = interval.end_unbounded ? TL_TS_MAX : interval.end - 1;
        if (!tl_range_overlaps(interval.start, int_max,
                               plan->t1, plan->t2, plan->t2_unbounded)) {
            continue;
        }

        /* Clip to lower bound and add if still valid */
        if (clip_interval_lower(&interval, plan->t1)) {
            plan->tombstones[plan->tomb_count++] = interval;
        }
    }

    return TL_OK;
}

/**
 * Add tombstone intervals from a memrun to the plan.
 */
static tl_status_t add_memrun_tombstones(tl_plan_t* plan,
                                          const tl_memrun_t* mr) {
    size_t tomb_count = tl_memrun_tombs_len(mr);
    if (tomb_count == 0) {
        return TL_OK;
    }

    tl_status_t st = ensure_tomb_capacity(plan, tomb_count);
    if (st != TL_OK) {
        return st;
    }

    const tl_interval_t* tombs = tl_memrun_tombs_data(mr);

    for (size_t i = 0; i < tomb_count; i++) {
        tl_interval_t interval = tombs[i];

        /* Skip if interval doesn't overlap query range */
        tl_ts_t int_max = interval.end_unbounded ? TL_TS_MAX : interval.end - 1;
        if (!tl_range_overlaps(interval.start, int_max,
                               plan->t1, plan->t2, plan->t2_unbounded)) {
            continue;
        }

        /* Clip to lower bound and add if still valid */
        if (clip_interval_lower(&interval, plan->t1)) {
            plan->tombstones[plan->tomb_count++] = interval;
        }
    }

    return TL_OK;
}

/**
 * Add tombstone intervals from active memview to the plan.
 */
static tl_status_t add_active_tombstones(tl_plan_t* plan,
                                          const tl_memview_t* mv) {
    size_t tomb_count = tl_memview_tomb_len(mv);
    if (tomb_count == 0) {
        return TL_OK;
    }

    tl_status_t st = ensure_tomb_capacity(plan, tomb_count);
    if (st != TL_OK) {
        return st;
    }

    const tl_interval_t* tombs = tl_memview_tomb_data(mv);

    for (size_t i = 0; i < tomb_count; i++) {
        tl_interval_t interval = tombs[i];

        /* Skip if interval doesn't overlap query range */
        tl_ts_t int_max = interval.end_unbounded ? TL_TS_MAX : interval.end - 1;
        if (!tl_range_overlaps(interval.start, int_max,
                               plan->t1, plan->t2, plan->t2_unbounded)) {
            continue;
        }

        /* Clip to lower bound and add if still valid */
        if (clip_interval_lower(&interval, plan->t1)) {
            plan->tombstones[plan->tomb_count++] = interval;
        }
    }

    return TL_OK;
}

/**
 * Compare intervals by start timestamp for sorting.
 */
static int tomb_cmp(const void* a, const void* b) {
    const tl_interval_t* ia = (const tl_interval_t*)a;
    const tl_interval_t* ib = (const tl_interval_t*)b;

    if (ia->start < ib->start) return -1;
    if (ia->start > ib->start) return 1;
    return 0;
}

/**
 * Sort tombstone intervals by start timestamp.
 */
static void sort_tombstones(tl_plan_t* plan) {
    if (plan->tomb_count <= 1) {
        return;
    }

    qsort(plan->tombstones, plan->tomb_count,
          sizeof(tl_interval_t), tomb_cmp);
}

/**
 * Clip tombstone intervals to upper bound (t2) for bounded queries.
 *
 * For bounded queries [t1, t2):
 * - If tombstone end > t2, clip end to t2
 * - If tombstone is unbounded [x, +inf), it becomes [max(x, t1), t2)
 * - Removes intervals that start at or past t2
 *
 * For unbounded queries, this is a no-op.
 *
 * Precondition: tombstones are already clipped to lower bound.
 */
static void clip_tombstones_upper(tl_plan_t* plan) {
    if (plan->t2_unbounded || plan->tomb_count == 0) {
        return;  /* Nothing to clip for unbounded queries */
    }

    size_t write = 0;
    for (size_t read = 0; read < plan->tomb_count; read++) {
        tl_interval_t* interval = &plan->tombstones[read];

        /* Remove intervals that start at or past t2 */
        if (interval->start >= plan->t2) {
            continue;
        }

        /* Clip unbounded intervals to t2 */
        if (interval->end_unbounded) {
            interval->end_unbounded = false;
            interval->end = plan->t2;
        } else if (interval->end > plan->t2) {
            /* Clip bounded intervals that extend past t2 */
            interval->end = plan->t2;
        }

        /* Copy to output position if needed */
        if (write != read) {
            plan->tombstones[write] = *interval;
        }
        write++;
    }

    plan->tomb_count = write;
}

/**
 * Coalesce overlapping/adjacent tombstone intervals in-place.
 *
 * Precondition: tombstones are sorted by start timestamp.
 * Result: disjoint intervals with gaps between them.
 *
 * Algorithm (LLD Section 4.4):
 * - Merge intervals that overlap or are adjacent
 * - Unbounded interval absorbs all subsequent intervals
 */
static void coalesce_tombstones(tl_plan_t* plan) {
    if (plan->tomb_count <= 1) {
        return;
    }

    size_t write = 0;  /* Write position for coalesced output */

    for (size_t read = 1; read < plan->tomb_count; read++) {
        tl_interval_t* cur = &plan->tombstones[write];
        const tl_interval_t* next = &plan->tombstones[read];

        /* If current is unbounded, it absorbs everything */
        if (cur->end_unbounded) {
            break;
        }

        /* Check if next overlaps or is adjacent to current:
         * Overlap: next.start < cur.end
         * Adjacent: next.start == cur.end
         * Combined: next.start <= cur.end */
        if (next->start <= cur->end) {
            /* Merge: extend current to cover next */
            if (next->end_unbounded) {
                cur->end_unbounded = true;
                /* No need to update end - unbounded means infinite */
            } else if (next->end > cur->end) {
                cur->end = next->end;
            }
            /* Continue to potentially merge more */
        } else {
            /* Gap between intervals - emit current, start new */
            write++;
            plan->tombstones[write] = *next;
        }
    }

    /* Update count to number of coalesced intervals */
    plan->tomb_count = write + 1;
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

    tl_status_t st;
    const tl_manifest_t* manifest = snapshot->manifest;
    const tl_memview_t* mv = tl_snapshot_memview(snapshot);

    /*
     * Check if range is empty (bounded only).
     * Unbounded ranges are never empty.
     */
    if (tl_range_is_empty(t1, t2, t2_unbounded)) {
        return TL_OK;
    }

    /*
     * Step 1: Add L1 segment sources.
     * Use binary search to find first potentially overlapping segment.
     */
    size_t l1_start = tl_manifest_l1_find_first_overlap(manifest, t1);
    for (size_t i = l1_start; i < tl_manifest_l1_count(manifest); i++) {
        tl_segment_t* seg = tl_manifest_l1_get(manifest, i);

        /* Stop early if segment starts past range end */
        if (!t2_unbounded && seg->min_ts >= t2) {
            plan->segments_pruned += (tl_manifest_l1_count(manifest) - i);
            break;
        }

        /* Check overlap */
        if (!tl_range_overlaps(seg->min_ts, seg->max_ts, t1, t2, t2_unbounded)) {
            plan->segments_pruned++;
            continue;
        }

        st = add_segment_source(plan, seg, seg->generation);
        if (st != TL_OK) goto fail;

        /* Defensive: include L1 tombstones if present (should be empty in V1). */
        st = add_segment_tombstones(plan, seg);
        if (st != TL_OK) goto fail;
    }

    /* Count pruned segments from before l1_start */
    plan->segments_pruned += l1_start;

    /*
     * Step 2: Add L0 segment sources.
     * L0 segments may overlap and are in flush order.
     * Assign priorities based on position (later = higher priority).
     */
    for (size_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        tl_segment_t* seg = tl_manifest_l0_get(manifest, i);

        /* Check overlap */
        if (!tl_range_overlaps(seg->min_ts, seg->max_ts, t1, t2, t2_unbounded)) {
            plan->segments_pruned++;
            continue;
        }

        /* L0 priority: use generation (newer flushes have higher gen) */
        st = add_segment_source(plan, seg, seg->generation);
        if (st != TL_OK) goto fail;

        st = add_segment_tombstones(plan, seg);
        if (st != TL_OK) goto fail;
    }

    /*
     * Step 3: Add sealed memrun sources.
     * Memruns are in FIFO order (oldest first).
     * Assign priorities: higher index = newer = higher priority.
     */
    size_t sealed_len = tl_memview_sealed_len(mv);
    for (size_t i = 0; i < sealed_len; i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(mv, i);

        /* Check if memrun has any data */
        if (!tl_memrun_has_records(mr) && !tl_memrun_has_tombstones(mr)) {
            plan->memruns_pruned++;
            continue;
        }

        /* Check overlap */
        if (!tl_range_overlaps(tl_memrun_min_ts(mr), tl_memrun_max_ts(mr),
                               t1, t2, t2_unbounded)) {
            plan->memruns_pruned++;
            continue;
        }

        /* Priority for memruns: base at segment max gen + index */
        uint32_t base_priority = 0;
        if (tl_manifest_l0_count(manifest) > 0) {
            base_priority = tl_manifest_l0_get(manifest,
                                tl_manifest_l0_count(manifest) - 1)->generation + 1;
        }

        st = add_memrun_source(plan, mr, base_priority + (uint32_t)i);
        if (st != TL_OK) goto fail;

        st = add_memrun_tombstones(plan, mr);
        if (st != TL_OK) goto fail;
    }

    /*
     * Step 4: Add active memview source.
     * Active data is the newest and has highest priority.
     */
    if (mv->has_data && tl_memview_overlaps(mv, t1, t2, t2_unbounded)) {
        size_t active_run_len = tl_memview_run_len(mv);
        size_t active_ooo_len = tl_memview_ooo_total_len(mv);

        if (active_run_len > 0 || active_ooo_len > 0) {
            st = add_active_source(plan, mv);
            if (st != TL_OK) goto fail;
        }

        st = add_active_tombstones(plan, mv);
        if (st != TL_OK) goto fail;
    }

    /*
     * Step 5: Sort, coalesce, and clip tombstones (LLD Section 4.4).
     * - Sort by start timestamp
     * - Merge overlapping/adjacent intervals
     * - Clip to upper bound [t1, t2) for bounded queries
     * This ensures efficient filtering during merge.
     */
    sort_tombstones(plan);
    coalesce_tombstones(plan);
    clip_tombstones_upper(plan);

    return TL_OK;

fail:
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
