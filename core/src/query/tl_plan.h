#ifndef TL_PLAN_H
#define TL_PLAN_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "tl_snapshot.h"
#include "tl_segment_iter.h"
#include "tl_memrun_iter.h"
#include "tl_active_iter.h"

/*===========================================================================
 * Query Plan
 *
 * A query plan is built from a snapshot for a given range [t1, t2) or
 * [t1, +inf). It identifies all sources (segments, memruns, active memview)
 * that overlap the range and prepares iterators for them.
 *
 * The plan is the input to the merge iterator, which combines all sources
 * into a single sorted stream.
 *
 * UNBOUNDED QUERY DESIGN:
 * - If t2_unbounded == true, the query is [t1, +inf)
 * - When t2_unbounded is true, the 't2' field is ignored (pass 0 for clarity)
 *
 * Thread Safety:
 * - Not thread-safe; create one plan per query per thread
 * - Snapshot must remain valid for the lifetime of the plan
 *===========================================================================*/

/*---------------------------------------------------------------------------
 * Iterator Source Types
 *
 * A union of all iterator types to enable polymorphic iteration.
 *---------------------------------------------------------------------------*/

typedef enum tl_iter_kind {
    TL_ITER_SEGMENT,    /* Segment iterator */
    TL_ITER_MEMRUN,     /* Sealed memrun iterator */
    TL_ITER_ACTIVE      /* Active memview iterator */
} tl_iter_kind_t;

typedef struct tl_iter_source {
    tl_iter_kind_t kind;

    union {
        tl_segment_iter_t segment;
        tl_memrun_iter_t  memrun;
        tl_active_iter_t  active;
    } iter;

    /* For priority in merge: newer sources have higher priority.
     * Segments: use generation (higher = newer)
     * Memruns: index in sealed queue (0 = oldest)
     * Active: always highest priority (youngest data) */
    uint32_t priority;

    /* Tombstone watermark for immutable sources (segments/memruns). */
    tl_seq_t watermark;
} tl_iter_source_t;

/*---------------------------------------------------------------------------
 * Query Plan Structure
 *---------------------------------------------------------------------------*/

typedef struct tl_plan {
    /* Allocator for dynamic allocations */
    tl_alloc_ctx_t* alloc;

    /* Query range */
    tl_ts_t         t1;
    tl_ts_t         t2;              /* ONLY valid if !t2_unbounded */
    bool            t2_unbounded;

    /* Source snapshot (must remain valid) */
    tl_snapshot_t*  snapshot;

    /* Array of iterator sources (dynamically allocated) */
    tl_iter_source_t* sources;
    size_t          source_count;
    size_t          source_capacity;

    /* Tombstone intervals from all sources.
     * Merged and sorted for efficient filtering.
     * Intervals are COPIED into this array. */
    tl_interval_t*  tombstones;
    size_t          tomb_count;
    size_t          tomb_capacity;

    /* Plan statistics */
    size_t          segments_pruned;
    size_t          memruns_pruned;
} tl_plan_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Build a query plan from a snapshot.
 *
 * This function:
 * 1. Prunes segments that don't overlap [t1, t2)
 * 2. Prunes memruns that don't overlap [t1, t2)
 * 3. Creates iterators for overlapping sources
 * 4. Collects and clips tombstone intervals
 *
 * @param plan         Plan to initialize
 * @param snapshot     Source snapshot (must remain valid)
 * @param alloc        Allocator for plan's dynamic data
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY used if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @return TL_OK on success, error code on failure
 */
tl_status_t tl_plan_build(tl_plan_t* plan,
                           tl_snapshot_t* snapshot,
                           tl_alloc_ctx_t* alloc,
                           tl_ts_t t1, tl_ts_t t2,
                           bool t2_unbounded);

/**
 * Destroy a query plan.
 *
 * Frees dynamically allocated memory (sources, tombstones).
 * Does NOT release the snapshot - caller is responsible for that.
 *
 * Idempotent: Safe to call on:
 * - NULL plan pointer (no-op)
 * - Zeroed plan (e.g., from memset(0)) - all NULL checks pass
 * - Already-destroyed plan (pointers set to NULL after free)
 *
 * This enables simpler cleanup paths: callers can unconditionally call
 * destroy() without checking initialization state.
 *
 * @param plan  Plan to destroy (may be NULL or zeroed)
 */
void tl_plan_destroy(tl_plan_t* plan);

/*===========================================================================
 * Accessors
 *===========================================================================*/

/** Get the number of sources in the plan. */
TL_INLINE size_t tl_plan_source_count(const tl_plan_t* plan) {
    TL_ASSERT(plan != NULL);
    return plan->source_count;
}

/** Get a source by index. */
TL_INLINE tl_iter_source_t* tl_plan_source(tl_plan_t* plan, size_t idx) {
    TL_ASSERT(plan != NULL);
    TL_ASSERT(idx < plan->source_count);
    return &plan->sources[idx];
}

/** Get tombstone intervals. */
TL_INLINE const tl_interval_t* tl_plan_tombstones(const tl_plan_t* plan) {
    TL_ASSERT(plan != NULL);
    return plan->tombstones;
}

/** Get tombstone count. */
TL_INLINE size_t tl_plan_tomb_count(const tl_plan_t* plan) {
    TL_ASSERT(plan != NULL);
    return plan->tomb_count;
}

/** Check if plan is empty (no data sources). */
TL_INLINE bool tl_plan_is_empty(const tl_plan_t* plan) {
    TL_ASSERT(plan != NULL);
    return plan->source_count == 0;
}

#endif /* TL_PLAN_H */
