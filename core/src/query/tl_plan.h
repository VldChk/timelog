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
 * Built from a snapshot for a given range [t1, t2) or [t1, +inf), the
 * plan identifies every source (segment, sealed memrun, active
 * memview) that overlaps the range and primes iterators for them. The
 * plan is then fed to the K-way merge iterator, which produces a
 * single sorted record stream.
 *
 * Range semantics:
 * - t2_unbounded == true means [t1, +inf); the t2 field is ignored.
 * - Otherwise the query is the half-open interval [t1, t2).
 *
 * Thread Safety:
 * - Not thread-safe; one plan per query per thread.
 * - Snapshot must remain valid for the lifetime of the plan.
 *===========================================================================*/

/*---------------------------------------------------------------------------
 * Iterator Source Types
 *
 * Tagged-union envelope that lets the merge iterator drive segment,
 * memrun, and active-memview iterators through one polymorphic API.
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
 * Destroy a query plan, freeing its sources and tombstone arrays.
 *
 * Does NOT release the snapshot; that is the caller's responsibility.
 *
 * Idempotent and safe on NULL, on a zero-initialised plan, and on an
 * already-destroyed plan (internal pointers are nulled after free).
 * Callers can therefore unconditionally call destroy() in cleanup
 * paths without tracking initialisation state.
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
