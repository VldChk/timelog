#ifndef TL_MANIFEST_H
#define TL_MANIFEST_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_atomic.h"
#include "tl_segment.h"

/*===========================================================================
 * Manifest Structure
 *
 * The manifest is the atomic publication root for the storage layer.
 * Immutable after publication. Replaced via copy-on-write.
 *
 * Invariants:
 * - L1 segments sorted by window_start
 * - L1 segments non-overlapping by window
 * - L0 segments in flush order (oldest first)
 * - version monotonically increasing
 *
 * Ownership:
 * - Manifest holds strong references to all its segments (acquired on build)
 * - When manifest is released and refcnt hits 0, all segment references are
 *   released
 *
 * Reference: Storage LLD Section 3.7, Section 8
 *===========================================================================*/

typedef struct tl_manifest {
    /* Version for debugging and metrics */
    uint64_t version;

    /* L1 segments: non-overlapping, sorted by window_start */
    tl_segment_t** l1;
    uint32_t       n_l1;
    uint32_t       cap_l1; /* Capacity cache (diagnostic; == n_l1 when published) */

    /* L0 segments: may overlap, in flush order */
    tl_segment_t** l0;
    uint32_t       n_l0;
    uint32_t       cap_l0; /* Capacity cache (diagnostic; == n_l0 when published) */

    /* Cached global bounds (optional optimization) */
    bool      has_bounds;
    tl_ts_t   min_ts;
    tl_ts_t   max_ts;

    /* Reference counting */
    tl_atomic_u32 refcnt;

    /* Allocator (for destruction) */
    tl_alloc_ctx_t* alloc;
} tl_manifest_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Create an empty manifest.
 * Returned manifest has refcnt = 1 (caller owns reference).
 */
tl_status_t tl_manifest_create(tl_alloc_ctx_t* alloc, tl_manifest_t** out);

/*===========================================================================
 * Reference Counting
 *
 * Same memory ordering rules as segment reference counting.
 * When refcnt hits 0, all segment references are released.
 *===========================================================================*/

/**
 * Increment reference count (pin manifest).
 * Returns the manifest for convenience.
 */
tl_manifest_t* tl_manifest_acquire(tl_manifest_t* m);

/**
 * Decrement reference count.
 * Destroys manifest and releases all segment references when refcnt reaches 0.
 */
void tl_manifest_release(tl_manifest_t* m);

/**
 * Get current reference count (for debugging).
 */
TL_INLINE uint32_t tl_manifest_refcnt(const tl_manifest_t* m) {
    return tl_atomic_load_relaxed_u32(&((tl_manifest_t*)m)->refcnt);
}

/*===========================================================================
 * Copy-on-Write Builder
 *
 * For manifest updates (flush or compaction), we build a new manifest
 * from the old one with modifications.
 *
 * Usage pattern:
 * 1. Initialize builder with base manifest (or NULL for initial)
 * 2. Queue additions/removals
 * 3. Build new manifest
 * 4. Destroy builder (cleans up temporary buffers)
 *
 * Reference: Storage LLD Section 8
 *===========================================================================*/

typedef struct tl_manifest_builder {
    tl_alloc_ctx_t* alloc;
    const tl_manifest_t* base;      /* Old manifest (NULL for initial) */

    /* Pending additions */
    tl_segment_t**  add_l0;
    size_t          add_l0_len;
    size_t          add_l0_cap;

    tl_segment_t**  add_l1;
    size_t          add_l1_len;
    size_t          add_l1_cap;

    /* Pending removals (by pointer comparison) */
    tl_segment_t**  remove_l0;
    size_t          remove_l0_len;
    size_t          remove_l0_cap;

    tl_segment_t**  remove_l1;
    size_t          remove_l1_len;
    size_t          remove_l1_cap;
} tl_manifest_builder_t;

/**
 * Initialize builder from existing manifest (or NULL for initial).
 * Does NOT acquire reference on base (builder is short-lived).
 */
void tl_manifest_builder_init(tl_manifest_builder_t* mb,
                               tl_alloc_ctx_t* alloc,
                               const tl_manifest_t* base);

/**
 * Destroy builder and free temporary buffers.
 * Does NOT destroy base manifest or any segments.
 */
void tl_manifest_builder_destroy(tl_manifest_builder_t* mb);

/**
 * Queue an L0 segment for addition.
 * Segment is NOT acquired until build().
 */
tl_status_t tl_manifest_builder_add_l0(tl_manifest_builder_t* mb,
                                        tl_segment_t* seg);

/**
 * Queue an L1 segment for addition.
 * Segment is NOT acquired until build().
 */
tl_status_t tl_manifest_builder_add_l1(tl_manifest_builder_t* mb,
                                        tl_segment_t* seg);

/**
 * Queue an L0 segment for removal.
 */
tl_status_t tl_manifest_builder_remove_l0(tl_manifest_builder_t* mb,
                                           tl_segment_t* seg);

/**
 * Queue an L1 segment for removal.
 */
tl_status_t tl_manifest_builder_remove_l1(tl_manifest_builder_t* mb,
                                           tl_segment_t* seg);

/**
 * Build the new manifest.
 *
 * Steps:
 * 1. Allocate new manifest
 * 2. Copy segments from base, excluding removals
 * 3. Add new segments
 * 4. Sort L1 by window_start
 * 5. Compute cached bounds
 * 6. Set version = base->version + 1 (or 1 if base is NULL)
 * 7. Acquire references on ALL included segments
 *
 * Returned manifest has refcnt = 1 (caller owns reference).
 *
 * @param mb  Builder
 * @param out Output new manifest
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EINVAL if removal list contains non-existent or duplicate segments,
 *         TL_EOVERFLOW if resulting segment count exceeds UINT32_MAX
 */
tl_status_t tl_manifest_builder_build(tl_manifest_builder_t* mb,
                                       tl_manifest_t** out);

/*===========================================================================
 * Accessors
 *===========================================================================*/

TL_INLINE uint32_t tl_manifest_l0_count(const tl_manifest_t* m) {
    return m->n_l0;
}

TL_INLINE uint32_t tl_manifest_l1_count(const tl_manifest_t* m) {
    return m->n_l1;
}

TL_INLINE tl_segment_t* tl_manifest_l0_get(const tl_manifest_t* m, size_t idx) {
    TL_ASSERT(idx < m->n_l0);
    return m->l0[idx];
}

TL_INLINE tl_segment_t* tl_manifest_l1_get(const tl_manifest_t* m, size_t idx) {
    TL_ASSERT(idx < m->n_l1);
    return m->l1[idx];
}

TL_INLINE uint64_t tl_manifest_version(const tl_manifest_t* m) {
    return m->version;
}

/*===========================================================================
 * Navigation
 *===========================================================================*/

/**
 * Binary search L1 segments for first with seg->max_ts >= t1.
 * Returns index of first potentially overlapping segment.
 * Returns m->n_l1 if no such segment exists.
 *
 * Used by read path for L1 pruning (Read Path LLD Section 4.1).
 *
 * Note: Uses max_ts (not window_end) for precise pruning.
 * Since L1 segments are non-overlapping by window and sorted by window_start,
 * max_ts is also monotonically non-decreasing.
 *
 * Complexity: O(log n_l1)
 */
size_t tl_manifest_l1_find_first_overlap(const tl_manifest_t* m, tl_ts_t t1);

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG
/**
 * Validate manifest invariants.
 * @return true if valid, false if invariants violated
 *
 * Checks:
 * - L1 segments sorted by window_start
 * - L1 segments non-overlapping by window
 * - All segment pointers non-NULL
 * - Cached bounds correct (if has_bounds)
 */
bool tl_manifest_validate(const tl_manifest_t* m);
#endif

#endif /* TL_MANIFEST_H */
