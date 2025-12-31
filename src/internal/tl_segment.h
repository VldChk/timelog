#ifndef TL_SEGMENT_H
#define TL_SEGMENT_H

#include "tl_defs.h"
#include "tl_alloc.h"
#include "tl_atomic.h"
#include "tl_page.h"
#include "tl_tombstones.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Segment kind: delta (flush output) or main (compaction output).
 */
typedef enum tl_segment_kind {
    TL_SEG_DELTA = 0,  /* Output of memtable flush */
    TL_SEG_MAIN  = 1   /* Output of compaction */
} tl_segment_kind_t;

/**
 * Immutable segment structure.
 *
 * A segment is the unit of storage organization:
 * - Produced by flush (delta) or compaction (main)
 * - Contains pages and/or tombstones
 * - Referenced by manifests
 * - Lifetime managed by reference counting
 *
 * Invariants:
 * - Immutable after creation
 * - Pages are sorted by min_ts
 * - Page ranges within segment are non-overlapping
 * - Tombstone-only segments have page_count == 0 but meaningful min/max_ts
 */
typedef struct tl_segment {
    /* Hot metadata */
    tl_ts_t             min_ts;        /* Min timestamp across pages or tombstones */
    tl_ts_t             max_ts;        /* Max timestamp across pages or tombstones */
    uint64_t            record_count;  /* Sum of page counts */
    uint32_t            page_count;    /* Number of pages */
    uint32_t            kind;          /* tl_segment_kind_t */
    uint32_t            generation;    /* Monotonic ID for diagnostics/ordering */
    uint32_t            reserved;

    /* Page catalog (may be empty for tombstone-only segments) */
    tl_page_catalog_t   catalog;

    /* Tombstones flushed with this segment (may be NULL) */
    tl_tombstones_t*    tombstones;

    /* Allocator used for this segment */
    const tl_allocator_t* alloc;

    /* Lifetime management: reference count */
    tl_atomic_u32_t     refcnt;
} tl_segment_t;

/**
 * Create a segment from pages and tombstones.
 *
 * @param alloc      Allocator to use
 * @param pages      Array of page pointers (ownership transferred)
 * @param n_pages    Number of pages
 * @param tombstones Tombstone set (ownership transferred, may be NULL)
 * @param kind       Segment kind (delta or main)
 * @param generation Generation number for diagnostics
 * @param out        Output pointer for new segment
 * @return TL_OK on success
 */
tl_status_t tl_segment_create(const tl_allocator_t* alloc,
                               tl_page_t** pages,
                               uint32_t n_pages,
                               tl_tombstones_t* tombstones,
                               tl_segment_kind_t kind,
                               uint32_t generation,
                               tl_segment_t** out);

/**
 * Create a tombstone-only segment.
 *
 * @param alloc      Allocator to use
 * @param tombstones Tombstone set (ownership transferred, must not be NULL/empty)
 * @param kind       Segment kind
 * @param generation Generation number
 * @param out        Output pointer for new segment
 * @return TL_OK on success, TL_EINVAL if tombstones empty
 */
tl_status_t tl_segment_create_tombstone_only(const tl_allocator_t* alloc,
                                              tl_tombstones_t* tombstones,
                                              tl_segment_kind_t kind,
                                              uint32_t generation,
                                              tl_segment_t** out);

/**
 * Increment segment reference count.
 *
 * @param seg Segment to acquire
 * @return New reference count
 */
uint32_t tl_segment_acquire(tl_segment_t* seg);

/**
 * Decrement segment reference count.
 *
 * When refcnt reaches 0, the segment is destroyed.
 *
 * @param seg Segment to release
 * @return New reference count (0 means segment was destroyed)
 */
uint32_t tl_segment_release(tl_segment_t* seg);

/**
 * Check if segment overlaps query range [t1, t2).
 *
 * Uses the standard overlap predicate:
 *   seg.max_ts >= t1 AND (t2 unbounded OR seg.min_ts < t2)
 *
 * @param seg Segment to check
 * @param t1  Range start (inclusive)
 * @param t2  Range end (exclusive)
 * @param t2_unbounded True if range has no upper bound
 * @return true if segment overlaps range
 */
TL_INLINE bool tl_segment_overlaps(const tl_segment_t* seg, tl_ts_t t1, tl_ts_t t2,
                                   bool t2_unbounded) {
    if (seg == NULL) return false;
    return seg->max_ts >= t1 && tl_ts_before_end(seg->min_ts, t2, t2_unbounded);
}

/**
 * Validate segment invariants (debug/test).
 *
 * Checks:
 * - Page catalog is sorted by min_ts
 * - Each page passes validation
 * - min_ts/max_ts are correct
 * - Tombstones are well-formed
 *
 * @param seg Segment to validate
 * @return TL_OK if valid, TL_EINTERNAL if invariant violated
 */
tl_status_t tl_segment_validate(const tl_segment_t* seg);

/*===========================================================================
 * Segment Builder
 *===========================================================================*/

/**
 * Segment builder for constructing segments from sorted record streams.
 *
 * Usage:
 *   1. tl_segment_builder_init() with config
 *   2. tl_segment_builder_add() records in sorted order
 *   3. tl_segment_builder_set_tombstones() (optional)
 *   4. tl_segment_builder_finish() to create the segment
 */
typedef struct tl_segment_builder {
    const tl_allocator_t* alloc;

    /* Page building */
    tl_page_builder_t     page_builder;
    tl_page_t**           pages;        /* Accumulated pages */
    uint32_t              n_pages;
    uint32_t              pages_cap;

    /* Tombstones */
    tl_tombstones_t*      tombstones;

    /* Config */
    uint32_t              page_capacity;  /* Records per page */
    tl_segment_kind_t     kind;
    uint32_t              generation;
} tl_segment_builder_t;

/**
 * Initialize a segment builder.
 *
 * @param builder       Builder to initialize
 * @param alloc         Allocator to use
 * @param page_capacity Maximum records per page
 * @param kind          Segment kind (delta or main)
 * @param generation    Generation number
 * @return TL_OK on success
 */
tl_status_t tl_segment_builder_init(tl_segment_builder_t* builder,
                                     const tl_allocator_t* alloc,
                                     uint32_t page_capacity,
                                     tl_segment_kind_t kind,
                                     uint32_t generation);

/**
 * Destroy segment builder resources.
 *
 * Note: This also destroys any pages that were built but not yet
 * transferred to a segment.
 */
void tl_segment_builder_destroy(tl_segment_builder_t* builder);

/**
 * Add a record to the segment.
 *
 * Precondition: records must be added in non-decreasing timestamp order.
 *
 * When the current page fills, it is automatically finalized and a
 * new page is started.
 *
 * @param builder Builder to add to
 * @param ts      Timestamp
 * @param handle  Handle
 * @return TL_OK on success
 */
tl_status_t tl_segment_builder_add(tl_segment_builder_t* builder,
                                    tl_ts_t ts,
                                    tl_handle_t handle);

/**
 * Set tombstones for the segment.
 *
 * Ownership of tombstones is transferred to the builder.
 *
 * @param builder    Builder to set tombstones for
 * @param tombstones Tombstone set (ownership transferred)
 */
void tl_segment_builder_set_tombstones(tl_segment_builder_t* builder,
                                        tl_tombstones_t* tombstones);

/**
 * Finish building and create an immutable segment.
 *
 * This finalizes any in-progress page and creates the segment.
 *
 * @param builder Builder to finish
 * @param out     Output pointer for new segment
 * @return TL_OK on success, TL_EOF if builder has no content
 */
tl_status_t tl_segment_builder_finish(tl_segment_builder_t* builder,
                                       tl_segment_t** out);

#ifdef __cplusplus
}
#endif

#endif /* TL_SEGMENT_H */
