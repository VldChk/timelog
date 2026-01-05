#ifndef TL_SEGMENT_H
#define TL_SEGMENT_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_atomic.h"
#include "../internal/tl_intervals.h"
#include "tl_page.h"

/*===========================================================================
 * Segment Level
 *
 * Segments are classified by their level:
 * - L0 (delta layer): Flush outputs, may overlap, may carry tombstones
 * - L1 (main layer): Compaction outputs, non-overlapping, no tombstones
 *
 * Reference: Storage LLD Section 3.6
 *===========================================================================*/

typedef enum tl_segment_level {
    TL_SEG_L0 = 0,              /* Delta layer (flush output) */
    TL_SEG_L1 = 1               /* Main layer (compaction output) */
} tl_segment_level_t;

/*===========================================================================
 * Tombstones (Immutable Interval Set)
 *
 * Matches Storage LLD Section 3.5 exactly.
 * Segment holds a POINTER to this struct (NULL if no tombstones).
 *
 * Invariants:
 * - Intervals are sorted by start
 * - Non-overlapping
 * - Coalesced (no adjacent intervals)
 *===========================================================================*/

typedef struct tl_tombstones {
    uint32_t       n;           /* Number of intervals */
    tl_interval_t* v;           /* Sorted, non-overlapping, coalesced */
} tl_tombstones_t;

/*===========================================================================
 * Segment Structure
 *
 * Immutable after construction.
 *
 * L0 Segment Rules:
 * - level = TL_SEG_L0
 * - window_start = window_end = 0
 * - tombstones allowed (may be non-NULL)
 *
 * L1 Segment Rules:
 * - level = TL_SEG_L1
 * - window_start/window_end set to partition boundaries
 * - tombstones must be NULL (tombstones folded during compaction)
 * - All records satisfy: window_start <= ts < window_end
 *
 * Tombstone-Only Segment (L0 only):
 * - page_count = 0, record_count = 0
 * - tombstones != NULL && tombstones->n > 0
 * - min_ts/max_ts derived from tombstones
 *
 * Reference: Storage LLD Section 3.6, Section 5
 *===========================================================================*/

typedef struct tl_segment {
    /* Bounds (for pruning) - max_ts is INCLUSIVE for pruning purposes */
    tl_ts_t   min_ts;           /* Minimum timestamp (inclusive) */
    tl_ts_t   max_ts;           /* Maximum timestamp (inclusive) */

    /* Counts */
    uint64_t  record_count;     /* Total records (sum of page counts) */
    uint32_t  page_count;       /* Number of pages (0 for tombstone-only) */

    /* Level and generation */
    uint32_t  level;            /* tl_segment_level_t */
    uint32_t  generation;       /* Monotonic generation counter (diagnostics) */

    /* Window bounds (L1 only, 0 for L0) */
    tl_ts_t   window_start;     /* Inclusive start (L1 only) */
    tl_ts_t   window_end;       /* Exclusive end (L1 only) */

    /* Page catalog */
    tl_page_catalog_t catalog;

    /* Tombstones (L0 only, NULL for L1) */
    tl_tombstones_t* tombstones;

    /* Reference counting for snapshot safety */
    tl_atomic_u32 refcnt;

    /* Allocator (for destruction) */
    tl_alloc_ctx_t* alloc;
} tl_segment_t;

/*===========================================================================
 * Segment Builder API
 *===========================================================================*/

/**
 * Build an L0 segment from sorted records and optional tombstones.
 *
 * Used by flush builder (Write Path LLD Section 4.3).
 *
 * @param alloc             Allocator context
 * @param records           Sorted record array (may be NULL if tombstone-only)
 * @param record_count      Number of records (may be 0)
 * @param tombstones        Tombstone array (borrowed, copied into segment)
 * @param tombstones_len    Number of tombstones (must be <= UINT32_MAX)
 * @param target_page_bytes Target page size
 * @param generation        Generation counter for diagnostics
 * @param out               Output segment pointer
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EINVAL if both record_count == 0 and tombstones_len == 0,
 *         TL_EINVAL if tombstones_len > UINT32_MAX
 *
 * Segment bounds for tombstone-only segments:
 * - min_ts = min(tombstones[i].start)
 * - max_ts = max(tombstones[i].end - 1) for bounded, TL_TS_MAX for unbounded
 *
 * Returned segment has refcnt = 1 (caller owns reference).
 */
tl_status_t tl_segment_build_l0(tl_alloc_ctx_t* alloc,
                                 const tl_record_t* records, size_t record_count,
                                 const tl_interval_t* tombstones, size_t tombstones_len,
                                 size_t target_page_bytes,
                                 uint32_t generation,
                                 tl_segment_t** out);

/**
 * Build an L1 segment from sorted records within a window.
 *
 * Used by compaction builder (Compaction Policy LLD Section 7).
 *
 * @param alloc             Allocator context
 * @param records           Sorted record array (must not be NULL, count > 0)
 * @param record_count      Number of records
 * @param target_page_bytes Target page size
 * @param window_start      Window start (inclusive)
 * @param window_end        Window end (exclusive)
 * @param generation        Generation counter
 * @param out               Output segment pointer
 * @return TL_OK on success, TL_ENOMEM on failure, TL_EINVAL if records empty
 *
 * Precondition: All records satisfy window_start <= ts < window_end.
 *
 * Returned segment has refcnt = 1 (caller owns reference).
 */
tl_status_t tl_segment_build_l1(tl_alloc_ctx_t* alloc,
                                 const tl_record_t* records, size_t record_count,
                                 size_t target_page_bytes,
                                 tl_ts_t window_start, tl_ts_t window_end,
                                 uint32_t generation,
                                 tl_segment_t** out);

/*===========================================================================
 * Reference Counting
 *
 * Memory ordering for reference counting:
 * - Acquire (increment): relaxed is sufficient for the fetch-add itself
 * - Release (decrement): release ordering ensures all prior writes are visible
 *   before the potential destruction
 * - Destruction: acquire fence before destroy to synchronize with releasers
 *
 * Pattern for release:
 *   uint32_t old = tl_atomic_fetch_sub_u32(&refcnt, 1, TL_MO_RELEASE);
 *   if (old == 1) {
 *       tl_atomic_fence(TL_MO_ACQUIRE);
 *       destroy(obj);
 *   }
 *
 * Reference: Implementation Notes Section 7.2, 7.3
 *===========================================================================*/

/**
 * Increment reference count (pin segment).
 * Returns the segment for convenience.
 */
tl_segment_t* tl_segment_acquire(tl_segment_t* seg);

/**
 * Decrement reference count. Destroys segment when refcnt reaches 0.
 */
void tl_segment_release(tl_segment_t* seg);

/**
 * Get current reference count (for debugging).
 */
TL_INLINE uint32_t tl_segment_refcnt(const tl_segment_t* seg) {
    return tl_atomic_load_relaxed_u32(&((tl_segment_t*)seg)->refcnt);
}

/*===========================================================================
 * Accessors
 *===========================================================================*/

TL_INLINE bool tl_segment_is_l0(const tl_segment_t* seg) {
    return seg->level == TL_SEG_L0;
}

TL_INLINE bool tl_segment_is_l1(const tl_segment_t* seg) {
    return seg->level == TL_SEG_L1;
}

TL_INLINE bool tl_segment_is_tombstone_only(const tl_segment_t* seg) {
    return seg->page_count == 0 && seg->tombstones != NULL && seg->tombstones->n > 0;
}

TL_INLINE bool tl_segment_has_tombstones(const tl_segment_t* seg) {
    return seg->tombstones != NULL && seg->tombstones->n > 0;
}

/**
 * Get immutable view of tombstones for read path.
 * Returns empty view if tombstones is NULL.
 */
TL_INLINE tl_intervals_imm_t tl_segment_tombstones_imm(const tl_segment_t* seg) {
    tl_intervals_imm_t imm;
    if (seg->tombstones != NULL) {
        imm.data = seg->tombstones->v;
        imm.len = seg->tombstones->n;
    } else {
        imm.data = NULL;
        imm.len = 0;
    }
    return imm;
}

/**
 * Get page catalog (for iteration).
 */
TL_INLINE const tl_page_catalog_t* tl_segment_catalog(const tl_segment_t* seg) {
    return &seg->catalog;
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG
/**
 * Validate segment invariants.
 * @return true if valid, false if invariants violated
 *
 * Checks:
 * - L0: window_start == window_end == 0
 * - L1: tombstones == NULL, records within window bounds
 * - Tombstone-only: page_count == 0, tombstones non-empty
 * - Page catalog valid
 * - min_ts/max_ts correct
 */
bool tl_segment_validate(const tl_segment_t* seg);
#endif

#endif /* TL_SEGMENT_H */
