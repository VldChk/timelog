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
 * - Coalesced (no adjacent intervals with equal max_seq)
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

    /* Record-only bounds (valid when page_count > 0) */
    tl_ts_t   record_min_ts;    /* First record ts (inclusive) */
    tl_ts_t   record_max_ts;    /* Last record ts (inclusive) */

    /* Tombstone-only bounds (valid when tombstones exist) */
    tl_ts_t   tomb_min_ts;      /* Min tombstone start */
    tl_ts_t   tomb_max_ts;      /* Max tombstone end-1 (or TL_TS_MAX if unbounded) */

    /* Counts */
    uint64_t  record_count;     /* Cached total; validated vs page catalog */
    uint32_t  page_count;       /* Number of pages (0 for tombstone-only) */

    /* Level and generation */
    uint32_t  level;            /* tl_segment_level_t */
    uint32_t  generation;       /* Monotonic generation counter (diagnostics) */
    /*
     * Tombstone watermark applied to this segment.
     *
     * CONTRACT: For immutable source S with S.applied_seq = X, all
     * tombstones with seq <= X were physically applied to S's records
     * at build time. Surviving records have either:
     *   - tomb_seq <= X: tombstone already applied, record survived
     *   - tomb_seq > X:  tombstone newer, must be checked at query time
     *
     * INVARIANT: applied_seq >= max(tombstones[i].max_seq) for all
     * tombstones stored in this segment.
     *
     * INVARIANT: For L0 segments produced in order, applied_seq is
     * non-decreasing with generation (flush assigns op_seq at seal time).
     *
     * CRITICAL: During flush, applied_seq and the tombstone set MUST come
     * from the same snapshot to preserve the watermark guarantee.
     */
    tl_seq_t  applied_seq;

    /* Window bounds (L1 only, 0 for L0) */
    tl_ts_t   window_start;     /* Inclusive start (L1 only) */
    tl_ts_t   window_end;       /* Exclusive end (L1 only) */
    bool      window_end_unbounded; /* True if window extends to +infinity (L1 only) */

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
 *         TL_EINVAL if tombstones_len > UINT32_MAX,
 *         TL_EINVAL if tombstones_len > 0 but tombstones == NULL,
 *         TL_EINVAL if record_count > 0 but records == NULL
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
                                 tl_seq_t applied_seq,
                                 tl_segment_t** out);

/**
 * Build an L1 segment from sorted records within a window.
 *
 * Used by compaction builder (Compaction Policy LLD Section 7).
 *
 * @param alloc               Allocator context
 * @param records             Sorted record array (must not be NULL, count > 0)
 * @param record_count        Number of records
 * @param target_page_bytes   Target page size
 * @param window_start        Window start (inclusive)
 * @param window_end          Window end (exclusive); TL_TS_MAX when unbounded
 * @param window_end_unbounded True if window extends to +infinity
 * @param generation          Generation counter
 * @param out                 Output segment pointer (set to NULL on error)
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EINVAL if records empty or NULL,
 *         TL_EINVAL if window_end_unbounded is true but window_end != TL_TS_MAX
 *
 * Precondition: All records satisfy window_start <= ts < window_end
 *               (or ts >= window_start if window_end_unbounded).
 * Invariant: window_end_unbounded implies window_end == TL_TS_MAX.
 *            This is enforced at runtime (returns TL_EINVAL on violation).
 *
 * Returned segment has refcnt = 1 (caller owns reference).
 */
tl_status_t tl_segment_build_l1(tl_alloc_ctx_t* alloc,
                                 const tl_record_t* records, size_t record_count,
                                 size_t target_page_bytes,
                                 tl_ts_t window_start, tl_ts_t window_end,
                                 bool window_end_unbounded,
                                 uint32_t generation,
                                 tl_seq_t applied_seq,
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

TL_INLINE bool tl_segment_has_records(const tl_segment_t* seg) {
    return seg->page_count > 0;
}

TL_INLINE bool tl_segment_has_tombstones(const tl_segment_t* seg) {
    return seg->tombstones != NULL && seg->tombstones->n > 0;
}

TL_INLINE tl_ts_t tl_segment_record_min_ts(const tl_segment_t* seg) {
    return seg->record_min_ts;
}

TL_INLINE tl_ts_t tl_segment_record_max_ts(const tl_segment_t* seg) {
    return seg->record_max_ts;
}

TL_INLINE tl_ts_t tl_segment_tomb_min_ts(const tl_segment_t* seg) {
    return seg->tomb_min_ts;
}

TL_INLINE tl_ts_t tl_segment_tomb_max_ts(const tl_segment_t* seg) {
    return seg->tomb_max_ts;
}

TL_INLINE tl_seq_t tl_segment_applied_seq(const tl_segment_t* seg) {
    return seg->applied_seq;
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
