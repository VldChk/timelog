#ifndef TL_INTERVALS_H
#define TL_INTERVALS_H

#include "tl_defs.h"
#include "tl_alloc.h"

/*===========================================================================
 * Interval Set
 *
 * Canonical store for tombstone intervals. The set is kept in a fully
 * canonical form: half-open [start, end) intervals, sorted by start,
 * non-overlapping and non-adjacent (any touching intervals are coalesced).
 * Each interval also carries the maximum tombstone sequence number that
 * covered it, which the read path uses to enforce write-vs-delete ordering.
 *
 * The same data layout is exposed mutably (with coalescing insert) and as
 * an immutable view; the mutable form is used while building tombstones in
 * the memtable, the immutable form is what gets attached to sealed runs
 * and on-disk segments and what the read path scans.
 *
 * Not thread-safe; callers serialise access externally.
 *===========================================================================*/

/**
 * Half-open interval [start, end), or [start, +inf) when end_unbounded.
 *
 * The end field is meaningful only when end_unbounded is false; the writer
 * stores zero in that case to keep the union obvious in debuggers. Always
 * consult end_unbounded before reading end.
 */
typedef struct tl_interval {
    tl_ts_t  start;
    tl_ts_t  end;          /* Valid only when end_unbounded == false. */
    bool     end_unbounded;
    tl_seq_t max_seq;      /* Max tombstone seq covering this interval. */
} tl_interval_t;

/**
 * Mutable interval set. The canonicalisation invariants (sorted, disjoint,
 * coalesced) are restored by every insert, so callers can rely on them
 * without re-validating.
 */
typedef struct tl_intervals {
    tl_interval_t*  data;
    size_t          len;
    size_t          cap;
    tl_alloc_ctx_t* alloc;
} tl_intervals_t;

/** Immutable view over the same data layout used by tl_intervals_t. */
typedef struct tl_intervals_imm {
    const tl_interval_t* data;
    size_t               len;
} tl_intervals_imm_t;

/*---------------------------------------------------------------------------
 * Lifecycle
 *---------------------------------------------------------------------------*/

void tl_intervals_init(tl_intervals_t* iv, tl_alloc_ctx_t* alloc);

/**
 * Release storage and reset to a valid empty state. Idempotent so it can
 * appear in any cleanup path regardless of how far init progressed.
 */
void tl_intervals_destroy(tl_intervals_t* iv);

void tl_intervals_clear(tl_intervals_t* iv);

/*---------------------------------------------------------------------------
 * Insertion (with coalescing)
 *---------------------------------------------------------------------------*/

/**
 * Insert a bounded interval [t1, t2).
 *
 * Semantics:
 * - t1 > t2:  Returns TL_EINVAL (invalid interval)
 * - t1 == t2: Returns TL_OK (no-op, empty interval not stored)
 * - t1 < t2:  Inserts and coalesces
 *
 * @return TL_OK on success (including no-op for t1==t2)
 *         TL_EINVAL if t1 > t2
 *         TL_ENOMEM on allocation failure
 *
 * Coalescing rules:
 * - Overlapping intervals are merged.
 * - Adjacent intervals (end1 == start2) are merged.
 * - Unboundedness propagates: merging with [x, +inf) yields unbounded result.
 */
tl_status_t tl_intervals_insert(tl_intervals_t* iv,
                                 tl_ts_t t1,
                                 tl_ts_t t2,
                                 tl_seq_t seq);

/**
 * Insert an unbounded interval [t1, +inf).
 *
 * This interval contains ALL timestamps >= t1, including INT64_MAX.
 * When merged with any overlapping/adjacent bounded interval, the result
 * is unbounded.
 *
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_intervals_insert_unbounded(tl_intervals_t* iv,
                                           tl_ts_t t1,
                                           tl_seq_t seq);

/*---------------------------------------------------------------------------
 * Point Containment
 *---------------------------------------------------------------------------*/

/**
 * Get max tombstone seq covering ts (0 if none).
 */
tl_seq_t tl_intervals_imm_max_seq(tl_intervals_imm_t iv, tl_ts_t ts);

/*---------------------------------------------------------------------------
 * Set Operations
 *---------------------------------------------------------------------------*/

/**
 * Compute union of two immutable interval sets into output.
 * Output is cleared first.
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_intervals_union_imm(tl_intervals_t* out,
                                   tl_intervals_imm_t a,
                                   tl_intervals_imm_t b);

/**
 * Clip intervals to [t1, t2) range.
 * Intervals fully outside the range are removed.
 * Intervals partially inside are truncated.
 * Modifies in place.
 *
 * Unbounded interval handling:
 * - An unbounded interval [start, +inf) clipped to [t1, t2) becomes:
 *   - Removed if start >= t2
 *   - Bounded [max(start, t1), t2) otherwise
 *
 * After clipping, all intervals are guaranteed to be bounded.
 *
 * Precondition: t1 < t2 (the clip range must be non-empty and bounded)
 */
void tl_intervals_clip(tl_intervals_t* iv, tl_ts_t t1, tl_ts_t t2);

/**
 * Clip intervals to [t1, +inf) - only lower bound.
 *
 * Removes intervals that end before t1 (bounded intervals where end <= t1).
 * Truncates intervals that overlap t1 (sets start = max(start, t1)).
 * Unbounded intervals [start, +inf) are kept if start >= t1 or truncated otherwise.
 *
 * This is used for unbounded queries where we cannot clip to a finite upper bound.
 *
 * Unlike tl_intervals_clip(), unbounded intervals remain unbounded after clipping.
 *
 * @param iv  Interval set to clip in place
 * @param t1  Lower bound (inclusive)
 */
void tl_intervals_clip_lower(tl_intervals_t* iv, tl_ts_t t1);

/*---------------------------------------------------------------------------
 * Accessors
 *---------------------------------------------------------------------------*/

TL_INLINE size_t tl_intervals_len(const tl_intervals_t* iv) {
    return iv->len;
}

TL_INLINE bool tl_intervals_is_empty(const tl_intervals_t* iv) {
    return iv->len == 0;
}

TL_INLINE const tl_interval_t* tl_intervals_get(const tl_intervals_t* iv, size_t idx) {
    TL_ASSERT(idx < iv->len);
    return &iv->data[idx];
}

/**
 * Create an immutable view of the intervals.
 */
TL_INLINE tl_intervals_imm_t tl_intervals_as_imm(const tl_intervals_t* iv) {
    tl_intervals_imm_t imm;
    imm.data = iv->data;
    imm.len = iv->len;
    return imm;
}

/**
 * Detach the underlying array and transfer ownership to the caller. The
 * source set becomes empty (its capacity is released too). The returned
 * buffer must be freed with the same allocator that was used to construct
 * the set.
 *
 * @return Array pointer, or NULL if the set was empty.
 */
tl_interval_t* tl_intervals_take(tl_intervals_t* iv, size_t* out_len);

/*---------------------------------------------------------------------------
 * Cursor-Based Iteration
 *
 * The query path scans records in non-decreasing timestamp order. A cursor
 * over the (also sorted) interval set lets us match each record against
 * tombstones in amortised O(1): the cursor only ever moves forward, so the
 * combined cost over a scan is O(records + intervals).
 *---------------------------------------------------------------------------*/

typedef struct tl_intervals_cursor {
    const tl_interval_t* data;  /* Borrowed; outlives the cursor. */
    size_t               len;
    size_t               pos;
} tl_intervals_cursor_t;

/**
 * Initialize cursor from immutable interval set.
 */
TL_INLINE void tl_intervals_cursor_init(tl_intervals_cursor_t* cur,
                                        tl_intervals_imm_t iv) {
    cur->data = iv.data;
    cur->len = iv.len;
    cur->pos = 0;
}

/**
 * Return the highest tombstone sequence number covering ts and advance the
 * cursor past intervals that ended before ts. An unbounded interval stops
 * the cursor's forward motion entirely, since it covers all subsequent
 * timestamps.
 *
 * Precondition: ts values across successive calls are non-decreasing.
 * @return The covering tombstone seq, or 0 when ts is uncovered.
 */
tl_seq_t tl_intervals_cursor_max_seq(tl_intervals_cursor_t* cur, tl_ts_t ts);

/**
 * Skip-ahead helper used to fast-forward iteration past a covered region.
 *
 * If ts falls inside a bounded interval [start, end), *out is set to end so
 * the caller can resume scanning at the first uncovered timestamp. If ts
 * falls inside an unbounded interval, no uncovered timestamps remain and
 * the function returns false. If ts is already uncovered, *out is set to ts.
 *
 * @return true if a next uncovered timestamp exists, false if everything
 *         remaining is swallowed by an unbounded interval.
 */
bool tl_intervals_cursor_skip_to(tl_intervals_cursor_t* cur, tl_ts_t ts,
                                  tl_ts_t* out);

/*---------------------------------------------------------------------------
 * Validation (Debug)
 *---------------------------------------------------------------------------*/

#ifdef TL_DEBUG
/**
 * Verify the canonical-form invariants on a raw interval array. Shared by
 * segment and memview validators so they all enforce the same rules:
 *   1. Bounded intervals satisfy start < end.
 *   2. Intervals are sorted by start.
 *   3. They are pairwise non-overlapping (prev->end <= cur->start).
 *   4. They are coalesced (prev->end != cur->start).
 *   5. No bounded interval follows an unbounded one.
 *
 * @param data May be NULL when len == 0.
 * @return true on a valid array, false on any invariant violation.
 */
bool tl_intervals_arr_validate(const tl_interval_t* data, size_t len);

/** Convenience wrapper that validates the array embedded in iv. */
bool tl_intervals_validate(const tl_intervals_t* iv);
#endif

#endif /* TL_INTERVALS_H */
