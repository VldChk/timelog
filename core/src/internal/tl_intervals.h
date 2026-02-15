#ifndef TL_INTERVALS_H
#define TL_INTERVALS_H

#include "tl_defs.h"
#include "tl_alloc.h"

/*===========================================================================
 * Interval Set
 *
 * Stores half-open time intervals [t1, t2) representing tombstones
 * with an associated max sequence number for that range.
 * Provides:
 * - Mutable insert with automatic coalescing
 * - Immutable snapshot for storage attachment
 * - Binary search for point containment
 * - Union of two interval sets
 * - Clipping to a range
 *
 * Used by:
 * - tl_memtable_t.active_tombs (mutable, receives new tombstones)
 * - tl_memrun_t.tombs (immutable, from sealed memtable)
 * - tl_segment_t.tombstones (immutable, attached to L0 segments)
 * - Read path effective tombstone computation (union + clip)
 *
 * Thread Safety:
 * - Not thread-safe. Caller must provide synchronization.
 *===========================================================================*/

/**
 * A single half-open interval [start, end) with max tombstone seq.
 * If end_unbounded is true, represents [start, +inf).
 *
 * When end_unbounded is true, the 'end' field is ignored (set to 0 for clarity).
 * Always check end_unbounded BEFORE reading 'end'.
 */
typedef struct tl_interval {
    tl_ts_t  start;        /* Inclusive start bound */
    tl_ts_t  end;          /* Exclusive end bound (ONLY valid if !end_unbounded) */
    bool     end_unbounded;/* True => [start, +inf), 'end' is ignored */
    tl_seq_t max_seq;      /* Max tombstone seq covering this interval */
} tl_interval_t;

/**
 * Mutable interval set with automatic coalescing.
 * Invariants:
 * - Intervals are sorted by start.
 * - No two intervals overlap.
 * - No two intervals are adjacent (coalesced).
 */
typedef struct tl_intervals {
    tl_interval_t*  data;
    size_t          len;
    size_t          cap;
    tl_alloc_ctx_t* alloc;
} tl_intervals_t;

/**
 * Immutable interval array (for storage/snapshot).
 * Same invariants as mutable set.
 */
typedef struct tl_intervals_imm {
    const tl_interval_t* data;
    size_t               len;
} tl_intervals_imm_t;

/*---------------------------------------------------------------------------
 * Lifecycle
 *---------------------------------------------------------------------------*/

void tl_intervals_init(tl_intervals_t* iv, tl_alloc_ctx_t* alloc);

/**
 * Destroy interval set and free memory.
 * Idempotent: safe to call on already-destroyed or zero-initialized sets.
 * After this call, iv is in a valid empty state.
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
 * Check if timestamp ts is contained in any interval (max_seq > 0).
 * @return true if ts is in [start, end) for some interval, false otherwise
 */
bool tl_intervals_contains(const tl_intervals_t* iv, tl_ts_t ts);
bool tl_intervals_imm_contains(tl_intervals_imm_t iv, tl_ts_t ts);

/**
 * Get max tombstone seq covering ts (0 if none).
 */
tl_seq_t tl_intervals_max_seq(const tl_intervals_t* iv, tl_ts_t ts);
tl_seq_t tl_intervals_imm_max_seq(tl_intervals_imm_t iv, tl_ts_t ts);

/*---------------------------------------------------------------------------
 * Set Operations
 *---------------------------------------------------------------------------*/

/**
 * Compute union of two interval sets into output.
 * Output is cleared first.
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_intervals_union(tl_intervals_t* out,
                               const tl_intervals_t* a,
                               const tl_intervals_t* b);

/**
 * Union variant with immutable inputs.
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
 * Take ownership of intervals array.
 * @return Array pointer (caller must free), NULL if empty
 */
tl_interval_t* tl_intervals_take(tl_intervals_t* iv, size_t* out_len);

/**
 * Compute total span covered by intervals (for delete debt metric).
 * Used by compaction policy for delete-debt calculation.
 *
 * Unbounded interval handling:
 * - SHOULD only be called after clipping to a bounded window.
 * - If an unbounded interval is present, returns TL_TS_MAX (saturated).
 *   This signals "infinite delete debt" which forces compaction.
 *
 * Overflow handling:
 * - Uses saturating addition to prevent signed overflow.
 * - Returns TL_TS_MAX if sum would overflow.
 *
 * @return Sum of (end - start) for all intervals, or TL_TS_MAX if unbounded/overflow
 */
tl_ts_t tl_intervals_covered_span(const tl_intervals_t* iv);

/*---------------------------------------------------------------------------
 * Cursor-Based Iteration (for tombstone filtering)
 *
 * The tombstone filter uses a cursor over sorted intervals to achieve
 * amortized O(1) per-record filtering. The cursor advances forward only.
 *---------------------------------------------------------------------------*/

/**
 * Cursor for efficient tombstone filtering during iteration.
 * Maintains position in a sorted interval set.
 */
typedef struct tl_intervals_cursor {
    const tl_interval_t* data;  /* Interval array (borrowed) */
    size_t               len;   /* Array length */
    size_t               pos;   /* Current position */
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
 * Get max tombstone seq at ts and advance cursor.
 *
 * Algorithm:
 * - Advance cursor while ts >= cur.end (for bounded intervals)
 * - Return max_seq if cur.start <= ts (and ts < cur.end for bounded, always for unbounded)
 *
 * Unbounded interval handling:
 * - An unbounded interval [start, +inf) covers all ts >= start.
 * - Once cursor reaches an unbounded interval, it stays there (all future ts are covered).
 *
 * @param ts Timestamp to check
 * @return max tombstone seq covering ts, or 0 if none
 *
 * Precondition: Timestamps must be passed in non-decreasing order.
 */
tl_seq_t tl_intervals_cursor_max_seq(tl_intervals_cursor_t* cur, tl_ts_t ts);

/**
 * Get the next uncovered timestamp after the current position.
 * Used for skip-ahead optimization during tombstone filtering.
 *
 * If ts is covered by interval [start, end), sets *out = end and returns true.
 * If ts is covered by unbounded interval [start, +inf), returns false
 *   (no uncovered timestamps exist after this point).
 * If ts is not covered, sets *out = ts and returns true.
 *
 * @param cur Cursor
 * @param ts  Timestamp to check
 * @param out Output: next uncovered timestamp (only valid if returns true)
 * @return true if there is a next uncovered timestamp, false if all remaining
 *         timestamps are covered by an unbounded interval
 */
bool tl_intervals_cursor_skip_to(tl_intervals_cursor_t* cur, tl_ts_t ts,
                                  tl_ts_t* out);

/*---------------------------------------------------------------------------
 * Validation (Debug)
 *---------------------------------------------------------------------------*/

#ifdef TL_DEBUG
/**
 * Validate raw interval array invariants.
 *
 * This is the shared validator used by segment and memview validation.
 * Checks:
 * 1. Each bounded interval has start < end
 * 2. Sorted by start timestamp
 * 3. Non-overlapping (prev->end <= cur->start)
 * 4. Non-adjacent / coalesced (prev->end != cur->start)
 * 5. No intervals after an unbounded interval
 *
 * @param data  Array of intervals (may be NULL if len == 0)
 * @param len   Number of intervals
 * @return true if valid, false if any invariant violated
 */
bool tl_intervals_arr_validate(const tl_interval_t* data, size_t len);

/**
 * Validate interval set invariants.
 * Calls tl_intervals_arr_validate() on the internal array.
 *
 * @return true if valid, false if invariants violated
 */
bool tl_intervals_validate(const tl_intervals_t* iv);
#endif

#endif /* TL_INTERVALS_H */
