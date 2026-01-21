/*
============================================================================

   COMBINED HEADER FILE: query.h

   Generated from: core/src/query/
   Generated at:   2026-01-20 23:27:38

   This file combines all .h files from the query/ subfolder.

   Files included:
 *   - tl_active_iter.h
 *   - tl_filter.h
 *   - tl_memrun_iter.h
 *   - tl_merge_iter.h
 *   - tl_pagespan_iter.h
 *   - tl_plan.h
 *   - tl_point.h
 *   - tl_segment_iter.h
 *   - tl_snapshot.h

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: tl_active_iter.h
/*   FROM: query/
/*
/******************************************************************************/
#ifndef TL_ACTIVE_ITER_H
#define TL_ACTIVE_ITER_H

#include "../internal/tl_defs.h"
#include "../delta/tl_memview.h"

/*===========================================================================
 * Active Memview Iterator
 *
 * Two-way merge over active_run and active_ooo from a memview.
 * Follows the same pattern as tl_memrun_iter but operates on memview buffers.
 *
 * UNBOUNDED QUERY DESIGN:
 * - If t2_unbounded == true, the query is [t1, +inf)
 * - When t2_unbounded is true, the 't2' field is ignored (pass 0 for clarity)
 *
 * Thread Safety:
 * - Not thread-safe (each thread needs its own iterator)
 * - Memview must remain valid for the lifetime of the iterator
 *
 * Reference: Read Path LLD Section 5.2
 *===========================================================================*/

typedef struct tl_active_iter {
    const tl_memview_t* mv;

    /* Range bounds */
    tl_ts_t         t1;
    tl_ts_t         t2;              /* ONLY valid if !t2_unbounded */
    bool            t2_unbounded;

    /* Positions in run and ooo */
    size_t          run_pos;
    size_t          run_end;
    size_t          ooo_pos;
    size_t          ooo_end;

    /* State */
    bool            done;
    bool            has_current;
    tl_record_t     current;
} tl_active_iter_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Initialize active iterator for range [t1, t2) or [t1, +inf).
 *
 * After init, call tl_active_iter_next() to get the first record.
 *
 * @param it           Iterator to initialize
 * @param mv           Memview to iterate (must remain valid)
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY used if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 */
void tl_active_iter_init(tl_active_iter_t* it,
                          const tl_memview_t* mv,
                          tl_ts_t t1, tl_ts_t t2,
                          bool t2_unbounded);

/*===========================================================================
 * Iteration
 *===========================================================================*/

/**
 * Advance to next record.
 *
 * @param it   Iterator
 * @param out  Output record (may be NULL)
 * @return TL_OK if record available, TL_EOF if exhausted
 */
tl_status_t tl_active_iter_next(tl_active_iter_t* it, tl_record_t* out);

/**
 * Seek to first record with ts >= target.
 *
 * @param it     Iterator
 * @param target Target timestamp
 */
void tl_active_iter_seek(tl_active_iter_t* it, tl_ts_t target);

/*===========================================================================
 * State Queries
 *===========================================================================*/

/**
 * Check if iterator is exhausted.
 */
TL_INLINE bool tl_active_iter_done(const tl_active_iter_t* it) {
    TL_ASSERT(it != NULL);
    return it->done;
}

/**
 * Peek at current record without advancing.
 * Precondition: !done && has_current
 */
TL_INLINE const tl_record_t* tl_active_iter_peek(const tl_active_iter_t* it) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(!it->done && it->has_current);
    return &it->current;
}

/**
 * Check if iterator has a current record.
 */
TL_INLINE bool tl_active_iter_has_current(const tl_active_iter_t* it) {
    TL_ASSERT(it != NULL);
    return !it->done && it->has_current;
}

#endif /* TL_ACTIVE_ITER_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_active_iter.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_filter.h
/*   FROM: query/
/*
/******************************************************************************/
#ifndef TL_FILTER_H
#define TL_FILTER_H

#include "../internal/tl_defs.h"
#include "../internal/tl_intervals.h"
#include "tl_merge_iter.h"

/*===========================================================================
 * Filtered Iterator
 *
 * Wraps a K-way merge iterator and filters out records covered by tombstones.
 * Uses a cursor-based approach for efficient filtering with amortized O(1)
 * per-record cost.
 *
 * Algorithm (Read Path LLD Section 7):
 * 1. Get next record from merge iterator
 * 2. Check if record's timestamp is deleted using tombstone cursor
 * 3. If deleted, skip and repeat
 * 4. If not deleted, return the record
 *
 * The tombstone cursor takes advantage of the fact that both the merge iterator
 * output and the tombstone intervals are sorted. The cursor advances forward
 * only, never backwards, achieving amortized O(1) per record.
 *
 * Thread Safety:
 * - Not thread-safe (each thread needs its own iterator)
 * - Underlying merge iterator must remain valid
 *
 * Reference: Read Path LLD Section 7
 *===========================================================================*/

typedef struct tl_filter_iter {
    /* Underlying K-way merge iterator (borrowed, must remain valid) */
    tl_kmerge_iter_t*     merge;

    /* Tombstone cursor for efficient deletion checking */
    tl_intervals_cursor_t tomb_cursor;

    /* State */
    bool                  done;
} tl_filter_iter_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Initialize filtered iterator.
 *
 * @param it      Iterator to initialize
 * @param merge   Underlying K-way merge iterator (must remain valid)
 * @param tombs   Tombstone intervals (sorted, non-overlapping)
 */
void tl_filter_iter_init(tl_filter_iter_t* it,
                          tl_kmerge_iter_t* merge,
                          tl_intervals_imm_t tombs);

/*===========================================================================
 * Iteration
 *===========================================================================*/

/**
 * Get next visible record.
 *
 * Skips records that are covered by tombstones.
 * Returns records in non-decreasing timestamp order.
 *
 * @param it   Iterator
 * @param out  Output record
 * @return TL_OK if record available, TL_EOF if exhausted
 */
tl_status_t tl_filter_iter_next(tl_filter_iter_t* it, tl_record_t* out);

/*===========================================================================
 * State Queries
 *===========================================================================*/

/**
 * Check if iterator is exhausted.
 */
TL_INLINE bool tl_filter_iter_done(const tl_filter_iter_t* it) {
    TL_ASSERT(it != NULL);
    return it->done;
}

#endif /* TL_FILTER_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_filter.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memrun_iter.h
/*   FROM: query/
/*
/******************************************************************************/
#ifndef TL_MEMRUN_ITER_H
#define TL_MEMRUN_ITER_H

#include "../internal/tl_defs.h"
#include "../delta/tl_memrun.h"

/*===========================================================================
 * Memrun Iterator
 *
 * Two-way merge over run[] and ooo[] arrays within a memrun.
 * Produces records in timestamp order (run preferred on ties for stability).
 *
 * UNBOUNDED QUERY DESIGN:
 * - If t2_unbounded == true, the query is [t1, +inf)
 * - When t2_unbounded is true, the 't2' field is ignored (pass 0 for clarity)
 *
 * Thread Safety:
 * - Not thread-safe (each thread needs its own iterator)
 * - Memrun must remain valid for the lifetime of the iterator
 *
 * Reference: Read Path LLD Section 5.2
 *===========================================================================*/

typedef struct tl_memrun_iter {
    const tl_memrun_t* mr;

    /* Range bounds */
    tl_ts_t         t1;
    tl_ts_t         t2;              /* ONLY valid if !t2_unbounded */
    bool            t2_unbounded;

    /* Positions in run and ooo */
    size_t          run_pos;
    size_t          run_end;
    size_t          ooo_pos;
    size_t          ooo_end;

    /* State */
    bool            done;
    bool            has_current;
    tl_record_t     current;
} tl_memrun_iter_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Initialize memrun iterator for range [t1, t2) or [t1, +inf).
 *
 * After init, call tl_memrun_iter_next() to get the first record.
 *
 * @param it           Iterator to initialize
 * @param mr           Memrun to iterate (must remain valid)
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY used if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 */
void tl_memrun_iter_init(tl_memrun_iter_t* it,
                          const tl_memrun_t* mr,
                          tl_ts_t t1, tl_ts_t t2,
                          bool t2_unbounded);

/*===========================================================================
 * Iteration
 *===========================================================================*/

/**
 * Advance to next record.
 *
 * @param it   Iterator
 * @param out  Output record (may be NULL)
 * @return TL_OK if record available, TL_EOF if exhausted
 */
tl_status_t tl_memrun_iter_next(tl_memrun_iter_t* it, tl_record_t* out);

/**
 * Seek to first record with ts >= target.
 *
 * If target is before current position, does nothing.
 * If target is past range end, iterator becomes exhausted.
 *
 * @param it     Iterator
 * @param target Target timestamp
 */
void tl_memrun_iter_seek(tl_memrun_iter_t* it, tl_ts_t target);

/*===========================================================================
 * State Queries
 *===========================================================================*/

/**
 * Check if iterator is exhausted.
 */
TL_INLINE bool tl_memrun_iter_done(const tl_memrun_iter_t* it) {
    TL_ASSERT(it != NULL);
    return it->done;
}

/**
 * Peek at current record without advancing.
 * Precondition: !done && has_current
 */
TL_INLINE const tl_record_t* tl_memrun_iter_peek(const tl_memrun_iter_t* it) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(!it->done && it->has_current);
    return &it->current;
}

/**
 * Check if iterator has a current record.
 */
TL_INLINE bool tl_memrun_iter_has_current(const tl_memrun_iter_t* it) {
    TL_ASSERT(it != NULL);
    return !it->done && it->has_current;
}

#endif /* TL_MEMRUN_ITER_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_memrun_iter.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_merge_iter.h
/*   FROM: query/
/*
/******************************************************************************/
#ifndef TL_KMERGE_ITER_H
#define TL_KMERGE_ITER_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_heap.h"
#include "tl_plan.h"

/*===========================================================================
 * K-way Merge Iterator
 *
 * K-way merge over all component iterators (segments, memruns, active).
 * Uses a min-heap to efficiently produce records in sorted order.
 *
 * NOTE: This is distinct from tl_merge_iter_t in tl_flush.h, which is
 * a simple two-way merge used during flush. This is a K-way merge for
 * the read path query execution.
 *
 * The merge iterator takes a query plan as input. The plan contains
 * initialized iterators for all sources that overlap the query range.
 *
 * Algorithm:
 * 1. Initialize: prime each source iterator with next(), push onto heap
 * 2. On next(): pop minimum, output record, advance source, push replacement
 * 3. Continue until heap is empty
 *
 * Tie-Breaking (implementation detail, not a public guarantee):
 * - On timestamp ties, sources are ordered by component_id (source index)
 * - This provides deterministic results for testing, but clients must not
 *   depend on tie-break ordering - it may change in future versions
 *
 * Thread Safety:
 * - Not thread-safe (each thread needs its own iterator)
 * - Plan must remain valid for the lifetime of the iterator
 *
 * Reference: Read Path LLD Section 6
 *===========================================================================*/

typedef struct tl_kmerge_iter {
    /* Min-heap for K-way merge */
    tl_heap_t       heap;

    /* Source plan (borrowed, must remain valid) */
    tl_plan_t*      plan;

    /* State */
    bool            done;

    /* Allocator (borrowed) */
    tl_alloc_ctx_t* alloc;
} tl_kmerge_iter_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Initialize K-way merge iterator from query plan.
 *
 * Primes all component iterators and builds the initial heap.
 * If no sources have data, the iterator starts exhausted.
 *
 * @param it     Iterator to initialize
 * @param plan   Query plan (must remain valid; owned by caller)
 * @param alloc  Allocator for heap data
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_kmerge_iter_init(tl_kmerge_iter_t* it,
                                 tl_plan_t* plan,
                                 tl_alloc_ctx_t* alloc);

/**
 * Destroy K-way merge iterator.
 *
 * Frees heap data but does NOT destroy the plan.
 * Safe to call on zero-initialized or partially initialized iterator.
 */
void tl_kmerge_iter_destroy(tl_kmerge_iter_t* it);

/*===========================================================================
 * Iteration
 *===========================================================================*/

/**
 * Get next record from merged stream.
 *
 * Returns records in non-decreasing timestamp order.
 * Duplicates (same timestamp from different sources) are preserved.
 *
 * @param it   Iterator
 * @param out  Output record
 * @return TL_OK if record available, TL_EOF if exhausted
 */
tl_status_t tl_kmerge_iter_next(tl_kmerge_iter_t* it, tl_record_t* out);

/**
 * Seek all sources to first record with ts >= target.
 *
 * Used for skip-ahead optimization when filtering tombstones.
 * After seek, the iterator is repositioned so that the next call to
 * tl_kmerge_iter_next() returns the first record with ts >= target.
 *
 * Semantics:
 * - Forward-only: if target <= current position, this is a no-op
 * - After seek, the heap is rebuilt with new positions from all sources
 * - If all sources are exhausted after seek, iterator becomes done
 *
 * @param it     Iterator
 * @param target Target timestamp to seek to
 */
void tl_kmerge_iter_seek(tl_kmerge_iter_t* it, tl_ts_t target);

/*===========================================================================
 * State Queries
 *===========================================================================*/

/**
 * Check if iterator is exhausted.
 */
TL_INLINE bool tl_kmerge_iter_done(const tl_kmerge_iter_t* it) {
    TL_ASSERT(it != NULL);
    return it->done;
}

/**
 * Peek at minimum timestamp without advancing.
 *
 * Useful for skip-ahead optimization.
 *
 * @param it  Iterator
 * @return Pointer to minimum timestamp, or NULL if exhausted
 */
TL_INLINE const tl_ts_t* tl_kmerge_iter_peek_ts(const tl_kmerge_iter_t* it) {
    TL_ASSERT(it != NULL);
    if (it->done) return NULL;
    const tl_heap_entry_t* entry = tl_heap_peek(&it->heap);
    return entry != NULL ? &entry->ts : NULL;
}

#endif /* TL_KMERGE_ITER_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_merge_iter.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_pagespan_iter.h
/*   FROM: query/
/*
/******************************************************************************/
#ifndef TL_PAGESPAN_ITER_H
#define TL_PAGESPAN_ITER_H

/**
 * @file tl_pagespan_iter.h
 * @brief Core PageSpan Enumeration API (Zero-Copy without Binding Duplication)
 *
 * This API provides a stable interface for enumerating contiguous page spans
 * within a timelog's segments. It moves span enumeration logic from bindings
 * into core, eliminating algorithm duplication and layout coupling.
 *
 * Key contracts:
 * - Spans are contiguous slices of page memory (zero-copy)
 * - Each span view owns a reference to the owner; caller must decref
 * - Views remain valid after iterator close (each holds its own owner ref)
 * - Empty ranges (t1 >= t2) return TL_OK; first next() returns TL_EOF
 *   (owner/hooks are still created and released on close)
 *
 * Thread safety:
 * - The owner refcount is NOT atomic (B4 constraint)
 * - All incref/decref operations MUST be serialized by the caller
 * - For CPython bindings, the GIL provides this serialization
 *
 * Reference: docs/timelog_v2_lld_pagespan_core_api_unification.md
 */

#include "timelog/timelog.h"
#include <string.h>  /* For memset in view_release inline */

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * Opaque Types
 *===========================================================================*/

/**
 * Opaque owner that pins the resources backing spans.
 * Reference-counted; when refcnt reaches 0, releases snapshot and calls
 * the optional release hook.
 */
typedef struct tl_pagespan_owner tl_pagespan_owner_t;

/**
 * Opaque iterator over spans for a time range.
 * Holds a reference to its owner (released on close).
 */
typedef struct tl_pagespan_iter tl_pagespan_iter_t;

/*===========================================================================
 * Span View
 *
 * Returned by iter_next for each contiguous page slice in the query range.
 * The view's owner is an owned reference - caller MUST decref when done.
 *
 * Invariants:
 * - len is always > 0 for returned views
 * - ts and h point to contiguous arrays of len elements
 * - first_ts == ts[0], last_ts == ts[len-1]
 * - View remains valid as long as owner is alive (refcnt > 0)
 *===========================================================================*/

typedef struct tl_pagespan_view {
    tl_pagespan_owner_t* owner;     /**< Owned ref (caller must decref) */
    const tl_ts_t*       ts;        /**< Pointer to page ts array (read-only) */
    const tl_handle_t*   h;         /**< Pointer to page handle array (read-only) */
    uint32_t             len;       /**< Row count (always > 0) */
    tl_ts_t              first_ts;  /**< == ts[0] */
    tl_ts_t              last_ts;   /**< == ts[len-1] */
} tl_pagespan_view_t;

/*===========================================================================
 * Release Hooks (Binding Integration)
 *
 * Bindings need to drop pins and run deferred DECREF logic when the last
 * span is released. Core does not know about Python, so an optional release
 * hook is provided.
 *
 * Destruction order (CRITICAL):
 * 1. Copy out hooks from owner struct
 * 2. Release snapshot/segment refs (no binding code runs)
 * 3. Free owner struct BEFORE calling hook
 * 4. Invoke on_release(user) if non-NULL
 *
 * Rationale: The hook may Py_DECREF the timelog, which owns the allocator.
 * Freeing owner after the hook could use a freed allocator (UAF).
 *
 * Constraints:
 * - Hook must NOT assume owner struct exists (it has been freed)
 * - Hook must NOT call back into pagespan API (re-entrancy forbidden)
 * - For CPython, hook must run with GIL held
 *===========================================================================*/

typedef void (*tl_pagespan_owner_release_fn)(void* user);

typedef struct tl_pagespan_owner_hooks {
    void*                         user;       /**< Opaque user context */
    tl_pagespan_owner_release_fn  on_release; /**< Optional release callback */
} tl_pagespan_owner_hooks_t;

/*===========================================================================
 * Flags
 *
 * B4 Constraints:
 * - TL_PAGESPAN_SEGMENTS_ONLY is required (return TL_EINVAL if not set)
 * - TL_PAGESPAN_VISIBLE_ONLY is reserved (return TL_EINVAL if set)
 * - flags == 0 is treated as TL_PAGESPAN_DEFAULT
 *===========================================================================*/

enum {
    TL_PAGESPAN_SEGMENTS_ONLY    = 1u << 0,  /**< Ignore memview/memtable */
    TL_PAGESPAN_INCLUDE_L0       = 1u << 1,  /**< Include L0 segments */
    TL_PAGESPAN_INCLUDE_L1       = 1u << 2,  /**< Include L1 segments */
    TL_PAGESPAN_VISIBLE_ONLY     = 1u << 3,  /**< Reserved (EINVAL in B4) */
    TL_PAGESPAN_REQUIRE_ZEROCOPY = 1u << 4   /**< Must not allocate staging */
};

/**
 * Default flags for B4: segments only, both L0/L1, zero-copy required.
 */
#define TL_PAGESPAN_DEFAULT \
    (TL_PAGESPAN_SEGMENTS_ONLY | TL_PAGESPAN_INCLUDE_L0 | \
     TL_PAGESPAN_INCLUDE_L1 | TL_PAGESPAN_REQUIRE_ZEROCOPY)

/*===========================================================================
 * Iterator API
 *===========================================================================*/

/**
 * Open a pagespan iterator for the half-open range [t1, t2).
 *
 * Acquires a snapshot internally; resources are pinned until all returned
 * views are released.
 *
 * Empty range behavior (t1 >= t2):
 * - Returns TL_OK and creates a valid iterator
 * - First call to iter_next() returns TL_EOF
 * - Owner/hooks are still created and released on close
 * - This follows standard iterator semantics
 *
 * @param tl     Open timelog instance (must not be NULL)
 * @param t1     Range start (inclusive)
 * @param t2     Range end (exclusive)
 * @param flags  Combination of TL_PAGESPAN_* flags (0 = DEFAULT)
 * @param hooks  Optional release hooks (may be NULL)
 * @param out    Output iterator pointer (must not be NULL)
 *
 * @return TL_OK      - Iterator created successfully
 * @return TL_EINVAL  - NULL tl/out, unsupported flags, or flag violation
 * @return TL_ESTATE  - Timelog not open
 * @return TL_ENOMEM  - Allocation failure
 */
TL_API tl_status_t tl_pagespan_iter_open(
    tl_timelog_t* tl,
    tl_ts_t t1,
    tl_ts_t t2,
    uint32_t flags,
    const tl_pagespan_owner_hooks_t* hooks,
    tl_pagespan_iter_t** out);

/**
 * Get the next span from the iterator.
 *
 * On success (TL_OK), out_view is filled with a span descriptor.
 * The view's owner reference is already incremented; caller must
 * release it via tl_pagespan_owner_decref() or tl_pagespan_view_release().
 *
 * Span ordering: L1 segments first (sorted by window), then L0 segments.
 * Within each segment, pages are enumerated in timestamp order.
 *
 * @param it        Iterator (must not be NULL, must not be closed)
 * @param out_view  Output span view (must not be NULL)
 *
 * @return TL_OK   - Span returned in out_view
 * @return TL_EOF  - No more spans (iterator exhausted)
 */
TL_API tl_status_t tl_pagespan_iter_next(
    tl_pagespan_iter_t* it,
    tl_pagespan_view_t* out_view);

/**
 * Close the iterator and release its owner reference.
 *
 * Safe to call on NULL. The iterator is freed and the pointer is invalidated;
 * callers must not use the pointer after this call (set to NULL after calling).
 * Previously returned views remain valid until their owner refs are released.
 *
 * @param it  Iterator to close (may be NULL, invalidated after call)
 */
TL_API void tl_pagespan_iter_close(tl_pagespan_iter_t* it);

/*===========================================================================
 * Owner Reference Counting
 *
 * CONCURRENCY CONSTRAINT (B4):
 * The refcount is plain uint32_t, NOT atomic. All incref/decref operations
 * MUST be serialized by the caller. For CPython bindings, the GIL provides
 * this serialization.
 *
 * Future enhancement: If multi-threaded bindings are needed, change to
 * _Atomic uint32_t with fetch_add/fetch_sub (acq_rel ordering).
 *===========================================================================*/

/**
 * Increment owner reference count.
 * Thread safety: Caller must ensure serialization.
 *
 * @param owner  Owner to incref (must not be NULL)
 */
TL_API void tl_pagespan_owner_incref(tl_pagespan_owner_t* owner);

/**
 * Decrement owner reference count.
 * When refcnt reaches 0, destroys owner and calls release hook if provided.
 * Thread safety: Caller must ensure serialization.
 *
 * @param owner  Owner to decref (must not be NULL)
 */
TL_API void tl_pagespan_owner_decref(tl_pagespan_owner_t* owner);

/*===========================================================================
 * View Helper
 *===========================================================================*/

/**
 * Release a span view's owner reference and zero the view struct.
 * Convenience wrapper around tl_pagespan_owner_decref().
 *
 * @param v  View to release (may be NULL or have NULL owner)
 */
static inline void tl_pagespan_view_release(tl_pagespan_view_t* v) {
    if (v != NULL && v->owner != NULL) {
        tl_pagespan_owner_decref(v->owner);
    }
    if (v != NULL) {
        memset(v, 0, sizeof(*v));
    }
}

#ifdef __cplusplus
}
#endif

#endif /* TL_PAGESPAN_ITER_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_pagespan_iter.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_plan.h
/*   FROM: query/
/*
/******************************************************************************/
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
 *
 * Reference: Read Path LLD Section 4
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
 * @param plan  Plan to destroy
 */
void tl_plan_destroy(tl_plan_t* plan);

/*===========================================================================
 * Accessors
 *===========================================================================*/

/**
 * Get the number of sources in the plan.
 */
TL_INLINE size_t tl_plan_source_count(const tl_plan_t* plan) {
    TL_ASSERT(plan != NULL);
    return plan->source_count;
}

/**
 * Get a source by index.
 */
TL_INLINE tl_iter_source_t* tl_plan_source(tl_plan_t* plan, size_t idx) {
    TL_ASSERT(plan != NULL);
    TL_ASSERT(idx < plan->source_count);
    return &plan->sources[idx];
}

/**
 * Get tombstone intervals.
 */
TL_INLINE const tl_interval_t* tl_plan_tombstones(const tl_plan_t* plan) {
    TL_ASSERT(plan != NULL);
    return plan->tombstones;
}

/**
 * Get tombstone count.
 */
TL_INLINE size_t tl_plan_tomb_count(const tl_plan_t* plan) {
    TL_ASSERT(plan != NULL);
    return plan->tomb_count;
}

/**
 * Check if plan is empty (no data sources).
 */
TL_INLINE bool tl_plan_is_empty(const tl_plan_t* plan) {
    TL_ASSERT(plan != NULL);
    return plan->source_count == 0;
}

#endif /* TL_PLAN_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_plan.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_point.h
/*   FROM: query/
/*
/******************************************************************************/
#ifndef TL_POINT_H
#define TL_POINT_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "tl_snapshot.h"

/*===========================================================================
 * Point Lookup Fast Path
 *
 * Dedicated single-timestamp lookup that bypasses the full K-way merge.
 * Uses direct binary search on each component to find all records with
 * the exact timestamp.
 *
 * Algorithm (Read Path LLD Section 8):
 * 1. Tombstone check: if any tombstone covers ts, return empty immediately
 * 2. L1 lookup: binary search window, catalog, page for ts
 * 3. L0 lookup: scan overlapping segments with binary search
 * 4. Memview lookup: binary search active_run, active_ooo, sealed memruns
 * 5. Concatenate results (duplicates preserved, order unspecified)
 *
 * Complexity:
 * - O(log S1) to find L1 window
 * - O(log P) per segment page catalog
 * - O(log rows) per page binary search
 * - Much cheaper than full K-way merge for single-timestamp queries
 *
 * Thread Safety:
 * - Snapshot must remain valid for the lifetime of the result
 * - Result array is owned by caller
 *
 * Reference: Read Path LLD Section 8, timelog_v1_c_software_design_spec.md
 *===========================================================================*/

/**
 * Result of point lookup.
 * Contains array of matching records (caller must free).
 */
typedef struct tl_point_result {
    tl_record_t*    records;    /* Array of matching records (owned) */
    size_t          count;      /* Number of records */
    size_t          capacity;   /* Allocated capacity */
    tl_alloc_ctx_t* alloc;      /* Allocator for cleanup */
} tl_point_result_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Perform point lookup for exact timestamp.
 *
 * Finds all visible records with record.ts == ts in the snapshot.
 * Uses direct binary search on each component (no K-way merge).
 *
 * If any tombstone covers ts, returns empty result (not an error).
 * This is correct: the timestamp is deleted.
 *
 * @param result  Output result (caller-allocated, zero-initialized)
 * @param snap    Snapshot to search
 * @param ts      Timestamp to find
 * @param alloc   Allocator for result records
 * @return TL_OK on success (even if no records found),
 *         TL_ENOMEM on allocation failure
 */
tl_status_t tl_point_lookup(tl_point_result_t* result,
                             const tl_snapshot_t* snap,
                             tl_ts_t ts,
                             tl_alloc_ctx_t* alloc);

/**
 * Destroy point result and free records array.
 * Safe to call on zero-initialized or empty result.
 * After this call, result is in a zero-initialized state.
 */
void tl_point_result_destroy(tl_point_result_t* result);

/*===========================================================================
 * Accessors
 *===========================================================================*/

/**
 * Check if result is empty.
 */
TL_INLINE bool tl_point_result_empty(const tl_point_result_t* result) {
    return result->count == 0;
}

/**
 * Get record by index.
 */
TL_INLINE const tl_record_t* tl_point_result_get(const tl_point_result_t* result,
                                                  size_t idx) {
    TL_ASSERT(idx < result->count);
    return &result->records[idx];
}

#endif /* TL_POINT_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_point.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_segment_iter.h
/*   FROM: query/
/*
/******************************************************************************/
#ifndef TL_SEGMENT_ITER_H
#define TL_SEGMENT_ITER_H

#include "../internal/tl_defs.h"
#include "../storage/tl_segment.h"

/*===========================================================================
 * Segment Iterator
 *
 * Iterates over records within a segment for a given range [t1, t2) or
 * [t1, +inf). Uses page catalog for pruning and within-page binary search
 * for efficient navigation.
 *
 * Algorithm:
 * 1. Initialize: find first and last pages that might overlap the range
 * 2. For each page: use binary search to find row boundaries
 * 3. Iterate through rows, checking range bounds
 *
 * UNBOUNDED QUERY DESIGN:
 * - If t2_unbounded == true, the query is [t1, +inf)
 * - When t2_unbounded is true, the 't2' field is ignored (pass 0 for clarity)
 * - All comparisons must check t2_unbounded FIRST before using t2
 *
 * Thread Safety:
 * - Not thread-safe (each thread needs its own iterator)
 * - Segment must remain valid for the lifetime of the iterator
 *
 * Reference: Read Path LLD Section 5.1
 *===========================================================================*/

typedef struct tl_segment_iter {
    const tl_segment_t* seg;

    /* Range bounds */
    tl_ts_t         t1;
    tl_ts_t         t2;              /* ONLY valid if !t2_unbounded */
    bool            t2_unbounded;

    /* Current page */
    size_t          page_idx;        /* Current page index */
    size_t          page_end;        /* Last page index (exclusive) */

    /* Current position within page */
    size_t          row_idx;         /* Current row within page */
    size_t          row_end;         /* End row within page (exclusive) */

    /* State */
    bool            done;
    bool            has_current;
    tl_record_t     current;
} tl_segment_iter_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Initialize segment iterator for range [t1, t2) or [t1, +inf).
 *
 * UNBOUNDED QUERIES:
 * - If t2_unbounded == true, the query is [t1, +inf)
 * - When t2_unbounded is true, t2 is IGNORED (pass 0 or any value)
 *
 * After init, call tl_segment_iter_next() to get the first record.
 * If the segment doesn't overlap the range, the iterator starts exhausted.
 *
 * @param it           Iterator to initialize
 * @param seg          Segment to iterate (must remain valid)
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY used if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 */
void tl_segment_iter_init(tl_segment_iter_t* it,
                           const tl_segment_t* seg,
                           tl_ts_t t1, tl_ts_t t2,
                           bool t2_unbounded);

/*===========================================================================
 * Iteration
 *===========================================================================*/

/**
 * Advance to next record.
 *
 * @param it   Iterator
 * @param out  Output record (may be NULL if only checking for existence)
 * @return TL_OK if record available, TL_EOF if exhausted
 */
tl_status_t tl_segment_iter_next(tl_segment_iter_t* it, tl_record_t* out);

/**
 * Seek to first record with ts >= target.
 *
 * Used for skip-ahead optimization in merge iteration.
 * If target is before current position, does nothing (no backwards seek).
 * If target is past the range end, iterator becomes exhausted.
 *
 * After seek, call tl_segment_iter_next() to get the record at the new position.
 *
 * @param it     Iterator
 * @param target Target timestamp to seek to
 */
void tl_segment_iter_seek(tl_segment_iter_t* it, tl_ts_t target);

/*===========================================================================
 * State Queries
 *===========================================================================*/

/**
 * Check if iterator is exhausted.
 */
TL_INLINE bool tl_segment_iter_done(const tl_segment_iter_t* it) {
    TL_ASSERT(it != NULL);
    return it->done;
}

/**
 * Peek at current record without advancing.
 *
 * Precondition: !done && has_current
 * The current record is set after a successful tl_segment_iter_next().
 */
TL_INLINE const tl_record_t* tl_segment_iter_peek(const tl_segment_iter_t* it) {
    TL_ASSERT(it != NULL);
    TL_ASSERT(!it->done && it->has_current);
    return &it->current;
}

/**
 * Check if iterator has a current record ready for peek.
 */
TL_INLINE bool tl_segment_iter_has_current(const tl_segment_iter_t* it) {
    TL_ASSERT(it != NULL);
    return !it->done && it->has_current;
}

#endif /* TL_SEGMENT_ITER_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_segment_iter.h
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_snapshot.h
/*   FROM: query/
/*
/******************************************************************************/
#ifndef TL_SNAPSHOT_H
#define TL_SNAPSHOT_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../storage/tl_manifest.h"
#include "../delta/tl_memview.h"

/*===========================================================================
 * Snapshot: Complete Point-in-Time View
 *
 * A snapshot captures a consistent view of the timelog at a point in time.
 * It contains:
 * - Manifest (pinned via acquire, released on destroy)
 * - Memview (owned, captured at acquisition time)
 *
 * The snapshot is completely immutable after acquisition and can be used
 * for queries without holding any locks.
 *
 * Acquisition Protocol (from Software Design Spec Section 4.2):
 * 1. Lock writer_mu
 * 2. Read seqlock (must be even)
 * 3. Acquire manifest reference
 * 4. Capture memview (locks memtable_mu internally)
 * 5. Read seqlock again
 * 6. Unlock writer_mu
 * 7. If seq1 != seq2 OR seq1 is odd: retry
 *
 * Thread Safety:
 * - Acquisition requires internal locking (handled automatically)
 * - After acquisition, fully immutable - no synchronization needed
 * - Release is thread-safe (reference counting)
 *
 * Reference: Read Path LLD Section 1, Software Design Spec Section 4.2
 *===========================================================================*/

/*
 * Forward declaration of tl_timelog_t.
 * We cannot include tl_timelog.c's struct definition, so we use opaque pointer.
 */
struct tl_timelog;

struct tl_snapshot {
    /*-----------------------------------------------------------------------
     * Manifest (pinned via acquire, released on destroy)
     *-----------------------------------------------------------------------*/
    tl_manifest_t*  manifest;

    /*-----------------------------------------------------------------------
     * Memview (shared, captured at acquisition time)
     *-----------------------------------------------------------------------*/
    tl_memview_shared_t* memview;

    /*-----------------------------------------------------------------------
     * Cached Bounds (computed at acquisition time)
     *-----------------------------------------------------------------------*/
    tl_ts_t         min_ts;          /* Global min across manifest + memview */
    tl_ts_t         max_ts;          /* Global max across manifest + memview */
    bool            has_data;        /* True if any visible data exists */

    /*-----------------------------------------------------------------------
     * Parent Reference (for debug state checks)
     *-----------------------------------------------------------------------*/
    const struct tl_timelog* parent;

    /*-----------------------------------------------------------------------
     * Lifecycle
     *-----------------------------------------------------------------------*/
    tl_alloc_ctx_t* alloc;           /* Allocator (borrowed) */

#ifdef TL_DEBUG
    uint32_t        iter_count;      /* Outstanding iterator count (debug) */
#endif
};

/*===========================================================================
 * Internal API (for query components)
 *===========================================================================*/

/**
 * Get manifest from snapshot.
 */
TL_INLINE const tl_manifest_t* tl_snapshot_manifest(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return snap->manifest;
}

/**
 * Get memview from snapshot.
 */
TL_INLINE const tl_memview_t* tl_snapshot_memview(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(snap->memview != NULL);
    return tl_memview_shared_view(snap->memview);
}

/**
 * Get allocator from snapshot.
 */
TL_INLINE tl_alloc_ctx_t* tl_snapshot_alloc(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return snap->alloc;
}

/**
 * Check if snapshot has any data.
 */
TL_INLINE bool tl_snapshot_has_data(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    return snap->has_data;
}

/**
 * Get minimum timestamp in snapshot.
 * Only valid if has_data is true.
 */
TL_INLINE tl_ts_t tl_snapshot_min_ts(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(snap->has_data);
    return snap->min_ts;
}

/**
 * Get maximum timestamp in snapshot.
 * Only valid if has_data is true.
 */
TL_INLINE tl_ts_t tl_snapshot_max_ts(const tl_snapshot_t* snap) {
    TL_ASSERT(snap != NULL);
    TL_ASSERT(snap->has_data);
    return snap->max_ts;
}

#ifdef TL_DEBUG
/**
 * Track iterator creation (debug only).
 * Must be called when creating an iterator from this snapshot.
 */
void tl_snapshot_iter_created(tl_snapshot_t* snap);

/**
 * Track iterator destruction (debug only).
 * Must be called when destroying an iterator from this snapshot.
 */
void tl_snapshot_iter_destroyed(tl_snapshot_t* snap);
#endif

/*===========================================================================
 * Internal Acquisition (called from tl_timelog.c)
 *
 * The public API (tl_snapshot_acquire, tl_snapshot_release) is declared in
 * timelog.h. The implementation is in tl_snapshot.c but is called from
 * tl_timelog.c wrapper functions.
 *===========================================================================*/

/**
 * Internal snapshot acquisition.
 * Called from tl_snapshot_acquire in tl_timelog.c.
 *
 * This function implements the seqlock protocol for snapshot consistency.
 * The caller (tl_snapshot_acquire in timelog.h) validates tl != NULL and
 * tl->is_open.
 *
 * @param tl    Timelog instance (cast to non-const internally for locking)
 * @param alloc Allocator context
 * @param out   Output snapshot pointer
 * @return TL_OK on success, TL_ENOMEM on allocation failure
 */
tl_status_t tl_snapshot_acquire_internal(struct tl_timelog* tl,
                                          tl_alloc_ctx_t* alloc,
                                          tl_snapshot_t** out);

/**
 * Internal snapshot release.
 * Called from tl_snapshot_release in tl_timelog.c.
 *
 * @param snap  Snapshot to release (may be NULL)
 */
void tl_snapshot_release_internal(tl_snapshot_t* snap);

#endif /* TL_SNAPSHOT_H */

/------------------------------------------------------------------------------/
/*   END OF: tl_snapshot.h
/------------------------------------------------------------------------------/
