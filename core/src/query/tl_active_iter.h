#ifndef TL_ACTIVE_ITER_H
#define TL_ACTIVE_ITER_H

#include "../internal/tl_defs.h"
#include "../delta/tl_memview.h"
#include "tl_submerge.h"

/*===========================================================================
 * Active Memview Iterator
 *
 * Internal K-way merge over active_run, OOO runs, and OOO head
 * from a memview. Uses tl_submerge for shared heap logic.
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

    /* Internal merge state */
    tl_submerge_t   merge;

    /* Output state */
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
 * @param alloc        Allocator for internal merge state
 * @return TL_OK on success, TL_ENOMEM/TL_EOVERFLOW on allocation failure
 */
tl_status_t tl_active_iter_init(tl_active_iter_t* it,
                                 const tl_memview_t* mv,
                                 tl_ts_t t1, tl_ts_t t2,
                                 bool t2_unbounded,
                                 tl_alloc_ctx_t* alloc);

/**
 * Destroy active iterator and free internal resources.
 */
void tl_active_iter_destroy(tl_active_iter_t* it);

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
