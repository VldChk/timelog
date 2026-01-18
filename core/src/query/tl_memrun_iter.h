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
