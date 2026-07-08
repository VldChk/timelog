#ifndef TL_DELTA_ITER_H
#define TL_DELTA_ITER_H

#include "../internal/tl_defs.h"
#include "../delta/tl_memrun.h"
#include "../delta/tl_memview.h"
#include "tl_submerge.h"

/*===========================================================================
 * Delta Iterator
 *
 * One internal K-way merge iterator over the delta components of either
 * a sealed memrun (sorted run + OOO runs) or the active memview
 * (active_run + OOO runs + OOO head). The two sources differ only in
 * initialization; next/seek/destroy/done are shared (C1).
 *
 * Range semantics:
 * - When t2_unbounded == true the query is [t1, +inf) and the t2 field
 *   is ignored (pass 0 for clarity).
 * - Otherwise the query is the half-open interval [t1, t2).
 *
 * Thread Safety:
 * - Not thread-safe (each thread needs its own iterator).
 * - The memrun/memview must remain valid for the iterator's lifetime.
 *===========================================================================*/

typedef struct tl_delta_iter {
    /* Range bounds */
    tl_ts_t         t1;
    tl_ts_t         t2;              /* ONLY valid if !t2_unbounded */
    bool            t2_unbounded;

    /* Internal merge state */
    tl_submerge_t   merge;

    /* Output state */
    bool            done;
} tl_delta_iter_t;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

/**
 * Initialize delta iterator over a sealed memrun for [t1, t2) or [t1, +inf).
 *
 * Delta components: sorted run + OOO runs, all filtered against the
 * memrun's applied_seq watermark (memruns have no per-record seqs).
 * Starts exhausted (done) when the memrun has no records or does not
 * overlap the range.
 *
 * Lifecycle contract:
 * - This API may allocate internal merge state.
 * - After each init attempt (success or failure), calling
 *   tl_delta_iter_destroy() is always safe.
 * - Re-initializing the same iterator without destroy is invalid.
 *
 * After init, call tl_delta_iter_next() to get the first record.
 *
 * @param it           Iterator to initialize
 * @param mr           Memrun to iterate (must remain valid)
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY used if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @param alloc        Allocator for internal merge state
 * @return TL_OK on success, TL_ENOMEM/TL_EOVERFLOW on allocation failure
 */
tl_status_t tl_delta_iter_init_memrun(tl_delta_iter_t* it,
                                      const tl_memrun_t* mr,
                                      tl_ts_t t1, tl_ts_t t2,
                                      bool t2_unbounded,
                                      tl_alloc_ctx_t* alloc);

/**
 * Initialize delta iterator over the active memview for [t1, t2) or
 * [t1, +inf).
 *
 * Delta components: active_run + OOO runs + OOO head, using per-record
 * seq arrays where available. The OOO head must be sorted before
 * iteration (asserted).
 *
 * Same lifecycle contract as tl_delta_iter_init_memrun().
 *
 * @param it           Iterator to initialize
 * @param mv           Memview to iterate (must remain valid)
 * @param t1           Range start (inclusive)
 * @param t2           Range end (exclusive) - ONLY used if !t2_unbounded
 * @param t2_unbounded True => [t1, +inf), t2 is ignored
 * @param alloc        Allocator for internal merge state
 * @return TL_OK on success, TL_ENOMEM/TL_EOVERFLOW on allocation failure
 */
tl_status_t tl_delta_iter_init_memview(tl_delta_iter_t* it,
                                       const tl_memview_t* mv,
                                       tl_ts_t t1, tl_ts_t t2,
                                       bool t2_unbounded,
                                       tl_alloc_ctx_t* alloc);

/**
 * Destroy delta iterator and free internal resources.
 *
 * Safe to call on a zeroed or partially initialized iterator.
 */
void tl_delta_iter_destroy(tl_delta_iter_t* it);

/*===========================================================================
 * Iteration
 *===========================================================================*/

/**
 * Advance to next record.
 *
 * @param it   Iterator
 * @param out  Output record (may be NULL)
 * @param out_watermark Source watermark for the emitted record (optional)
 * @return TL_OK if record available, TL_EOF if exhausted, or error status
 */
tl_status_t tl_delta_iter_next(tl_delta_iter_t* it,
                               tl_record_t* out,
                               tl_seq_t* out_watermark);

/**
 * Seek to first record with ts >= target.
 *
 * If target is before current position, does nothing.
 * If target is past range end, iterator becomes exhausted.
 *
 * @param it     Iterator
 * @param target Target timestamp
 * @return TL_OK on success, TL_ENOMEM/TL_EOVERFLOW on internal growth failure
 *
 * On error, iterator transitions to done=true.
 */
tl_status_t tl_delta_iter_seek(tl_delta_iter_t* it, tl_ts_t target);

/*===========================================================================
 * State Queries
 *===========================================================================*/

/** Check if iterator is exhausted. */
TL_INLINE bool tl_delta_iter_done(const tl_delta_iter_t* it) {
    TL_ASSERT(it != NULL);
    return it->done;
}

#endif /* TL_DELTA_ITER_H */
