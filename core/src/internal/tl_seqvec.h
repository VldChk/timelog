#ifndef TL_SEQVEC_H
#define TL_SEQVEC_H

#include "tl_defs.h"
#include "tl_alloc.h"

/*===========================================================================
 * Sequence Vector
 *
 * A dynamic array of tl_seq_t values. Used to track per-record sequence
 * numbers alongside tl_recvec_t in mutable layers (memtable/memview).
 *
 * Thread Safety:
 * - Not thread-safe. Caller must provide synchronization.
 *===========================================================================*/

typedef struct tl_seqvec {
    tl_seq_t*       data;
    size_t          len;
    size_t          cap;
    tl_alloc_ctx_t* alloc; /* Allocator context (borrowed, not owned) */
} tl_seqvec_t;

/*---------------------------------------------------------------------------*/
/* Lifecycle */
/*---------------------------------------------------------------------------*/

void tl_seqvec_init(tl_seqvec_t* sv, tl_alloc_ctx_t* alloc);
void tl_seqvec_destroy(tl_seqvec_t* sv);
void tl_seqvec_clear(tl_seqvec_t* sv);

/*---------------------------------------------------------------------------*/
/* Capacity */
/*---------------------------------------------------------------------------*/

tl_status_t tl_seqvec_reserve(tl_seqvec_t* sv, size_t min_cap);

/*---------------------------------------------------------------------------*/
/* Insertion */
/*---------------------------------------------------------------------------*/

tl_status_t tl_seqvec_push(tl_seqvec_t* sv, tl_seq_t seq);
tl_status_t tl_seqvec_push_n_const(tl_seqvec_t* sv, tl_seq_t seq, size_t n);

/*---------------------------------------------------------------------------*/
/* Ownership Transfer */
/*---------------------------------------------------------------------------*/

tl_seq_t* tl_seqvec_take(tl_seqvec_t* sv, size_t* out_len);

/*---------------------------------------------------------------------------*/
/* Accessors */
/*---------------------------------------------------------------------------*/

TL_INLINE size_t tl_seqvec_len(const tl_seqvec_t* sv) {
    return sv->len;
}

TL_INLINE const tl_seq_t* tl_seqvec_data(const tl_seqvec_t* sv) {
    return sv->data;
}

#endif /* TL_SEQVEC_H */
