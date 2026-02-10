#include "tl_seqvec.h"
#include <string.h>

/*===========================================================================*/
/* Internal Helpers */
/*===========================================================================*/

static const size_t SEQVEC_MIN_CAPACITY = 16;

/*===========================================================================*/
/* Lifecycle */
/*===========================================================================*/

void tl_seqvec_init(tl_seqvec_t* sv, tl_alloc_ctx_t* alloc) {
    TL_ASSERT(sv != NULL);
    TL_ASSERT(alloc != NULL);

    sv->data = NULL;
    sv->len = 0;
    sv->cap = 0;
    sv->alloc = alloc;
}

void tl_seqvec_destroy(tl_seqvec_t* sv) {
    if (sv == NULL) {
        return;
    }

    if (sv->data != NULL) {
        tl__free(sv->alloc, sv->data);
    }

    sv->data = NULL;
    sv->len = 0;
    sv->cap = 0;
}

void tl_seqvec_clear(tl_seqvec_t* sv) {
    TL_ASSERT(sv != NULL);
    sv->len = 0;
}

/*===========================================================================*/
/* Capacity */
/*===========================================================================*/

tl_status_t tl_seqvec_reserve(tl_seqvec_t* sv, size_t min_cap) {
    TL_ASSERT(sv != NULL);

    if (min_cap <= sv->cap) {
        return TL_OK;
    }

    size_t new_cap = tl__grow_capacity(sv->cap, min_cap, SEQVEC_MIN_CAPACITY);
    if (new_cap == 0 || tl__alloc_would_overflow(new_cap, sizeof(tl_seq_t))) {
        return TL_ENOMEM;
    }

    tl_seq_t* new_data = tl__realloc(sv->alloc, sv->data,
                                     new_cap * sizeof(tl_seq_t));
    if (new_data == NULL) {
        return TL_ENOMEM;
    }

    sv->data = new_data;
    sv->cap = new_cap;
    return TL_OK;
}

/*===========================================================================*/
/* Insertion */
/*===========================================================================*/

tl_status_t tl_seqvec_push(tl_seqvec_t* sv, tl_seq_t seq) {
    TL_ASSERT(sv != NULL);

    if (sv->len == SIZE_MAX) {
        return TL_ENOMEM;
    }

    tl_status_t st = tl_seqvec_reserve(sv, sv->len + 1);
    if (st != TL_OK) {
        return st;
    }

    sv->data[sv->len] = seq;
    sv->len++;
    return TL_OK;
}

tl_status_t tl_seqvec_push_n_const(tl_seqvec_t* sv, tl_seq_t seq, size_t n) {
    TL_ASSERT(sv != NULL);

    if (n == 0) {
        return TL_OK;
    }

    if (n > SIZE_MAX - sv->len) {
        return TL_ENOMEM;
    }

    tl_status_t st = tl_seqvec_reserve(sv, sv->len + n);
    if (st != TL_OK) {
        return st;
    }

    for (size_t i = 0; i < n; i++) {
        sv->data[sv->len + i] = seq;
    }
    sv->len += n;
    return TL_OK;
}

/*===========================================================================*/
/* Ownership Transfer */
/*===========================================================================*/

tl_seq_t* tl_seqvec_take(tl_seqvec_t* sv, size_t* out_len) {
    TL_ASSERT(sv != NULL);
    TL_ASSERT(out_len != NULL);

    tl_seq_t* data = sv->data;
    *out_len = sv->len;

    sv->data = NULL;
    sv->len = 0;
    sv->cap = 0;

    return data;
}
