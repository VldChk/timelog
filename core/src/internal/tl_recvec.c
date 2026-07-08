#include "tl_recvec.h"
#include <stdlib.h>  /* qsort */
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/* Initial capacity sized for typical batch inserts; large enough that the
 * first push avoids an immediate reallocation for batch ingestion paths. */
static const size_t RECVEC_MIN_CAPACITY = 16;

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

void tl_recvec_init(tl_recvec_t* rv, tl_alloc_ctx_t* alloc) {
    TL_ASSERT(rv != NULL);
    TL_ASSERT(alloc != NULL);

    rv->data = NULL;
    rv->len = 0;
    rv->cap = 0;
    rv->alloc = alloc;
}

void tl_recvec_destroy(tl_recvec_t* rv) {
    if (rv == NULL) {
        return;
    }

    if (rv->data != NULL) {
        tl__free(rv->alloc, rv->data);
    }

    /* Reset to the canonical empty state so destroy is idempotent. The
     * allocator pointer is borrowed and intentionally retained. */
    rv->data = NULL;
    rv->len = 0;
    rv->cap = 0;
}

void tl_recvec_clear(tl_recvec_t* rv) {
    TL_ASSERT(rv != NULL);
    rv->len = 0;
}

/*===========================================================================
 * Capacity Management
 *===========================================================================*/

tl_status_t tl_recvec_reserve(tl_recvec_t* rv, size_t min_cap) {
    TL_ASSERT(rv != NULL);

    if (min_cap <= rv->cap) {
        return TL_OK;
    }

    size_t new_cap = tl__grow_capacity(rv->cap, min_cap, RECVEC_MIN_CAPACITY);
    if (new_cap == 0 || tl__alloc_would_overflow(new_cap, sizeof(tl_record_t))) {
        return TL_ENOMEM;
    }

    tl_record_t* new_data = tl__realloc(rv->alloc, rv->data,
                                         new_cap * sizeof(tl_record_t));
    if (new_data == NULL) {
        return TL_ENOMEM;
    }

    rv->data = new_data;
    rv->cap = new_cap;
    return TL_OK;
}

/*===========================================================================
 * Insertion
 *===========================================================================*/

tl_status_t tl_recvec_push(tl_recvec_t* rv, tl_ts_t ts, tl_handle_t handle) {
    TL_ASSERT(rv != NULL);

    if (rv->len == SIZE_MAX) {
        return TL_ENOMEM;
    }

    tl_status_t s = tl_recvec_reserve(rv, rv->len + 1);
    if (s != TL_OK) {
        return s;
    }

    rv->data[rv->len].ts = ts;
    rv->data[rv->len].handle = handle;
    rv->len++;
    return TL_OK;
}

tl_status_t tl_recvec_push_n(tl_recvec_t* rv, const tl_record_t* records, size_t n) {
    TL_ASSERT(rv != NULL);

    if (n == 0) {
        return TL_OK;
    }

    TL_ASSERT(records != NULL);

    /* Overflow guard for the eventual rv->len + n addition. */
    if (n > SIZE_MAX - rv->len) {
        return TL_ENOMEM;
    }

    tl_status_t s = tl_recvec_reserve(rv, rv->len + n);
    if (s != TL_OK) {
        return s;
    }

    memcpy(&rv->data[rv->len], records, n * sizeof(tl_record_t));
    rv->len += n;
    return TL_OK;
}

/*===========================================================================*/
/* Sorting With Seq */
/*===========================================================================*/

typedef struct tl_recseq_pair {
    tl_record_t rec;
    tl_seq_t    seq;
} tl_recseq_pair_t;

static int cmp_recseq_pair(const void* a, const void* b) {
    const tl_recseq_pair_t* ra = (const tl_recseq_pair_t*)a;
    const tl_recseq_pair_t* rb = (const tl_recseq_pair_t*)b;

    if (ra->rec.ts < rb->rec.ts) return -1;
    if (ra->rec.ts > rb->rec.ts) return 1;
    if (ra->rec.handle < rb->rec.handle) return -1;
    if (ra->rec.handle > rb->rec.handle) return 1;
    if (ra->seq < rb->seq) return -1;
    if (ra->seq > rb->seq) return 1;
    return 0;
}

tl_status_t tl_recvec_sort_with_seqs(tl_recvec_t* rv, tl_seq_t* seqs) {
    TL_ASSERT(rv != NULL);
    TL_ASSERT(seqs != NULL);

    if (rv->len <= 1) {
        return TL_OK;
    }

    if (tl__alloc_would_overflow(rv->len, sizeof(tl_recseq_pair_t))) {
        return TL_ENOMEM;
    }

    tl_recseq_pair_t* tmp = tl__malloc(rv->alloc, rv->len * sizeof(tl_recseq_pair_t));
    if (tmp == NULL) {
        return TL_ENOMEM;
    }

    for (size_t i = 0; i < rv->len; i++) {
        tmp[i].rec = rv->data[i];
        tmp[i].seq = seqs[i];
    }

    qsort(tmp, rv->len, sizeof(tl_recseq_pair_t), cmp_recseq_pair);

    for (size_t i = 0; i < rv->len; i++) {
        rv->data[i] = tmp[i].rec;
        seqs[i] = tmp[i].seq;
    }

    tl__free(rv->alloc, tmp);
    return TL_OK;
}

/*===========================================================================
 * Ownership Transfer
 *===========================================================================*/

tl_record_t* tl_recvec_take(tl_recvec_t* rv, size_t* out_len) {
    TL_ASSERT(rv != NULL);
    TL_ASSERT(out_len != NULL);

    tl_record_t* data = rv->data;
    *out_len = rv->len;

    rv->data = NULL;
    rv->len = 0;
    rv->cap = 0;

    return data;
}
