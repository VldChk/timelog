#ifndef TL_RECVEC_H
#define TL_RECVEC_H

#include "tl_defs.h"
#include "tl_status.h"
#include "tl_alloc.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Dynamic vector of tl_record_t.
 *
 * Design choices:
 * - Amortized O(1) append via geometric growth (1.5x)
 * - No shrinking (caller must explicitly compact)
 * - Supports move semantics for ownership transfer
 * - Pin-aware: can track external references to prevent invalidating reallocs
 */
typedef struct tl_recvec {
    tl_record_t*          data;       /* Record array */
    size_t                len;        /* Current count */
    size_t                cap;        /* Allocated capacity */
    const tl_allocator_t* alloc;      /* Allocator (not owned) */
    uint32_t              pin_count;  /* External references (for snapshot safety) */
} tl_recvec_t;

/**
 * Initialize an empty vector.
 *
 * @param vec   Vector to initialize
 * @param alloc Allocator to use (may be NULL for libc)
 */
void tl_recvec_init(tl_recvec_t* vec, const tl_allocator_t* alloc);

/**
 * Initialize with pre-allocated capacity.
 *
 * @param vec      Vector to initialize
 * @param alloc    Allocator to use
 * @param init_cap Initial capacity
 * @return TL_OK or TL_ENOMEM
 */
tl_status_t tl_recvec_init_cap(tl_recvec_t* vec, const tl_allocator_t* alloc,
                                size_t init_cap);

/**
 * Destroy vector and free memory.
 */
void tl_recvec_destroy(tl_recvec_t* vec);

/**
 * Clear vector (set len=0) without freeing memory.
 */
void tl_recvec_clear(tl_recvec_t* vec);

/**
 * Append a single record.
 *
 * @return TL_OK on success, TL_ENOMEM if growth fails
 */
tl_status_t tl_recvec_push(tl_recvec_t* vec, tl_ts_t ts, tl_handle_t handle);

/**
 * Append multiple records.
 *
 * @return TL_OK on success, TL_ENOMEM if growth fails
 */
tl_status_t tl_recvec_push_n(tl_recvec_t* vec, const tl_record_t* recs, size_t n);

/**
 * Ensure capacity for at least `needed` total elements.
 * Does not change len.
 *
 * @return TL_OK on success, TL_ENOMEM if allocation fails
 */
tl_status_t tl_recvec_reserve(tl_recvec_t* vec, size_t needed);

/**
 * Shrink capacity to match length (release excess memory).
 *
 * @return TL_OK on success, TL_ENOMEM if realloc fails (unlikely)
 */
tl_status_t tl_recvec_shrink_to_fit(tl_recvec_t* vec);

/**
 * Move ownership from src to dst.
 * After move, src is empty and dst owns the data.
 */
void tl_recvec_move(tl_recvec_t* dst, tl_recvec_t* src);

/**
 * Sort vector by timestamp using stable sort.
 * Used at memrun seal time for out-of-order buffer.
 */
void tl_recvec_sort_by_ts(tl_recvec_t* vec);

/**
 * Binary search for lower_bound of timestamp.
 *
 * @param ts Target timestamp
 * @return Index of first element with rec.ts >= ts, or len if none
 */
size_t tl_recvec_lower_bound(const tl_recvec_t* vec, tl_ts_t ts);

/**
 * Pin-aware operations for snapshot safety.
 * When pin_count > 0, growth must allocate new buffer and retire old.
 */
void tl_recvec_pin(tl_recvec_t* vec);
void tl_recvec_unpin(tl_recvec_t* vec);
bool tl_recvec_is_pinned(const tl_recvec_t* vec);

/*
 * Inline accessors
 */
TL_INLINE size_t tl_recvec_len(const tl_recvec_t* vec) {
    return vec ? vec->len : 0;
}

TL_INLINE size_t tl_recvec_cap(const tl_recvec_t* vec) {
    return vec ? vec->cap : 0;
}

TL_INLINE bool tl_recvec_empty(const tl_recvec_t* vec) {
    return vec == NULL || vec->len == 0;
}

TL_INLINE tl_record_t* tl_recvec_data(tl_recvec_t* vec) {
    return vec ? vec->data : NULL;
}

TL_INLINE const tl_record_t* tl_recvec_data_const(const tl_recvec_t* vec) {
    return vec ? vec->data : NULL;
}

TL_INLINE tl_record_t* tl_recvec_at(tl_recvec_t* vec, size_t i) {
    return (vec && i < vec->len) ? &vec->data[i] : NULL;
}

#ifdef __cplusplus
}
#endif

#endif /* TL_RECVEC_H */
