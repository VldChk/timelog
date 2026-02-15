#ifndef TL_OOORUN_H
#define TL_OOORUN_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_atomic.h"

/*===========================================================================
 * OOO Run: Immutable Sorted Records
 *
 * Represents a sorted run of out-of-order records. Immutable after creation.
 * Reference counted so runs can be pinned by memviews and memruns.
 *===========================================================================*/

typedef struct tl_ooorun {
    tl_atomic_u32   refcnt;     /* Reference count */
    tl_alloc_ctx_t* alloc;      /* Allocator (borrowed) */

    tl_record_t*    records;    /* Sorted by (ts, handle) */
    size_t          len;        /* Record count */

    tl_ts_t         min_ts;     /* records[0].ts */
    tl_ts_t         max_ts;     /* records[len - 1].ts */

    tl_seq_t        applied_seq;/* Tombstone watermark applied to this run */

    uint64_t        gen;        /* Monotonic generation for tie-breaks */
} tl_ooorun_t;

/*===========================================================================
 * OOO Runset: Immutable Array of Runs
 *
 * Holds a stable array of run pointers. Immutable after creation.
 *===========================================================================*/

typedef struct tl_ooorunset {
    tl_atomic_u32   refcnt;     /* Reference count */
    tl_alloc_ctx_t* alloc;      /* Allocator (borrowed) */

    size_t          count;      /* Number of runs */
    size_t          total_len;  /* Sum of run lengths */

    tl_ooorun_t*    runs[];     /* Flexible array of run pointers */
} tl_ooorunset_t;

/*===========================================================================
 * Run Lifecycle
 *===========================================================================*/

tl_status_t tl_ooorun_create(tl_alloc_ctx_t* alloc,
                              tl_record_t* records, size_t len,
                              tl_seq_t applied_seq,
                              uint64_t gen,
                              tl_ooorun_t** out);

tl_ooorun_t* tl_ooorun_acquire(tl_ooorun_t* run);
void tl_ooorun_release(tl_ooorun_t* run);

/*===========================================================================
 * Runset Lifecycle
 *===========================================================================*/

tl_status_t tl_ooorunset_create(tl_alloc_ctx_t* alloc,
                                 tl_ooorun_t* const* runs,
                                 size_t count,
                                 tl_ooorunset_t** out);

tl_status_t tl_ooorunset_append(tl_alloc_ctx_t* alloc,
                                 tl_ooorunset_t* old_set,
                                 tl_ooorun_t* run,
                                 tl_ooorunset_t** out);

tl_ooorunset_t* tl_ooorunset_acquire(tl_ooorunset_t* set);
void tl_ooorunset_release(tl_ooorunset_t* set);

/*===========================================================================
 * Accessors
 *===========================================================================*/

TL_INLINE size_t tl_ooorun_len(const tl_ooorun_t* run) {
    return run->len;
}

TL_INLINE const tl_record_t* tl_ooorun_records(const tl_ooorun_t* run) {
    return run->records;
}

TL_INLINE tl_ts_t tl_ooorun_min_ts(const tl_ooorun_t* run) {
    return run->min_ts;
}

TL_INLINE tl_ts_t tl_ooorun_max_ts(const tl_ooorun_t* run) {
    return run->max_ts;
}

TL_INLINE uint64_t tl_ooorun_gen(const tl_ooorun_t* run) {
    return run->gen;
}

TL_INLINE tl_seq_t tl_ooorun_applied_seq(const tl_ooorun_t* run) {
    return run->applied_seq;
}

TL_INLINE size_t tl_ooorunset_count(const tl_ooorunset_t* set) {
    return (set == NULL) ? 0 : set->count;
}

TL_INLINE size_t tl_ooorunset_total_len(const tl_ooorunset_t* set) {
    return (set == NULL) ? 0 : set->total_len;
}

TL_INLINE tl_ooorun_t* tl_ooorunset_run_at(const tl_ooorunset_t* set, size_t idx) {
    return set->runs[idx];
}

#endif /* TL_OOORUN_H */
