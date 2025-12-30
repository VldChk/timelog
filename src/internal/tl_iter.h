#ifndef TL_ITER_H
#define TL_ITER_H

#include "tl_defs.h"
#include "tl_status.h"
#include "tl_alloc.h"
#include "tl_segment.h"
#include "tl_memtable.h"

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * Base Iterator Interface
 *===========================================================================*/

/**
 * Iterator state enumeration.
 */
typedef enum tl_iter_state {
    TL_ITER_READY = 0,   /* Has current record ready */
    TL_ITER_EOF   = 1,   /* Exhausted */
    TL_ITER_ERROR = 2    /* Error occurred */
} tl_iter_state_t;

/**
 * Common iterator vtable for polymorphic iteration.
 */
typedef struct tl_iter_vtable {
    /* Get current record (must be in READY state) */
    const tl_record_t* (*peek)(void* self);

    /* Advance to next record */
    tl_status_t (*advance)(void* self);

    /* Seek to first record >= ts (optional, may return TL_EOF if beyond range) */
    tl_status_t (*seek)(void* self, tl_ts_t ts);

    /* Get current state */
    tl_iter_state_t (*state)(void* self);

    /* Destroy iterator */
    void (*destroy)(void* self);
} tl_iter_vtable_t;

/**
 * Generic iterator handle.
 */
typedef struct tl_component_iter {
    const tl_iter_vtable_t* vtable;
    void*                   impl;
    uint32_t                component_id;  /* For tie-breaking in merge */
} tl_component_iter_t;

/*===========================================================================
 * Array Iterator (simple sorted array iteration)
 *===========================================================================*/

/**
 * Simple iterator over a sorted record array.
 * Used as a building block for other iterators.
 */
typedef struct tl_array_iter {
    const tl_record_t*  data;
    size_t              len;
    size_t              idx;
    tl_ts_t             t1;
    tl_ts_t             t2;
    tl_record_t         current;
    tl_iter_state_t     state;
    const tl_allocator_t* alloc;
} tl_array_iter_t;

tl_status_t tl_array_iter_create(const tl_allocator_t* alloc,
                                  const tl_record_t* data,
                                  size_t len,
                                  tl_ts_t t1,
                                  tl_ts_t t2,
                                  tl_array_iter_t** out);

void tl_array_iter_destroy(tl_array_iter_t* it);

const tl_record_t* tl_array_iter_peek(tl_array_iter_t* it);
tl_status_t tl_array_iter_advance(tl_array_iter_t* it);
tl_status_t tl_array_iter_seek(tl_array_iter_t* it, tl_ts_t ts);
tl_iter_state_t tl_array_iter_state(tl_array_iter_t* it);

/*===========================================================================
 * Segment Iterator
 *===========================================================================*/

/**
 * Iterator over a segment's pages for range [t1, t2).
 *
 * Uses two-level navigation:
 * 1. Page catalog to find candidate pages
 * 2. Within-page binary search for boundaries
 *
 * Handles page delete flags:
 * - FULLY_DELETED: skip page entirely
 * - FULLY_LIVE: no per-row checks
 * - PARTIAL_DELETED: consult row delete mask
 */
typedef struct tl_segment_iter {
    const tl_segment_t* seg;
    tl_ts_t             t1;
    tl_ts_t             t2;

    /* Current position */
    uint32_t            page_idx;
    uint32_t            page_end;     /* One past last candidate page */
    uint32_t            row_idx;
    uint32_t            row_end;      /* One past last row in current page */

    /* Current page cache */
    const tl_page_t*    current_page;

    /* Current record */
    tl_record_t         current;
    tl_iter_state_t     state;

    /* Allocator */
    const tl_allocator_t* alloc;
} tl_segment_iter_t;

/**
 * Create a segment iterator for range [t1, t2).
 *
 * @param alloc Allocator
 * @param seg   Segment to iterate
 * @param t1    Range start (inclusive)
 * @param t2    Range end (exclusive)
 * @param out   Output iterator
 * @return TL_OK on success
 */
tl_status_t tl_segment_iter_create(const tl_allocator_t* alloc,
                                    const tl_segment_t* seg,
                                    tl_ts_t t1,
                                    tl_ts_t t2,
                                    tl_segment_iter_t** out);

void tl_segment_iter_destroy(tl_segment_iter_t* it);

/* Vtable accessors */
const tl_record_t* tl_segment_iter_peek(tl_segment_iter_t* it);
tl_status_t tl_segment_iter_advance(tl_segment_iter_t* it);
tl_status_t tl_segment_iter_seek(tl_segment_iter_t* it, tl_ts_t ts);
tl_iter_state_t tl_segment_iter_state(tl_segment_iter_t* it);

/*===========================================================================
 * Two-Way Merge Iterator (for memrun: run + ooo)
 *===========================================================================*/

/**
 * Iterator merging two sorted arrays (run + ooo from memrun).
 *
 * Both arrays must be sorted by timestamp.
 * Produces records in non-decreasing timestamp order.
 */
typedef struct tl_twoway_iter {
    const tl_record_t*  run;
    size_t              run_len;
    size_t              run_idx;

    const tl_record_t*  ooo;
    size_t              ooo_len;
    size_t              ooo_idx;

    /* Range bounds */
    tl_ts_t             t1;
    tl_ts_t             t2;

    /* Current record */
    tl_record_t         current;
    tl_iter_state_t     state;

    const tl_allocator_t* alloc;
} tl_twoway_iter_t;

/**
 * Create a two-way merge iterator for range [t1, t2).
 *
 * @param alloc   Allocator
 * @param run     In-order array (sorted)
 * @param run_len Length of run
 * @param ooo     Out-of-order array (sorted)
 * @param ooo_len Length of ooo
 * @param t1      Range start
 * @param t2      Range end
 * @param out     Output iterator
 * @return TL_OK on success
 */
tl_status_t tl_twoway_iter_create(const tl_allocator_t* alloc,
                                   const tl_record_t* run,
                                   size_t run_len,
                                   const tl_record_t* ooo,
                                   size_t ooo_len,
                                   tl_ts_t t1,
                                   tl_ts_t t2,
                                   tl_twoway_iter_t** out);

void tl_twoway_iter_destroy(tl_twoway_iter_t* it);

const tl_record_t* tl_twoway_iter_peek(tl_twoway_iter_t* it);
tl_status_t tl_twoway_iter_advance(tl_twoway_iter_t* it);
tl_status_t tl_twoway_iter_seek(tl_twoway_iter_t* it, tl_ts_t ts);
tl_iter_state_t tl_twoway_iter_state(tl_twoway_iter_t* it);

#ifdef __cplusplus
}
#endif

#endif /* TL_ITER_H */
