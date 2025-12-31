#ifndef TL_FILTER_H
#define TL_FILTER_H

#include "tl_defs.h"
#include "tl_status.h"
#include "tl_alloc.h"
#include "tl_merge.h"
#include "tl_tombstones.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Tombstone filter cursor.
 *
 * Maintains position in sorted tombstone list for efficient filtering.
 * Because input timestamps are non-decreasing, cursor only advances forward.
 */
typedef struct tl_tomb_cursor {
    const tl_tombstones_t* tombs;
    uint32_t               idx;       /* Current interval index */
    tl_ts_t                cur_start; /* Current interval start */
    tl_ts_t                cur_end;   /* Current interval end */
    bool                   cur_end_unbounded; /* Current interval open-ended */
} tl_tomb_cursor_t;

/**
 * Initialize tombstone cursor.
 */
void tl_tomb_cursor_init(tl_tomb_cursor_t* cur, const tl_tombstones_t* tombs);

/**
 * Check if timestamp is deleted and advance cursor.
 *
 * Because timestamps are non-decreasing, cursor only moves forward.
 * This provides amortized O(1) per check over the entire query.
 *
 * @param cur Cursor
 * @param ts  Timestamp to check
 * @return true if ts is deleted (falls within a tombstone interval)
 */
bool tl_tomb_cursor_is_deleted(tl_tomb_cursor_t* cur, tl_ts_t ts);

/**
 * Filtered iterator: wraps merge iterator with tombstone filtering.
 *
 * Automatically skips records covered by tombstones.
 */
typedef struct tl_filtered_iter {
    tl_merge_iter_t*  merge;   /* Underlying merge iterator (not owned) */
    tl_tomb_cursor_t  cursor;  /* Tombstone cursor */

    /* Current state */
    tl_record_t       current;
    tl_iter_state_t   state;

    const tl_allocator_t* alloc;
} tl_filtered_iter_t;

/**
 * Create a filtered iterator.
 *
 * The merge iterator is NOT consumed; caller retains ownership.
 *
 * @param alloc Allocator
 * @param merge Merge iterator to wrap
 * @param tombs Effective tombstones (may be NULL for no filtering)
 * @param out   Output iterator
 * @return TL_OK on success
 */
tl_status_t tl_filtered_iter_create(const tl_allocator_t* alloc,
                                     tl_merge_iter_t* merge,
                                     const tl_tombstones_t* tombs,
                                     tl_filtered_iter_t** out);

void tl_filtered_iter_destroy(tl_filtered_iter_t* it);

const tl_record_t* tl_filtered_iter_peek(tl_filtered_iter_t* it);
tl_status_t tl_filtered_iter_advance(tl_filtered_iter_t* it);
tl_iter_state_t tl_filtered_iter_state(tl_filtered_iter_t* it);

#ifdef __cplusplus
}
#endif

#endif /* TL_FILTER_H */
