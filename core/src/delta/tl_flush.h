#ifndef TL_FLUSH_H
#define TL_FLUSH_H

#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../storage/tl_segment.h"
#include "tl_memrun.h"

/*===========================================================================
 * Flush Builder
 *
 * Builds L0 segments from sealed memruns. Serialized by flush_mu in tl_timelog.
 *
 * The flush builder:
 * 1. Merges run + ooo arrays into a single sorted stream (two-way merge)
 * 2. Passes merged records + tombstones to tl_segment_build_l0
 * 3. Returns the built L0 segment
 *
 * Reference: Write Path LLD Section 4.3
 *===========================================================================*/

/*===========================================================================
 * Flush Context
 *
 * Stack-allocated by caller. Contains configuration for flush build.
 *===========================================================================*/

typedef struct tl_flush_ctx {
    tl_alloc_ctx_t* alloc;              /* Allocator */
    size_t          target_page_bytes;  /* Page size target */
    uint32_t        generation;         /* Generation for L0 segment */
} tl_flush_ctx_t;

/*===========================================================================
 * Two-Way Merge Iterator
 *
 * Produces records in timestamp order from two sorted inputs.
 * Stable merge: if timestamps are equal, prefers first input (run over ooo).
 *
 * Usage:
 *   tl_merge_iter_t it;
 *   tl_merge_iter_init(&it, run, run_len, ooo, ooo_len);
 *   while (!tl_merge_iter_done(&it)) {
 *       const tl_record_t* rec = tl_merge_iter_next(&it);
 *       // Process rec
 *   }
 *
 * Thread Safety:
 * - Not thread-safe. Each thread should use its own iterator.
 *===========================================================================*/

typedef struct tl_merge_iter {
    const tl_record_t* a;       /* First input array (e.g., run) */
    size_t             a_len;   /* Length of first array */
    size_t             a_pos;   /* Current position in first array */

    const tl_record_t* b;       /* Second input array (e.g., ooo) */
    size_t             b_len;   /* Length of second array */
    size_t             b_pos;   /* Current position in second array */
} tl_merge_iter_t;

/*===========================================================================
 * Merge Iterator API
 *===========================================================================*/

/**
 * Initialize a merge iterator.
 *
 * @param it    Iterator to initialize
 * @param a     First sorted array (may be NULL if a_len == 0)
 * @param a_len Length of first array
 * @param b     Second sorted array (may be NULL if b_len == 0)
 * @param b_len Length of second array
 */
void tl_merge_iter_init(tl_merge_iter_t* it,
                         const tl_record_t* a, size_t a_len,
                         const tl_record_t* b, size_t b_len);

/**
 * Get the next record from the merge.
 *
 * Stable merge: If both inputs have equal timestamps, returns from 'a' first.
 *
 * @param it  Iterator
 * @return Pointer to next record, or NULL if exhausted
 */
const tl_record_t* tl_merge_iter_next(tl_merge_iter_t* it);

/**
 * Check if iterator is exhausted.
 */
TL_INLINE bool tl_merge_iter_done(const tl_merge_iter_t* it) {
    return it->a_pos >= it->a_len && it->b_pos >= it->b_len;
}

/**
 * Get count of remaining records.
 */
TL_INLINE size_t tl_merge_iter_remaining(const tl_merge_iter_t* it) {
    return (it->a_len - it->a_pos) + (it->b_len - it->b_pos);
}

/*===========================================================================
 * Flush Build API
 *===========================================================================*/

/**
 * Build an L0 segment from a memrun.
 *
 * Algorithm:
 * 1. Check for addition overflow: run_len + ooo_len
 * 2. If both run and ooo empty but tombs non-empty: build tombstone-only segment
 * 3. Check for multiplication overflow: total_records * sizeof(tl_record_t)
 * 4. Allocate merged[] buffer
 * 5. Merge run + ooo into merged[] using two-way merge iterator
 * 6. Call tl_segment_build_l0(merged, tombstones)
 * 7. Free merged[] buffer
 *
 * @param ctx      Flush context with configuration
 * @param mr       Pinned memrun (caller holds reference)
 * @param out_seg  Output: built L0 segment (caller takes ownership, refcnt = 1)
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EOVERFLOW if total_records * sizeof overflows,
 *         TL_EINVAL if memrun is completely empty (no records, no tombstones)
 */
tl_status_t tl_flush_build(const tl_flush_ctx_t* ctx,
                            const tl_memrun_t* mr,
                            tl_segment_t** out_seg);

#endif /* TL_FLUSH_H */
