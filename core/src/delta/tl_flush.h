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
 * The flush builder merges the in-order run and every OOO run into a single
 * sorted stream via a k-way merge, then hands the merged records plus the
 * memrun's tombstones to tl_segment_build_l0 to produce an L0 segment.
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
    tl_seq_t        applied_seq;        /* Output segment watermark.
                                         * Must satisfy: applied_seq >= max(ctx->tombs.max_seq). */
    tl_intervals_imm_t tombs;           /* Snapshot-visible tombstones clipped to
                                         * memrun bounds, used only for record
                                         * filtering during merge. This is NOT
                                         * the same set as mr->tombs persisted
                                         * into the output L0 segment. */
    bool            collect_drops;      /* Collect dropped records */
} tl_flush_ctx_t;

/*===========================================================================
 * Flush Build API
 *===========================================================================*/

/**
 * Build an L0 segment from a memrun.
 *
 * Performs a stable k-way merge of the in-order run and every OOO run, applies
 * the snapshot-visible tombstones to drop records the merge would otherwise
 * keep, and hands the surviving records (plus the memrun's persisted
 * tombstones) to tl_segment_build_l0. If no records survive but tombstones
 * exist, a tombstone-only segment is produced.
 *
 * @param ctx              Flush context with configuration
 * @param mr               Pinned memrun (caller holds reference)
 * @param out_seg          Output: built L0 segment (caller takes ownership,
 *                         refcnt = 1). May be NULL if all records are dropped
 *                         and no tombstones exist.
 * @param out_dropped      Output: dropped records (ts, handle) for on_drop
 *                         callback. Owned by caller; free with alloc.
 *                         NULL when no records were dropped.
 * @param out_dropped_len  Output: length of out_dropped
 * @return TL_OK on success,
 *         TL_ENOMEM on allocation failure,
 *         TL_EOVERFLOW if total_records * sizeof overflows,
 *         TL_EINVAL if memrun is completely empty (no records, no tombstones)
 */
tl_status_t tl_flush_build(const tl_flush_ctx_t* ctx,
                            const tl_memrun_t* mr,
                            tl_segment_t** out_seg,
                            tl_record_t** out_dropped,
                            size_t* out_dropped_len);

#endif /* TL_FLUSH_H */
