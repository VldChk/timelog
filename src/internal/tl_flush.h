#ifndef TL_FLUSH_H
#define TL_FLUSH_H

#include "tl_defs.h"
#include "tl_alloc.h"
#include "tl_memtable.h"
#include "tl_segment.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Flush a sealed memrun into an immutable delta segment.
 *
 * This function:
 * 1. Merges run + ooo into a single sorted stream
 * 2. Pages the stream using segment builder
 * 3. Creates tombstone set from memrun tombstones
 * 4. Produces a complete delta segment
 *
 * @param alloc             Allocator to use
 * @param mr                Memrun to flush (not consumed; remains valid)
 * @param target_page_bytes Target page size for paging
 * @param generation        Generation number for the segment
 * @param out               Output pointer for new segment
 * @return TL_OK on success, TL_EOF if memrun is empty
 */
tl_status_t tl_flush_memrun(const tl_allocator_t* alloc,
                             const tl_memrun_t* mr,
                             size_t target_page_bytes,
                             uint32_t generation,
                             tl_segment_t** out);

#ifdef __cplusplus
}
#endif

#endif /* TL_FLUSH_H */
