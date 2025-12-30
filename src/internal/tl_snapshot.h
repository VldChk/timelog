#ifndef TL_SNAPSHOT_H
#define TL_SNAPSHOT_H

#include "tl_defs.h"
#include "tl_alloc.h"
#include "tl_manifest.h"
#include "tl_memtable.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Snapshot: stable view for read isolation.
 *
 * A snapshot captures:
 * - Pinned manifest (immutable segment catalog)
 * - Pinned memview (sealed memruns + active buffer snapshot)
 *
 * Properties:
 * - Immutable after creation
 * - Manifest and memview remain valid for snapshot lifetime
 * - Multiple iterators can be created from same snapshot
 *
 * The snapshot is acquired under the view_seq seqlock protocol:
 * - Reader spins until view_seq is even (stable)
 * - Acquires manifest and memview references
 * - Validates view_seq unchanged
 * - If changed, retries
 *
 * This guarantees "exactly-once visibility": each record is seen
 * either in memview OR in manifest segments, never both/neither.
 */
struct tl_snapshot {
    /* Pinned manifest (reference counted) */
    tl_manifest_t*    manifest;

    /* Pinned memview (owns this copy) */
    tl_memview_t*     memview;

    /* Cached global bounds (optional optimization) */
    bool              has_bounds;
    tl_ts_t           min_ts;
    tl_ts_t           max_ts;

    /* Parent timelog (for internal access, not owned) */
    struct tl_timelog* tl;

    /* Allocator */
    const tl_allocator_t* alloc;
};

/**
 * Acquire a snapshot from a timelog instance.
 *
 * Uses seqlock protocol for lock-free snapshot acquisition:
 * 1. Load view_seq, verify even (stable)
 * 2. Pin manifest
 * 3. Capture memview
 * 4. Verify view_seq unchanged
 * 5. If changed, release and retry
 *
 * @param tl  Timelog instance
 * @param out Output pointer for snapshot
 * @return TL_OK on success, TL_ENOMEM if allocation fails
 */
tl_status_t tl_snapshot_acquire_internal(struct tl_timelog* tl,
                                          tl_snapshot_t** out);

/**
 * Release a snapshot.
 *
 * Releases manifest and memview references.
 * Iterators created from this snapshot become invalid.
 */
void tl_snapshot_release_internal(tl_snapshot_t* snap);

/**
 * Check if snapshot is empty (no data).
 */
bool tl_snapshot_empty(const tl_snapshot_t* snap);

/**
 * Get snapshot min timestamp.
 * Returns TL_TS_MAX if empty.
 */
tl_ts_t tl_snapshot_min_ts(const tl_snapshot_t* snap);

/**
 * Get snapshot max timestamp.
 * Returns TL_TS_MIN if empty.
 */
tl_ts_t tl_snapshot_max_ts(const tl_snapshot_t* snap);

#ifdef __cplusplus
}
#endif

#endif /* TL_SNAPSHOT_H */
