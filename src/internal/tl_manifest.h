#ifndef TL_MANIFEST_H
#define TL_MANIFEST_H

#include "tl_defs.h"
#include "tl_alloc.h"
#include "tl_atomic.h"
#include "tl_segment.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Immutable manifest structure.
 *
 * The manifest is the root catalog that snapshots pin. It contains:
 * - Main segments: long-lived, mostly non-overlapping
 * - Delta segments: recent flush outputs, may overlap
 *
 * Key properties:
 * - Immutable after creation
 * - Published via serialized pointer swap (writer_mu)
 * - Reference counted for snapshot pinning
 * - New manifests are built by copying and modifying
 */
typedef struct tl_manifest {
    /* Version number for diagnostics/debugging */
    uint64_t            version;

    /* Main segments: sorted by min_ts */
    uint32_t            n_main;
    tl_segment_t**      main;        /* Array of segment pointers */

    /* Delta segments: bounded by max_delta_segments config */
    uint32_t            n_delta;
    tl_segment_t**      delta;       /* Array of segment pointers */

    /* Cached global bounds (optional optimization) */
    bool                has_bounds;
    tl_ts_t             min_ts;
    tl_ts_t             max_ts;

    /* Allocator used for this manifest */
    const tl_allocator_t* alloc;

    /* Lifetime management */
    tl_atomic_u32_t     refcnt;
} tl_manifest_t;

/**
 * Create an empty manifest.
 *
 * @param alloc   Allocator to use
 * @param version Initial version number
 * @param out     Output pointer for new manifest
 * @return TL_OK on success
 */
tl_status_t tl_manifest_create_empty(const tl_allocator_t* alloc,
                                      uint64_t version,
                                      tl_manifest_t** out);

/**
 * Build a new manifest from an existing one with changes.
 *
 * This is the primary mechanism for manifest updates:
 * 1. Acquire old manifest
 * 2. Build new manifest with changes
 * 3. Publish new manifest
 * 4. Release old manifest
 *
 * Changes are specified via optional parameters:
 * - add_delta: segment to append to delta list (refcount incremented)
 * - add_main: segment to append to main list (refcount incremented)
 * - remove_delta: array of segments to remove from delta list
 * - remove_main: array of segments to remove from main list
 *
 * @param alloc         Allocator to use
 * @param old           Previous manifest (segments are shared)
 * @param add_delta     Delta segment to add (may be NULL)
 * @param add_main      Main segment to add (may be NULL)
 * @param remove_delta  Delta segments to remove (may be NULL)
 * @param n_remove_delta Number of delta segments to remove
 * @param remove_main   Main segments to remove (may be NULL)
 * @param n_remove_main Number of main segments to remove
 * @param out           Output pointer for new manifest
 * @return TL_OK on success
 */
tl_status_t tl_manifest_build(const tl_allocator_t* alloc,
                               const tl_manifest_t* old,
                               tl_segment_t* add_delta,
                               tl_segment_t* add_main,
                               tl_segment_t** remove_delta,
                               uint32_t n_remove_delta,
                               tl_segment_t** remove_main,
                               uint32_t n_remove_main,
                               tl_manifest_t** out);

/**
 * Increment manifest reference count.
 *
 * @param m Manifest to acquire
 * @return New reference count
 */
uint32_t tl_manifest_acquire(tl_manifest_t* m);

/**
 * Decrement manifest reference count.
 *
 * When refcnt reaches 0, the manifest is destroyed.
 * Note: Segments have their own refcounts and may survive the manifest.
 *
 * @param m Manifest to release
 * @return New reference count (0 means manifest was destroyed)
 */
uint32_t tl_manifest_release(tl_manifest_t* m);

/**
 * Get total number of segments in manifest.
 */
TL_INLINE uint32_t tl_manifest_segment_count(const tl_manifest_t* m) {
    return m ? (m->n_main + m->n_delta) : 0;
}

/**
 * Validate manifest invariants (debug/test).
 *
 * Checks:
 * - All segment pointers are non-NULL
 * - Main segments are sorted by min_ts
 * - Each segment passes validation
 * - Cached bounds are correct
 *
 * @param m Manifest to validate
 * @return TL_OK if valid
 */
tl_status_t tl_manifest_validate(const tl_manifest_t* m);

/**
 * Recompute and cache global min/max timestamps.
 *
 * @param m Manifest to update (must be newly created, not yet published)
 */
void tl_manifest_compute_bounds(tl_manifest_t* m);

#ifdef __cplusplus
}
#endif

#endif /* TL_MANIFEST_H */
