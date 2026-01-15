#ifndef TL_PAGESPAN_ITER_H
#define TL_PAGESPAN_ITER_H

/**
 * @file tl_pagespan_iter.h
 * @brief Core PageSpan Enumeration API (Zero-Copy without Binding Duplication)
 *
 * This API provides a stable interface for enumerating contiguous page spans
 * within a timelog's segments. It moves span enumeration logic from bindings
 * into core, eliminating algorithm duplication and layout coupling.
 *
 * Key contracts:
 * - Spans are contiguous slices of page memory (zero-copy)
 * - Each span view owns a reference to the owner; caller must decref
 * - Views remain valid after iterator close (each holds its own owner ref)
 * - Empty ranges (t1 >= t2) return TL_OK; first next() returns TL_EOF
 *   (owner/hooks are still created and released on close)
 *
 * Thread safety:
 * - The owner refcount is NOT atomic (B4 constraint)
 * - All incref/decref operations MUST be serialized by the caller
 * - For CPython bindings, the GIL provides this serialization
 *
 * Reference: docs/timelog_v2_lld_pagespan_core_api_unification.md
 */

#include "timelog/timelog.h"
#include <string.h>  /* For memset in view_release inline */

#ifdef __cplusplus
extern "C" {
#endif

/*===========================================================================
 * Opaque Types
 *===========================================================================*/

/**
 * Opaque owner that pins the resources backing spans.
 * Reference-counted; when refcnt reaches 0, releases snapshot and calls
 * the optional release hook.
 */
typedef struct tl_pagespan_owner tl_pagespan_owner_t;

/**
 * Opaque iterator over spans for a time range.
 * Holds a reference to its owner (released on close).
 */
typedef struct tl_pagespan_iter tl_pagespan_iter_t;

/*===========================================================================
 * Span View
 *
 * Returned by iter_next for each contiguous page slice in the query range.
 * The view's owner is an owned reference - caller MUST decref when done.
 *
 * Invariants:
 * - len is always > 0 for returned views
 * - ts and h point to contiguous arrays of len elements
 * - first_ts == ts[0], last_ts == ts[len-1]
 * - View remains valid as long as owner is alive (refcnt > 0)
 *===========================================================================*/

typedef struct tl_pagespan_view {
    tl_pagespan_owner_t* owner;     /**< Owned ref (caller must decref) */
    const tl_ts_t*       ts;        /**< Pointer to page ts array (read-only) */
    const tl_handle_t*   h;         /**< Pointer to page handle array (read-only) */
    uint32_t             len;       /**< Row count (always > 0) */
    tl_ts_t              first_ts;  /**< == ts[0] */
    tl_ts_t              last_ts;   /**< == ts[len-1] */
} tl_pagespan_view_t;

/*===========================================================================
 * Release Hooks (Binding Integration)
 *
 * Bindings need to drop pins and run deferred DECREF logic when the last
 * span is released. Core does not know about Python, so an optional release
 * hook is provided.
 *
 * Destruction order (CRITICAL):
 * 1. Copy out hooks from owner struct
 * 2. Release snapshot/segment refs (no binding code runs)
 * 3. Free owner struct BEFORE calling hook
 * 4. Invoke on_release(user) if non-NULL
 *
 * Rationale: The hook may Py_DECREF the timelog, which owns the allocator.
 * Freeing owner after the hook could use a freed allocator (UAF).
 *
 * Constraints:
 * - Hook must NOT assume owner struct exists (it has been freed)
 * - Hook must NOT call back into pagespan API (re-entrancy forbidden)
 * - For CPython, hook must run with GIL held
 *===========================================================================*/

typedef void (*tl_pagespan_owner_release_fn)(void* user);

typedef struct tl_pagespan_owner_hooks {
    void*                         user;       /**< Opaque user context */
    tl_pagespan_owner_release_fn  on_release; /**< Optional release callback */
} tl_pagespan_owner_hooks_t;

/*===========================================================================
 * Flags
 *
 * B4 Constraints:
 * - TL_PAGESPAN_SEGMENTS_ONLY is required (return TL_EINVAL if not set)
 * - TL_PAGESPAN_VISIBLE_ONLY is reserved (return TL_EINVAL if set)
 * - flags == 0 is treated as TL_PAGESPAN_DEFAULT
 *===========================================================================*/

enum {
    TL_PAGESPAN_SEGMENTS_ONLY    = 1u << 0,  /**< Ignore memview/memtable */
    TL_PAGESPAN_INCLUDE_L0       = 1u << 1,  /**< Include L0 segments */
    TL_PAGESPAN_INCLUDE_L1       = 1u << 2,  /**< Include L1 segments */
    TL_PAGESPAN_VISIBLE_ONLY     = 1u << 3,  /**< Reserved (EINVAL in B4) */
    TL_PAGESPAN_REQUIRE_ZEROCOPY = 1u << 4   /**< Must not allocate staging */
};

/**
 * Default flags for B4: segments only, both L0/L1, zero-copy required.
 */
#define TL_PAGESPAN_DEFAULT \
    (TL_PAGESPAN_SEGMENTS_ONLY | TL_PAGESPAN_INCLUDE_L0 | \
     TL_PAGESPAN_INCLUDE_L1 | TL_PAGESPAN_REQUIRE_ZEROCOPY)

/*===========================================================================
 * Iterator API
 *===========================================================================*/

/**
 * Open a pagespan iterator for the half-open range [t1, t2).
 *
 * Acquires a snapshot internally; resources are pinned until all returned
 * views are released.
 *
 * Empty range behavior (t1 >= t2):
 * - Returns TL_OK and creates a valid iterator
 * - First call to iter_next() returns TL_EOF
 * - Owner/hooks are still created and released on close
 * - This follows standard iterator semantics
 *
 * @param tl     Open timelog instance (must not be NULL)
 * @param t1     Range start (inclusive)
 * @param t2     Range end (exclusive)
 * @param flags  Combination of TL_PAGESPAN_* flags (0 = DEFAULT)
 * @param hooks  Optional release hooks (may be NULL)
 * @param out    Output iterator pointer (must not be NULL)
 *
 * @return TL_OK      - Iterator created successfully
 * @return TL_EINVAL  - NULL tl/out, unsupported flags, or flag violation
 * @return TL_ESTATE  - Timelog not open
 * @return TL_ENOMEM  - Allocation failure
 */
TL_API tl_status_t tl_pagespan_iter_open(
    tl_timelog_t* tl,
    tl_ts_t t1,
    tl_ts_t t2,
    uint32_t flags,
    const tl_pagespan_owner_hooks_t* hooks,
    tl_pagespan_iter_t** out);

/**
 * Get the next span from the iterator.
 *
 * On success (TL_OK), out_view is filled with a span descriptor.
 * The view's owner reference is already incremented; caller must
 * release it via tl_pagespan_owner_decref() or tl_pagespan_view_release().
 *
 * Span ordering: L1 segments first (sorted by window), then L0 segments.
 * Within each segment, pages are enumerated in timestamp order.
 *
 * @param it        Iterator (must not be NULL, must not be closed)
 * @param out_view  Output span view (must not be NULL)
 *
 * @return TL_OK   - Span returned in out_view
 * @return TL_EOF  - No more spans (iterator exhausted)
 */
TL_API tl_status_t tl_pagespan_iter_next(
    tl_pagespan_iter_t* it,
    tl_pagespan_view_t* out_view);

/**
 * Close the iterator and release its owner reference.
 *
 * Safe to call on NULL. The iterator is freed and the pointer is invalidated;
 * callers must not use the pointer after this call (set to NULL after calling).
 * Previously returned views remain valid until their owner refs are released.
 *
 * @param it  Iterator to close (may be NULL, invalidated after call)
 */
TL_API void tl_pagespan_iter_close(tl_pagespan_iter_t* it);

/*===========================================================================
 * Owner Reference Counting
 *
 * CONCURRENCY CONSTRAINT (B4):
 * The refcount is plain uint32_t, NOT atomic. All incref/decref operations
 * MUST be serialized by the caller. For CPython bindings, the GIL provides
 * this serialization.
 *
 * Future enhancement: If multi-threaded bindings are needed, change to
 * _Atomic uint32_t with fetch_add/fetch_sub (acq_rel ordering).
 *===========================================================================*/

/**
 * Increment owner reference count.
 * Thread safety: Caller must ensure serialization.
 *
 * @param owner  Owner to incref (must not be NULL)
 */
TL_API void tl_pagespan_owner_incref(tl_pagespan_owner_t* owner);

/**
 * Decrement owner reference count.
 * When refcnt reaches 0, destroys owner and calls release hook if provided.
 * Thread safety: Caller must ensure serialization.
 *
 * @param owner  Owner to decref (must not be NULL)
 */
TL_API void tl_pagespan_owner_decref(tl_pagespan_owner_t* owner);

/*===========================================================================
 * View Helper
 *===========================================================================*/

/**
 * Release a span view's owner reference and zero the view struct.
 * Convenience wrapper around tl_pagespan_owner_decref().
 *
 * @param v  View to release (may be NULL or have NULL owner)
 */
static inline void tl_pagespan_view_release(tl_pagespan_view_t* v) {
    if (v != NULL && v->owner != NULL) {
        tl_pagespan_owner_decref(v->owner);
    }
    if (v != NULL) {
        memset(v, 0, sizeof(*v));
    }
}

#ifdef __cplusplus
}
#endif

#endif /* TL_PAGESPAN_ITER_H */
