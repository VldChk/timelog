/*===========================================================================
 * tl_pagespan_iter.c - PageSpan Iterator Implementation
 *
 * Streaming iterator over page spans for a time range.
 * Moves span enumeration logic from bindings into core, eliminating
 * algorithm duplication and layout coupling.
 *
 * Key design decisions:
 * - Streaming (no pre-allocation of span array)
 * - Each view owns a reference to the owner
 * - Owner refcount is plain uint32_t (caller serialization required)
 * - Free owner before calling release hook (allocator lifetime safety)
 *
 * Reference: docs/timelog_v2_lld_pagespan_core_api_unification.md
 *===========================================================================*/

#include "tl_pagespan_iter.h"
#include "tl_snapshot.h"
#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_range.h"
#include "../internal/tl_timelog_internal.h"
#include "../storage/tl_page.h"
#include "../storage/tl_segment.h"
#include "../storage/tl_manifest.h"

#include <string.h>

/*===========================================================================
 * Internal Types
 *===========================================================================*/

/**
 * Owner structure - pins snapshot resources backing spans.
 *
 * CONCURRENCY CONSTRAINT:
 * The refcount is plain uint32_t, NOT atomic. All incref/decref operations
 * MUST be serialized by the caller (GIL for CPython bindings).
 */
struct tl_pagespan_owner {
    uint32_t                    refcnt;     /* NOT atomic - see constraint above */
    tl_snapshot_t*              snapshot;   /* Owned reference */
    tl_alloc_ctx_t*             alloc;      /* Borrowed from timelog */
    tl_pagespan_owner_hooks_t   hooks;      /* Copied from iter_open */
};

/**
 * Iterator phase state machine.
 * L1 segments are enumerated before L0 (matches B4 behavior).
 */
typedef enum {
    PHASE_L1   = 0,     /* Iterating L1 segments */
    PHASE_L0   = 1,     /* Iterating L0 segments */
    PHASE_DONE = 2      /* All segments exhausted */
} iter_phase_t;

/**
 * Iterator structure - streaming iteration over page spans.
 */
struct tl_pagespan_iter {
    tl_pagespan_owner_t*    owner;      /* Owned reference (released on close) */
    tl_alloc_ctx_t*         alloc;      /* Allocator (for iter cleanup) */
    const tl_manifest_t*    manifest;   /* Borrowed from snapshot */
    tl_ts_t                 t1;         /* Range start (inclusive) */
    tl_ts_t                 t2;         /* Range end (exclusive) */
    uint32_t                flags;      /* TL_PAGESPAN_* flags */

    iter_phase_t            phase;      /* Current phase */
    uint32_t                seg_idx;    /* Current segment index in phase */

    const tl_segment_t*     current_seg;    /* Current segment (NULL if none) */
    uint32_t                page_idx;       /* Current page index in segment */
    uint32_t                page_end;       /* End page index (exclusive) */

    bool                    closed;     /* True after close() called */
};

/*===========================================================================
 * Owner Lifecycle
 *===========================================================================*/

/**
 * Create a new owner with the given snapshot.
 * Initial refcount is 1 (caller owns the reference).
 */
static tl_status_t owner_create(
    tl_snapshot_t* snapshot,
    tl_alloc_ctx_t* alloc,
    const tl_pagespan_owner_hooks_t* hooks,
    tl_pagespan_owner_t** out)
{
    TL_ASSERT(snapshot != NULL);
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    tl_pagespan_owner_t* owner = tl__malloc(alloc, sizeof(tl_pagespan_owner_t));
    if (owner == NULL) {
        return TL_ENOMEM;
    }

    owner->refcnt = 1;
    owner->snapshot = snapshot;
    owner->alloc = alloc;

    /* Copy hooks (NULL-safe) */
    if (hooks != NULL) {
        owner->hooks = *hooks;
    } else {
        memset(&owner->hooks, 0, sizeof(owner->hooks));
    }

    *out = owner;
    return TL_OK;
}

/**
 * Destroy owner and release all resources.
 *
 * DESTRUCTION ORDER (CRITICAL - allocator lifetime safety):
 * 1. Copy out hooks from owner struct
 * 2. Release snapshot (no binding code runs)
 * 3. Free owner struct BEFORE calling hook
 * 4. Call release hook if non-NULL
 *
 * Rationale: The hook may Py_DECREF the timelog, which owns the allocator.
 * Freeing owner after the hook could use a freed allocator (UAF).
 */
static void owner_destroy(tl_pagespan_owner_t* owner) {
    TL_ASSERT(owner != NULL);
    TL_ASSERT(owner->refcnt == 0);

    /* Step 1: Copy out hooks before freeing owner */
    tl_snapshot_t* snap = owner->snapshot;
    tl_alloc_ctx_t* alloc = owner->alloc;
    tl_pagespan_owner_hooks_t hooks = owner->hooks;

    /* Step 2: Release snapshot (no binding code runs here) */
    if (snap != NULL) {
        tl_snapshot_release(snap);
    }

    /* Step 3: Free owner struct BEFORE calling hook */
    tl__free(alloc, owner);

    /* Step 4: Call release hook (may run binding code, e.g., Py_DECREF) */
    if (hooks.on_release != NULL) {
        hooks.on_release(hooks.user);
    }
}

void tl_pagespan_owner_incref(tl_pagespan_owner_t* owner) {
    TL_ASSERT(owner != NULL);
    TL_ASSERT(owner->refcnt > 0);       /* Must not be dead */
    TL_ASSERT(owner->refcnt < UINT32_MAX);  /* Overflow check */
    owner->refcnt++;
}

void tl_pagespan_owner_decref(tl_pagespan_owner_t* owner) {
    TL_ASSERT(owner != NULL);
    TL_ASSERT(owner->refcnt > 0);  /* Must not be dead */

    owner->refcnt--;
    if (owner->refcnt == 0) {
        owner_destroy(owner);
    }
}

/*===========================================================================
 * Segment Cursor Initialization
 *
 * Canonical algorithm from tl_segment_iter_init (Section 5.3 of plan).
 * Finds the page range [first, last) that overlaps with [t1, t2).
 *===========================================================================*/

/**
 * Initialize cursor for a segment.
 * Returns true if segment has pages overlapping [t1, t2), false otherwise.
 */
static bool init_segment_cursor(tl_pagespan_iter_t* it, const tl_segment_t* seg) {
    TL_ASSERT(it != NULL);

    /* Null segment or no pages */
    if (seg == NULL || seg->page_count == 0) {
        return false;
    }

    /* Check segment-level bounds overlap with half-open [t1, t2) */
    /* Note: B4 does not support unbounded ranges (t2_unbounded = false) */
    if (!tl_range_overlaps(seg->min_ts, seg->max_ts, it->t1, it->t2, false)) {
        return false;
    }

    const tl_page_catalog_t* cat = tl_segment_catalog(seg);

    /*
     * Find first page with max_ts >= t1.
     * This is the first page that might contain records >= t1.
     */
    size_t first = tl_page_catalog_find_first_ge(cat, it->t1);

    /*
     * Find first page with min_ts >= t2.
     * This is the first page that definitely starts after our range.
     * All pages before this index might contain records < t2.
     */
    size_t last = tl_page_catalog_find_start_ge(cat, it->t2);

    /* No overlapping pages */
    if (first >= last) {
        return false;
    }

    /* Validate cast to uint32_t (page counts are bounded by segment build) */
    TL_ASSERT(first <= UINT32_MAX);
    TL_ASSERT(last <= UINT32_MAX);

    it->current_seg = seg;
    it->page_idx = (uint32_t)first;
    it->page_end = (uint32_t)last;

    return true;
}

/*===========================================================================
 * Segment Advancement
 *
 * State machine: PHASE_L1 -> PHASE_L0 -> PHASE_DONE
 * Within each phase, iterate segment indices in order.
 *===========================================================================*/

/**
 * Advance to the next segment in the current phase or transition to next phase.
 * Returns true if a new segment was found, false if exhausted.
 */
static bool advance_to_next_segment(tl_pagespan_iter_t* it) {
    TL_ASSERT(it != NULL);

    const tl_manifest_t* m = it->manifest;

    for (;;) {
        switch (it->phase) {
        case PHASE_L1:
            /* Check if L1 is enabled */
            if (!(it->flags & TL_PAGESPAN_INCLUDE_L1)) {
                it->phase = PHASE_L0;
                it->seg_idx = 0;
                continue;
            }

            /* Try next L1 segment */
            while (it->seg_idx < tl_manifest_l1_count(m)) {
                const tl_segment_t* seg = tl_manifest_l1_get(m, it->seg_idx);
                it->seg_idx++;

                if (init_segment_cursor(it, seg)) {
                    return true;
                }
            }

            /* L1 exhausted, move to L0 */
            it->phase = PHASE_L0;
            it->seg_idx = 0;
            break;

        case PHASE_L0:
            /* Check if L0 is enabled */
            if (!(it->flags & TL_PAGESPAN_INCLUDE_L0)) {
                it->phase = PHASE_DONE;
                return false;
            }

            /* Try next L0 segment */
            while (it->seg_idx < tl_manifest_l0_count(m)) {
                const tl_segment_t* seg = tl_manifest_l0_get(m, it->seg_idx);
                it->seg_idx++;

                if (init_segment_cursor(it, seg)) {
                    return true;
                }
            }

            /* L0 exhausted */
            it->phase = PHASE_DONE;
            return false;

        case PHASE_DONE:
            return false;
        }
    }
}

/*===========================================================================
 * Iterator API Implementation
 *===========================================================================*/

tl_status_t tl_pagespan_iter_open(
    tl_timelog_t* tl,
    tl_ts_t t1,
    tl_ts_t t2,
    uint32_t flags,
    const tl_pagespan_owner_hooks_t* hooks,
    tl_pagespan_iter_t** out)
{
    /* Step 1: Validate required args */
    if (tl == NULL || out == NULL) {
        return TL_EINVAL;
    }

    *out = NULL;

    /* Step 2: Normalize flags (0 -> DEFAULT) */
    if (flags == 0) {
        flags = TL_PAGESPAN_DEFAULT;
    }

    /* Step 3: Validate B4 flag requirements */
    /* SEGMENTS_ONLY is required */
    if (!(flags & TL_PAGESPAN_SEGMENTS_ONLY)) {
        return TL_EINVAL;
    }

    /* VISIBLE_ONLY is reserved (return EINVAL if set) */
    if (flags & TL_PAGESPAN_VISIBLE_ONLY) {
        return TL_EINVAL;
    }

    /* Verify timelog is open */
    if (!tl->is_open) {
        return TL_ESTATE;
    }

    /* Get allocator from timelog */
    tl_alloc_ctx_t* alloc = &tl->alloc;

    /* Step 4: Detect empty range (t1 >= t2) */
    bool empty_range = tl_range_is_empty(t1, t2, false);

    /*
     * Step 5: Acquire snapshot - ALWAYS, even for empty range.
     *
     * RATIONALE (hook symmetry for bindings):
     * Bindings call pins_enter() before iter_open() and rely on the release
     * hook to call pins_exit(). If we skip owner creation for empty ranges,
     * the hook never runs and pins leak. Always creating an owner ensures
     * symmetric lifecycle: if iter_open succeeds, the hook WILL be called
     * when all views are released and the iterator is closed.
     */
    tl_snapshot_t* snap = NULL;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    if (st != TL_OK) {
        return st;
    }

    /* Step 6: Create owner (refcnt=1, holds snapshot and hooks) */
    tl_pagespan_owner_t* owner = NULL;
    st = owner_create(snap, alloc, hooks, &owner);
    if (st != TL_OK) {
        tl_snapshot_release(snap);
        return st;
    }

    /* Step 7: Create iterator */
    tl_pagespan_iter_t* it = tl__malloc(alloc, sizeof(tl_pagespan_iter_t));
    if (it == NULL) {
        /* Owner has refcnt=1 from owner_create; decref triggers destroy */
        tl_pagespan_owner_decref(owner);
        return TL_ENOMEM;
    }

    memset(it, 0, sizeof(*it));
    it->owner = owner;
    it->alloc = alloc;
    it->t1 = t1;
    it->t2 = t2;
    it->flags = flags;
    it->closed = false;
    it->manifest = tl_snapshot_manifest(snap);

    if (empty_range) {
        /* Empty range: go directly to PHASE_DONE, first next() returns EOF */
        it->phase = PHASE_DONE;
    } else {
        /* Normal case: setup for iteration */
        if (flags & TL_PAGESPAN_INCLUDE_L1) {
            it->phase = PHASE_L1;
        } else if (flags & TL_PAGESPAN_INCLUDE_L0) {
            it->phase = PHASE_L0;
        } else {
            /* Neither L1 nor L0 enabled - will return EOF immediately */
            it->phase = PHASE_DONE;
        }
    }
    it->seg_idx = 0;
    it->current_seg = NULL;

    *out = it;
    return TL_OK;
}

tl_status_t tl_pagespan_iter_next(
    tl_pagespan_iter_t* it,
    tl_pagespan_view_t* out_view)
{
    /* Defensive NULL checks (match iter_open pattern) */
    if (it == NULL || out_view == NULL) {
        return TL_EINVAL;
    }

    /* Clear output */
    memset(out_view, 0, sizeof(*out_view));

    /* Check if closed or done */
    if (it->closed || it->phase == PHASE_DONE) {
        return TL_EOF;
    }

    /* Owner is always valid (created even for empty range for hook symmetry) */
    TL_ASSERT(it->owner != NULL);

    for (;;) {
        /* If no current segment, advance to next */
        if (it->current_seg == NULL) {
            if (!advance_to_next_segment(it)) {
                return TL_EOF;
            }
        }

        /* Scan pages in current segment */
        const tl_page_catalog_t* cat = tl_segment_catalog(it->current_seg);

        while (it->page_idx < it->page_end) {
            const tl_page_meta_t* meta = tl_page_catalog_get(cat, it->page_idx);
            const tl_page_t* page = meta->page;

            /*
             * Page flag validation (B4/V1 constraint):
             *
             * V1/B4 only supports TL_PAGE_FULLY_LIVE. Any other state indicates
             * corruption or a bug. We error out loudly rather than silently
             * skipping, which could hide data loss.
             *
             * If V2 introduces PARTIAL_DELETED pages with row bitmaps, this
             * code must be updated to handle visibility splitting.
             */
            if (page->flags != TL_PAGE_FULLY_LIVE) {
                /* Corruption or unsupported page state - internal error */
                return TL_EINTERNAL;
            }

            /* Compute row bounds within page */
            size_t row_start = tl_page_lower_bound(page, it->t1);
            size_t row_end = tl_page_lower_bound(page, it->t2);

            /* If no rows in range, skip page */
            if (row_start >= row_end) {
                it->page_idx++;
                continue;
            }

            /* Validate row bounds */
            TL_ASSERT(row_start < page->count);
            TL_ASSERT(row_end <= page->count);
            TL_ASSERT(row_end - row_start <= UINT32_MAX);

            /* Build view */
            uint32_t len = (uint32_t)(row_end - row_start);

            out_view->owner = it->owner;
            out_view->ts = &page->ts[row_start];
            out_view->h = &page->h[row_start];
            out_view->len = len;
            out_view->first_ts = page->ts[row_start];
            out_view->last_ts = page->ts[row_end - 1];

            /* Increment owner refcount for this view */
            tl_pagespan_owner_incref(it->owner);

            /* Advance to next page for next call */
            it->page_idx++;

            return TL_OK;
        }

        /* Current segment exhausted, move to next */
        it->current_seg = NULL;
    }
}

void tl_pagespan_iter_close(tl_pagespan_iter_t* it) {
    if (it == NULL || it->closed) {
        return;
    }

    it->closed = true;

    /*
     * CRITICAL: Free iterator BEFORE releasing owner reference (C-03 fix).
     *
     * The owner's release hook may Py_DECREF the timelog, which owns the
     * allocator. If owner decref triggers destroy -> hook -> allocator freed,
     * then calling tl__free(alloc, it) would be use-after-free.
     *
     * Correct order:
     * 1. Cache owner pointer
     * 2. Free iterator using allocator (while allocator is still valid)
     * 3. Release owner reference (may trigger destroy and hook)
     *
     * This mirrors the pattern in owner_destroy() which frees the owner
     * struct before calling the release hook.
     */
    tl_pagespan_owner_t* owner = it->owner;
    tl_alloc_ctx_t* alloc = it->alloc;

    /* Step 1: Free iterator struct while allocator is valid */
    tl__free(alloc, it);

    /* Step 2: Release owner reference (may trigger destroy and hook) */
    if (owner != NULL) {
        tl_pagespan_owner_decref(owner);
    }
}
