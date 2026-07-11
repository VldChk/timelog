/*===========================================================================
 * tl_pagespan_iter.c - PageSpan Iterator Implementation
 *
 * Streaming iterator over the contiguous page slices that fall within a
 * query time range. Each next() returns one slice; spans are not
 * pre-materialised into an array, so memory use is independent of the
 * number of spans in the range.
 *
 * The iterator returns view structs that share a single reference-
 * counted "owner". Atomic refcounting on the owner lets independent
 * threads release individual views without synchronisation, and lets
 * the owner outlive the iterator if any view is still held.
 *
 * Owner teardown frees the owner struct BEFORE invoking the release
 * hook, because a binding hook can free the allocator that owns the
 * struct (allocator lifetime safety; see header for full rationale).
 *===========================================================================*/

#include "tl_pagespan_iter.h"
#include "tl_snapshot.h"
#include "../internal/tl_atomic.h"
#include "../internal/tl_defs.h"
#include "../internal/tl_alloc.h"
#include "../internal/tl_refcount.h"
#include "../internal/tl_range.h"
#include "tl_segment_range.h"
#include "../internal/tl_timelog_internal.h"
#include "../storage/tl_page.h"
#include "../storage/tl_segment.h"
#include "../storage/tl_manifest.h"

#include <string.h>

/* When > 0, the iterator allocation in tl_pagespan_iter_open() fails
 * and the counter is decremented. Used to exercise the failure path
 * after the owner has been created. Test-only. */
#ifdef TL_TEST_HOOKS
volatile int tl_test_pagespan_fail_iter_alloc = 0;
#endif

/*===========================================================================
 * Internal Types
 *===========================================================================*/

/**
 * Owner structure - pins snapshot resources backing spans.
 */
struct tl_pagespan_owner {
    tl_atomic_u32               refcnt;
    tl_snapshot_t*              snapshot;   /* Owned reference */
    tl_alloc_ctx_t*             alloc;      /* Borrowed from timelog */
    tl_pagespan_owner_hooks_t   hooks;      /* Copied from iter_open */
    bool                        hook_armed; /* Hook runs only after successful open */
};

/**
 * Iterator phase state machine. L1 segments are enumerated before L0
 * so that compacted (non-overlapping) data is returned first, then any
 * not-yet-compacted overlay.
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

    tl_atomic_init_u32(&owner->refcnt, 1);
    owner->snapshot = snapshot;
    owner->alloc = alloc;
    owner->hook_armed = false;

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
 * The release hook MUST run after the owner struct is freed: a binding
 * hook may Py_DECREF the timelog and thereby free the allocator that
 * holds the owner struct. Calling tl__free(alloc, owner) after the hook
 * would use a freed allocator. The ordering below is therefore part of
 * the owner's correctness contract, not an optimisation.
 */
static void owner_destroy(tl_pagespan_owner_t* owner) {
    TL_ASSERT(owner != NULL);
    TL_ASSERT(tl_atomic_load_relaxed_u32(&owner->refcnt) == 0);

    /* Copy hook fields out before any of the resources they may
     * indirectly reference get released. */
    tl_snapshot_t* snap = owner->snapshot;
    tl_alloc_ctx_t* alloc = owner->alloc;
    tl_pagespan_owner_hooks_t hooks = owner->hooks;
    bool hook_armed = owner->hook_armed;

    /* Release pins and free the owner while the allocator is still
     * guaranteed alive. */
    if (snap != NULL) {
        tl_snapshot_release(snap);
    }
    tl__free(alloc, owner);

    /* Now safe to run binding code that may free the allocator. */
    if (hook_armed && hooks.on_release != NULL) {
        hooks.on_release(hooks.user);
    }
}

void tl_pagespan_owner_incref(tl_pagespan_owner_t* owner) {
    TL_ASSERT(owner != NULL);
    TL_REFCOUNT_ACQUIRE(&owner->refcnt,
                        "pagespan owner incref after final release",
                        "pagespan owner refcount overflow");
}

void tl_pagespan_owner_decref(tl_pagespan_owner_t* owner) {
    TL_ASSERT(owner != NULL);
    TL_REFCOUNT_RELEASE(&owner->refcnt, {
        owner_destroy(owner);
    }, "pagespan owner double-release: refcnt was 0 before decrement");
}

/*===========================================================================
 * Segment Cursor Initialization
 *
 * Finds the page range [first, last) within a segment that overlaps the
 * query range [t1, t2).
 *===========================================================================*/

/**
 * Position the iterator's cursor at the first page of `seg` that
 * overlaps the query range. Returns false if no pages overlap or the
 * segment is empty, in which case caller advances to the next segment.
 */
static bool init_segment_cursor(tl_pagespan_iter_t* it, const tl_segment_t* seg) {
    TL_ASSERT(it != NULL);

    if (seg == NULL || seg->page_count == 0) {
        return false;
    }

    /* Unbounded ranges are not supported by this iterator yet, so
     * t2_unbounded is hard-coded to false. */
    if (!tl_range_overlaps(seg->min_ts, seg->max_ts, it->t1, it->t2, false)) {
        return false;
    }

    size_t first = 0;
    size_t last = 0;
    if (!tl_segment_page_range(seg, it->t1, it->t2, false, &first, &last)) {
        return false;
    }

    /* Page counts are capped during segment build. */
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
            if (!(it->flags & TL_PAGESPAN_INCLUDE_L1)) {
                it->phase = PHASE_L0;
                it->seg_idx = 0;
                continue;
            }

            bool early_stop = false;
            size_t l1_count = tl_manifest_l1_count(m);
            while (it->seg_idx < l1_count) {
                const tl_segment_t* seg = tl_manifest_l1_get(m, it->seg_idx);
                /* Early-terminate the L1 scan once min_ts >= t2.
                 *
                 * L1 segments have strictly increasing min_ts because:
                 *   - L1 is sorted by window_start
                 *   - windows are non-overlapping: window_start[i] >= window_end[i-1]
                 *   - records lie within their window: min_ts >= window_start
                 * Chaining these: min_ts[i] >= window_start[i] >=
                 * window_end[i-1] > max_ts[i-1]. So once one segment
                 * starts at or after t2, all later ones do too. */
                if (seg->min_ts >= it->t2) {
                    early_stop = true;
                    break;
                }
                it->seg_idx++;

                if (init_segment_cursor(it, seg)) {
                    return true;
                }
            }

            if (early_stop || it->seg_idx >= l1_count) {
                it->phase = PHASE_L0;
                it->seg_idx = 0;
            }
            break;

        case PHASE_L0:
            if (!(it->flags & TL_PAGESPAN_INCLUDE_L0)) {
                it->phase = PHASE_DONE;
                return false;
            }

            while (it->seg_idx < tl_manifest_l0_count(m)) {
                const tl_segment_t* seg = tl_manifest_l0_get(m, it->seg_idx);
                it->seg_idx++;

                if (init_segment_cursor(it, seg)) {
                    return true;
                }
            }

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
    if (tl == NULL || out == NULL) {
        return TL_EINVAL;
    }

    *out = NULL;

    if (flags == 0) {
        flags = TL_PAGESPAN_DEFAULT;
    }

    /* SEGMENTS_ONLY is currently mandatory; memview/memtable iteration
     * is not implemented yet. */
    if (!(flags & TL_PAGESPAN_SEGMENTS_ONLY)) {
        return TL_EINVAL;
    }

    /* VISIBLE_ONLY (tombstone-aware filtering) is reserved. */
    if (flags & TL_PAGESPAN_VISIBLE_ONLY) {
        return TL_EINVAL;
    }

    if (!tl->is_open) {
        return TL_ESTATE;
    }

    tl_alloc_ctx_t* alloc = &tl->alloc;

    bool empty_range = tl_range_is_empty(t1, t2, false);

    /* Acquire a snapshot even for an empty range. Bindings pair
     * pins_enter() before iter_open() with pins_exit() via the
     * release hook; skipping owner creation here would skip the hook
     * and leak the pin. Always going through the owner path keeps the
     * lifecycle symmetric: if iter_open succeeds, the hook is
     * guaranteed to fire when the iterator and all its views are
     * released. */
    tl_snapshot_t* snap = NULL;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    if (st != TL_OK) {
        return st;
    }

    tl_pagespan_owner_t* owner = NULL;
    st = owner_create(snap, alloc, hooks, &owner);
    if (st != TL_OK) {
        tl_snapshot_release(snap);
        return st;
    }

#ifdef TL_TEST_HOOKS
    if (tl_test_pagespan_fail_iter_alloc > 0) {
        tl_test_pagespan_fail_iter_alloc--;
        tl_pagespan_owner_decref(owner);
        return TL_ENOMEM;
    }
#endif

    tl_pagespan_iter_t* it = tl__malloc(alloc, sizeof(tl_pagespan_iter_t));
    if (it == NULL) {
        /* owner_create gave the owner refcnt=1; decref triggers destroy. */
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
        /* Empty range: first next() returns EOF without scanning. */
        it->phase = PHASE_DONE;
    } else {
        if (flags & TL_PAGESPAN_INCLUDE_L1) {
            it->phase = PHASE_L1;
        } else if (flags & TL_PAGESPAN_INCLUDE_L0) {
            it->phase = PHASE_L0;
        } else {
            it->phase = PHASE_DONE;
        }
    }
    it->seg_idx = 0;
    it->current_seg = NULL;

    /* Arm the release hook only after a successful open: a failure
     * path above must not run the user's hook. */
    owner->hook_armed = true;

    *out = it;
    return TL_OK;
}

tl_status_t tl_pagespan_iter_next(
    tl_pagespan_iter_t* it,
    tl_pagespan_view_t* out_view)
{
    if (it == NULL || out_view == NULL) {
        return TL_EINVAL;
    }

    memset(out_view, 0, sizeof(*out_view));

    if (it->closed || it->phase == PHASE_DONE) {
        return TL_EOF;
    }

    /* Owner is always created in iter_open, even for empty ranges. */
    TL_ASSERT(it->owner != NULL);

    for (;;) {
        if (it->current_seg == NULL) {
            if (!advance_to_next_segment(it)) {
                return TL_EOF;
            }
        }

        const tl_page_catalog_t* cat = tl_segment_catalog(it->current_seg);

        while (it->page_idx < it->page_end) {
            const tl_page_meta_t* meta = tl_page_catalog_get(cat, it->page_idx);
            const tl_page_t* page = meta->page;

            size_t row_start = tl_page_lower_bound(page, it->t1);
            size_t row_end = tl_page_lower_bound(page, it->t2);

            if (row_start >= row_end) {
                it->page_idx++;
                continue;
            }

            TL_ASSERT(row_start < page->count);
            TL_ASSERT(row_end <= page->count);
            TL_ASSERT(row_end - row_start <= UINT32_MAX);

            uint32_t len = (uint32_t)(row_end - row_start);

            out_view->owner = it->owner;
            out_view->ts = &page->ts[row_start];
            out_view->h = &page->h[row_start];
            out_view->len = len;
            out_view->first_ts = page->ts[row_start];
            out_view->last_ts = page->ts[row_end - 1];

            /* Each returned view holds its own owner reference; the
             * caller releases it via view_release/owner_decref. */
            tl_pagespan_owner_incref(it->owner);

            it->page_idx++;

            return TL_OK;
        }

        it->current_seg = NULL;
    }
}

void tl_pagespan_iter_close(tl_pagespan_iter_t* it) {
    if (it == NULL || it->closed) {
        return;
    }

    it->closed = true;

    /* Same allocator-lifetime contract as owner_destroy(): the release
     * hook fired by owner_decref may free the allocator that owns this
     * iterator, so the iterator must be freed first. */
    tl_pagespan_owner_t* owner = it->owner;
    tl_alloc_ctx_t* alloc = it->alloc;

    tl__free(alloc, it);

    if (owner != NULL) {
        tl_pagespan_owner_decref(owner);
    }
}
