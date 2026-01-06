#include "tl_segment.h"
#include <string.h>  /* memcpy */

/*===========================================================================
 * Internal: Compute Tombstone Bounds
 *
 * For tombstone-only segments, we derive min_ts/max_ts from tombstones.
 *
 * Rules:
 * - min_ts = min(tombstones[i].start)
 * - max_ts = max(tombstones[i].end - 1) for bounded intervals
 *          = TL_TS_MAX for unbounded intervals [start, +inf)
 *
 * IMPORTANT: Never read tombstones[i].end when end_unbounded is true.
 *===========================================================================*/

static void compute_tombstone_bounds(const tl_interval_t* tombstones, size_t n,
                                      tl_ts_t* out_min, tl_ts_t* out_max) {
    TL_ASSERT(n > 0);
    TL_ASSERT(tombstones != NULL);

    tl_ts_t min_ts = tombstones[0].start;
    tl_ts_t max_ts;

    /* Check if any interval is unbounded */
    bool has_unbounded = false;
    for (size_t i = 0; i < n; i++) {
        if (tombstones[i].end_unbounded) {
            has_unbounded = true;
            break;
        }
    }

    if (has_unbounded) {
        max_ts = TL_TS_MAX;
    } else {
        /* All bounded: find max(end - 1) */
        max_ts = tombstones[0].end - 1;
        for (size_t i = 1; i < n; i++) {
            if (tombstones[i].start < min_ts) {
                min_ts = tombstones[i].start;
            }
            tl_ts_t end_inclusive = tombstones[i].end - 1;
            if (end_inclusive > max_ts) {
                max_ts = end_inclusive;
            }
        }
    }

    /* Also check remaining intervals for min_ts */
    for (size_t i = 1; i < n; i++) {
        if (tombstones[i].start < min_ts) {
            min_ts = tombstones[i].start;
        }
    }

    *out_min = min_ts;
    *out_max = max_ts;
}

/*===========================================================================
 * Internal: Allocate and Copy Tombstones
 *===========================================================================*/

static tl_status_t create_tombstones(tl_alloc_ctx_t* alloc,
                                      const tl_interval_t* src, size_t n,
                                      tl_tombstones_t** out) {
    if (n == 0) {
        *out = NULL;
        return TL_OK;
    }

    tl_tombstones_t* ts = TL_NEW(alloc, tl_tombstones_t);
    if (ts == NULL) {
        return TL_ENOMEM;
    }

    ts->v = TL_NEW_ARRAY(alloc, tl_interval_t, n);
    if (ts->v == NULL) {
        TL_FREE(alloc, ts);
        return TL_ENOMEM;
    }

    memcpy(ts->v, src, n * sizeof(tl_interval_t));
    ts->n = (uint32_t)n;

    *out = ts;
    return TL_OK;
}

static void destroy_tombstones(tl_tombstones_t* ts, tl_alloc_ctx_t* alloc) {
    if (ts == NULL) {
        return;
    }
    if (ts->v != NULL) {
        TL_FREE(alloc, ts->v);
    }
    TL_FREE(alloc, ts);
}

/*===========================================================================
 * Internal: Destroy Segment (called when refcnt hits 0)
 *===========================================================================*/

static void segment_destroy(tl_segment_t* seg) {
    TL_ASSERT(seg != NULL);
    tl_alloc_ctx_t* alloc = seg->alloc;

    /* Destroy all pages */
    for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
        tl_page_t* page = seg->catalog.pages[i].page;
        tl_page_destroy(page, alloc);
    }

    /* Destroy catalog (frees metadata array, not pages) */
    tl_page_catalog_destroy(&seg->catalog);

    /* Destroy tombstones */
    destroy_tombstones(seg->tombstones, alloc);

    /* Free segment itself */
    TL_FREE(alloc, seg);
}

/*===========================================================================
 * Internal: Build Pages from Record Stream
 *
 * Partitions records into pages and populates the catalog.
 * On error, all pages already built are destroyed (rollback).
 *===========================================================================*/

static tl_status_t build_pages(tl_segment_t* seg,
                                const tl_record_t* records, size_t record_count,
                                size_t target_page_bytes) {
    tl_alloc_ctx_t* alloc = seg->alloc;
    tl_page_builder_t pb;
    tl_page_builder_init(&pb, alloc, target_page_bytes);

    size_t cap = pb.records_per_page;
    size_t n_pages = (record_count + cap - 1) / cap;

    /* Reserve catalog space */
    tl_status_t st = tl_page_catalog_reserve(&seg->catalog, n_pages);
    if (st != TL_OK) {
        return st;
    }

    /* Build pages */
    size_t offset = 0;
    while (offset < record_count) {
        size_t chunk = record_count - offset;
        if (chunk > cap) {
            chunk = cap;
        }

        tl_page_t* page = NULL;
        st = tl_page_builder_build(&pb, &records[offset], chunk, &page);
        if (st != TL_OK) {
            goto rollback;
        }

        st = tl_page_catalog_push(&seg->catalog, page);
        if (st != TL_OK) {
            tl_page_destroy(page, alloc);
            goto rollback;
        }

        offset += chunk;
    }

    return TL_OK;

rollback:
    /*
     * Destroy all pages built so far. They're stored in the catalog
     * which the caller will destroy, but the catalog doesn't own pages.
     */
    for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
        tl_page_destroy(seg->catalog.pages[i].page, alloc);
    }
    seg->catalog.n_pages = 0;
    return st;
}

/*===========================================================================
 * L0 Segment Builder
 *===========================================================================*/

tl_status_t tl_segment_build_l0(tl_alloc_ctx_t* alloc,
                                 const tl_record_t* records, size_t record_count,
                                 const tl_interval_t* tombstones, size_t tombstones_len,
                                 size_t target_page_bytes,
                                 uint32_t generation,
                                 tl_segment_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    /* Must have either records or tombstones */
    if (record_count == 0 && tombstones_len == 0) {
        return TL_EINVAL;
    }

    /* Check tombstones_len overflow */
    if (tombstones_len > UINT32_MAX) {
        return TL_EINVAL;
    }

    /* Allocate segment */
    tl_segment_t* seg = TL_NEW(alloc, tl_segment_t);
    if (seg == NULL) {
        return TL_ENOMEM;
    }

    seg->alloc = alloc;
    seg->level = TL_SEG_L0;
    seg->generation = generation;
    seg->window_start = 0;
    seg->window_end = 0;
    tl_atomic_init_u32(&seg->refcnt, 1);

    /* Initialize catalog */
    tl_page_catalog_init(&seg->catalog, alloc);

    /* Create tombstones (copies the array) */
    tl_status_t st = create_tombstones(alloc, tombstones, tombstones_len, &seg->tombstones);
    if (st != TL_OK) {
        /*
         * Cleanup: destroy catalog for consistency with build_pages error path.
         * Note: catalog.pages is NULL at this point (no reserve called yet),
         * so destroy is a no-op. However, calling it maintains consistent
         * cleanup patterns and is defensive against future changes.
         */
        tl_page_catalog_destroy(&seg->catalog);
        TL_FREE(alloc, seg);
        return st;
    }

    /* Build pages if we have records */
    if (record_count > 0) {
        TL_ASSERT(records != NULL);
        st = build_pages(seg, records, record_count, target_page_bytes);
        if (st != TL_OK) {
            destroy_tombstones(seg->tombstones, alloc);
            tl_page_catalog_destroy(&seg->catalog);
            TL_FREE(alloc, seg);
            return st;
        }
    }

    /* Set counts */
    seg->record_count = (uint64_t)record_count;
    seg->page_count = seg->catalog.n_pages;

    /*
     * Compute bounds.
     *
     * L0 segment bounds must cover BOTH records AND tombstones.
     * This is required for correct query planning and compaction selection.
     * A read in range [A, B) must consider any L0 segment whose bounds
     * overlap [A, B), and tombstones affect what data is visible.
     */
    if (record_count > 0 && tombstones_len > 0) {
        /* Both records and tombstones: union of bounds */
        tl_ts_t rec_min = seg->catalog.pages[0].min_ts;
        tl_ts_t rec_max = seg->catalog.pages[seg->catalog.n_pages - 1].max_ts;

        tl_ts_t tomb_min, tomb_max;
        compute_tombstone_bounds(tombstones, tombstones_len, &tomb_min, &tomb_max);

        seg->min_ts = TL_MIN(rec_min, tomb_min);
        seg->max_ts = TL_MAX(rec_max, tomb_max);
    } else if (record_count > 0) {
        /* Records only: bounds from pages */
        seg->min_ts = seg->catalog.pages[0].min_ts;
        seg->max_ts = seg->catalog.pages[seg->catalog.n_pages - 1].max_ts;
    } else {
        /* Tombstone-only: bounds from tombstones */
        TL_ASSERT(tombstones_len > 0);
        compute_tombstone_bounds(tombstones, tombstones_len, &seg->min_ts, &seg->max_ts);
    }

    *out = seg;
    return TL_OK;
}

/*===========================================================================
 * L1 Segment Builder
 *===========================================================================*/

tl_status_t tl_segment_build_l1(tl_alloc_ctx_t* alloc,
                                 const tl_record_t* records, size_t record_count,
                                 size_t target_page_bytes,
                                 tl_ts_t window_start, tl_ts_t window_end,
                                 uint32_t generation,
                                 tl_segment_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    /* L1 must have records */
    if (record_count == 0 || records == NULL) {
        return TL_EINVAL;
    }

    /* Allocate segment */
    tl_segment_t* seg = TL_NEW(alloc, tl_segment_t);
    if (seg == NULL) {
        return TL_ENOMEM;
    }

    seg->alloc = alloc;
    seg->level = TL_SEG_L1;
    seg->generation = generation;
    seg->window_start = window_start;
    seg->window_end = window_end;
    seg->tombstones = NULL;  /* L1 never has tombstones */
    tl_atomic_init_u32(&seg->refcnt, 1);

    /* Initialize catalog */
    tl_page_catalog_init(&seg->catalog, alloc);

    /* Build pages */
    tl_status_t st = build_pages(seg, records, record_count, target_page_bytes);
    if (st != TL_OK) {
        tl_page_catalog_destroy(&seg->catalog);
        TL_FREE(alloc, seg);
        return st;
    }

    /* Set counts */
    seg->record_count = (uint64_t)record_count;
    seg->page_count = seg->catalog.n_pages;

    /* Bounds from pages */
    seg->min_ts = seg->catalog.pages[0].min_ts;
    seg->max_ts = seg->catalog.pages[seg->catalog.n_pages - 1].max_ts;

    *out = seg;
    return TL_OK;
}

/*===========================================================================
 * Reference Counting
 *===========================================================================*/

tl_segment_t* tl_segment_acquire(tl_segment_t* seg) {
    if (seg == NULL) {
        return NULL;
    }
    /* Relaxed is sufficient for increment: we already have a reference */
    tl_atomic_fetch_add_u32(&seg->refcnt, 1, TL_MO_RELAXED);
    return seg;
}

void tl_segment_release(tl_segment_t* seg) {
    if (seg == NULL) {
        return;
    }

    /*
     * Release ordering ensures all prior writes to segment data are visible
     * to the thread that will destroy the segment.
     */
    uint32_t old = tl_atomic_fetch_sub_u32(&seg->refcnt, 1, TL_MO_RELEASE);
    TL_ASSERT(old >= 1);

    if (old == 1) {
        /*
         * We're the last owner. Acquire fence synchronizes with all prior
         * releasers to ensure we see all their writes before destruction.
         */
        tl_atomic_fence(TL_MO_ACQUIRE);
        segment_destroy(seg);
    }
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/* Include for tl_intervals_arr_validate */
#include "../internal/tl_intervals.h"

/**
 * Validate segment invariants.
 *
 * L0 Invariants:
 * 1. window_start == window_end == 0
 * 2. Tombstones allowed (validated via shared validator)
 * 3. Bounds COVER both page bounds AND tombstone bounds
 *
 * L1 Invariants:
 * 1. tombstones MUST be NULL (not just n==0)
 * 2. window_start < window_end OR window_end == TL_TS_MAX (unbounded)
 * 3. Records within window: min_ts >= window_start, max_ts < window_end
 *    (except for unbounded window_end == TL_TS_MAX)
 * 4. Bounds EQUAL page bounds (no tombstones to widen)
 *
 * Common Invariants:
 * 1. Valid level (L0 or L1)
 * 2. min_ts <= max_ts
 * 3. Page catalog validates
 * 4. Record count matches sum of page counts
 * 5. page_count == catalog.n_pages
 */
bool tl_segment_validate(const tl_segment_t* seg) {
    if (seg == NULL) {
        return false;
    }

    /* Common: Check level is valid */
    if (seg->level != TL_SEG_L0 && seg->level != TL_SEG_L1) {
        return false;
    }

    /*
     * CRITICAL: Validate page_count == catalog.n_pages BEFORE any indexing.
     *
     * If a segment is corrupted with page_count > 0 but catalog.n_pages == 0,
     * we must detect this before attempting to access catalog.pages[0].
     * Validation should return false, not crash.
     */
    if (seg->page_count != seg->catalog.n_pages) {
        return false;
    }

    /*=========================================================================
     * L0-Specific Validation
     *=========================================================================*/
    if (seg->level == TL_SEG_L0) {
        /* L0: window bounds must be 0 */
        if (seg->window_start != 0 || seg->window_end != 0) {
            return false;
        }

        /* L0: validate tombstones if present (using shared validator) */
        if (seg->tombstones != NULL && seg->tombstones->n > 0) {
            if (!tl_intervals_arr_validate(seg->tombstones->v, seg->tombstones->n)) {
                return false;
            }
        }

        /*
         * L0: Compute required coverage bounds from BOTH pages AND tombstones.
         *
         * The segment's min_ts/max_ts must COVER all content - i.e., they must
         * be <= the minimum and >= the maximum of all pages and tombstones.
         *
         * IMPORTANT: We use an explicit has_content flag rather than sentinel
         * checks like (required_min != TL_TS_MAX) because TL_TS_MAX is a valid
         * timestamp. A segment with a single record at TL_TS_MAX must still
         * have its bounds validated.
         */
        bool has_content = false;
        tl_ts_t required_min = TL_TS_MAX;
        tl_ts_t required_max = TL_TS_MIN;

        /* Page bounds contribute to required coverage */
        if (seg->catalog.n_pages > 0) {
            const tl_page_meta_t* first = &seg->catalog.pages[0];
            const tl_page_meta_t* last = &seg->catalog.pages[seg->catalog.n_pages - 1];
            required_min = first->min_ts;
            required_max = last->max_ts;
            has_content = true;
        }

        /* Tombstone bounds ALSO contribute to required coverage */
        if (seg->tombstones != NULL && seg->tombstones->n > 0) {
            /* Minimum: first tombstone's start (tombstones are sorted) */
            tl_ts_t tomb_min = seg->tombstones->v[0].start;
            if (!has_content || tomb_min < required_min) {
                required_min = tomb_min;
            }

            /* Maximum: last tombstone's end (or TL_TS_MAX if unbounded) */
            const tl_interval_t* last_tomb = &seg->tombstones->v[seg->tombstones->n - 1];
            tl_ts_t tomb_max;
            if (last_tomb->end_unbounded) {
                tomb_max = TL_TS_MAX;
            } else {
                /* end is exclusive, max is inclusive: max_ts = end - 1 */
                tomb_max = last_tomb->end - 1;
            }
            if (!has_content || tomb_max > required_max) {
                required_max = tomb_max;
            }
            has_content = true;
        }

        /* L0: segment bounds must COVER all content */
        if (has_content) {
            if (seg->min_ts > required_min) {
                return false;  /* Segment min doesn't cover content min */
            }
            if (seg->max_ts < required_max) {
                return false;  /* Segment max doesn't cover content max */
            }
        }

        /* L0 tombstone-only: must have tombstones if no pages/records */
        if (seg->catalog.n_pages == 0 && seg->record_count == 0) {
            if (seg->tombstones == NULL || seg->tombstones->n == 0) {
                return false;
            }
        }
    }

    /*=========================================================================
     * L1-Specific Validation
     *=========================================================================*/
    else if (seg->level == TL_SEG_L1) {
        /*
         * L1: tombstones MUST be NULL (not just n==0)
         *
         * This is a strict invariant. L1 segments have tombstones folded
         * during compaction - the pointer itself should be NULL.
         */
        if (seg->tombstones != NULL) {
            return false;
        }

        /* L1: must have records */
        if (seg->record_count == 0) {
            return false;
        }

        /*
         * L1: window bounds validation
         *
         * Normal case: window_start < window_end
         * Unbounded-end: window_end == TL_TS_MAX (covers all future timestamps)
         */
        if (seg->window_start >= seg->window_end) {
            /* Only valid if window_end is the unbounded sentinel */
            if (seg->window_end != TL_TS_MAX) {
                return false;
            }
        }

        /* L1: records within window and bounds must EQUAL page bounds */
        if (seg->catalog.n_pages > 0) {
            /* min_ts must be >= window_start */
            if (seg->min_ts < seg->window_start) {
                return false;
            }

            /*
             * For bounded windows (window_end != TL_TS_MAX):
             *   max_ts must be < window_end (half-open interval)
             * For unbounded windows (window_end == TL_TS_MAX):
             *   No upper bound check needed
             */
            if (seg->window_end != TL_TS_MAX) {
                if (seg->max_ts >= seg->window_end) {
                    return false;
                }
            }

            /* L1: bounds must EQUAL page bounds (no tombstones to widen) */
            const tl_page_meta_t* first = &seg->catalog.pages[0];
            const tl_page_meta_t* last = &seg->catalog.pages[seg->catalog.n_pages - 1];

            if (seg->min_ts != first->min_ts) {
                return false;
            }
            if (seg->max_ts != last->max_ts) {
                return false;
            }
        }
    }

    /*=========================================================================
     * Common Validation
     *=========================================================================*/

    /* Common: min_ts <= max_ts */
    if (seg->min_ts > seg->max_ts) {
        return false;
    }

    /* page_count == catalog.n_pages already validated at function entry */

    /* Common: record count matches sum of page counts */
    uint64_t computed_records = 0;
    for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
        computed_records += seg->catalog.pages[i].count;
    }
    if (seg->record_count != computed_records) {
        return false;
    }

    /* Common: page catalog validates */
    if (!tl_page_catalog_validate(&seg->catalog)) {
        return false;
    }

    return true;
}

#endif /* TL_DEBUG */
