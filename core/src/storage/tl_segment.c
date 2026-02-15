#include "tl_segment.h"
#include "../internal/tl_refcount.h"
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
    TL_ASSERT(n > 0 && tombstones != NULL);

    /* Tombstones are canonicalized, so end > start >= TL_TS_MIN
     * and (end - 1) is always safe. */
    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;

    for (size_t i = 0; i < n; i++) {
        const tl_interval_t* t = &tombstones[i];

        if (t->start < min_ts) {
            min_ts = t->start;
        }

        if (t->end_unbounded) {
            max_ts = TL_TS_MAX;
        } else {
            TL_ASSERT(t->end > t->start && "Tombstone must be non-empty (canonicalized)");
            tl_ts_t end_inclusive = t->end - 1;
            if (end_inclusive > max_ts) {
                max_ts = end_inclusive;
            }
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

    for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
        tl_page_t* page = seg->catalog.pages[i].page;
        tl_page_destroy(page, alloc);
    }

    tl_page_catalog_destroy(&seg->catalog);

    if (seg->page_prefix_counts != NULL) {
        TL_FREE(alloc, seg->page_prefix_counts);
    }

    destroy_tombstones(seg->tombstones, alloc);
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
    /* Overflow-safe ceiling division */
    size_t n_pages = record_count / cap + (record_count % cap != 0 ? 1 : 0);

    tl_status_t st = tl_page_catalog_reserve(&seg->catalog, n_pages);
    if (st != TL_OK) {
        return st;
    }

    size_t offset = 0;
    while (offset < record_count) {
        size_t chunk = record_count - offset;
        if (chunk > cap) {
            chunk = cap;
        }

        /* Cross-page ordering check: last of previous page <= first of next */
        if (offset > 0) {
            if (records[offset - 1].ts > records[offset].ts) {
                st = TL_EINVAL;
                goto rollback;
            }
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
                                 tl_seq_t applied_seq,
                                 tl_segment_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    if (record_count == 0 && tombstones_len == 0) {
        return TL_EINVAL;
    }
    if (applied_seq == 0) {
        return TL_EINVAL;
    }

    if (tombstones_len > UINT32_MAX) {
        return TL_EINVAL;
    }

    /* NULL pointer with non-zero count is UB for memcpy */
    if (tombstones_len > 0 && tombstones == NULL) {
        return TL_EINVAL;
    }
    if (record_count > 0 && records == NULL) {
        return TL_EINVAL;
    }

    /* Validate tombstone intervals (release-mode safety) */
    for (size_t i = 0; i < tombstones_len; i++) {
        const tl_interval_t* cur = &tombstones[i];
        if (cur->max_seq == 0 || cur->max_seq > applied_seq) {
            return TL_EINVAL;
        }
        if (!cur->end_unbounded && cur->end <= cur->start) {
            return TL_EINVAL;
        }
        if (i > 0) {
            const tl_interval_t* prev = &tombstones[i - 1];
            if (cur->start < prev->start) {
                return TL_EINVAL;
            }
            if (prev->end_unbounded) {
                return TL_EINVAL;
            }
            if (!prev->end_unbounded && prev->end > cur->start) {
                return TL_EINVAL;
            }
            if (!prev->end_unbounded &&
                prev->end == cur->start &&
                prev->max_seq == cur->max_seq) {
                return TL_EINVAL;
            }
        }
        if (cur->end_unbounded && i + 1 < tombstones_len) {
            return TL_EINVAL;
        }
    }

    tl_segment_t* seg = TL_NEW(alloc, tl_segment_t);
    if (seg == NULL) {
        return TL_ENOMEM;
    }

    seg->alloc = alloc;
    seg->level = TL_SEG_L0;
    seg->generation = generation;
    seg->applied_seq = applied_seq;
    seg->window_start = 0;
    seg->window_end = 0;
    seg->window_end_unbounded = false;
    seg->record_min_ts = 0;
    seg->record_max_ts = 0;
    seg->tomb_min_ts = 0;
    seg->tomb_max_ts = 0;
    seg->page_prefix_counts = NULL;
    tl_atomic_init_u32(&seg->refcnt, 1);

    tl_page_catalog_init(&seg->catalog, alloc);

    tl_status_t st = create_tombstones(alloc, tombstones, tombstones_len, &seg->tombstones);
    if (st != TL_OK) {
        tl_page_catalog_destroy(&seg->catalog);
        TL_FREE(alloc, seg);
        return st;
    }

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

    seg->record_count = (uint64_t)record_count;
    seg->page_count = seg->catalog.n_pages;

    if (seg->page_count > 0) {
        size_t prefix_len = (size_t)seg->page_count + 1;
        seg->page_prefix_counts = TL_NEW_ARRAY(alloc, uint64_t, prefix_len);
        if (seg->page_prefix_counts == NULL) {
            destroy_tombstones(seg->tombstones, alloc);
            for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
                tl_page_destroy(seg->catalog.pages[i].page, alloc);
            }
            tl_page_catalog_destroy(&seg->catalog);
            TL_FREE(alloc, seg);
            return TL_ENOMEM;
        }
        seg->page_prefix_counts[0] = 0;
        for (uint32_t i = 0; i < seg->page_count; i++) {
            seg->page_prefix_counts[i + 1] =
                seg->page_prefix_counts[i] + seg->catalog.pages[i].count;
        }
    }

    /* L0 bounds must cover both records and tombstones for correct overlap checks */
    if (record_count > 0) {
        seg->record_min_ts = seg->catalog.pages[0].min_ts;
        seg->record_max_ts = seg->catalog.pages[seg->catalog.n_pages - 1].max_ts;
    }
    if (tombstones_len > 0) {
        compute_tombstone_bounds(tombstones, tombstones_len,
                                  &seg->tomb_min_ts, &seg->tomb_max_ts);
    }

    if (record_count > 0 && tombstones_len > 0) {
        seg->min_ts = TL_MIN(seg->record_min_ts, seg->tomb_min_ts);
        seg->max_ts = TL_MAX(seg->record_max_ts, seg->tomb_max_ts);
    } else if (record_count > 0) {
        seg->min_ts = seg->record_min_ts;
        seg->max_ts = seg->record_max_ts;
    } else {
        TL_ASSERT(tombstones_len > 0);
        seg->min_ts = seg->tomb_min_ts;
        seg->max_ts = seg->tomb_max_ts;
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
                                 bool window_end_unbounded,
                                 uint32_t generation,
                                 tl_seq_t applied_seq,
                                 tl_segment_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);
    *out = NULL;  /* Defensive initialization */

    /* Runtime check for L1 unbounded invariant.
     * TL_ASSERT becomes UB in release builds, so this defensive check
     * ensures callers cannot create invalid L1 segments.
     * Invariant: window_end_unbounded implies window_end == TL_TS_MAX */
    if (window_end_unbounded && window_end != TL_TS_MAX) {
        return TL_EINVAL;
    }

    if (applied_seq == 0) {
        return TL_EINVAL;
    }

    /* L1 must have records */
    if (record_count == 0 || records == NULL) {
        return TL_EINVAL;
    }

    tl_segment_t* seg = TL_NEW(alloc, tl_segment_t);
    if (seg == NULL) {
        return TL_ENOMEM;
    }

    seg->alloc = alloc;
    seg->level = TL_SEG_L1;
    seg->generation = generation;
    seg->applied_seq = applied_seq;
    seg->window_start = window_start;
    seg->window_end = window_end;
    seg->window_end_unbounded = window_end_unbounded;
    seg->tombstones = NULL;
    seg->record_min_ts = 0;
    seg->record_max_ts = 0;
    seg->tomb_min_ts = 0;
    seg->tomb_max_ts = 0;
    seg->page_prefix_counts = NULL;
    tl_atomic_init_u32(&seg->refcnt, 1);

    tl_page_catalog_init(&seg->catalog, alloc);

    tl_status_t st = build_pages(seg, records, record_count, target_page_bytes);
    if (st != TL_OK) {
        tl_page_catalog_destroy(&seg->catalog);
        TL_FREE(alloc, seg);
        return st;
    }

    seg->record_count = (uint64_t)record_count;
    seg->page_count = seg->catalog.n_pages;

    if (seg->page_count > 0) {
        size_t prefix_len = (size_t)seg->page_count + 1;
        seg->page_prefix_counts = TL_NEW_ARRAY(alloc, uint64_t, prefix_len);
        if (seg->page_prefix_counts == NULL) {
            for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
                tl_page_destroy(seg->catalog.pages[i].page, alloc);
            }
            tl_page_catalog_destroy(&seg->catalog);
            TL_FREE(alloc, seg);
            return TL_ENOMEM;
        }
        seg->page_prefix_counts[0] = 0;
        for (uint32_t i = 0; i < seg->page_count; i++) {
            seg->page_prefix_counts[i + 1] =
                seg->page_prefix_counts[i] + seg->catalog.pages[i].count;
        }
    }

    /* L1 has no tombstones, so bounds == page bounds */
    seg->record_min_ts = seg->catalog.pages[0].min_ts;
    seg->record_max_ts = seg->catalog.pages[seg->catalog.n_pages - 1].max_ts;
    seg->min_ts = seg->record_min_ts;
    seg->max_ts = seg->record_max_ts;

    /* Release-mode validation: records must be within window [start, end) */
    if (seg->min_ts < window_start ||
        (!window_end_unbounded && seg->max_ts >= window_end)) {
        segment_destroy(seg);
        return TL_EINVAL;
    }

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
     *
     * The atomic fetch_sub + post-assertion is correct and race-free.
     * Do NOT add a pre-check load (TOCTOU race). If old==0 after decrement,
     * this indicates a double-release bug which the assertion catches.
     */
    TL_REFCOUNT_RELEASE(&seg->refcnt,
                        segment_destroy(seg),
                        "segment double-release: refcnt was 0 before decrement");
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/* Include for tl_intervals_arr_validate */
#include "../internal/tl_intervals.h"

/** Validate segment invariants (level-specific + common checks). */
bool tl_segment_validate(const tl_segment_t* seg) {
    if (seg == NULL) {
        return false;
    }

    if (seg->level != TL_SEG_L0 && seg->level != TL_SEG_L1) {
        return false;
    }
    if (seg->applied_seq == 0) {
        return false;
    }

    /* Validate before indexing to avoid OOB on corrupted state */
    if (seg->page_count != seg->catalog.n_pages) {
        return false;
    }

    /*=========================================================================
     * L0-Specific Validation
     *=========================================================================*/
    if (seg->level == TL_SEG_L0) {
        if (seg->window_start != 0 || seg->window_end != 0) {
            return false;
        }

        if (seg->tombstones != NULL && seg->tombstones->n > 0) {
            if (!tl_intervals_arr_validate(seg->tombstones->v, seg->tombstones->n)) {
                return false;
            }
            for (uint32_t i = 0; i < seg->tombstones->n; i++) {
                if (seg->tombstones->v[i].max_seq > seg->applied_seq) {
                    return false;
                }
            }
        }

        /*
         * Verify bounds cover all content (pages + tombstones).
         * Use has_content flag since TL_TS_MAX is a valid timestamp.
         */
        bool has_content = false;
        tl_ts_t required_min = TL_TS_MAX;
        tl_ts_t required_max = TL_TS_MIN;

        if (seg->catalog.n_pages > 0) {
            const tl_page_meta_t* first = &seg->catalog.pages[0];
            const tl_page_meta_t* last = &seg->catalog.pages[seg->catalog.n_pages - 1];
            if (seg->record_min_ts != first->min_ts) {
                return false;
            }
            if (seg->record_max_ts != last->max_ts) {
                return false;
            }
            required_min = first->min_ts;
            required_max = last->max_ts;
            has_content = true;
        }

        if (seg->tombstones != NULL && seg->tombstones->n > 0) {
            tl_ts_t tomb_min_check, tomb_max_check;
            compute_tombstone_bounds(seg->tombstones->v, seg->tombstones->n,
                                     &tomb_min_check, &tomb_max_check);
            if (seg->tomb_min_ts != tomb_min_check) {
                return false;
            }
            if (seg->tomb_max_ts != tomb_max_check) {
                return false;
            }
            tl_ts_t tomb_min = seg->tombstones->v[0].start;
            if (!has_content || tomb_min < required_min) {
                required_min = tomb_min;
            }

            const tl_interval_t* last_tomb = &seg->tombstones->v[seg->tombstones->n - 1];
            tl_ts_t tomb_max;
            if (last_tomb->end_unbounded) {
                tomb_max = TL_TS_MAX;
            } else {
                tomb_max = last_tomb->end - 1;
            }
            if (!has_content || tomb_max > required_max) {
                required_max = tomb_max;
            }
            has_content = true;
        }

        if (has_content) {
            if (seg->min_ts > required_min) {
                return false;
            }
            if (seg->max_ts < required_max) {
                return false;
            }
        }

        /* Tombstone-only L0 must actually have tombstones */
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
        /* L1 tombstones folded at compaction; pointer must be NULL */
        if (seg->tombstones != NULL) {
            return false;
        }

        if (seg->record_count == 0) {
            return false;
        }

        if (seg->window_end_unbounded) {
            if (seg->window_end != TL_TS_MAX) {
                return false;
            }
        } else {
            if (seg->window_start >= seg->window_end) {
                return false;
            }
        }

        /* Records must be within window; bounds must equal page bounds */
        if (seg->catalog.n_pages > 0) {
            if (seg->min_ts < seg->window_start) {
                return false;
            }

            if (!seg->window_end_unbounded) {
                if (seg->max_ts >= seg->window_end) {
                    return false;
                }
            }

            const tl_page_meta_t* first = &seg->catalog.pages[0];
            const tl_page_meta_t* last = &seg->catalog.pages[seg->catalog.n_pages - 1];

            if (seg->record_min_ts != first->min_ts) {
                return false;
            }
            if (seg->record_max_ts != last->max_ts) {
                return false;
            }
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

    if (seg->min_ts > seg->max_ts) {
        return false;
    }

    uint64_t computed_records = 0;
    for (uint32_t i = 0; i < seg->catalog.n_pages; i++) {
        computed_records += seg->catalog.pages[i].count;
    }
    if (seg->record_count != computed_records) {
        return false;
    }

    if (!tl_page_catalog_validate(&seg->catalog)) {
        return false;
    }

    return true;
}

#endif /* TL_DEBUG */
