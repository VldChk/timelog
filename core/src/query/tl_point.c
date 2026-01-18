#include "tl_point.h"
#include "tl_snapshot.h"
#include "../internal/tl_intervals.h"
#include "../storage/tl_manifest.h"
#include "../storage/tl_segment.h"
#include "../storage/tl_page.h"
#include "../delta/tl_memview.h"
#include "../delta/tl_memrun.h"
#include <string.h>

/*===========================================================================
 * Constants
 *===========================================================================*/

#define TL_POINT_INIT_CAP 8

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Ensure result has capacity for additional records.
 */
static tl_status_t ensure_capacity(tl_point_result_t* result, size_t additional) {
    size_t needed = result->count + additional;
    if (needed <= result->capacity) {
        return TL_OK;
    }

    size_t new_cap = (result->capacity == 0) ? TL_POINT_INIT_CAP : result->capacity;
    while (new_cap < needed) {
        /* Overflow guard */
        if (new_cap > SIZE_MAX / 2) {
            return TL_ENOMEM;
        }
        new_cap *= 2;
    }

    /* Overflow guard for allocation size */
    if (new_cap > SIZE_MAX / sizeof(tl_record_t)) {
        return TL_ENOMEM;
    }

    tl_record_t* new_arr = tl__malloc(result->alloc, new_cap * sizeof(tl_record_t));
    if (new_arr == NULL) {
        return TL_ENOMEM;
    }

    if (result->records != NULL) {
        memcpy(new_arr, result->records, result->count * sizeof(tl_record_t));
        tl__free(result->alloc, result->records);
    }

    result->records = new_arr;
    result->capacity = new_cap;
    return TL_OK;
}

/**
 * Add a record to the result.
 */
static tl_status_t add_record(tl_point_result_t* result, tl_ts_t ts, tl_handle_t handle) {
    tl_status_t st = ensure_capacity(result, 1);
    if (st != TL_OK) {
        return st;
    }

    result->records[result->count].ts = ts;
    result->records[result->count].handle = handle;
    result->count++;
    return TL_OK;
}

/**
 * Binary search for lower bound in a sorted record array.
 * Returns index of first record with ts >= target.
 */
static size_t records_lower_bound(const tl_record_t* data, size_t len, tl_ts_t target) {
    size_t lo = 0;
    size_t hi = len;

    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (data[mid].ts < target) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    return lo;
}

/**
 * Collect all records with exact timestamp from a sorted array.
 */
static tl_status_t collect_from_sorted(tl_point_result_t* result,
                                        const tl_record_t* data, size_t len,
                                        tl_ts_t ts) {
    if (len == 0 || data == NULL) {
        return TL_OK;
    }

    /* Binary search to find first occurrence */
    size_t idx = records_lower_bound(data, len, ts);

    /* Collect all matching records */
    while (idx < len && data[idx].ts == ts) {
        tl_status_t st = add_record(result, data[idx].ts, data[idx].handle);
        if (st != TL_OK) {
            return st;
        }
        idx++;
    }

    return TL_OK;
}

/**
 * Collect matching records from a page.
 */
static tl_status_t collect_from_page(tl_point_result_t* result,
                                      const tl_page_t* page,
                                      tl_ts_t ts) {
    /* Binary search to find first occurrence */
    size_t idx = tl_page_lower_bound(page, ts);

    /* Collect all matching records */
    tl_record_t rec;
    while (idx < page->count) {
        if (tl_page_row_is_deleted(page, idx)) {
            idx++;
            continue;
        }

        tl_page_get_record(page, idx, &rec);
        if (rec.ts != ts) {
            break;
        }
        tl_status_t st = add_record(result, rec.ts, rec.handle);
        if (st != TL_OK) {
            return st;
        }
        idx++;
    }

    return TL_OK;
}

/**
 * Collect matching records from a segment.
 */
static tl_status_t collect_from_segment(tl_point_result_t* result,
                                         const tl_segment_t* seg,
                                         tl_ts_t ts) {
    /* Check if segment contains ts */
    if (ts < seg->min_ts || ts > seg->max_ts) {
        return TL_OK;
    }

    /* Handle tombstone-only segments */
    if (seg->page_count == 0) {
        return TL_OK;
    }

    const tl_page_catalog_t* cat = tl_segment_catalog(seg);

    /* Binary search catalog to find pages that might contain ts */
    size_t page_idx = tl_page_catalog_find_first_ge(cat, ts);

    /* Search pages that could contain ts */
    while (page_idx < tl_page_catalog_count(cat)) {
        const tl_page_meta_t* meta = tl_page_catalog_get(cat, page_idx);

        /* Stop if page starts after ts */
        if (meta->min_ts > ts) {
            break;
        }

        /* Skip if page ends before ts (shouldn't happen after find_first_ge) */
        if (meta->max_ts < ts) {
            page_idx++;
            continue;
        }

        /* Skip fully deleted pages (bitmask test for future flag compatibility) */
        if ((meta->flags & TL_PAGE_FULLY_DELETED) != 0) {
            page_idx++;
            continue;
        }

        /* Collect from this page */
        tl_status_t st = collect_from_page(result, meta->page, ts);
        if (st != TL_OK) {
            return st;
        }

        page_idx++;
    }

    return TL_OK;
}

/**
 * Collect matching records from a memrun.
 */
static tl_status_t collect_from_memrun(tl_point_result_t* result,
                                        const tl_memrun_t* mr,
                                        tl_ts_t ts) {
    /* Check if memrun contains ts */
    if (!tl_memrun_has_records(mr)) {
        return TL_OK;
    }

    tl_ts_t min_ts = tl_memrun_min_ts(mr);
    tl_ts_t max_ts = tl_memrun_max_ts(mr);
    if (ts < min_ts || ts > max_ts) {
        return TL_OK;
    }

    tl_status_t st;

    /* Collect from run (sorted) */
    st = collect_from_sorted(result,
                             tl_memrun_run_data(mr),
                             tl_memrun_run_len(mr),
                             ts);
    if (st != TL_OK) {
        return st;
    }

    /* Collect from ooo (sorted) */
    st = collect_from_sorted(result,
                             tl_memrun_ooo_data(mr),
                             tl_memrun_ooo_len(mr),
                             ts);
    if (st != TL_OK) {
        return st;
    }

    return TL_OK;
}

/**
 * Collect matching records from memview active buffers.
 */
static tl_status_t collect_from_memview(tl_point_result_t* result,
                                         const tl_memview_t* mv,
                                         tl_ts_t ts) {
    tl_status_t st;

    /* Collect from active_run (sorted) */
    st = collect_from_sorted(result,
                             tl_memview_run_data(mv),
                             tl_memview_run_len(mv),
                             ts);
    if (st != TL_OK) {
        return st;
    }

    /* Collect from active_ooo (sorted) */
    st = collect_from_sorted(result,
                             tl_memview_ooo_data(mv),
                             tl_memview_ooo_len(mv),
                             ts);
    if (st != TL_OK) {
        return st;
    }

    return TL_OK;
}

/**
 * Check if ts is covered by any tombstone in the snapshot.
 */
static bool is_deleted(const tl_snapshot_t* snap, tl_ts_t ts) {
    const tl_manifest_t* manifest = snap->manifest;
    const tl_memview_t* mv = tl_snapshot_memview(snap);

    /* Check memview tombstones */
    tl_intervals_imm_t mv_tombs = tl_memview_tombs_imm(mv);
    if (tl_intervals_imm_contains(mv_tombs, ts)) {
        return true;
    }

    /* Check sealed memrun tombstones */
    for (size_t i = 0; i < tl_memview_sealed_len(mv); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(mv, i);
        tl_intervals_imm_t mr_tombs = tl_memrun_tombs_imm(mr);
        if (tl_intervals_imm_contains(mr_tombs, ts)) {
            return true;
        }
    }

    /* Check L0 segment tombstones */
    for (size_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);
        tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
        if (tl_intervals_imm_contains(seg_tombs, ts)) {
            return true;
        }
    }

    /* Defensive: check L1 tombstones if present (should be empty in V1). */
    for (size_t i = 0; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);
        tl_intervals_imm_t seg_tombs = tl_segment_tombstones_imm(seg);
        if (tl_intervals_imm_contains(seg_tombs, ts)) {
            return true;
        }
    }

    return false;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_point_lookup(tl_point_result_t* result,
                             const tl_snapshot_t* snap,
                             tl_ts_t ts,
                             tl_alloc_ctx_t* alloc) {
    TL_ASSERT(result != NULL);
    TL_ASSERT(snap != NULL);
    TL_ASSERT(alloc != NULL);

    /* Initialize result */
    memset(result, 0, sizeof(*result));
    result->alloc = alloc;

    /* Fast path: no data in snapshot */
    if (!snap->has_data) {
        return TL_OK;
    }

    /* Step 1: Tombstone check first (LLD Section 8) */
    if (is_deleted(snap, ts)) {
        return TL_OK;  /* Deleted - return empty result */
    }

    tl_status_t st;
    const tl_manifest_t* manifest = snap->manifest;
    const tl_memview_t* mv = tl_snapshot_memview(snap);

    /* Step 2: L1 lookup (non-overlapping windows) */
    size_t l1_start = tl_manifest_l1_find_first_overlap(manifest, ts);
    for (size_t i = l1_start; i < tl_manifest_l1_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l1_get(manifest, i);

        /* L1 segments are sorted, stop if past ts */
        if (seg->min_ts > ts) {
            break;
        }

        st = collect_from_segment(result, seg, ts);
        if (st != TL_OK) {
            goto fail;
        }
    }

    /* Step 3: L0 lookup (overlapping segments) */
    for (size_t i = 0; i < tl_manifest_l0_count(manifest); i++) {
        const tl_segment_t* seg = tl_manifest_l0_get(manifest, i);

        st = collect_from_segment(result, seg, ts);
        if (st != TL_OK) {
            goto fail;
        }
    }

    /* Step 4: Memview lookup */

    /* Sealed memruns */
    for (size_t i = 0; i < tl_memview_sealed_len(mv); i++) {
        const tl_memrun_t* mr = tl_memview_sealed_get(mv, i);

        st = collect_from_memrun(result, mr, ts);
        if (st != TL_OK) {
            goto fail;
        }
    }

    /* Active buffers */
    st = collect_from_memview(result, mv, ts);
    if (st != TL_OK) {
        goto fail;
    }

    return TL_OK;

fail:
    tl_point_result_destroy(result);
    return st;
}

void tl_point_result_destroy(tl_point_result_t* result) {
    if (result == NULL) {
        return;
    }

    if (result->records != NULL) {
        tl__free(result->alloc, result->records);
    }

    memset(result, 0, sizeof(*result));
}
