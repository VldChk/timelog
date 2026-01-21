/*
============================================================================

   COMBINED SOURCE FILE: delta.c

   Generated from: core/src/delta/
   Generated at:   2026-01-20 23:27:38

   This file combines all .c files from the delta/ subfolder.

   Files included:
 *   - tl_flush.c
 *   - tl_memrun.c
 *   - tl_memtable.c
 *   - tl_memview.c

============================================================================
*/


/******************************************************************************/
/*
/*   FILE: tl_flush.c
/*   FROM: delta/
/*
/******************************************************************************/
#include "tl_flush.h"

/*===========================================================================
 * Merge Iterator Implementation
 *===========================================================================*/

void tl_merge_iter_init(tl_merge_iter_t* it,
                         const tl_record_t* a, size_t a_len,
                         const tl_record_t* b, size_t b_len) {
    TL_ASSERT(it != NULL);

    it->a = a;
    it->a_len = a_len;
    it->a_pos = 0;

    it->b = b;
    it->b_len = b_len;
    it->b_pos = 0;
}

const tl_record_t* tl_merge_iter_next(tl_merge_iter_t* it) {
    TL_ASSERT(it != NULL);

    /* If 'a' is exhausted, take from 'b' */
    if (it->a_pos >= it->a_len) {
        if (it->b_pos >= it->b_len) {
            return NULL; /* Both exhausted */
        }
        return &it->b[it->b_pos++];
    }

    /* If 'b' is exhausted, take from 'a' */
    if (it->b_pos >= it->b_len) {
        return &it->a[it->a_pos++];
    }

    /*
     * Both have elements: compare timestamps.
     * Stable merge: prefer 'a' (run) on equal timestamps.
     * This preserves insertion order: in-order records before OOO records
     * with the same timestamp.
     */
    if (it->a[it->a_pos].ts <= it->b[it->b_pos].ts) {
        return &it->a[it->a_pos++];
    } else {
        return &it->b[it->b_pos++];
    }
}

/*===========================================================================
 * Flush Build Implementation
 *===========================================================================*/

tl_status_t tl_flush_build(const tl_flush_ctx_t* ctx,
                            const tl_memrun_t* mr,
                            tl_segment_t** out_seg) {
    TL_ASSERT(ctx != NULL);
    TL_ASSERT(ctx->alloc != NULL);
    TL_ASSERT(mr != NULL);
    TL_ASSERT(out_seg != NULL);

    *out_seg = NULL;

    /*
     * Step 1: Addition overflow check FIRST.
     * If run_len + ooo_len would overflow size_t, reject early.
     */
    if (mr->run_len > SIZE_MAX - mr->ooo_len) {
        return TL_EOVERFLOW;
    }

    size_t total_records = mr->run_len + mr->ooo_len;

    /*
     * Step 2: Handle tombstone-only case.
     * If no records but tombstones exist, build tombstone-only L0 segment.
     */
    if (total_records == 0) {
        if (mr->tombs_len > 0) {
            /* Tombstone-only segment */
            return tl_segment_build_l0(ctx->alloc,
                                        NULL, 0,
                                        mr->tombs, mr->tombs_len,
                                        ctx->target_page_bytes,
                                        ctx->generation,
                                        out_seg);
        } else {
            /* Empty memrun should never reach here (invariant violation) */
            return TL_EINVAL;
        }
    }

    /*
     * Step 3: Multiplication overflow check.
     * total_records * sizeof(tl_record_t) must not overflow.
     */
    if (total_records > SIZE_MAX / sizeof(tl_record_t)) {
        return TL_EOVERFLOW;
    }

    /*
     * Step 4: Allocate merged buffer.
     */
    size_t merged_size = total_records * sizeof(tl_record_t);
    tl_record_t* merged = tl__malloc(ctx->alloc, merged_size);
    if (merged == NULL) {
        return TL_ENOMEM;
    }

    /*
     * Step 5: Merge run + ooo into merged[] using two-way merge iterator.
     * The iterator produces records in sorted order (stable: prefers run on ties).
     */
    tl_merge_iter_t it;
    tl_merge_iter_init(&it, mr->run, mr->run_len, mr->ooo, mr->ooo_len);

    size_t i = 0;
    while (!tl_merge_iter_done(&it)) {
        const tl_record_t* rec = tl_merge_iter_next(&it);
        TL_ASSERT(rec != NULL); /* Should not be NULL if not done */
        merged[i++] = *rec;
    }

    TL_ASSERT(i == total_records);

    /*
     * Step 6: Build L0 segment from merged records and tombstones.
     */
    tl_status_t st = tl_segment_build_l0(ctx->alloc,
                                          merged, total_records,
                                          mr->tombs, mr->tombs_len,
                                          ctx->target_page_bytes,
                                          ctx->generation,
                                          out_seg);

    /*
     * Step 7: Free merged buffer regardless of build result.
     */
    tl__free(ctx->alloc, merged);

    return st;
}

/------------------------------------------------------------------------------/
/*   END OF: tl_flush.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memrun.c
/*   FROM: delta/
/*
/******************************************************************************/
#include "tl_memrun.h"

/*===========================================================================
 * Internal: Bounds Computation
 *
 * CRITICAL: Bounds MUST include tombstones, not just records.
 * This ensures tombstones outside record bounds are NOT pruned during
 * read-path overlap checks (which would cause missed deletes).
 *===========================================================================*/

static void compute_bounds(tl_memrun_t* mr) {
    /* Start with invalid bounds */
    tl_ts_t min_ts = TL_TS_MAX;
    tl_ts_t max_ts = TL_TS_MIN;

    /* Record bounds from run (sorted, so first/last are min/max) */
    if (mr->run_len > 0) {
        min_ts = TL_MIN(min_ts, mr->run[0].ts);
        max_ts = TL_MAX(max_ts, mr->run[mr->run_len - 1].ts);
    }

    /* Record bounds from ooo (sorted, so first/last are min/max) */
    if (mr->ooo_len > 0) {
        min_ts = TL_MIN(min_ts, mr->ooo[0].ts);
        max_ts = TL_MAX(max_ts, mr->ooo[mr->ooo_len - 1].ts);
    }

    /* Tombstone bounds (CRITICAL for read-path correctness) */
    for (size_t i = 0; i < mr->tombs_len; i++) {
        const tl_interval_t* tomb = &mr->tombs[i];
        min_ts = TL_MIN(min_ts, tomb->start);

        if (tomb->end_unbounded) {
            /* Unbounded tombstone [start, +inf) => max_ts = TL_TS_MAX */
            max_ts = TL_TS_MAX;
        } else {
            /* Bounded tombstone [start, end) => max covered ts is end-1 */
            max_ts = TL_MAX(max_ts, tomb->end - 1);
        }
    }

    mr->min_ts = min_ts;
    mr->max_ts = max_ts;
}

/*===========================================================================
 * Creation
 *===========================================================================*/

/**
 * Initialize a pre-allocated memrun in-place.
 *
 * Takes ownership of the provided arrays (run, ooo, tombs).
 * Caller must ensure at least one array is non-empty.
 * Sets refcnt to 1.
 */
static void memrun_init_inplace(tl_memrun_t* mr,
                                 tl_alloc_ctx_t* alloc,
                                 tl_record_t* run, size_t run_len,
                                 tl_record_t* ooo, size_t ooo_len,
                                 tl_interval_t* tombs, size_t tombs_len) {
    TL_ASSERT(mr != NULL);
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(run_len > 0 || ooo_len > 0 || tombs_len > 0);

    /* Null-check arrays when length is non-zero */
    TL_ASSERT(run_len == 0 || run != NULL);
    TL_ASSERT(ooo_len == 0 || ooo != NULL);
    TL_ASSERT(tombs_len == 0 || tombs != NULL);

    /* Take ownership of arrays */
    mr->run = run;
    mr->run_len = run_len;
    mr->ooo = ooo;
    mr->ooo_len = ooo_len;
    mr->tombs = tombs;
    mr->tombs_len = tombs_len;

    /* Store allocator */
    mr->alloc = alloc;

    /* Initialize reference count to 1 (caller owns) */
    tl_atomic_init_u32(&mr->refcnt, 1);

    /* Compute bounds (includes tombstones) */
    compute_bounds(mr);
}

tl_status_t tl_memrun_create(tl_alloc_ctx_t* alloc,
                              tl_record_t* run, size_t run_len,
                              tl_record_t* ooo, size_t ooo_len,
                              tl_interval_t* tombs, size_t tombs_len,
                              tl_memrun_t** out) {
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(out != NULL);

    *out = NULL;

    /* All empty is invalid */
    if (run_len == 0 && ooo_len == 0 && tombs_len == 0) {
        return TL_EINVAL;
    }

    /* Allocate memrun struct */
    tl_memrun_t* mr = TL_NEW(alloc, tl_memrun_t);
    if (mr == NULL) {
        /* Arrays NOT freed - caller retains ownership */
        return TL_ENOMEM;
    }

    /* Initialize in-place */
    memrun_init_inplace(mr, alloc, run, run_len, ooo, ooo_len, tombs, tombs_len);

    *out = mr;
    return TL_OK;
}

/*===========================================================================
 * Reference Counting
 *===========================================================================*/

tl_memrun_t* tl_memrun_acquire(tl_memrun_t* mr) {
    if (mr == NULL) {
        return NULL;
    }

    /* Relaxed: we already have a reference, so no ordering needed for increment */
    tl_atomic_fetch_add_u32(&mr->refcnt, 1, TL_MO_RELAXED);
    return mr;
}

void tl_memrun_release(tl_memrun_t* mr) {
    if (mr == NULL) {
        return;
    }

    /* Release ordering: ensure all prior writes are visible before potential destruction */
    uint32_t old = tl_atomic_fetch_sub_u32(&mr->refcnt, 1, TL_MO_RELEASE);

    if (old == 1) {
        /* Acquire fence: synchronize with all releasers before destruction */
        tl_atomic_fence(TL_MO_ACQUIRE);

        /* Free owned arrays */
        if (mr->run != NULL) {
            tl__free(mr->alloc, mr->run);
        }
        if (mr->ooo != NULL) {
            tl__free(mr->alloc, mr->ooo);
        }
        if (mr->tombs != NULL) {
            tl__free(mr->alloc, mr->tombs);
        }

        /* Free memrun struct */
        tl__free(mr->alloc, mr);
    }
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/**
 * Check if record array is sorted by timestamp (non-decreasing).
 */
static bool is_records_sorted(const tl_record_t* arr, size_t len) {
    if (len <= 1) {
        return true;
    }
    for (size_t i = 0; i < len - 1; i++) {
        if (arr[i].ts > arr[i + 1].ts) {
            return false;
        }
    }
    return true;
}

/**
 * Check if tombstone array is sorted, non-overlapping, and coalesced.
 */
static bool is_tombs_valid(const tl_interval_t* arr, size_t len) {
    if (len <= 1) {
        return true;
    }
    for (size_t i = 0; i < len - 1; i++) {
        const tl_interval_t* curr = &arr[i];
        const tl_interval_t* next = &arr[i + 1];

        /* Must be sorted by start */
        if (curr->start > next->start) {
            return false;
        }

        /* If current is unbounded, nothing should follow */
        if (curr->end_unbounded) {
            return false;
        }

        /* Must not overlap: curr->end <= next->start */
        if (curr->end > next->start) {
            return false;
        }

        /* Must not be adjacent (should be coalesced): curr->end < next->start */
        if (curr->end == next->start) {
            return false;
        }
    }
    return true;
}

bool tl_memrun_validate(const tl_memrun_t* mr) {
    if (mr == NULL) {
        return false;
    }

    /* Reference count must be positive */
    if (tl_memrun_refcnt(mr) == 0) {
        return false;
    }

    /* At least one component must be non-empty */
    if (mr->run_len == 0 && mr->ooo_len == 0 && mr->tombs_len == 0) {
        return false;
    }

    /* Check run sorted */
    if (!is_records_sorted(mr->run, mr->run_len)) {
        return false;
    }

    /* Check ooo sorted */
    if (!is_records_sorted(mr->ooo, mr->ooo_len)) {
        return false;
    }

    /* Check tombs valid */
    if (!is_tombs_valid(mr->tombs, mr->tombs_len)) {
        return false;
    }

    /* Verify min_ts */
    tl_ts_t expected_min = TL_TS_MAX;
    if (mr->run_len > 0) {
        expected_min = TL_MIN(expected_min, mr->run[0].ts);
    }
    if (mr->ooo_len > 0) {
        expected_min = TL_MIN(expected_min, mr->ooo[0].ts);
    }
    for (size_t i = 0; i < mr->tombs_len; i++) {
        expected_min = TL_MIN(expected_min, mr->tombs[i].start);
    }
    if (mr->min_ts != expected_min) {
        return false;
    }

    /* Verify max_ts */
    tl_ts_t expected_max = TL_TS_MIN;
    if (mr->run_len > 0) {
        expected_max = TL_MAX(expected_max, mr->run[mr->run_len - 1].ts);
    }
    if (mr->ooo_len > 0) {
        expected_max = TL_MAX(expected_max, mr->ooo[mr->ooo_len - 1].ts);
    }
    for (size_t i = 0; i < mr->tombs_len; i++) {
        const tl_interval_t* tomb = &mr->tombs[i];
        if (tomb->end_unbounded) {
            expected_max = TL_TS_MAX;
        } else {
            expected_max = TL_MAX(expected_max, tomb->end - 1);
        }
    }
    if (mr->max_ts != expected_max) {
        return false;
    }

    return true;
}

#endif /* TL_DEBUG */

/------------------------------------------------------------------------------/
/*   END OF: tl_memrun.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memtable.c
/*   FROM: delta/
/*
/******************************************************************************/
#include "tl_memtable.h"
#include "../internal/tl_locks.h"
#include <string.h>

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_memtable_init(tl_memtable_t* mt,
                              tl_alloc_ctx_t* alloc,
                              size_t memtable_max_bytes,
                              size_t ooo_budget_bytes,
                              size_t sealed_max_runs) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(alloc != NULL);
    TL_ASSERT(sealed_max_runs > 0);

    memset(mt, 0, sizeof(*mt));

    /* Store allocator */
    mt->alloc = alloc;

    /* Initialize active buffers */
    tl_recvec_init(&mt->active_run, alloc);
    tl_recvec_init(&mt->active_ooo, alloc);
    tl_intervals_init(&mt->active_tombs, alloc);

    /* Preallocate sealed queue (CRITICAL: no realloc on seal path) */
    mt->sealed = TL_NEW_ARRAY(alloc, tl_memrun_t*, sealed_max_runs);
    if (mt->sealed == NULL) {
        tl_recvec_destroy(&mt->active_run);
        tl_recvec_destroy(&mt->active_ooo);
        tl_intervals_destroy(&mt->active_tombs);
        return TL_ENOMEM;
    }
    mt->sealed_len = 0;
    mt->sealed_max_runs = sealed_max_runs;

    /* Store configuration */
    mt->memtable_max_bytes = memtable_max_bytes;
    mt->ooo_budget_bytes = ooo_budget_bytes;

    /* Initialize metadata */
    mt->last_inorder_ts = TL_TS_MIN;
    mt->active_bytes_est = 0;
    mt->epoch = 0;

    return TL_OK;
}

void tl_memtable_destroy(tl_memtable_t* mt) {
    if (mt == NULL) {
        return;
    }

    /* Release all sealed memruns */
    for (size_t i = 0; i < mt->sealed_len; i++) {
        if (mt->sealed[i] != NULL) {
            tl_memrun_release(mt->sealed[i]);
        }
    }

    /* Free sealed queue array */
    if (mt->sealed != NULL) {
        tl__free(mt->alloc, mt->sealed);
        mt->sealed = NULL;
    }
    mt->sealed_len = 0;

    /* Destroy active buffers */
    tl_recvec_destroy(&mt->active_run);
    tl_recvec_destroy(&mt->active_ooo);
    tl_intervals_destroy(&mt->active_tombs);
}

/*===========================================================================
 * Insert Operations
 *===========================================================================*/

tl_status_t tl_memtable_insert(tl_memtable_t* mt, tl_ts_t ts, tl_handle_t handle) {
    TL_ASSERT(mt != NULL);

    tl_status_t st;

    /* Route to appropriate buffer based on timestamp ordering */
    if (tl_recvec_len(&mt->active_run) == 0) {
        /* First record: goes to run */
        st = tl_recvec_push(&mt->active_run, ts, handle);
        if (st != TL_OK) {
            return st;
        }
        mt->last_inorder_ts = ts;
    } else if (ts >= mt->last_inorder_ts) {
        /* In-order: fast path to run */
        st = tl_recvec_push(&mt->active_run, ts, handle);
        if (st != TL_OK) {
            return st;
        }
        mt->last_inorder_ts = ts;
    } else {
        /* Out-of-order: sorted insert to ooo */
        size_t idx = tl_recvec_lower_bound(&mt->active_ooo, ts);
        st = tl_recvec_insert(&mt->active_ooo, idx, ts, handle);
        if (st != TL_OK) {
            return st;
        }
    }

    /* Update metadata AFTER successful insert */
    mt->epoch++;
    mt->active_bytes_est += TL_RECORD_SIZE;

    return TL_OK;
}

/**
 * Check if entire batch is sorted (non-decreasing by timestamp).
 * Returns true if batch is sorted, false otherwise.
 * FULL CHECK, NO SAMPLING - sampling could miss unsorted sections.
 */
static bool batch_is_sorted(const tl_record_t* records, size_t n) {
    if (n <= 1) {
        return true;
    }
    for (size_t i = 0; i < n - 1; i++) {
        if (records[i].ts > records[i + 1].ts) {
            return false;
        }
    }
    return true;
}

tl_status_t tl_memtable_insert_batch(tl_memtable_t* mt,
                                      const tl_record_t* records, size_t n,
                                      uint32_t flags) {
    TL_ASSERT(mt != NULL);
    (void)flags; /* Hint only - we verify sortedness regardless */

    if (n == 0) {
        return TL_OK;
    }

    TL_ASSERT(records != NULL);

    tl_status_t st;
    size_t inserted = 0;

    /* Determine if we can use fast path (bulk append to run) */
    bool use_fast_path = false;
    bool first_fits = (tl_recvec_len(&mt->active_run) == 0) ||
                      (records[0].ts >= mt->last_inorder_ts);

    if (first_fits) {
        /* Verify batch is sorted: FULL CHECK, NO SAMPLING */
        if (batch_is_sorted(records, n)) {
            use_fast_path = true;
        }
    }

    if (use_fast_path) {
        /* Fast path: bulk append to active_run */
        size_t len = tl_recvec_len(&mt->active_run);

        /* Check for addition overflow before computing new capacity */
        if (n > SIZE_MAX - len) {
            return TL_EOVERFLOW;
        }

        /* Pre-reserve to make this all-or-nothing (no partial state on failure) */
        size_t new_cap = len + n;
        st = tl_recvec_reserve(&mt->active_run, new_cap);
        if (st != TL_OK) {
            /* No records inserted, clean failure */
            return st;
        }

        /* Copy all records (cannot fail after reserve).
         *
         * ATOMICITY: push_n is a memcpy-based operation that cannot partially
         * fail after successful reserve. If it returns error (shouldn't happen),
         * no records were inserted (memcpy is all-or-nothing). Therefore we
         * return without updating metadata - this maintains consistency.
         *
         * If push_n ever changed to allow partial writes, this would need
         * to handle partial metadata updates like the slow path does. */
        st = tl_recvec_push_n(&mt->active_run, records, n);
        if (st != TL_OK) {
            /* Reserve succeeded but push_n failed - should never happen.
             * No records were inserted, return without metadata update. */
            return st;
        }

        mt->last_inorder_ts = records[n - 1].ts;
        inserted = n;
    } else {
        /* Slow path: per-record insert */
        for (size_t i = 0; i < n; i++) {
            tl_ts_t ts = records[i].ts;
            tl_handle_t handle = records[i].handle;

            if (tl_recvec_len(&mt->active_run) == 0 || ts >= mt->last_inorder_ts) {
                st = tl_recvec_push(&mt->active_run, ts, handle);
                if (st != TL_OK) {
                    /* Partial failure: update metadata for what we inserted */
                    if (inserted > 0) {
                        mt->epoch++;
                        mt->active_bytes_est += inserted * TL_RECORD_SIZE;
                    }
                    return st;
                }
                mt->last_inorder_ts = ts;
            } else {
                size_t idx = tl_recvec_lower_bound(&mt->active_ooo, ts);
                st = tl_recvec_insert(&mt->active_ooo, idx, ts, handle);
                if (st != TL_OK) {
                    /* Partial failure: update metadata for what we inserted */
                    if (inserted > 0) {
                        mt->epoch++;
                        mt->active_bytes_est += inserted * TL_RECORD_SIZE;
                    }
                    return st;
                }
            }
            inserted++;
        }
    }

    /* Update metadata ONCE at end (all records inserted successfully) */
    mt->epoch++;
    mt->active_bytes_est += inserted * TL_RECORD_SIZE;

    return TL_OK;
}

tl_status_t tl_memtable_insert_tombstone(tl_memtable_t* mt, tl_ts_t t1, tl_ts_t t2) {
    TL_ASSERT(mt != NULL);

    /* Delegate to tl_intervals which handles validation and coalescing */
    tl_status_t st = tl_intervals_insert(&mt->active_tombs, t1, t2);

    if (st == TL_OK && t1 < t2) {
        /* Only update metadata if actual insert happened (not empty interval) */
        mt->epoch++;
        mt->active_bytes_est += sizeof(tl_interval_t);
    }

    return st;
}

tl_status_t tl_memtable_insert_tombstone_unbounded(tl_memtable_t* mt, tl_ts_t t1) {
    TL_ASSERT(mt != NULL);

    tl_status_t st = tl_intervals_insert_unbounded(&mt->active_tombs, t1);

    if (st == TL_OK) {
        mt->epoch++;
        mt->active_bytes_est += sizeof(tl_interval_t);
    }

    return st;
}

/*===========================================================================
 * Seal Operations
 *===========================================================================*/

bool tl_memtable_should_seal(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);

    /* Check total active bytes */
    if (mt->active_bytes_est >= mt->memtable_max_bytes) {
        return true;
    }

    /* Check OOO bytes specifically (skip if budget is 0 = unlimited) */
    if (mt->ooo_budget_bytes > 0) {
        size_t ooo_bytes = tl_recvec_len(&mt->active_ooo) * TL_RECORD_SIZE;
        if (ooo_bytes >= mt->ooo_budget_bytes) {
            return true;
        }
    }

    return false;
}

bool tl_memtable_ooo_budget_exceeded(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);

    if (mt->ooo_budget_bytes == 0) {
        return false;  /* Unlimited budget */
    }

    size_t ooo_bytes = tl_recvec_len(&mt->active_ooo) * TL_RECORD_SIZE;
    return ooo_bytes >= mt->ooo_budget_bytes;
}

bool tl_memtable_is_active_empty(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);
    return tl_recvec_is_empty(&mt->active_run) &&
           tl_recvec_is_empty(&mt->active_ooo) &&
           tl_intervals_is_empty(&mt->active_tombs);
}

tl_status_t tl_memtable_seal(tl_memtable_t* mt, tl_mutex_t* mu, tl_cond_t* cond) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(mu != NULL);

    /* Step 1: Check if anything to seal (no lock needed - under writer_mu) */
    if (tl_memtable_is_active_empty(mt)) {
        return TL_OK; /* Nothing to seal */
    }

    /* Step 2: Check queue capacity FIRST (under memtable_mu) */
    TL_LOCK(mu, TL_LOCK_MEMTABLE_MU);
    if (mt->sealed_len >= mt->sealed_max_runs) {
        TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);
        return TL_EBUSY; /* Active state PRESERVED */
    }
    TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);

    /*
     * Step 3: Take ownership of active arrays FIRST.
     * We do this before allocating memrun so that if tl_memrun_create
     * fails, we can restore the arrays to the memtable.
     * However, tl_recvec_take and tl_intervals_take reset the vectors,
     * so we need to be careful about rollback.
     *
     * DESIGN: The plan says "check capacity, allocate memrun, then take".
     * But tl_memrun_create handles allocation internally. We must
     * try tl_memrun_create first (which allocates internally), and if
     * it fails due to TL_ENOMEM, we've already detached the arrays.
     *
     * SOLUTION: Take arrays, try create. If create fails:
     * - For TL_EINVAL: shouldn't happen (checked non-empty above)
     * - For TL_ENOMEM: arrays were taken but memrun alloc failed.
     *   We must restore them. But tl_recvec has no "restore" API.
     *
     * REVISED SOLUTION: We know we're non-empty. Take the arrays,
     * and tl_memrun_create will succeed unless OOM. On OOM, we lose
     * the arrays (they're freed in cleanup). This violates "preserve
     * active state on ENOMEM".
     *
     * CORRECT SOLUTION: Attempt a dummy allocation first to test if
     * memory is available, OR accept that on OOM during seal, data
     * may be lost. The plan says "active preserved on ENOMEM".
     *
     * IMPLEMENTATION: Pre-allocate the memrun struct (just the struct,
     * not with tl_memrun_create). Then take arrays, initialize manually,
     * compute bounds. This matches the plan exactly.
     */

    /* Step 3: Pre-allocate memrun struct BEFORE detaching arrays */
    tl_memrun_t* mr = TL_NEW(mt->alloc, tl_memrun_t);
    if (mr == NULL) {
        return TL_ENOMEM; /* Active state PRESERVED */
    }

    /* Step 4: Take ownership of active arrays (cannot fail after alloc) */
    size_t run_len = 0;
    size_t ooo_len = 0;
    size_t tombs_len = 0;

    tl_record_t* run = tl_recvec_take(&mt->active_run, &run_len);
    tl_record_t* ooo = tl_recvec_take(&mt->active_ooo, &ooo_len);
    tl_interval_t* tombs = tl_intervals_take(&mt->active_tombs, &tombs_len);

    /* Step 5: Initialize memrun manually (not using tl_memrun_create) */
    mr->run = run;
    mr->run_len = run_len;
    mr->ooo = ooo;
    mr->ooo_len = ooo_len;
    mr->tombs = tombs;
    mr->tombs_len = tombs_len;
    mr->alloc = mt->alloc;
    tl_atomic_init_u32(&mr->refcnt, 1); /* Queue owns one reference */

    /* Compute bounds (MUST include tombstones) */
    /* Inline bounds computation to avoid depending on tl_memrun_create */
    {
        tl_ts_t min_ts = TL_TS_MAX;
        tl_ts_t max_ts = TL_TS_MIN;

        if (mr->run_len > 0) {
            min_ts = TL_MIN(min_ts, mr->run[0].ts);
            max_ts = TL_MAX(max_ts, mr->run[mr->run_len - 1].ts);
        }
        if (mr->ooo_len > 0) {
            min_ts = TL_MIN(min_ts, mr->ooo[0].ts);
            max_ts = TL_MAX(max_ts, mr->ooo[mr->ooo_len - 1].ts);
        }
        for (size_t i = 0; i < mr->tombs_len; i++) {
            const tl_interval_t* tomb = &mr->tombs[i];
            min_ts = TL_MIN(min_ts, tomb->start);
            if (tomb->end_unbounded) {
                max_ts = TL_TS_MAX;
            } else {
                max_ts = TL_MAX(max_ts, tomb->end - 1);
            }
        }
        mr->min_ts = min_ts;
        mr->max_ts = max_ts;
    }

    /* Step 6: Push to sealed queue (under memtable_mu) */
    TL_LOCK(mu, TL_LOCK_MEMTABLE_MU);
    /* Re-check capacity (defensive - single writer, but be safe) */
    TL_ASSERT(mt->sealed_len < mt->sealed_max_runs);
    mt->sealed[mt->sealed_len++] = mr;
    TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);

    /* Step 7: Reset active metadata AFTER successful enqueue */
    mt->last_inorder_ts = TL_TS_MIN;
    mt->active_bytes_est = 0;
    mt->epoch++;  /* Memtable state changed (active -> sealed) */

    /* Signal waiters if provided */
    if (cond != NULL) {
        tl_cond_signal(cond);
    }

    return TL_OK;
}

/*===========================================================================
 * Sealed Queue Operations
 *===========================================================================*/

bool tl_memtable_has_sealed(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);
    return mt->sealed_len > 0;
}

bool tl_memtable_is_sealed_full(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);
    return mt->sealed_len >= mt->sealed_max_runs;
}

tl_status_t tl_memtable_peek_oldest(tl_memtable_t* mt, tl_memrun_t** out) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(out != NULL);

    if (mt->sealed_len == 0) {
        *out = NULL;
        return TL_OK;
    }

    /* Peek oldest (FIFO: index 0) and acquire reference */
    tl_memrun_t* mr = mt->sealed[0];
    *out = tl_memrun_acquire(mr);
    return TL_OK;
}

void tl_memtable_pop_oldest(tl_memtable_t* mt, tl_cond_t* cond) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(mt->sealed_len > 0);

    /* Get oldest (FIFO: index 0) */
    tl_memrun_t* mr = mt->sealed[0];

    /* Shift remaining elements down */
    if (mt->sealed_len > 1) {
        memmove(&mt->sealed[0], &mt->sealed[1],
                (mt->sealed_len - 1) * sizeof(tl_memrun_t*));
    }
    mt->sealed_len--;

    /* Release queue's reference */
    tl_memrun_release(mr);

    /* Sealed queue changed (flush removed a memrun) */
    mt->epoch++;

    /* Signal waiters (backpressure) */
    if (cond != NULL) {
        tl_cond_signal(cond);
    }
}

size_t tl_memtable_sealed_len(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);
    return mt->sealed_len;
}

/*===========================================================================
 * Backpressure
 *===========================================================================*/

bool tl_memtable_wait_for_space(tl_memtable_t* mt, tl_mutex_t* mu,
                                 tl_cond_t* cond, uint32_t timeout_ms) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(mu != NULL);
    TL_ASSERT(cond != NULL);

    /*
     * Loop to handle spurious wakeups properly.
     * memtable_cond is dedicated to sealed queue space signaling.
     * Use monotonic time to track actual elapsed time across wakeups.
     */
    uint64_t start_ms = tl_monotonic_ms();
    uint64_t deadline_ms = start_ms + timeout_ms;

    while (mt->sealed_len >= mt->sealed_max_runs) {
        uint64_t now_ms = tl_monotonic_ms();

        /* Check if deadline passed (handles wraparound via unsigned math) */
        if (now_ms >= deadline_ms) {
            /* Timeout expired */
            break;
        }

        /* Compute remaining time (safe: now_ms < deadline_ms) */
        uint64_t remaining = deadline_ms - now_ms;
        uint32_t wait_ms = (remaining > UINT32_MAX) ? UINT32_MAX : (uint32_t)remaining;

        /* Wait with remaining timeout */
        bool signaled = tl_cond_timedwait(cond, mu, wait_ms);
        if (!signaled) {
            /* Timed out - but re-check condition before returning */
            break;
        }

        /* Signaled (possibly spuriously) - loop will re-check condition */
    }

    return (mt->sealed_len < mt->sealed_max_runs);
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/**
 * Check if record array is sorted.
 */
static bool debug_records_sorted(const tl_record_t* arr, size_t len) {
    if (len <= 1) return true;
    for (size_t i = 0; i < len - 1; i++) {
        if (arr[i].ts > arr[i + 1].ts) return false;
    }
    return true;
}

bool tl_memtable_validate(const tl_memtable_t* mt) {
    if (mt == NULL) {
        return false;
    }

    /* Check active_run is sorted */
    if (!debug_records_sorted(tl_recvec_data(&mt->active_run),
                              tl_recvec_len(&mt->active_run))) {
        return false;
    }

    /* Check active_ooo is sorted */
    if (!debug_records_sorted(tl_recvec_data(&mt->active_ooo),
                              tl_recvec_len(&mt->active_ooo))) {
        return false;
    }

    /* Check active_tombs is valid */
    if (!tl_intervals_validate(&mt->active_tombs)) {
        return false;
    }

    /* Check sealed queue bounds */
    if (mt->sealed_len > mt->sealed_max_runs) {
        return false;
    }

    /* Check sealed entries are non-NULL */
    for (size_t i = 0; i < mt->sealed_len; i++) {
        if (mt->sealed[i] == NULL) {
            return false;
        }
    }

    return true;
}

#endif /* TL_DEBUG */

/------------------------------------------------------------------------------/
/*   END OF: tl_memtable.c
/------------------------------------------------------------------------------/

/******************************************************************************/
/*
/*   FILE: tl_memview.c
/*   FROM: delta/
/*
/******************************************************************************/
#include "tl_memview.h"
#include "../internal/tl_range.h"
#include "../internal/tl_locks.h"
#include <string.h>

/*===========================================================================
 * Internal Helpers
 *===========================================================================*/

/**
 * Update bounds with a record array.
 * Assumes records are sorted by timestamp.
 */
static void update_bounds_from_records(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                        bool* has_data,
                                        const tl_record_t* data, size_t len) {
    if (len == 0) {
        return;
    }

    tl_ts_t rec_min = data[0].ts;
    tl_ts_t rec_max = data[len - 1].ts;

    if (!*has_data) {
        *min_ts = rec_min;
        *max_ts = rec_max;
        *has_data = true;
    } else {
        if (rec_min < *min_ts) *min_ts = rec_min;
        if (rec_max > *max_ts) *max_ts = rec_max;
    }
}

/**
 * Update bounds with tombstone intervals.
 * Tombstones contribute to bounds per read-path overlap rules.
 */
static void update_bounds_from_tombs(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                      bool* has_data,
                                      const tl_interval_t* data, size_t len) {
    if (len == 0) {
        return;
    }

    /* Min is first interval's start (intervals are sorted by start) */
    tl_ts_t tomb_min = data[0].start;

    /* Max is determined by last interval's end (or TL_TS_MAX if unbounded) */
    const tl_interval_t* last = &data[len - 1];
    tl_ts_t tomb_max;
    if (last->end_unbounded) {
        tomb_max = TL_TS_MAX;
    } else {
        /*
         * Tombstone [start, end) covers timestamps up to end-1.
         * For overlap checking, we use end-1 as the max bound.
         * However, we must be careful: if end == TL_TS_MIN (impossible
         * for a valid interval), subtracting would underflow.
         * Valid intervals have start < end, so end > TL_TS_MIN.
         */
        tomb_max = last->end - 1;
    }

    if (!*has_data) {
        *min_ts = tomb_min;
        *max_ts = tomb_max;
        *has_data = true;
    } else {
        if (tomb_min < *min_ts) *min_ts = tomb_min;
        if (tomb_max > *max_ts) *max_ts = tomb_max;
    }
}

/**
 * Update bounds from a memrun.
 */
static void update_bounds_from_memrun(tl_ts_t* min_ts, tl_ts_t* max_ts,
                                       bool* has_data,
                                       const tl_memrun_t* mr) {
    /*
     * Memrun has precomputed bounds that already include tombstones.
     * However, we need to check if it has data first.
     */
    bool mr_has_records = tl_memrun_has_records(mr);
    bool mr_has_tombs = tl_memrun_has_tombstones(mr);

    if (!mr_has_records && !mr_has_tombs) {
        return;
    }

    tl_ts_t mr_min = tl_memrun_min_ts(mr);
    tl_ts_t mr_max = tl_memrun_max_ts(mr);

    if (!*has_data) {
        *min_ts = mr_min;
        *max_ts = mr_max;
        *has_data = true;
    } else {
        if (mr_min < *min_ts) *min_ts = mr_min;
        if (mr_max > *max_ts) *max_ts = mr_max;
    }
}

/**
 * Deep-copy a record array.
 * Returns NULL on allocation failure or if len == 0.
 */
static tl_record_t* copy_records(tl_alloc_ctx_t* alloc,
                                  const tl_record_t* src, size_t len) {
    if (len == 0 || src == NULL) {
        return NULL;
    }

    size_t bytes = len * sizeof(tl_record_t);
    tl_record_t* dst = tl__malloc(alloc, bytes);
    if (dst == NULL) {
        return NULL;
    }

    memcpy(dst, src, bytes);
    return dst;
}

/**
 * Deep-copy an interval array.
 * Returns NULL on allocation failure or if len == 0.
 */
static tl_interval_t* copy_intervals(tl_alloc_ctx_t* alloc,
                                      const tl_interval_t* src, size_t len) {
    if (len == 0 || src == NULL) {
        return NULL;
    }

    size_t bytes = len * sizeof(tl_interval_t);
    tl_interval_t* dst = tl__malloc(alloc, bytes);
    if (dst == NULL) {
        return NULL;
    }

    memcpy(dst, src, bytes);
    return dst;
}

/**
 * Allocate and populate sealed memrun array.
 * Acquires references to each memrun.
 * On failure, releases any already-acquired references.
 */
static tl_status_t copy_sealed_memruns(tl_memview_t* mv,
                                        tl_memtable_t* mt,
                                        tl_mutex_t* memtable_mu) {
    /*
     * Lock memtable_mu to safely access the sealed queue.
     * We need to:
     * 1. Read sealed_len
     * 2. Allocate array
     * 3. Acquire each memrun
     * All under the lock to ensure the queue doesn't change.
     *
     * Use TL_LOCK for debug-mode lock ordering validation.
     */
    TL_LOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);

    size_t len = mt->sealed_len;
    if (len == 0) {
        mv->sealed = NULL;
        mv->sealed_len = 0;
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        return TL_OK;
    }

    /* Allocate array */
    mv->sealed = tl__malloc(mv->alloc, len * sizeof(tl_memrun_t*));
    if (mv->sealed == NULL) {
        TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
        return TL_ENOMEM;
    }

    /* Copy pointers and acquire each memrun */
    for (size_t i = 0; i < len; i++) {
        mv->sealed[i] = tl_memrun_acquire(mt->sealed[i]);
    }
    mv->sealed_len = len;

    TL_UNLOCK(memtable_mu, TL_LOCK_MEMTABLE_MU);
    return TL_OK;
}

/*===========================================================================
 * Lifecycle
 *===========================================================================*/

tl_status_t tl_memview_capture(tl_memview_t* mv,
                                tl_memtable_t* mt,
                                tl_mutex_t* memtable_mu,
                                tl_alloc_ctx_t* alloc) {
    TL_ASSERT(mv != NULL);
    TL_ASSERT(mt != NULL);
    TL_ASSERT(memtable_mu != NULL);
    TL_ASSERT(alloc != NULL);

    /* Initialize to empty state */
    memset(mv, 0, sizeof(*mv));
    mv->alloc = alloc;
    mv->has_data = false;

    tl_status_t status;

    /*
     * Step 1: Copy active buffers.
     * Caller holds writer_mu which protects active state.
     */

    /* Copy active_run */
    size_t run_len = tl_memtable_run_len(mt);
    if (run_len > 0) {
        mv->active_run = copy_records(alloc, tl_memtable_run_data(mt), run_len);
        if (mv->active_run == NULL) {
            status = TL_ENOMEM;
            goto fail;
        }
        mv->active_run_len = run_len;
    }

    /* Copy active_ooo */
    size_t ooo_len = tl_memtable_ooo_len(mt);
    if (ooo_len > 0) {
        mv->active_ooo = copy_records(alloc, tl_memtable_ooo_data(mt), ooo_len);
        if (mv->active_ooo == NULL) {
            status = TL_ENOMEM;
            goto fail;
        }
        mv->active_ooo_len = ooo_len;
    }

    /* Copy active_tombs */
    tl_intervals_imm_t tombs_imm = tl_memtable_tombs_imm(mt);
    if (tombs_imm.len > 0) {
        mv->active_tombs = copy_intervals(alloc, tombs_imm.data, tombs_imm.len);
        if (mv->active_tombs == NULL) {
            status = TL_ENOMEM;
            goto fail;
        }
        mv->active_tombs_len = tombs_imm.len;
    }

    /*
     * Step 2: Pin sealed memruns.
     * This function locks memtable_mu internally.
     */
    status = copy_sealed_memruns(mv, mt, memtable_mu);
    if (status != TL_OK) {
        goto fail;
    }

    /*
     * Step 3: Compute bounds.
     * Include records AND tombstones per read-path overlap rules.
     */
    update_bounds_from_records(&mv->min_ts, &mv->max_ts, &mv->has_data,
                               mv->active_run, mv->active_run_len);
    update_bounds_from_records(&mv->min_ts, &mv->max_ts, &mv->has_data,
                               mv->active_ooo, mv->active_ooo_len);
    update_bounds_from_tombs(&mv->min_ts, &mv->max_ts, &mv->has_data,
                             mv->active_tombs, mv->active_tombs_len);

    for (size_t i = 0; i < mv->sealed_len; i++) {
        update_bounds_from_memrun(&mv->min_ts, &mv->max_ts, &mv->has_data,
                                  mv->sealed[i]);
    }

    return TL_OK;

fail:
    tl_memview_destroy(mv);
    return status;
}

void tl_memview_destroy(tl_memview_t* mv) {
    if (mv == NULL) {
        return;
    }

    /* Free copied active buffers */
    if (mv->active_run != NULL) {
        tl__free(mv->alloc, mv->active_run);
        mv->active_run = NULL;
    }
    mv->active_run_len = 0;

    if (mv->active_ooo != NULL) {
        tl__free(mv->alloc, mv->active_ooo);
        mv->active_ooo = NULL;
    }
    mv->active_ooo_len = 0;

    if (mv->active_tombs != NULL) {
        tl__free(mv->alloc, mv->active_tombs);
        mv->active_tombs = NULL;
    }
    mv->active_tombs_len = 0;

    /* Release pinned sealed memruns */
    if (mv->sealed != NULL) {
        for (size_t i = 0; i < mv->sealed_len; i++) {
            if (mv->sealed[i] != NULL) {
                tl_memrun_release(mv->sealed[i]);
            }
        }
        tl__free(mv->alloc, mv->sealed);
        mv->sealed = NULL;
    }
    mv->sealed_len = 0;

    /* Reset bounds */
    mv->min_ts = 0;
    mv->max_ts = 0;
    mv->has_data = false;
}

/*===========================================================================
 * Shared Memview (Snapshot Cache)
 *===========================================================================*/

tl_status_t tl_memview_shared_capture(tl_memview_shared_t** out,
                                       tl_memtable_t* mt,
                                       tl_mutex_t* memtable_mu,
                                       tl_alloc_ctx_t* alloc,
                                       uint64_t epoch) {
    TL_ASSERT(out != NULL);
    TL_ASSERT(mt != NULL);
    TL_ASSERT(memtable_mu != NULL);
    TL_ASSERT(alloc != NULL);

    *out = NULL;

    tl_memview_shared_t* mv = TL_NEW(alloc, tl_memview_shared_t);
    if (mv == NULL) {
        return TL_ENOMEM;
    }

    memset(mv, 0, sizeof(*mv));
    mv->epoch = epoch;
    tl_atomic_init_u32(&mv->refcnt, 1);

    tl_status_t st = tl_memview_capture(&mv->view, mt, memtable_mu, alloc);
    if (st != TL_OK) {
        tl__free(alloc, mv);
        return st;
    }

    *out = mv;
    return TL_OK;
}

tl_memview_shared_t* tl_memview_shared_acquire(tl_memview_shared_t* mv) {
    if (mv == NULL) {
        return NULL;
    }

    tl_atomic_fetch_add_u32(&mv->refcnt, 1, TL_MO_RELAXED);
    return mv;
}

void tl_memview_shared_release(tl_memview_shared_t* mv) {
    if (mv == NULL) {
        return;
    }

    uint32_t old = tl_atomic_fetch_sub_u32(&mv->refcnt, 1, TL_MO_RELEASE);
    TL_ASSERT(old >= 1);

    if (old == 1) {
        tl_atomic_fence(TL_MO_ACQUIRE);
        tl_memview_destroy(&mv->view);
        tl__free(mv->view.alloc, mv);
    }
}

/*===========================================================================
 * Query Support
 *===========================================================================*/

bool tl_memview_overlaps(const tl_memview_t* mv, tl_ts_t t1, tl_ts_t t2,
                         bool t2_unbounded) {
    TL_ASSERT(mv != NULL);

    if (!mv->has_data) {
        return false;
    }

    /*
     * Use tl_range_overlaps from tl_range.h.
     * Memview bounds are [min_ts, max_ts] (inclusive).
     * Query range is [t1, t2) or [t1, +inf).
     */
    return tl_range_overlaps(mv->min_ts, mv->max_ts, t1, t2, t2_unbounded);
}

/*===========================================================================
 * Validation (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG

/* Include for tl_intervals_arr_validate */
#include "../internal/tl_intervals.h"

/**
 * Validate memview invariants.
 *
 * Invariants:
 * 1. active_run is sorted (non-decreasing timestamps)
 * 2. active_ooo is sorted (non-decreasing timestamps)
 * 3. active_tombs is valid (sorted, non-overlapping, coalesced)
 * 4. sealed memrun pointers non-NULL
 * 5. has_data consistent with actual content
 */
bool tl_memview_validate(const tl_memview_t* mv) {
    if (mv == NULL) {
        return false;
    }

    /*
     * Invariant 1: active_run is sorted (non-decreasing timestamps)
     *
     * Use accessor functions for encapsulation.
     */
    const tl_record_t* run = tl_memview_run_data(mv);
    size_t run_len = tl_memview_run_len(mv);
    for (size_t i = 1; i < run_len; i++) {
        if (run[i].ts < run[i - 1].ts) {
            return false;
        }
    }

    /*
     * Invariant 2: active_ooo is sorted (non-decreasing timestamps)
     */
    const tl_record_t* ooo = tl_memview_ooo_data(mv);
    size_t ooo_len = tl_memview_ooo_len(mv);
    for (size_t i = 1; i < ooo_len; i++) {
        if (ooo[i].ts < ooo[i - 1].ts) {
            return false;
        }
    }

    /*
     * Invariant 3: active_tombs is valid
     *
     * Uses the shared tl_intervals_arr_validate() function.
     */
    const tl_interval_t* tombs = tl_memview_tomb_data(mv);
    size_t tombs_len = tl_memview_tomb_len(mv);
    if (!tl_intervals_arr_validate(tombs, tombs_len)) {
        return false;
    }

    /*
     * Invariant 4: sealed memrun pointers non-NULL
     */
    size_t sealed_len = tl_memview_sealed_len(mv);
    for (size_t i = 0; i < sealed_len; i++) {
        if (tl_memview_sealed_get(mv, i) == NULL) {
            return false;
        }
    }

    /*
     * Invariant 5: has_data consistency
     *
     * If has_data is true, there must be some content.
     * Content can be: records in run, records in ooo, tombstones, or sealed memruns.
     */
    if (tl_memview_has_data(mv)) {
        bool has_content = (run_len > 0 || ooo_len > 0 ||
                           tombs_len > 0 || sealed_len > 0);
        if (!has_content) {
            return false;  /* has_data true but no content */
        }
    }

    return true;
}

#endif /* TL_DEBUG */

/------------------------------------------------------------------------------/
/*   END OF: tl_memview.c
/------------------------------------------------------------------------------/
