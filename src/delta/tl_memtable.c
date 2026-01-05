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

        /* Copy all records (cannot fail after reserve) */
        st = tl_recvec_push_n(&mt->active_run, records, n);
        if (st != TL_OK) {
            /* Defensive: should not fail after reserve, but handle it */
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
     * maint_cond is shared and may be signaled for other reasons.
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
