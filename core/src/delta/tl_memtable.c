#include "tl_memtable.h"
#include "../internal/tl_locks.h"
#include <stdlib.h>
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
    tl_recvec_init(&mt->ooo_head, alloc);
    tl_intervals_init(&mt->active_tombs, alloc);

    /* Preallocate sealed queue (CRITICAL: no realloc on seal path) */
    mt->sealed = TL_NEW_ARRAY(alloc, tl_memrun_t*, sealed_max_runs);
    if (mt->sealed == NULL) {
        tl_recvec_destroy(&mt->active_run);
        tl_recvec_destroy(&mt->ooo_head);
        tl_intervals_destroy(&mt->active_tombs);
        return TL_ENOMEM;
    }
    mt->sealed_head = 0;
    mt->sealed_len = 0;
    mt->sealed_max_runs = sealed_max_runs;
    mt->sealed_epoch = 0;

    /* Store configuration */
    mt->memtable_max_bytes = memtable_max_bytes;
    mt->ooo_budget_bytes = ooo_budget_bytes;
    mt->ooo_chunk_records = 0;  /* Derived below */
    mt->ooo_run_limit = TL_DEFAULT_OOO_RUN_LIMIT;

    /* Initialize metadata */
    mt->last_inorder_ts = TL_TS_MIN;
    mt->active_bytes_est = 0;
    mt->epoch = 0;

    mt->ooo_runs = NULL;
    mt->ooo_head_sorted = true;
    mt->ooo_head_last_ts = TL_TS_MIN;
    mt->ooo_head_last_handle = 0;
    mt->ooo_next_gen = 0;

    /* Derive OOO chunk size from budget (bounded) */
    size_t budget_records = (ooo_budget_bytes / TL_RECORD_SIZE);
    size_t chunk = budget_records / TL_OOO_TARGET_RUNS;
    if (chunk < TL_OOO_CHUNK_MIN_RECORDS) {
        chunk = TL_OOO_CHUNK_MIN_RECORDS;
    }
    if (chunk > TL_OOO_CHUNK_MAX_RECORDS) {
        chunk = TL_OOO_CHUNK_MAX_RECORDS;
    }
    if (chunk == 0) {
        chunk = TL_OOO_CHUNK_MIN_RECORDS;
    }
    mt->ooo_chunk_records = chunk;

    return TL_OK;
}

void tl_memtable_destroy(tl_memtable_t* mt) {
    if (mt == NULL) {
        return;
    }

    /* Release all sealed memruns */
    for (size_t i = 0; i < mt->sealed_len; i++) {
        size_t idx = tl_memtable_sealed_index(mt, i);
        if (mt->sealed[idx] != NULL) {
            tl_memrun_release(mt->sealed[idx]);
        }
    }

    /* Free sealed queue array */
    if (mt->sealed != NULL) {
        tl__free(mt->alloc, (void*)mt->sealed);
        mt->sealed = NULL;
    }
    mt->sealed_len = 0;
    mt->sealed_head = 0;
    mt->sealed_epoch = 0;

    /* Destroy active buffers */
    tl_recvec_destroy(&mt->active_run);
    tl_recvec_destroy(&mt->ooo_head);
    tl_intervals_destroy(&mt->active_tombs);
    if (mt->ooo_runs != NULL) {
        tl_ooorunset_release(mt->ooo_runs);
        mt->ooo_runs = NULL;
    }
}

/*===========================================================================
 * Insert Operations
 *===========================================================================*/

/**
 * Comparison function for qsort.
 * Sorts records by (ts, handle) in non-decreasing order.
 */
static int cmp_record_ts_head(const void* a, const void* b) {
    const tl_record_t* ra = (const tl_record_t*)a;
    const tl_record_t* rb = (const tl_record_t*)b;

    if (ra->ts < rb->ts) return -1;
    if (ra->ts > rb->ts) return 1;
    if (ra->handle < rb->handle) return -1;
    if (ra->handle > rb->handle) return 1;
    return 0;
}

static void memtable_add_bytes(tl_memtable_t* mt, size_t add) {
    if (add == 0) {
        return;
    }
    if (mt->active_bytes_est > SIZE_MAX - add) {
        mt->active_bytes_est = SIZE_MAX;
        return;
    }
    mt->active_bytes_est += add;
}

static void memtable_add_record_bytes(tl_memtable_t* mt, size_t count) {
    if (count == 0) {
        return;
    }
    if (tl__alloc_would_overflow(count, TL_RECORD_SIZE)) {
        mt->active_bytes_est = SIZE_MAX;
        return;
    }
    memtable_add_bytes(mt, count * TL_RECORD_SIZE);
}

static void memtable_adjust_tomb_bytes(tl_memtable_t* mt,
                                       size_t before_len,
                                       size_t after_len) {
    if (before_len == after_len) {
        return;
    }

    size_t diff = (after_len > before_len)
                    ? (after_len - before_len)
                    : (before_len - after_len);

    if (tl__alloc_would_overflow(diff, sizeof(tl_interval_t))) {
        /* Saturate conservatively on overflow. */
        if (after_len > before_len) {
            mt->active_bytes_est = SIZE_MAX;
        } else {
            mt->active_bytes_est = 0;
        }
        return;
    }

    size_t bytes = diff * sizeof(tl_interval_t);

    if (after_len > before_len) {
        memtable_add_bytes(mt, bytes);
    } else {
        if (mt->active_bytes_est < bytes) {
            mt->active_bytes_est = 0;
        } else {
            mt->active_bytes_est -= bytes;
        }
    }
}

static size_t memtable_ooo_bytes_est(const tl_memtable_t* mt) {
    size_t total_len = tl_memtable_ooo_total_len(mt);
    if (tl__alloc_would_overflow(total_len, TL_RECORD_SIZE)) {
        return SIZE_MAX;
    }
    return total_len * TL_RECORD_SIZE;
}

static void ooo_head_note_append(tl_memtable_t* mt, tl_ts_t ts, tl_handle_t handle) {
    size_t head_len = tl_recvec_len(&mt->ooo_head);
    if (head_len <= 1) {
        mt->ooo_head_sorted = true;
        mt->ooo_head_last_ts = ts;
        mt->ooo_head_last_handle = handle;
        return;
    }

    if (mt->ooo_head_sorted) {
        if (ts < mt->ooo_head_last_ts ||
            (ts == mt->ooo_head_last_ts && handle < mt->ooo_head_last_handle)) {
            mt->ooo_head_sorted = false;
        }
    }

    mt->ooo_head_last_ts = ts;
    mt->ooo_head_last_handle = handle;
}

static tl_status_t memtable_flush_ooo_head(tl_memtable_t* mt, bool required) {
    size_t head_len = tl_recvec_len(&mt->ooo_head);
    if (head_len == 0) {
        return TL_OK;
    }

    if (!required && mt->ooo_run_limit > 0 &&
        tl_ooorunset_count(mt->ooo_runs) >= mt->ooo_run_limit) {
        return TL_EBUSY;
    }

    if (head_len > SIZE_MAX / sizeof(tl_record_t)) {
        return TL_EOVERFLOW;
    }

    size_t bytes = head_len * sizeof(tl_record_t);
    tl_record_t* copy = tl__malloc(mt->alloc, bytes);
    if (copy == NULL) {
        return TL_ENOMEM;
    }
    memcpy(copy, tl_recvec_data(&mt->ooo_head), bytes);

    if (!mt->ooo_head_sorted && head_len > 1) {
        qsort(copy, head_len, sizeof(tl_record_t), cmp_record_ts_head);
    }

    uint64_t gen = ++mt->ooo_next_gen;
    tl_ooorun_t* run = NULL;
    tl_status_t st = tl_ooorun_create(mt->alloc, copy, head_len, gen, &run);
    if (st != TL_OK) {
        tl__free(mt->alloc, copy);
        return st;
    }

    tl_ooorunset_t* new_set = NULL;
    st = tl_ooorunset_append(mt->alloc, mt->ooo_runs, run, &new_set);
    if (st != TL_OK) {
        tl_ooorun_release(run);
        return st;
    }

    tl_ooorunset_t* old_set = mt->ooo_runs;
    mt->ooo_runs = new_set;
    if (old_set != NULL) {
        tl_ooorunset_release(old_set);
    }
    tl_ooorun_release(run); /* Runset now owns a reference */

    tl_recvec_clear(&mt->ooo_head);
    mt->ooo_head_sorted = true;
    mt->ooo_head_last_ts = TL_TS_MIN;
    mt->ooo_head_last_handle = 0;

    mt->epoch++;

    return TL_OK;
}

tl_status_t tl_memtable_insert(tl_memtable_t* mt, tl_ts_t ts, tl_handle_t handle) {
    TL_ASSERT(mt != NULL);

    tl_status_t st;

    /* Route to appropriate buffer based on timestamp ordering */
    if (tl_recvec_len(&mt->active_run) == 0 ||
        ts >= mt->last_inorder_ts) {
        /* In-order: fast path to run */
        st = tl_recvec_push(&mt->active_run, ts, handle);
        if (st != TL_OK) {
            return st;
        }
        mt->last_inorder_ts = ts;
    } else {
        /* Out-of-order: append to OOO head (sorted on flush/seal). */
        st = tl_recvec_push(&mt->ooo_head, ts, handle);
        if (st != TL_OK) {
            return st;
        }
        ooo_head_note_append(mt, ts, handle);
    }

    /* Update metadata AFTER successful insert */
    mt->epoch++;
    memtable_add_record_bytes(mt, 1);

    /* Best-effort head flush when threshold reached */
    if (tl_recvec_len(&mt->ooo_head) >= mt->ooo_chunk_records) {
        tl_status_t flush_st = memtable_flush_ooo_head(mt, false);
        if (flush_st != TL_OK) {
            return TL_EBUSY; /* Insert succeeded, flush failed */
        }
    }

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
        /* Slow path: per-record insert
         *
         * C-08 fix: Pre-reserve both vectors to guarantee all-or-nothing semantics.
         * This ensures that if any allocation would fail, we fail BEFORE inserting
         * any records. Callers can then safely rollback INCREF on all input handles.
         *
         * TRADEOFF: We reserve up to 2N slots total (worst case: all go to run OR
         * all go to ooo). This may fail earlier under memory pressure than actual
         * inserts would, but guarantees atomicity which is more important for API
         * correctness. Memory is virtual, so over-reservation doesn't waste physical
         * RAM immediately.
         */
        size_t run_len = tl_recvec_len(&mt->active_run);
        size_t ooo_len = tl_recvec_len(&mt->ooo_head);

        /* Overflow checks before computing sums */
        if (n > SIZE_MAX - run_len || n > SIZE_MAX - ooo_len) {
            return TL_EOVERFLOW;
        }

        /* Pre-reserve to guarantee all-or-nothing semantics */
        st = tl_recvec_reserve(&mt->active_run, run_len + n);
        if (st != TL_OK) {
            return st;  /* No records inserted, clean failure */
        }

        st = tl_recvec_reserve(&mt->ooo_head, ooo_len + n);
        if (st != TL_OK) {
            return st;  /* No records inserted, clean failure */
        }

        /* Loop: push/insert cannot fail on allocation after pre-reserve */
        for (size_t i = 0; i < n; i++) {
            tl_ts_t ts = records[i].ts;
            tl_handle_t handle = records[i].handle;

            if (tl_recvec_len(&mt->active_run) == 0 || ts >= mt->last_inorder_ts) {
                st = tl_recvec_push(&mt->active_run, ts, handle);
                /* Capacity guaranteed, can only fail on programming error */
                TL_ASSERT(st == TL_OK);
                mt->last_inorder_ts = ts;
            } else {
                /* OOO head append (sorted on flush/seal) */
                st = tl_recvec_push(&mt->ooo_head, ts, handle);
                /* Capacity guaranteed, can only fail on programming error */
                TL_ASSERT(st == TL_OK);
                ooo_head_note_append(mt, ts, handle);
            }
            inserted++;
        }
    }

    /* Update metadata ONCE at end (all records inserted successfully) */
    mt->epoch++;
    memtable_add_record_bytes(mt, inserted);

    /* Best-effort head flush when threshold reached */
    if (tl_recvec_len(&mt->ooo_head) >= mt->ooo_chunk_records) {
        tl_status_t flush_st = memtable_flush_ooo_head(mt, false);
        if (flush_st != TL_OK) {
            return TL_EBUSY; /* Inserted all records, flush failed */
        }
    }

    return TL_OK;
}

tl_status_t tl_memtable_insert_tombstone(tl_memtable_t* mt, tl_ts_t t1, tl_ts_t t2) {
    TL_ASSERT(mt != NULL);

    /* Delegate to tl_intervals which handles validation and coalescing */
    size_t before_len = tl_intervals_len(&mt->active_tombs);
    tl_status_t st = tl_intervals_insert(&mt->active_tombs, t1, t2);

    if (st == TL_OK && t1 < t2) {
        /* Only update metadata if actual insert happened (not empty interval) */
        mt->epoch++;
        size_t after_len = tl_intervals_len(&mt->active_tombs);
        memtable_adjust_tomb_bytes(mt, before_len, after_len);
    }

    return st;
}

tl_status_t tl_memtable_insert_tombstone_unbounded(tl_memtable_t* mt, tl_ts_t t1) {
    TL_ASSERT(mt != NULL);

    size_t before_len = tl_intervals_len(&mt->active_tombs);
    tl_status_t st = tl_intervals_insert_unbounded(&mt->active_tombs, t1);

    if (st == TL_OK) {
        mt->epoch++;
        size_t after_len = tl_intervals_len(&mt->active_tombs);
        memtable_adjust_tomb_bytes(mt, before_len, after_len);
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
        size_t ooo_bytes = memtable_ooo_bytes_est(mt);
        if (ooo_bytes >= mt->ooo_budget_bytes) {
            return true;
        }
    }

    if (mt->ooo_run_limit > 0 &&
        tl_ooorunset_count(mt->ooo_runs) >= mt->ooo_run_limit) {
        return true;
    }

    return false;
}

bool tl_memtable_ooo_budget_exceeded(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);

    if (mt->ooo_budget_bytes == 0) {
        return false;  /* Unlimited budget */
    }

    size_t ooo_bytes = memtable_ooo_bytes_est(mt);
    return ooo_bytes >= mt->ooo_budget_bytes;
}

bool tl_memtable_is_active_empty(const tl_memtable_t* mt) {
    TL_ASSERT(mt != NULL);
    return tl_recvec_is_empty(&mt->active_run) &&
           tl_recvec_is_empty(&mt->ooo_head) &&
           tl_ooorunset_total_len(mt->ooo_runs) == 0 &&
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
    tl_memrun_t* mr = NULL;
    tl_status_t alloc_st = tl_memrun_alloc(mt->alloc, &mr);
    if (alloc_st != TL_OK) {
        return TL_ENOMEM; /* Active state PRESERVED */
    }

    /* Step 4: Flush OOO head (required at seal) */
    tl_status_t flush_st = memtable_flush_ooo_head(mt, true);
    if (flush_st != TL_OK) {
        tl__free(mt->alloc, mr);
        return flush_st; /* Active state PRESERVED */
    }

    /* Step 5: Take ownership of active arrays and runset */
    size_t run_len = 0;
    size_t tombs_len = 0;

    tl_record_t* run = tl_recvec_take(&mt->active_run, &run_len);
    tl_interval_t* tombs = tl_intervals_take(&mt->active_tombs, &tombs_len);
    tl_ooorunset_t* ooo_runs = mt->ooo_runs;
    mt->ooo_runs = NULL;

    /* Step 6: Initialize memrun in-place (no allocations) */
    tl_status_t init_st = tl_memrun_init(mr, mt->alloc,
                                         run, run_len,
                                         ooo_runs,
                                         tombs, tombs_len);
    if (init_st != TL_OK) {
        /* Internal invariant violation - avoid leaks, but data is lost */
        if (run != NULL) tl__free(mt->alloc, run);
        if (ooo_runs != NULL) tl_ooorunset_release(ooo_runs);
        if (tombs != NULL) tl__free(mt->alloc, tombs);
        tl__free(mt->alloc, mr);
        return TL_EINTERNAL;
    }

    /* Step 7: Push to sealed queue (under memtable_mu) */
    TL_LOCK(mu, TL_LOCK_MEMTABLE_MU);
    /*
     * M-10 fix: Runtime check for queue capacity (defensive).
     * Single writer means this should never fail, but we check defensively
     * in case of future code changes. On failure, release memrun and return
     * TL_EBUSY without corrupting the queue.
     */
    if (mt->sealed_len >= mt->sealed_max_runs) {
        TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);
        tl_memrun_release(mr);
        return TL_EBUSY;
    }
    TL_ASSERT(mt->sealed_len < mt->sealed_max_runs);
    size_t idx = tl_memtable_sealed_index(mt, mt->sealed_len);
    mt->sealed[idx] = mr;
    mt->sealed_len++;
    mt->sealed_epoch++;
    TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);

    /* Step 8: Reset active metadata AFTER successful enqueue */
    mt->last_inorder_ts = TL_TS_MIN;
    mt->active_bytes_est = 0;
    mt->epoch++;  /* Memtable state changed (active -> sealed) */
    tl_recvec_clear(&mt->ooo_head);
    mt->ooo_head_sorted = true;
    mt->ooo_head_last_ts = TL_TS_MIN;
    mt->ooo_head_last_handle = 0;
    mt->ooo_next_gen = 0;

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

tl_status_t tl_memtable_peek_oldest(const tl_memtable_t* mt, tl_memrun_t** out) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(out != NULL);

    if (mt->sealed_len == 0) {
        *out = NULL;
        return TL_OK;
    }

    /* Peek oldest (FIFO: sealed_head) and acquire reference */
    tl_memrun_t* mr = tl_memtable_sealed_at(mt, 0);
    *out = tl_memrun_acquire(mr);
    return TL_OK;
}

void tl_memtable_pop_oldest(tl_memtable_t* mt, tl_cond_t* cond) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(mt->sealed_len > 0);

    /* Get oldest (FIFO: sealed_head) */
    size_t idx = tl_memtable_sealed_index(mt, 0);
    tl_memrun_t* mr = mt->sealed[idx];
    mt->sealed[idx] = NULL;

    /* Advance head */
    mt->sealed_head++;
    if (mt->sealed_head == mt->sealed_max_runs) {
        mt->sealed_head = 0;
    }
    mt->sealed_len--;
    if (mt->sealed_len == 0) {
        mt->sealed_head = 0;
    }
    mt->sealed_epoch++;

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

bool tl_memtable_wait_for_space(const tl_memtable_t* mt, tl_mutex_t* mu,
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

    /* OOO head is unsorted during append; do NOT check sortedness here.
     * Sortedness is enforced on head flush or seal. */

    /* Check active_tombs is valid */
    if (!tl_intervals_validate(&mt->active_tombs)) {
        return false;
    }

    /* Check sealed queue bounds */
    if (mt->sealed_len > mt->sealed_max_runs) {
        return false;
    }
    if (mt->sealed_head >= mt->sealed_max_runs) {
        return false;
    }

    /* Check sealed entries are non-NULL */
    for (size_t i = 0; i < mt->sealed_len; i++) {
        if (tl_memtable_sealed_at(mt, i) == NULL) {
            return false;
        }
    }

    return true;
}

#endif /* TL_DEBUG */
