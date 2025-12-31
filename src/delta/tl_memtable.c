#include "../internal/tl_memtable.h"
#include <string.h>
#include <stdlib.h>

/*===========================================================================
 * Memrun lifecycle
 *===========================================================================*/

static void memrun_destroy(tl_memrun_t* mr) {
    if (mr == NULL) return;

    const tl_allocator_t* alloc = mr->alloc;

    if (mr->run != NULL) tl__free(alloc, mr->run);
    if (mr->ooo != NULL) tl__free(alloc, mr->ooo);
    if (mr->tombs != NULL) tl__free(alloc, mr->tombs);

    tl__free(alloc, mr);
}

uint32_t tl_memrun_acquire(tl_memrun_t* mr) {
    if (mr == NULL) return 0;
    return tl_atomic_u32_fetch_add(&mr->refcnt, 1) + 1;
}

uint32_t tl_memrun_release(tl_memrun_t* mr) {
    if (mr == NULL) return 0;

    uint32_t old = tl_atomic_u32_fetch_sub(&mr->refcnt, 1);
    if (old == 1) {
        memrun_destroy(mr);
        return 0;
    }
    return old - 1;
}

/*===========================================================================
 * Memtable creation/destruction
 *===========================================================================*/

tl_status_t tl_memtable_create(const tl_allocator_t* alloc,
                                size_t memtable_max_bytes,
                                size_t target_page_bytes,
                                tl_memtable_t** out) {
    if (out == NULL) return TL_EINVAL;
    *out = NULL;

    tl_memtable_t* mt = tl__calloc(alloc, 1, sizeof(tl_memtable_t));
    if (mt == NULL) return TL_ENOMEM;

    mt->alloc = alloc;
    mt->memtable_max_bytes = memtable_max_bytes;
    mt->target_page_bytes = target_page_bytes;

    /* Initialize active buffers */
    tl_recvec_init(&mt->active_run, alloc);
    tl_recvec_init(&mt->active_ooo, alloc);
    tl_intervals_init(&mt->active_tombs, alloc);

    /* Initialize OOO tracking */
    mt->active_ooo_min = TL_TS_MAX;
    mt->active_ooo_max = TL_TS_MIN;
    mt->active_ooo_has_data = false;

    /* Initialize in-order tracking */
    mt->active_last_inorder_ts = TL_TS_MIN;
    mt->active_has_inorder = false;

    /* Initialize sealed queue */
    mt->sealed_cap = TL_SEALED_MAX_RUNS;
    mt->sealed = tl__calloc(alloc, mt->sealed_cap, sizeof(tl_memrun_t*));
    if (mt->sealed == NULL) {
        tl_recvec_destroy(&mt->active_run);
        tl_recvec_destroy(&mt->active_ooo);
        tl_intervals_destroy(&mt->active_tombs);
        tl__free(alloc, mt);
        return TL_ENOMEM;
    }
    mt->sealed_len = 0;

    /* Initialize mutex */
    if (tl_mutex_init(&mt->mu) != 0) {
        tl__free(alloc, mt->sealed);
        tl_recvec_destroy(&mt->active_run);
        tl_recvec_destroy(&mt->active_ooo);
        tl_intervals_destroy(&mt->active_tombs);
        tl__free(alloc, mt);
        return TL_EINTERNAL;
    }

    *out = mt;
    return TL_OK;
}

void tl_memtable_destroy(tl_memtable_t* mt) {
    if (mt == NULL) return;

    const tl_allocator_t* alloc = mt->alloc;

    /* Destroy active buffers */
    tl_recvec_destroy(&mt->active_run);
    tl_recvec_destroy(&mt->active_ooo);
    tl_intervals_destroy(&mt->active_tombs);

    /* Release all sealed memruns */
    for (size_t i = 0; i < mt->sealed_len; i++) {
        if (mt->sealed[i] != NULL) {
            tl_memrun_release(mt->sealed[i]);
        }
    }
    tl__free(alloc, mt->sealed);

    /* Destroy mutex */
    tl_mutex_destroy(&mt->mu);

    tl__free(alloc, mt);
}

/*===========================================================================
 * Record insertion
 *===========================================================================*/

/* Estimate bytes per record for accounting */
#define TL_RECORD_SIZE_EST (sizeof(tl_record_t) + 8)  /* Plus some overhead */

tl_status_t tl_memtable_insert(tl_memtable_t* mt, tl_ts_t ts, tl_handle_t handle) {
    if (mt == NULL) return TL_EINVAL;

    tl_status_t st;

    /* Decide: in-order or out-of-order? */
    if (!mt->active_has_inorder) {
        /* First record: goes to in-order run */
        st = tl_recvec_push(&mt->active_run, ts, handle);
        if (st != TL_OK) return st;

        mt->active_last_inorder_ts = ts;
        mt->active_has_inorder = true;
    } else if (ts >= mt->active_last_inorder_ts) {
        /* In-order: append to run */
        st = tl_recvec_push(&mt->active_run, ts, handle);
        if (st != TL_OK) return st;

        mt->active_last_inorder_ts = ts;
    } else {
        /* Out-of-order: append to OOO buffer */
        st = tl_recvec_push(&mt->active_ooo, ts, handle);
        if (st != TL_OK) return st;

        /* Track OOO bounds */
        if (!mt->active_ooo_has_data) {
            mt->active_ooo_min = ts;
            mt->active_ooo_max = ts;
            mt->active_ooo_has_data = true;
        } else {
            if (ts < mt->active_ooo_min) mt->active_ooo_min = ts;
            if (ts > mt->active_ooo_max) mt->active_ooo_max = ts;
        }
    }

    /* Update accounting */
    mt->active_bytes_est += TL_RECORD_SIZE_EST;
    mt->write_count++;

    return TL_OK;
}

tl_status_t tl_memtable_insert_batch(tl_memtable_t* mt,
                                      const tl_record_t* records,
                                      size_t n,
                                      uint32_t flags) {
    if (mt == NULL) return TL_EINVAL;
    if (n == 0) return TL_OK;
    if (records == NULL) return TL_EINVAL;

    /*
     * Fast path: if hint says mostly in-order AND first record >= last_inorder_ts
     * AND batch appears sorted, append entire batch to active_run.
     */
    bool try_fast_path = (flags & TL_APPEND_HINT_MOSTLY_ORDER) &&
                         (!mt->active_has_inorder ||
                          records[0].ts >= mt->active_last_inorder_ts);

    if (try_fast_path && n > 1) {
        /* Quick monotonicity check: sample up to 64 pairs */
        size_t sample_count = (n - 1 < 64) ? (n - 1) : 64;
        size_t stride = (n - 1) / sample_count;
        if (stride == 0) stride = 1;

        bool is_sorted = true;
        for (size_t i = 0; i < n - 1 && is_sorted; i += stride) {
            if (records[i].ts > records[i + 1].ts) {
                is_sorted = false;
            }
        }

        if (is_sorted) {
            /* Fast path: bulk append */
            tl_status_t st = tl_recvec_push_n(&mt->active_run, records, n);
            if (st != TL_OK) return st;

            mt->active_last_inorder_ts = records[n - 1].ts;
            if (!mt->active_has_inorder) mt->active_has_inorder = true;
            mt->active_bytes_est += n * TL_RECORD_SIZE_EST;
            mt->write_count += n;

            return TL_OK;
        }
    }

    /* Slow path: per-record insertion */
    for (size_t i = 0; i < n; i++) {
        tl_status_t st = tl_memtable_insert(mt, records[i].ts, records[i].handle);
        if (st != TL_OK) return st;
    }

    return TL_OK;
}

/*===========================================================================
 * Tombstone insertion
 *===========================================================================*/

/* Estimate bytes per tombstone interval */
#define TL_TOMBSTONE_SIZE_EST (sizeof(tl_interval_t) + 8)

tl_status_t tl_memtable_add_tombstone(tl_memtable_t* mt, tl_ts_t t1, tl_ts_t t2) {
    if (mt == NULL) return TL_EINVAL;

    /* Validate range */
    if (t2 < t1) return TL_EINVAL;

    /* Empty range is no-op */
    if (t1 == t2) return TL_OK;

    /* Insert with coalescing */
    tl_status_t st = tl_intervals_insert(&mt->active_tombs, t1, t2, false);
    if (st != TL_OK) return st;

    /* Update accounting (rough estimate; coalescing may reduce actual count) */
    mt->active_bytes_est += TL_TOMBSTONE_SIZE_EST;

    return TL_OK;
}

/*===========================================================================
 * Sealing
 *===========================================================================*/

bool tl_memtable_should_seal(const tl_memtable_t* mt) {
    if (mt == NULL) return false;

    /* Primary: memory threshold */
    if (mt->active_bytes_est >= mt->memtable_max_bytes) {
        return true;
    }

    /* Secondary: OOO budget exceeded */
    size_t run_len = tl_recvec_len(&mt->active_run);
    size_t ooo_len = tl_recvec_len(&mt->active_ooo);
    size_t total = run_len + ooo_len;

    if (total > 0 && ooo_len > 0) {
        size_t ooo_percent = (ooo_len * 100) / total;
        if (ooo_percent > TL_OOO_BUDGET_PERCENT && ooo_len > 100) {
            return true;
        }
    }

    return false;
}

bool tl_memtable_can_seal(const tl_memtable_t* mt) {
    if (mt == NULL) return false;
    return mt->sealed_len < TL_SEALED_MAX_RUNS;
}

size_t tl_memtable_sealed_count(const tl_memtable_t* mt) {
    return mt ? mt->sealed_len : 0;
}

/* Comparison function for sorting OOO records by timestamp */
static int compare_records_by_ts(const void* a, const void* b) {
    const tl_record_t* ra = (const tl_record_t*)a;
    const tl_record_t* rb = (const tl_record_t*)b;

    if (ra->ts < rb->ts) return -1;
    if (ra->ts > rb->ts) return 1;
    return 0;
}

tl_status_t tl_memtable_seal_active(tl_memtable_t* mt) {
    if (mt == NULL) return TL_EINVAL;

    /* Check if active is empty */
    size_t run_len = tl_recvec_len(&mt->active_run);
    size_t ooo_len = tl_recvec_len(&mt->active_ooo);
    size_t tombs_len = tl_intervals_len(&mt->active_tombs);

    if (run_len == 0 && ooo_len == 0 && tombs_len == 0) {
        return TL_EOF;  /* Nothing to seal */
    }

    /* Check backpressure */
    tl_mutex_lock(&mt->mu);
    if (mt->sealed_len >= TL_SEALED_MAX_RUNS) {
        tl_mutex_unlock(&mt->mu);
        return TL_EBUSY;
    }
    tl_mutex_unlock(&mt->mu);

    const tl_allocator_t* alloc = mt->alloc;

    /* Allocate memrun */
    tl_memrun_t* mr = tl__calloc(alloc, 1, sizeof(tl_memrun_t));
    if (mr == NULL) return TL_ENOMEM;

    mr->alloc = alloc;
    tl_atomic_u32_store(&mr->refcnt, 1);
    mr->is_published = false;

    /* Move in-order run (ownership transfer) */
    if (run_len > 0) {
        mr->run = mt->active_run.data;
        mr->run_len = run_len;

        /* Reset active_run to empty without freeing (ownership transferred) */
        mt->active_run.data = NULL;
        mt->active_run.len = 0;
        mt->active_run.cap = 0;
    }

    /* Move out-of-order buffer and sort */
    if (ooo_len > 0) {
        mr->ooo = mt->active_ooo.data;
        mr->ooo_len = ooo_len;

        /* Sort OOO in place */
        qsort(mr->ooo, mr->ooo_len, sizeof(tl_record_t), compare_records_by_ts);

        /* Reset active_ooo to empty */
        mt->active_ooo.data = NULL;
        mt->active_ooo.len = 0;
        mt->active_ooo.cap = 0;
    }

    /* Move tombstones */
    if (tombs_len > 0) {
        mr->tombs = mt->active_tombs.data;
        mr->tombs_len = tombs_len;

        /* Reset active_tombs */
        mt->active_tombs.data = NULL;
        mt->active_tombs.len = 0;
        mt->active_tombs.cap = 0;
    }

    /* Compute min/max timestamps */
    mr->min_ts = TL_TS_MAX;
    mr->max_ts = TL_TS_MIN;

    if (mr->run_len > 0) {
        if (mr->run[0].ts < mr->min_ts) mr->min_ts = mr->run[0].ts;
        if (mr->run[mr->run_len - 1].ts > mr->max_ts)
            mr->max_ts = mr->run[mr->run_len - 1].ts;
    }

    if (mr->ooo_len > 0) {
        /* OOO is now sorted */
        if (mr->ooo[0].ts < mr->min_ts) mr->min_ts = mr->ooo[0].ts;
        if (mr->ooo[mr->ooo_len - 1].ts > mr->max_ts)
            mr->max_ts = mr->ooo[mr->ooo_len - 1].ts;
    }

    /* Store OOO bounds for future reference */
    mr->ooo_min_ts = mt->active_ooo_min;
    mr->ooo_max_ts = mt->active_ooo_max;

    /* Reset active state */
    mt->active_ooo_min = TL_TS_MAX;
    mt->active_ooo_max = TL_TS_MIN;
    mt->active_ooo_has_data = false;
    mt->active_last_inorder_ts = TL_TS_MIN;
    mt->active_has_inorder = false;
    mt->active_bytes_est = 0;

    /* Add to sealed queue */
    tl_mutex_lock(&mt->mu);
    mt->sealed[mt->sealed_len++] = mr;
    mt->seal_count++;
    tl_mutex_unlock(&mt->mu);

    return TL_OK;
}

tl_memrun_t* tl_memtable_peek_oldest_sealed(tl_memtable_t* mt) {
    if (mt == NULL) return NULL;

    tl_mutex_lock(&mt->mu);
    tl_memrun_t* mr = (mt->sealed_len > 0) ? mt->sealed[0] : NULL;
    tl_mutex_unlock(&mt->mu);

    return mr;
}

tl_memrun_t* tl_memtable_pop_oldest_sealed(tl_memtable_t* mt) {
    if (mt == NULL) return NULL;

    tl_mutex_lock(&mt->mu);

    if (mt->sealed_len == 0) {
        tl_mutex_unlock(&mt->mu);
        return NULL;
    }

    tl_memrun_t* mr = mt->sealed[0];
    mr->is_published = true;

    /* Shift remaining entries */
    for (size_t i = 1; i < mt->sealed_len; i++) {
        mt->sealed[i - 1] = mt->sealed[i];
    }
    mt->sealed_len--;

    tl_mutex_unlock(&mt->mu);

    return mr;
}

/*===========================================================================
 * Memview (Snapshot View)
 *===========================================================================*/

tl_status_t tl_memtable_snapshot(tl_memtable_t* mt, tl_memview_t** out) {
    if (mt == NULL || out == NULL) return TL_EINVAL;
    *out = NULL;

    const tl_allocator_t* alloc = mt->alloc;

    tl_memview_t* mv = tl__calloc(alloc, 1, sizeof(tl_memview_t));
    if (mv == NULL) return TL_ENOMEM;

    mv->alloc = alloc;
    mv->min_ts = TL_TS_MAX;
    mv->max_ts = TL_TS_MIN;

    /*
     * Capture sealed memruns (only non-published ones).
     * Must hold lock during capture.
     */
    tl_mutex_lock(&mt->mu);

    /* Count non-published sealed memruns */
    size_t non_pub_count = 0;
    for (size_t i = 0; i < mt->sealed_len; i++) {
        if (!mt->sealed[i]->is_published) {
            non_pub_count++;
        }
    }

    if (non_pub_count > 0) {
        mv->sealed = tl__malloc(alloc, non_pub_count * sizeof(tl_memrun_t*));
        if (mv->sealed == NULL) {
            tl_mutex_unlock(&mt->mu);
            tl__free(alloc, mv);
            return TL_ENOMEM;
        }

        size_t idx = 0;
        for (size_t i = 0; i < mt->sealed_len; i++) {
            if (!mt->sealed[i]->is_published) {
                tl_memrun_acquire(mt->sealed[i]);
                mv->sealed[idx++] = mt->sealed[i];

                /* Update bounds */
                if (mt->sealed[i]->min_ts < mv->min_ts)
                    mv->min_ts = mt->sealed[i]->min_ts;
                if (mt->sealed[i]->max_ts > mv->max_ts)
                    mv->max_ts = mt->sealed[i]->max_ts;
            }
        }
        mv->sealed_len = non_pub_count;
    }

    tl_mutex_unlock(&mt->mu);

    /*
     * Copy active buffers snapshot.
     * Note: Writer must not be actively modifying during snapshot.
     * This is ensured by holding writer_mu at the tl_timelog level.
     */
    size_t run_len = tl_recvec_len(&mt->active_run);
    size_t ooo_len = tl_recvec_len(&mt->active_ooo);
    size_t tombs_len = tl_intervals_len(&mt->active_tombs);

    /* Copy active_run */
    if (run_len > 0) {
        mv->active_run = tl__malloc(alloc, run_len * sizeof(tl_record_t));
        if (mv->active_run == NULL) {
            tl_memview_release(mv);
            return TL_ENOMEM;
        }
        memcpy(mv->active_run, mt->active_run.data, run_len * sizeof(tl_record_t));
        mv->active_run_len = run_len;

        /* Update bounds */
        if (mv->active_run[0].ts < mv->min_ts)
            mv->min_ts = mv->active_run[0].ts;
        if (mv->active_run[run_len - 1].ts > mv->max_ts)
            mv->max_ts = mv->active_run[run_len - 1].ts;
    }

    /* Copy active_ooo */
    if (ooo_len > 0) {
        mv->active_ooo = tl__malloc(alloc, ooo_len * sizeof(tl_record_t));
        if (mv->active_ooo == NULL) {
            tl_memview_release(mv);
            return TL_ENOMEM;
        }
        memcpy(mv->active_ooo, mt->active_ooo.data, ooo_len * sizeof(tl_record_t));
        mv->active_ooo_len = ooo_len;

        /* Sort the snapshot copy (original stays unsorted) */
        qsort(mv->active_ooo, mv->active_ooo_len, sizeof(tl_record_t),
              compare_records_by_ts);

        /* Update bounds */
        if (mv->active_ooo[0].ts < mv->min_ts)
            mv->min_ts = mv->active_ooo[0].ts;
        if (mv->active_ooo[ooo_len - 1].ts > mv->max_ts)
            mv->max_ts = mv->active_ooo[ooo_len - 1].ts;
    }

    /* Copy active_tombs */
    if (tombs_len > 0) {
        mv->active_tombs = tl__malloc(alloc, tombs_len * sizeof(tl_interval_t));
        if (mv->active_tombs == NULL) {
            tl_memview_release(mv);
            return TL_ENOMEM;
        }
        memcpy(mv->active_tombs, mt->active_tombs.data,
               tombs_len * sizeof(tl_interval_t));
        mv->active_tombs_len = tombs_len;
    }

    *out = mv;
    return TL_OK;
}

void tl_memview_release(tl_memview_t* mv) {
    if (mv == NULL) return;

    const tl_allocator_t* alloc = mv->alloc;

    /* Release pinned memruns */
    for (size_t i = 0; i < mv->sealed_len; i++) {
        if (mv->sealed[i] != NULL) {
            tl_memrun_release(mv->sealed[i]);
        }
    }
    if (mv->sealed != NULL) tl__free(alloc, mv->sealed);

    /* Free copied active data */
    if (mv->active_run != NULL) tl__free(alloc, mv->active_run);
    if (mv->active_ooo != NULL) tl__free(alloc, mv->active_ooo);
    if (mv->active_tombs != NULL) tl__free(alloc, mv->active_tombs);

    tl__free(alloc, mv);
}

bool tl_memview_empty(const tl_memview_t* mv) {
    if (mv == NULL) return true;

    /* Check active data */
    if (mv->active_run_len > 0 || mv->active_ooo_len > 0 ||
        mv->active_tombs_len > 0) {
        return false;
    }

    /* Check sealed memruns */
    for (size_t i = 0; i < mv->sealed_len; i++) {
        if (!tl_memrun_empty(mv->sealed[i])) {
            return false;
        }
    }

    return true;
}

size_t tl_memview_record_count(const tl_memview_t* mv) {
    if (mv == NULL) return 0;

    size_t count = mv->active_run_len + mv->active_ooo_len;

    for (size_t i = 0; i < mv->sealed_len; i++) {
        count += tl_memrun_record_count(mv->sealed[i]);
    }

    return count;
}
