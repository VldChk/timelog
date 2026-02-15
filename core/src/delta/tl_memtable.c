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

    mt->alloc = alloc;

    tl_recvec_init(&mt->active_run, alloc);
    tl_seqvec_init(&mt->active_run_seqs, alloc);
    tl_recvec_init(&mt->ooo_head, alloc);
    tl_seqvec_init(&mt->ooo_head_seqs, alloc);
    tl_intervals_init(&mt->active_tombs, alloc);

    /* Preallocate: seal path must not realloc */
    mt->sealed = TL_NEW_ARRAY(alloc, tl_memrun_t*, sealed_max_runs);
    if (mt->sealed == NULL) {
        tl_recvec_destroy(&mt->active_run);
        tl_seqvec_destroy(&mt->active_run_seqs);
        tl_recvec_destroy(&mt->ooo_head);
        tl_seqvec_destroy(&mt->ooo_head_seqs);
        tl_intervals_destroy(&mt->active_tombs);
        return TL_ENOMEM;
    }
    mt->sealed_head = 0;
    mt->sealed_len = 0;
    mt->sealed_max_runs = sealed_max_runs;
    mt->sealed_epoch = 0;

    mt->memtable_max_bytes = memtable_max_bytes;
    mt->ooo_budget_bytes = ooo_budget_bytes;
    mt->ooo_chunk_records = 0;  /* Derived below */
    mt->ooo_run_limit = TL_DEFAULT_OOO_RUN_LIMIT;

    mt->last_inorder_ts = TL_TS_MIN;
    mt->active_bytes_est = 0;
    mt->epoch = 0;

    mt->ooo_runs = NULL;
    mt->ooo_head_sorted = true;
    mt->ooo_head_last_ts = TL_TS_MIN;
    mt->ooo_head_last_handle = 0;
    mt->ooo_next_gen = 0;

    /* Derive OOO chunk size from budget (bounded).
     * Use head-record footprint (record + seq watermark) to avoid
     * optimistic chunk sizing that can overshoot OOO budget pressure. */
    size_t ooo_head_record_bytes = TL_RECORD_SIZE + sizeof(tl_seq_t);
    size_t budget_records = (ooo_head_record_bytes == 0)
        ? 0
        : (ooo_budget_bytes / ooo_head_record_bytes);
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

    for (size_t i = 0; i < mt->sealed_len; i++) {
        size_t idx = tl_memtable_sealed_index(mt, i);
        if (mt->sealed[idx] != NULL) {
            tl_memrun_release(mt->sealed[idx]);
        }
    }

    if (mt->sealed != NULL) {
        tl__free(mt->alloc, (void*)mt->sealed);
        mt->sealed = NULL;
    }
    mt->sealed_len = 0;
    mt->sealed_head = 0;
    mt->sealed_epoch = 0;

    tl_recvec_destroy(&mt->active_run);
    tl_seqvec_destroy(&mt->active_run_seqs);
    tl_recvec_destroy(&mt->ooo_head);
    tl_seqvec_destroy(&mt->ooo_head_seqs);
    tl_intervals_destroy(&mt->active_tombs);
    if (mt->ooo_runs != NULL) {
        tl_ooorunset_release(mt->ooo_runs);
        mt->ooo_runs = NULL;
    }
}

/*===========================================================================
 * Insert Operations
 *===========================================================================*/

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
    size_t rec_bytes = TL_RECORD_SIZE + sizeof(tl_seq_t);
    if (tl__alloc_would_overflow(count, rec_bytes)) {
        mt->active_bytes_est = SIZE_MAX;
        return;
    }
    memtable_add_bytes(mt, count * rec_bytes);
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
        mt->active_bytes_est = SIZE_MAX;
        return;
    }

    size_t bytes = diff * sizeof(tl_interval_t);

    if (after_len > before_len) {
        memtable_add_bytes(mt, bytes);
    } else {
        if (mt->active_bytes_est < bytes) {
            mt->active_bytes_est = SIZE_MAX;
        } else {
            mt->active_bytes_est -= bytes;
        }
    }
}

static size_t memtable_ooo_bytes_est(const tl_memtable_t* mt) {
    size_t head_len = tl_recvec_len(&mt->ooo_head);
    size_t runs_len = tl_ooorunset_total_len(mt->ooo_runs);

    size_t bytes = 0;

    if (head_len > 0) {
        size_t head_bytes = TL_RECORD_SIZE + sizeof(tl_seq_t);
        if (tl__alloc_would_overflow(head_len, head_bytes)) {
            return SIZE_MAX;
        }
        bytes += head_len * head_bytes;
    }

    if (runs_len > 0) {
        if (tl__alloc_would_overflow(runs_len, TL_RECORD_SIZE)) {
            return SIZE_MAX;
        }
        if (bytes > SIZE_MAX - runs_len * TL_RECORD_SIZE) {
            return SIZE_MAX;
        }
        bytes += runs_len * TL_RECORD_SIZE;
    }

    return bytes;
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

static tl_status_t memtable_collect_drop(tl_memtable_t* mt,
                                         tl_record_t** dropped,
                                         size_t* dropped_len,
                                         size_t* dropped_cap,
                                         tl_ts_t ts,
                                         tl_handle_t handle) {
    if (dropped == NULL || dropped_len == NULL || dropped_cap == NULL) {
        return TL_OK;
    }

    if (*dropped_len >= *dropped_cap) {
        size_t new_cap = (*dropped_cap == 0) ? 64 : (*dropped_cap * 2);
        if (tl__alloc_would_overflow(new_cap, sizeof(tl_record_t))) {
            return TL_EOVERFLOW;
        }
        tl_record_t* new_arr = tl__realloc(mt->alloc, *dropped,
                                           new_cap * sizeof(tl_record_t));
        if (new_arr == NULL) {
            return TL_ENOMEM;
        }
        *dropped = new_arr;
        *dropped_cap = new_cap;
    }

    (*dropped)[*dropped_len].ts = ts;
    (*dropped)[*dropped_len].handle = handle;
    (*dropped_len)++;
    return TL_OK;
}

static tl_status_t memtable_flush_ooo_head(tl_memtable_t* mt,
                                           bool required,
                                           tl_seq_t applied_seq,
                                           tl_record_t** dropped,
                                           size_t* dropped_len,
                                           size_t* dropped_cap) {
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
    if (head_len > SIZE_MAX / sizeof(tl_seq_t)) {
        return TL_EOVERFLOW;
    }

    size_t bytes = head_len * sizeof(tl_record_t);
    size_t seq_bytes = head_len * sizeof(tl_seq_t);
    tl_record_t* copy = tl__malloc(mt->alloc, bytes);
    if (copy == NULL) {
        return TL_ENOMEM;
    }
    tl_seq_t* copy_seqs = tl__malloc(mt->alloc, seq_bytes);
    if (copy_seqs == NULL) {
        tl__free(mt->alloc, copy);
        return TL_ENOMEM;
    }

    memcpy(copy, tl_recvec_data(&mt->ooo_head), bytes);
    memcpy(copy_seqs, tl_seqvec_data(&mt->ooo_head_seqs), seq_bytes);

    if (!mt->ooo_head_sorted && head_len > 1) {
        tl_recvec_t tmp = {
            .data = copy,
            .len = head_len,
            .cap = head_len,
            .alloc = mt->alloc
        };
        tl_status_t sort_st = tl_recvec_sort_with_seqs(&tmp, copy_seqs);
        if (sort_st != TL_OK) {
            tl__free(mt->alloc, copy_seqs);
            tl__free(mt->alloc, copy);
            return sort_st;
        }
    }

    tl_intervals_imm_t tombs = tl_intervals_as_imm(&mt->active_tombs);
    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, tombs);

    size_t out_len = 0;
    for (size_t i = 0; i < head_len; i++) {
        tl_seq_t tomb_seq = 0;
        if (tombs.len > 0) {
            tomb_seq = tl_intervals_cursor_max_seq(&cur, copy[i].ts);
        }
        if (tomb_seq > copy_seqs[i]) {
            tl_status_t drop_st = memtable_collect_drop(mt, dropped, dropped_len,
                                                        dropped_cap, copy[i].ts,
                                                        copy[i].handle);
            if (drop_st != TL_OK) {
                tl__free(mt->alloc, copy_seqs);
                tl__free(mt->alloc, copy);
                return drop_st;
            }
            continue;
        }
        copy[out_len++] = copy[i];
    }

    tl__free(mt->alloc, copy_seqs);

    size_t dropped_count = head_len - out_len;
    size_t dec = 0;
    bool dec_valid = true;
    if (head_len > 0) {
        if (!tl__alloc_would_overflow(head_len, sizeof(tl_seq_t))) {
            dec = head_len * sizeof(tl_seq_t);
        } else {
            dec_valid = false;
        }
        if (dec_valid && dropped_count > 0) {
            if (!tl__alloc_would_overflow(dropped_count, TL_RECORD_SIZE)) {
                size_t drop_bytes = dropped_count * TL_RECORD_SIZE;
                if (dec <= SIZE_MAX - drop_bytes) {
                    dec += drop_bytes;
                } else {
                    dec_valid = false;
                }
            } else {
                dec_valid = false;
            }
        }
    }

    if (out_len == 0) {
        tl__free(mt->alloc, copy);
        tl_recvec_clear(&mt->ooo_head);
        tl_seqvec_clear(&mt->ooo_head_seqs);
        mt->ooo_head_sorted = true;
        mt->ooo_head_last_ts = TL_TS_MIN;
        mt->ooo_head_last_handle = 0;
        if (!dec_valid) {
            mt->active_bytes_est = SIZE_MAX;
        } else if (mt->active_bytes_est < dec) {
            mt->active_bytes_est = SIZE_MAX;
        } else {
            mt->active_bytes_est -= dec;
        }
        mt->epoch++;
        return TL_OK;
    }

    uint64_t gen = ++mt->ooo_next_gen;
    tl_ooorun_t* run = NULL;
    tl_status_t st = tl_ooorun_create(mt->alloc, copy, out_len, applied_seq,
                                      gen, &run);
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
    tl_seqvec_clear(&mt->ooo_head_seqs);
    mt->ooo_head_sorted = true;
    mt->ooo_head_last_ts = TL_TS_MIN;
    mt->ooo_head_last_handle = 0;

    mt->epoch++;
    if (!dec_valid) {
        mt->active_bytes_est = SIZE_MAX;
    } else if (mt->active_bytes_est < dec) {
        mt->active_bytes_est = SIZE_MAX;
    } else {
        mt->active_bytes_est -= dec;
    }

    return TL_OK;
}

tl_status_t tl_memtable_insert(tl_memtable_t* mt, tl_ts_t ts, tl_handle_t handle,
                                tl_seq_t seq) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(seq > 0);

    tl_status_t st;

    if (tl_recvec_len(&mt->active_run) == 0 ||
        ts >= mt->last_inorder_ts) {
        /* In-order: append to run */
        size_t run_len = tl_recvec_len(&mt->active_run);
        if (run_len == SIZE_MAX) {
            return TL_ENOMEM;
        }
        st = tl_recvec_reserve(&mt->active_run, run_len + 1);
        if (st != TL_OK) {
            return st;
        }
        st = tl_seqvec_reserve(&mt->active_run_seqs, run_len + 1);
        if (st != TL_OK) {
            return st;
        }
        st = tl_recvec_push(&mt->active_run, ts, handle);
        TL_ASSERT(st == TL_OK);
        st = tl_seqvec_push(&mt->active_run_seqs, seq);
        TL_ASSERT(st == TL_OK);
        mt->last_inorder_ts = ts;
    } else {
        /* Out-of-order: append to OOO head (sorted on flush/seal). */
        size_t head_len = tl_recvec_len(&mt->ooo_head);
        if (head_len == SIZE_MAX) {
            return TL_ENOMEM;
        }
        st = tl_recvec_reserve(&mt->ooo_head, head_len + 1);
        if (st != TL_OK) {
            return st;
        }
        st = tl_seqvec_reserve(&mt->ooo_head_seqs, head_len + 1);
        if (st != TL_OK) {
            return st;
        }
        st = tl_recvec_push(&mt->ooo_head, ts, handle);
        TL_ASSERT(st == TL_OK);
        st = tl_seqvec_push(&mt->ooo_head_seqs, seq);
        TL_ASSERT(st == TL_OK);
        ooo_head_note_append(mt, ts, handle);
    }

    mt->epoch++;
    memtable_add_record_bytes(mt, 1);

    /* Best-effort head flush when threshold reached */
    if (tl_recvec_len(&mt->ooo_head) >= mt->ooo_chunk_records) {
        tl_status_t flush_st = memtable_flush_ooo_head(mt, false, seq,
                                                       NULL, NULL, NULL);
        if (flush_st != TL_OK) {
            return TL_EBUSY; /* Insert succeeded, flush failed */
        }
    }

    return TL_OK;
}

/** Check if batch is sorted by timestamp (full scan, no sampling). */
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
                                      uint32_t flags,
                                      tl_seq_t seq) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(seq > 0);
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
        st = tl_seqvec_reserve(&mt->active_run_seqs, new_cap);
        if (st != TL_OK) {
            return st;
        }

        /* Cannot fail after reserve (memcpy is all-or-nothing) */
        st = tl_recvec_push_n(&mt->active_run, records, n);
        if (st != TL_OK) {
            return st;
        }
        st = tl_seqvec_push_n_const(&mt->active_run_seqs, seq, n);
        TL_ASSERT(st == TL_OK);

        mt->last_inorder_ts = records[n - 1].ts;
        inserted = n;
    } else {
        /* Slow path: pre-reserve both vectors for all-or-nothing semantics */
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
        st = tl_seqvec_reserve(&mt->active_run_seqs, run_len + n);
        if (st != TL_OK) {
            return st;
        }

        st = tl_recvec_reserve(&mt->ooo_head, ooo_len + n);
        if (st != TL_OK) {
            return st;  /* No records inserted, clean failure */
        }
        st = tl_seqvec_reserve(&mt->ooo_head_seqs, ooo_len + n);
        if (st != TL_OK) {
            return st;
        }

        /* Loop: push/insert cannot fail on allocation after pre-reserve */
        for (size_t i = 0; i < n; i++) {
            tl_ts_t ts = records[i].ts;
            tl_handle_t handle = records[i].handle;

            if (tl_recvec_len(&mt->active_run) == 0 || ts >= mt->last_inorder_ts) {
                st = tl_recvec_push(&mt->active_run, ts, handle);
                /* Capacity guaranteed, can only fail on programming error */
                TL_ASSERT(st == TL_OK);
                st = tl_seqvec_push(&mt->active_run_seqs, seq);
                TL_ASSERT(st == TL_OK);
                mt->last_inorder_ts = ts;
            } else {
                /* OOO head append (sorted on flush/seal) */
                st = tl_recvec_push(&mt->ooo_head, ts, handle);
                /* Capacity guaranteed, can only fail on programming error */
                TL_ASSERT(st == TL_OK);
                st = tl_seqvec_push(&mt->ooo_head_seqs, seq);
                TL_ASSERT(st == TL_OK);
                ooo_head_note_append(mt, ts, handle);
            }
            inserted++;
        }
    }

    mt->epoch++;
    memtable_add_record_bytes(mt, inserted);

    /* Best-effort head flush when threshold reached */
    if (tl_recvec_len(&mt->ooo_head) >= mt->ooo_chunk_records) {
        tl_status_t flush_st = memtable_flush_ooo_head(mt, false, seq,
                                                       NULL, NULL, NULL);
        if (flush_st != TL_OK) {
            return TL_EBUSY; /* Inserted all records, flush failed */
        }
    }

    return TL_OK;
}

tl_status_t tl_memtable_insert_tombstone(tl_memtable_t* mt, tl_ts_t t1, tl_ts_t t2,
                                          tl_seq_t seq) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(seq > 0);

    /* Delegate to tl_intervals which handles validation and coalescing */
    size_t before_len = tl_intervals_len(&mt->active_tombs);
    tl_status_t st = tl_intervals_insert(&mt->active_tombs, t1, t2, seq);

    if (st == TL_OK && t1 < t2) {
        /* Only update metadata if actual insert happened (not empty interval) */
        mt->epoch++;
        size_t after_len = tl_intervals_len(&mt->active_tombs);
        memtable_adjust_tomb_bytes(mt, before_len, after_len);
    }

    return st;
}

tl_status_t tl_memtable_insert_tombstone_unbounded(tl_memtable_t* mt, tl_ts_t t1,
                                                    tl_seq_t seq) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(seq > 0);

    size_t before_len = tl_intervals_len(&mt->active_tombs);
    tl_status_t st = tl_intervals_insert_unbounded(&mt->active_tombs, t1, seq);

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

    if (mt->active_bytes_est >= mt->memtable_max_bytes) {
        return true;
    }

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

tl_status_t tl_memtable_seal_ex(tl_memtable_t* mt, tl_mutex_t* mu, tl_cond_t* cond,
                                 tl_seq_t applied_seq,
                                 tl_record_t** out_dropped,
                                 size_t* out_dropped_len) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(mu != NULL);
    TL_ASSERT(applied_seq > 0);

    if (out_dropped != NULL && out_dropped_len != NULL) {
        *out_dropped = NULL;
        *out_dropped_len = 0;
    }

    tl_record_t* dropped = NULL;
    size_t dropped_len = 0;
    size_t dropped_cap = 0;

    /* Step 1: Nothing to seal? */
    if (tl_memtable_is_active_empty(mt)) {
        return TL_OK; /* Nothing to seal */
    }

    /* Step 2: Check queue capacity */
    TL_LOCK(mu, TL_LOCK_MEMTABLE_MU);
    if (mt->sealed_len >= mt->sealed_max_runs) {
        TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);
        return TL_EBUSY; /* Active state PRESERVED */
    }
    TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);

    /* Step 3: Pre-allocate memrun struct before detaching arrays.
     * This preserves active state on ENOMEM (arrays not yet taken). */
    tl_memrun_t* mr = NULL;
    tl_status_t alloc_st = tl_memrun_alloc(mt->alloc, &mr);
    if (alloc_st != TL_OK) {
        return TL_ENOMEM; /* Active state PRESERVED */
    }

    /* Step 4: Flush OOO head */
    tl_status_t flush_st = memtable_flush_ooo_head(mt, true, applied_seq,
                                                   &dropped, &dropped_len, &dropped_cap);
    if (flush_st != TL_OK) {
        if (dropped != NULL) {
            tl__free(mt->alloc, dropped);
        }
        tl__free(mt->alloc, mr);
        return flush_st; /* Active state PRESERVED */
    }

    /* Step 5: Take ownership of active arrays */
    size_t run_len = 0;
    size_t run_seqs_len = 0;
    size_t tombs_len = 0;

    tl_record_t* run = tl_recvec_take(&mt->active_run, &run_len);
    tl_seq_t* run_seqs = tl_seqvec_take(&mt->active_run_seqs, &run_seqs_len);
    tl_interval_t* tombs = tl_intervals_take(&mt->active_tombs, &tombs_len);
    tl_ooorunset_t* ooo_runs = mt->ooo_runs;
    mt->ooo_runs = NULL;

    if (run_len != run_seqs_len) {
        if (run != NULL) tl__free(mt->alloc, run);
        if (run_seqs != NULL) tl__free(mt->alloc, run_seqs);
        if (ooo_runs != NULL) tl_ooorunset_release(ooo_runs);
        if (tombs != NULL) tl__free(mt->alloc, tombs);
        if (dropped != NULL) tl__free(mt->alloc, dropped);
        tl__free(mt->alloc, mr);
        return TL_EINTERNAL;
    }

    if (run_len > 0 && tombs_len > 0) {
        tl_intervals_imm_t tombs_imm = { .data = tombs, .len = tombs_len };
        tl_intervals_cursor_t cur;
        tl_intervals_cursor_init(&cur, tombs_imm);
        size_t out_len = 0;
        for (size_t i = 0; i < run_len; i++) {
            tl_seq_t tomb_seq = tl_intervals_cursor_max_seq(&cur, run[i].ts);
            if (tomb_seq > run_seqs[i]) {
                tl_status_t drop_st = memtable_collect_drop(mt, &dropped, &dropped_len,
                                                            &dropped_cap, run[i].ts,
                                                            run[i].handle);
                if (drop_st != TL_OK) {
                    if (run != NULL) tl__free(mt->alloc, run);
                    if (run_seqs != NULL) tl__free(mt->alloc, run_seqs);
                    if (ooo_runs != NULL) tl_ooorunset_release(ooo_runs);
                    if (tombs != NULL) tl__free(mt->alloc, tombs);
                    if (dropped != NULL) tl__free(mt->alloc, dropped);
                    tl__free(mt->alloc, mr);
                    return drop_st;
                }
                continue;
            }
            run[out_len++] = run[i];
        }
        run_len = out_len;
    }

    if (run_seqs != NULL) {
        tl__free(mt->alloc, run_seqs);
        run_seqs = NULL;
    }

    /* Step 6: Initialize memrun in-place */
    tl_status_t init_st = tl_memrun_init(mr, mt->alloc,
                                         run, run_len,
                                         ooo_runs,
                                         tombs, tombs_len,
                                         applied_seq);
    if (init_st != TL_OK) {
        /* Internal invariant violation - avoid leaks, but data is lost */
        if (run != NULL) tl__free(mt->alloc, run);
        if (ooo_runs != NULL) tl_ooorunset_release(ooo_runs);
        if (tombs != NULL) tl__free(mt->alloc, tombs);
        if (dropped != NULL) tl__free(mt->alloc, dropped);
        tl__free(mt->alloc, mr);
        return TL_EINTERNAL;
    }

    /* Step 7: Push to sealed queue */
    TL_LOCK(mu, TL_LOCK_MEMTABLE_MU);
    if (mt->sealed_len >= mt->sealed_max_runs) {
        TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);
        tl_memrun_release(mr);
        if (dropped != NULL) tl__free(mt->alloc, dropped);
        return TL_EBUSY;
    }
    TL_ASSERT(mt->sealed_len < mt->sealed_max_runs);
    size_t idx = tl_memtable_sealed_index(mt, mt->sealed_len);
    mt->sealed[idx] = mr;
    mt->sealed_len++;
    mt->sealed_epoch++;
    TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);

    /* Step 8: Reset active state */
    mt->last_inorder_ts = TL_TS_MIN;
    mt->active_bytes_est = 0;
    mt->epoch++;  /* Memtable state changed (active -> sealed) */
    tl_recvec_clear(&mt->ooo_head);
    tl_seqvec_clear(&mt->ooo_head_seqs);
    mt->ooo_head_sorted = true;
    mt->ooo_head_last_ts = TL_TS_MIN;
    mt->ooo_head_last_handle = 0;
    mt->ooo_next_gen = 0;

    /* Signal waiters if provided */
    if (cond != NULL) {
        tl_cond_signal(cond);
    }

    if (out_dropped != NULL && out_dropped_len != NULL) {
        *out_dropped = dropped;
        *out_dropped_len = dropped_len;
    } else if (dropped != NULL) {
        tl__free(mt->alloc, dropped);
    }

    return TL_OK;
}

tl_status_t tl_memtable_seal(tl_memtable_t* mt, tl_mutex_t* mu, tl_cond_t* cond,
                              tl_seq_t applied_seq) {
    return tl_memtable_seal_ex(mt, mu, cond, applied_seq, NULL, NULL);
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

    if (!debug_records_sorted(tl_recvec_data(&mt->active_run),
                              tl_recvec_len(&mt->active_run))) {
        return false;
    }
    if (tl_seqvec_len(&mt->active_run_seqs) != tl_recvec_len(&mt->active_run)) {
        return false;
    }

    if (tl_seqvec_len(&mt->ooo_head_seqs) != tl_recvec_len(&mt->ooo_head)) {
        return false;
    }

    /* OOO head is unsorted during append; sorted on flush/seal */

    if (!tl_intervals_validate(&mt->active_tombs)) {
        return false;
    }

    if (mt->sealed_len > mt->sealed_max_runs) {
        return false;
    }
    if (mt->sealed_head >= mt->sealed_max_runs) {
        return false;
    }

    for (size_t i = 0; i < mt->sealed_len; i++) {
        if (tl_memtable_sealed_at(mt, i) == NULL) {
            return false;
        }
    }

    return true;
}

#endif /* TL_DEBUG */
