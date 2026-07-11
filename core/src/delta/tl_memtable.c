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

    /* Preallocated to its final capacity so the seal hot path never needs to
     * realloc and never has a partial-failure mode to roll back. */
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

    /* Pick OOO chunk size so a few chunks fit within the OOO byte budget.
     * Sizing uses the head-record footprint (record + per-record seq) instead
     * of just sizeof(tl_record_t); using the smaller value would let the head
     * grow past the budget before the threshold is crossed. */
    size_t ooo_head_record_bytes = TL_RECORD_SIZE + sizeof(tl_seq_t);
    size_t budget_records = ooo_budget_bytes / ooo_head_record_bytes;
    size_t chunk = budget_records / TL_OOO_TARGET_RUNS;
    if (chunk < TL_OOO_CHUNK_MIN_RECORDS) {
        chunk = TL_OOO_CHUNK_MIN_RECORDS;
    }
    if (chunk > TL_OOO_CHUNK_MAX_RECORDS) {
        chunk = TL_OOO_CHUNK_MAX_RECORDS;
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

static void memtable_sub_bytes(tl_memtable_t* mt, size_t dec, bool dec_valid) {
    if (!dec_valid || mt->active_bytes_est < dec) {
        mt->active_bytes_est = SIZE_MAX;
    } else {
        mt->active_bytes_est -= dec;
    }
}

static void memtable_reset_ooo_head(tl_memtable_t* mt) {
    tl_recvec_clear(&mt->ooo_head);
    tl_seqvec_clear(&mt->ooo_head_seqs);
    mt->ooo_head_sorted = true;
    mt->ooo_head_last_ts = TL_TS_MIN;
    mt->ooo_head_last_handle = 0;
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

static tl_status_t memtable_count_sorted_tomb_drops(const tl_record_t* records,
                                                    const tl_seq_t* seqs,
                                                    size_t len,
                                                    tl_intervals_imm_t tombs,
                                                    size_t* out_count) {
    TL_ASSERT(out_count != NULL);

    if (len == 0 || tombs.len == 0) {
        *out_count = 0;
        return TL_OK;
    }
    if (records == NULL || seqs == NULL) {
        return TL_EINTERNAL;
    }

    tl_intervals_cursor_t cur;
    tl_intervals_cursor_init(&cur, tombs);

    size_t count = 0;
    for (size_t i = 0; i < len; i++) {
        tl_seq_t tomb_seq = tl_intervals_cursor_max_seq(&cur, records[i].ts);
        if (tomb_seq > seqs[i]) {
            count++;
        }
    }
    *out_count = count;
    return TL_OK;
}

/*
 * Conservative opportunistic-flush gate for an unsorted OOO head: true if any
 * tombstone newer than the oldest head record overlaps the head's timestamp
 * range. O(H + T), no allocation, no sort. May return true when the exact
 * per-record count would be zero (e.g. a tombstone punching a hole between
 * head records); such false positives only delay the flush until seal, which
 * counts and drops exactly, and the head stays bounded by the OOO budget /
 * forced seal.
 */
static bool memtable_head_tombs_may_drop(const tl_memtable_t* mt,
                                         tl_intervals_imm_t tombs) {
    size_t head_len = tl_recvec_len(&mt->ooo_head);
    if (tombs.len == 0 || head_len == 0) {
        return false;
    }

    /* Only last_ts is tracked incrementally; compute min/max in one scan. */
    const tl_record_t* head = tl_recvec_data(&mt->ooo_head);
    tl_ts_t head_min = head[0].ts;
    tl_ts_t head_max = head[0].ts;
    for (size_t i = 1; i < head_len; i++) {
        head_min = TL_MIN(head_min, head[i].ts);
        head_max = TL_MAX(head_max, head[i].ts);
    }

    /* Seqs append monotonically, so seqs[0] is the oldest seq in the head; a
     * tombstone at or below it cannot drop anything (drops need strict >). */
    tl_seq_t head_min_seq = tl_seqvec_data(&mt->ooo_head_seqs)[0];

    for (size_t i = 0; i < tombs.len; i++) {
        const tl_interval_t* tomb = &tombs.data[i];
        if (tomb->start > head_max) {
            break; /* Intervals sorted by start: no later overlap possible. */
        }
        if (tomb->max_seq <= head_min_seq) {
            continue;
        }
        if (tomb->end_unbounded || tomb->end > head_min) {
            return true;
        }
    }
    return false;
}

static tl_status_t memtable_flush_ooo_head(tl_memtable_t* mt,
                                           bool required,
                                           tl_seq_t applied_seq,
                                           tl_recvec_t* dropped) {
    size_t head_len = tl_recvec_len(&mt->ooo_head);
    if (head_len == 0) {
        return TL_OK;
    }

    if (!required && mt->ooo_run_limit > 0 &&
        tl_ooorunset_count(mt->ooo_runs) >= mt->ooo_run_limit) {
        return TL_EBUSY;
    }

    bool collect_drops = (dropped != NULL);
    if (!required && !collect_drops) {
        tl_intervals_imm_t tombs = tl_intervals_as_imm(&mt->active_tombs);
        bool may_drop;
        if (mt->ooo_head_sorted || head_len <= 1) {
            /* Sorted head: exact zero-alloc cursor count. */
            size_t tomb_drops = 0;
            tl_status_t count_st = memtable_count_sorted_tomb_drops(
                tl_recvec_data(&mt->ooo_head),
                tl_seqvec_data(&mt->ooo_head_seqs),
                head_len,
                tombs,
                &tomb_drops);
            if (count_st != TL_OK) {
                return count_st;
            }
            may_drop = (tomb_drops > 0);
        } else {
            /* Unsorted head: conservative overlap scan instead of copy+sorting
             * the head just to count (the flush below would sort it again). */
            may_drop = memtable_head_tombs_may_drop(mt, tombs);
        }
        if (may_drop) {
            /* Opportunistic flushes have no callback sink. Keep the head in its
             * per-record-sequence form rather than either dropping callbacks or
             * collapsing tomb-covered records into a uniform-watermark OOO run. */
            return TL_OK;
        }
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

    size_t out_len = 0;
    if (collect_drops) {
        tl_intervals_imm_t tombs = tl_intervals_as_imm(&mt->active_tombs);
        tl_intervals_cursor_t cur;
        tl_intervals_cursor_init(&cur, tombs);

        for (size_t i = 0; i < head_len; i++) {
            tl_seq_t tomb_seq = 0;
            if (tombs.len > 0) {
                tomb_seq = tl_intervals_cursor_max_seq(&cur, copy[i].ts);
            }
            if (tomb_seq > copy_seqs[i]) {
                tl_status_t drop_st = tl_recvec_push(dropped, copy[i].ts,
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
    } else {
        out_len = head_len;
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
        memtable_reset_ooo_head(mt);
        memtable_sub_bytes(mt, dec, dec_valid);
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

    memtable_reset_ooo_head(mt);

    mt->epoch++;
    memtable_sub_bytes(mt, dec, dec_valid);

    return TL_OK;
}

tl_status_t tl_memtable_insert(tl_memtable_t* mt, tl_ts_t ts, tl_handle_t handle,
                                tl_seq_t seq) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(seq > 0);

    tl_status_t st;

    if (tl_recvec_len(&mt->active_run) == 0 ||
        ts >= mt->last_inorder_ts) {
        /* In-order fast path: append to the sorted run. */
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
        /* Out-of-order: append to the OOO head buffer. The head stays
         * unsorted until flush or seal, keeping ingest O(1). */
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

    /* Opportunistic head flush: once the head reaches the chunk size, turn it
     * into a sorted immutable run so the head buffer stays bounded. The
     * insert itself is already committed, so a flush failure only surfaces as
     * TL_EBUSY (the record IS in the log). */
    if (tl_recvec_len(&mt->ooo_head) >= mt->ooo_chunk_records) {
        tl_status_t flush_st = memtable_flush_ooo_head(mt, false, seq, NULL);
        if (flush_st != TL_OK) {
            return TL_EBUSY;
        }
    }

    return TL_OK;
}

/* Full scan: a hint of "mostly sorted" is not a guarantee, so we must verify
 * the entire batch before taking the fast-path bulk append. */
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
    (void)flags;

    if (n == 0) {
        return TL_OK;
    }

    TL_ASSERT(records != NULL);

    if (tl__alloc_would_overflow(n, sizeof(tl_record_t)) ||
        tl__alloc_would_overflow(n, sizeof(tl_seq_t))) {
        return TL_EOVERFLOW;
    }

    tl_status_t st;
    size_t inserted = 0;

    bool use_fast_path = false;
    bool first_fits = (tl_recvec_len(&mt->active_run) == 0) ||
                      (records[0].ts >= mt->last_inorder_ts);

    if (first_fits) {
        if (batch_is_sorted(records, n)) {
            use_fast_path = true;
        }
    }

    if (use_fast_path) {
        /* Bulk-append straight into the sorted run. */
        size_t len = tl_recvec_len(&mt->active_run);

        if (n > SIZE_MAX - len) {
            return TL_EOVERFLOW;
        }

        /* Reserve up front so the push step cannot fail partway through and
         * leave the batch in a half-inserted state. */
        size_t new_cap = len + n;
        st = tl_recvec_reserve(&mt->active_run, new_cap);
        if (st != TL_OK) {
            return st;
        }
        st = tl_seqvec_reserve(&mt->active_run_seqs, new_cap);
        if (st != TL_OK) {
            return st;
        }

        st = tl_recvec_push_n(&mt->active_run, records, n);
        if (st != TL_OK) {
            return st;
        }
        st = tl_seqvec_push_n_const(&mt->active_run_seqs, seq, n);
        TL_ASSERT(st == TL_OK);

        mt->last_inorder_ts = records[n - 1].ts;
        inserted = n;
    } else {
        /* Per-record path: pre-reserve worst-case capacity in both the run
         * and OOO head so each push is infallible and the whole batch is
         * all-or-nothing. */
        size_t run_len = tl_recvec_len(&mt->active_run);
        size_t ooo_len = tl_recvec_len(&mt->ooo_head);

        if (n > SIZE_MAX - run_len || n > SIZE_MAX - ooo_len) {
            return TL_EOVERFLOW;
        }

        st = tl_recvec_reserve(&mt->active_run, run_len + n);
        if (st != TL_OK) {
            return st;
        }
        st = tl_seqvec_reserve(&mt->active_run_seqs, run_len + n);
        if (st != TL_OK) {
            return st;
        }

        st = tl_recvec_reserve(&mt->ooo_head, ooo_len + n);
        if (st != TL_OK) {
            return st;
        }
        st = tl_seqvec_reserve(&mt->ooo_head_seqs, ooo_len + n);
        if (st != TL_OK) {
            return st;
        }

        for (size_t i = 0; i < n; i++) {
            tl_ts_t ts = records[i].ts;
            tl_handle_t handle = records[i].handle;

            if (tl_recvec_len(&mt->active_run) == 0 || ts >= mt->last_inorder_ts) {
                st = tl_recvec_push(&mt->active_run, ts, handle);
                TL_ASSERT(st == TL_OK);
                st = tl_seqvec_push(&mt->active_run_seqs, seq);
                TL_ASSERT(st == TL_OK);
                mt->last_inorder_ts = ts;
            } else {
                st = tl_recvec_push(&mt->ooo_head, ts, handle);
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

    if (tl_recvec_len(&mt->ooo_head) >= mt->ooo_chunk_records) {
        tl_status_t flush_st = memtable_flush_ooo_head(mt, false, seq, NULL);
        if (flush_st != TL_OK) {
            /* Records are already in the log; flush failure is signalled as
             * backpressure so the caller can retry the maintenance step. */
            return TL_EBUSY;
        }
    }

    return TL_OK;
}

tl_status_t tl_memtable_insert_tombstone(tl_memtable_t* mt, tl_ts_t t1, tl_ts_t t2,
                                          tl_seq_t seq) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(seq > 0);

    size_t before_len = tl_intervals_len(&mt->active_tombs);
    tl_status_t st = tl_intervals_insert(&mt->active_tombs, t1, t2, seq);

    /* Empty intervals (t1 == t2) succeed but are no-ops; skip bookkeeping in
     * that case so the epoch only ticks on observable state changes. */
    if (st == TL_OK && t1 < t2) {
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
        return false;  /* 0 means "no budget configured" */
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

    if (tl_memtable_is_active_empty(mt)) {
        return TL_OK;
    }

    /* Reject quickly when the sealed queue has no room: callers must apply
     * backpressure or wait. The same check is repeated under the lock at
     * publish time because flushers can drain entries concurrently. */
    TL_LOCK(mu, TL_LOCK_MEMTABLE_MU);
    if (mt->sealed_len >= mt->sealed_max_runs) {
        TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);
        return TL_EBUSY;
    }
    TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);

    tl_status_t st = TL_OK;
    tl_memrun_t* mr = NULL;
    tl_record_t* run = NULL;
    tl_seq_t* run_seqs = NULL;
    tl_interval_t* tombs = NULL;
    tl_ooorunset_t* ooo_runs = NULL;
    tl_recvec_t dropped_vec;
    tl_recvec_init(&dropped_vec, mt->alloc);

    /* Allocate the memrun shell before detaching the active arrays so that an
     * ENOMEM here leaves the writer-visible state intact and retryable. */
    st = tl_memrun_alloc(mt->alloc, &mr);
    if (st != TL_OK) {
        goto cleanup;
    }

    /* Size the drop buffer BEFORE any mutation so every push after the active
     * arrays are detached cannot need a failing allocation (failure-atomicity:
     * active state is PRESERVED on ENOMEM/EBUSY). The sorted active run and a
     * sorted OOO head get exact zero-alloc cursor counts; an unsorted head
     * uses head_len as a trivially correct upper bound instead of copy+sorting
     * it just to count — the mandatory head flush below sorts the same data
     * anyway. The over-reservation is bounded by one OOO chunk and is freed
     * with the drop buffer. */
    tl_intervals_imm_t active_tombs = tl_intervals_as_imm(&mt->active_tombs);
    size_t head_len = tl_recvec_len(&mt->ooo_head);
    size_t ooo_drop_bound = 0;
    if (active_tombs.len > 0 && head_len > 0) {
        if (mt->ooo_head_sorted || head_len <= 1) {
            st = memtable_count_sorted_tomb_drops(
                tl_recvec_data(&mt->ooo_head),
                tl_seqvec_data(&mt->ooo_head_seqs),
                head_len,
                active_tombs,
                &ooo_drop_bound);
            if (st != TL_OK) {
                goto cleanup;
            }
        } else {
            ooo_drop_bound = head_len;
        }
    }
    size_t active_drop_count = 0;
    st = memtable_count_sorted_tomb_drops(
        tl_recvec_data(&mt->active_run),
        tl_seqvec_data(&mt->active_run_seqs),
        tl_recvec_len(&mt->active_run),
        active_tombs,
        &active_drop_count);
    if (st != TL_OK) {
        goto cleanup;
    }

    if (ooo_drop_bound > SIZE_MAX - active_drop_count) {
        st = TL_EOVERFLOW;
        goto cleanup;
    }
    size_t needed_drops = ooo_drop_bound + active_drop_count;
    if (needed_drops > 0) {
        st = tl_recvec_reserve(&dropped_vec, needed_drops);
        if (st != TL_OK) {
            goto cleanup;
        }
    }

    /* Drain the OOO head into a final sorted run so the sealed memrun contains
     * a complete, immutable picture of pending out-of-order writes. */
    st = memtable_flush_ooo_head(mt, true, applied_seq, &dropped_vec);
    if (st != TL_OK) {
        goto cleanup;
    }

    /* Detach the active arrays into the memrun; from this point on the
     * memtable is empty and the new memrun owns the data. */
    size_t run_len = 0;
    size_t run_seqs_len = 0;
    size_t tombs_len = 0;

    run = tl_recvec_take(&mt->active_run, &run_len);
    run_seqs = tl_seqvec_take(&mt->active_run_seqs, &run_seqs_len);
    tombs = tl_intervals_take(&mt->active_tombs, &tombs_len);
    ooo_runs = mt->ooo_runs;
    mt->ooo_runs = NULL;

    if (run_len != run_seqs_len ||
        (run_len > 0 && (run == NULL || run_seqs == NULL))) {
        st = TL_EINTERNAL;
        goto cleanup;
    }

    if (run_len > 0 && tombs_len > 0) {
        tl_intervals_imm_t tombs_imm = { .data = tombs, .len = tombs_len };
        tl_intervals_cursor_t cur;
        tl_intervals_cursor_init(&cur, tombs_imm);
        size_t out_len = 0;
        for (size_t i = 0; i < run_len; i++) {
            tl_seq_t tomb_seq = tl_intervals_cursor_max_seq(&cur, run[i].ts);
            if (tomb_seq > run_seqs[i]) {
                /* Reserved above: this push never needs to allocate. */
                st = tl_recvec_push(&dropped_vec, run[i].ts, run[i].handle);
                if (st != TL_OK) {
                    goto cleanup;
                }
                continue;
            }
            run[out_len++] = run[i];
        }
        run_len = out_len;
    }

    tl__free(mt->alloc, run_seqs);
    run_seqs = NULL;

    st = tl_memrun_init(mr, mt->alloc,
                        run, run_len,
                        ooo_runs,
                        tombs, tombs_len,
                        applied_seq);
    if (st != TL_OK) {
        /* Invariant violation reaching this point means the arrays are no
         * longer reachable from the memtable: free them (via cleanup) so they
         * do not leak, even though the caller will lose the data. */
        st = TL_EINTERNAL;
        goto cleanup;
    }
    /* The memrun now owns the detached arrays. */
    run = NULL;
    tombs = NULL;
    ooo_runs = NULL;

    /* Publish: re-check capacity under the lock since concurrent flushers may
     * have changed the queue between the pre-check and now. */
    TL_LOCK(mu, TL_LOCK_MEMTABLE_MU);
    if (mt->sealed_len >= mt->sealed_max_runs) {
        TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);
        tl_memrun_release(mr);
        mr = NULL;
        st = TL_EBUSY;
        goto cleanup;
    }
    TL_ASSERT(mt->sealed_len < mt->sealed_max_runs);
    size_t idx = tl_memtable_sealed_index(mt, mt->sealed_len);
    mt->sealed[idx] = mr;
    mt->sealed_len++;
    mt->sealed_epoch++;
    TL_UNLOCK(mu, TL_LOCK_MEMTABLE_MU);

    mt->last_inorder_ts = TL_TS_MIN;
    mt->active_bytes_est = 0;
    mt->epoch++;
    memtable_reset_ooo_head(mt);
    mt->ooo_next_gen = 0;

    if (cond != NULL) {
        tl_cond_signal(cond);
    }

    if (out_dropped != NULL && out_dropped_len != NULL) {
        size_t dropped_len = 0;
        tl_record_t* dropped = tl_recvec_take(&dropped_vec, &dropped_len);
        if (dropped_len == 0 && dropped != NULL) {
            /* The upper-bound reservation can leave a non-NULL but empty
             * buffer; normalize so *out_dropped is NULL exactly when nothing
             * was dropped. */
            tl__free(mt->alloc, dropped);
            dropped = NULL;
        }
        *out_dropped = dropped;
        *out_dropped_len = dropped_len;
    } else {
        tl_recvec_destroy(&dropped_vec);
    }

    return TL_OK;

cleanup:
    tl__free(mt->alloc, run);
    tl__free(mt->alloc, run_seqs);
    if (ooo_runs != NULL) {
        tl_ooorunset_release(ooo_runs);
    }
    tl__free(mt->alloc, tombs);
    tl_recvec_destroy(&dropped_vec);
    tl__free(mt->alloc, mr);
    return st;
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

    /* FIFO: oldest entry sits at sealed_head; pin it for the caller. */
    tl_memrun_t* mr = tl_memtable_sealed_at(mt, 0);
    *out = tl_memrun_acquire(mr);
    return TL_OK;
}

void tl_memtable_pop_oldest(tl_memtable_t* mt, tl_cond_t* cond) {
    TL_ASSERT(mt != NULL);
    TL_ASSERT(mt->sealed_len > 0);

    size_t idx = tl_memtable_sealed_index(mt, 0);
    tl_memrun_t* mr = mt->sealed[idx];
    mt->sealed[idx] = NULL;

    /* Advance ring head; reset to 0 when the queue empties to keep the
     * starting index predictable across drain cycles. */
    mt->sealed_head++;
    if (mt->sealed_head == mt->sealed_max_runs) {
        mt->sealed_head = 0;
    }
    mt->sealed_len--;
    if (mt->sealed_len == 0) {
        mt->sealed_head = 0;
    }
    mt->sealed_epoch++;

    tl_memrun_release(mr);

    /* Bump the visible epoch so memview caches recognise the queue shrank. */
    mt->epoch++;

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

    /* Track an absolute deadline against the monotonic clock so spurious
     * wakeups cannot extend the total wait, and so that each retry only
     * blocks for the time still remaining. */
    uint64_t start_ms = tl_monotonic_ms();
    uint64_t deadline_ms = start_ms + timeout_ms;

    while (mt->sealed_len >= mt->sealed_max_runs) {
        uint64_t now_ms = tl_monotonic_ms();

        if (now_ms >= deadline_ms) {
            break;
        }

        uint64_t remaining = deadline_ms - now_ms;
        uint32_t wait_ms = (remaining > UINT32_MAX) ? UINT32_MAX : (uint32_t)remaining;

        bool signaled = tl_cond_timedwait(cond, mu, wait_ms);
        if (!signaled) {
            break;
        }
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

    /* No sortedness check on the OOO head: it is intentionally unsorted
     * during ingest and only sorted when flushed or sealed. */

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
