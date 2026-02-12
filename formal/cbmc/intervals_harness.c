#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include "../../core/src/internal/tl_intervals.h"

/* CBMC nondet declarations */
extern size_t nondet_size_t(void);
extern uint64_t nondet_u64(void);
extern int64_t nondet_i64(void);
extern _Bool nondet_bool(void);

void __CPROVER_assume(_Bool);
void __CPROVER_assert(_Bool, const char *);

/* Minimal allocator shims for harnessing container logic. */
void* tl__realloc(tl_alloc_ctx_t* ctx, void* ptr, size_t new_size) {
    (void)ctx;
    (void)ptr;
    if (new_size == 0) {
        return NULL;
    }
    return malloc(new_size);
}

void tl__free(tl_alloc_ctx_t* ctx, void* ptr) {
    (void)ctx;
    free(ptr);
}

#include "../../core/src/internal/tl_intervals.c"

static void assert_interval_invariants(const tl_intervals_t* iv) {
    if (iv->len == 0) {
        return;
    }

    for (size_t i = 0; i < iv->len; ++i) {
        const tl_interval_t* cur = &iv->data[i];
        __CPROVER_assert(cur->max_seq > 0, "interval max_seq is always positive");
        __CPROVER_assert(cur->end_unbounded || cur->start < cur->end,
                         "bounded intervals are non-empty");

        if (i > 0) {
            const tl_interval_t* prev = &iv->data[i - 1];
            __CPROVER_assert(prev->start <= cur->start,
                             "intervals are sorted by start");
            __CPROVER_assert(prev->end_unbounded || prev->end <= cur->start,
                             "intervals do not overlap");
            __CPROVER_assert(!( !prev->end_unbounded && prev->end == cur->start &&
                                prev->max_seq == cur->max_seq),
                             "adjacent equal-seq intervals are coalesced");
        }
    }
}

void harness_intervals_insert_invariants(void) {
    tl_alloc_ctx_t alloc = {0};
    tl_intervals_t iv;
    tl_intervals_init(&iv, &alloc);

    const size_t steps = nondet_size_t();
    __CPROVER_assume(steps <= 6);

    for (size_t i = 0; i < steps; ++i) {
        tl_ts_t t1 = nondet_i64();
        tl_ts_t t2 = nondet_i64();
        tl_seq_t seq = nondet_u64();
        if (seq == 0) {
            seq = 1;
        }

        tl_status_t st;
        if (nondet_bool()) {
            if (t1 <= t2) {
                st = tl_intervals_insert(&iv, t1, t2, seq);
            } else {
                st = TL_EINVAL;
            }
        } else {
            st = tl_intervals_insert_unbounded(&iv, t1, seq);
        }

        __CPROVER_assert(st == TL_OK || st == TL_EINVAL || st == TL_ENOMEM,
                         "insert returns expected status");
        assert_interval_invariants(&iv);
    }

    tl_intervals_destroy(&iv);
}

void harness_intervals_union_and_max_seq(void) {
    tl_alloc_ctx_t alloc = {0};
    tl_intervals_t a, b, out;
    tl_intervals_init(&a, &alloc);
    tl_intervals_init(&b, &alloc);
    tl_intervals_init(&out, &alloc);

    size_t na = nondet_size_t();
    size_t nb = nondet_size_t();
    __CPROVER_assume(na <= 4);
    __CPROVER_assume(nb <= 4);

    for (size_t i = 0; i < na; ++i) {
        tl_ts_t lo = nondet_i64();
        tl_ts_t hi = nondet_i64();
        __CPROVER_assume(lo <= hi);
        (void)tl_intervals_insert(&a, lo, hi, (tl_seq_t)(i + 1));
    }
    for (size_t i = 0; i < nb; ++i) {
        tl_ts_t lo = nondet_i64();
        tl_ts_t hi = nondet_i64();
        __CPROVER_assume(lo <= hi);
        (void)tl_intervals_insert(&b, lo, hi, (tl_seq_t)(i + 3));
    }

    tl_status_t st = tl_intervals_union(&out, &a, &b);
    __CPROVER_assert(st == TL_OK || st == TL_ENOMEM, "union status");

    if (st == TL_OK) {
        assert_interval_invariants(&out);

        tl_ts_t probes[5] = { TL_TS_MIN, -1, 0, 1, TL_TS_MAX };
        for (size_t i = 0; i < 5; ++i) {
            tl_ts_t ts = probes[i];
            tl_seq_t am = tl_intervals_max_seq(&a, ts);
            tl_seq_t bm = tl_intervals_max_seq(&b, ts);
            tl_seq_t om = tl_intervals_max_seq(&out, ts);
            __CPROVER_assert(om == (am > bm ? am : bm),
                             "union max_seq equals pointwise max");
        }
    }

    /* Overflow-sensitive boundary behavior for covered span. */
    tl_intervals_clear(&out);
    (void)tl_intervals_insert(&out, TL_TS_MIN, TL_TS_MAX, 1);
    __CPROVER_assert(tl_intervals_covered_span(&out) == TL_TS_MAX,
                     "covered_span saturates on huge boundary range");

    tl_intervals_clear(&out);
    (void)tl_intervals_insert(&out, TL_TS_MAX - 1, TL_TS_MAX, 1);
    __CPROVER_assert(tl_intervals_covered_span(&out) == 1,
                     "covered_span handles upper timestamp boundary without overflow");

    tl_intervals_destroy(&out);
    tl_intervals_destroy(&b);
    tl_intervals_destroy(&a);
}
