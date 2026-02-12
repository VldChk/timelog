#include <stdint.h>
#include "../../core/src/query/tl_filter.h"

extern uint64_t nondet_u64(void);
extern int64_t nondet_i64(void);

void __CPROVER_assert(_Bool, const char *);

/* Simple one-record model for merge iterator dependencies. */
static int g_emitted = 0;
static tl_record_t g_record;
static tl_seq_t g_watermark;
static tl_seq_t g_tomb_seq;

tl_status_t tl_kmerge_iter_next(tl_kmerge_iter_t* it, tl_record_t* out, tl_seq_t* out_watermark) {
    (void)it;
    if (g_emitted) {
        return TL_EOF;
    }
    g_emitted = 1;
    *out = g_record;
    *out_watermark = g_watermark;
    return TL_OK;
}


void tl_kmerge_iter_seek(tl_kmerge_iter_t* it, tl_ts_t target) {
    (void)it;
    (void)target;
}

tl_seq_t tl_intervals_cursor_max_seq(tl_intervals_cursor_t* cur, tl_ts_t ts) {
    (void)cur;
    (void)ts;
    return g_tomb_seq;
}

bool tl_intervals_cursor_skip_to(tl_intervals_cursor_t* cur, tl_ts_t ts, tl_ts_t* out) {
    (void)cur;
    *out = ts;
    return true;
}

#include "../../core/src/query/tl_filter.c"

void harness_filter_tombstone_watermark_predicate(void) {
    tl_kmerge_iter_t merge = {0};
    tl_filter_iter_t it;
    tl_record_t out = {0};

    g_record.ts = nondet_i64();
    g_record.handle = nondet_u64();
    g_watermark = nondet_u64();
    g_tomb_seq = nondet_u64();
    g_emitted = 0;

    tl_interval_t interval = {
        .start = TL_TS_MIN,
        .end = 0,
        .end_unbounded = true,
        .max_seq = 1,
    };
    tl_intervals_imm_t tombs = { .data = &interval, .len = 1 };

    tl_filter_iter_init(&it, &merge, tombs);

    tl_status_t st = tl_filter_iter_next(&it, &out);
    if (g_tomb_seq > g_watermark) {
        __CPROVER_assert(st == TL_EOF,
                         "record is filtered exactly when tomb_seq > watermark");
    } else {
        __CPROVER_assert(st == TL_OK,
                         "record is visible when tomb_seq <= watermark");
        __CPROVER_assert(out.ts == g_record.ts && out.handle == g_record.handle,
                         "visible record is returned unchanged");
    }
}
