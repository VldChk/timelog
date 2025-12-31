#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/timelog/timelog.h"
#include "../src/internal/tl_thread.h"
#include "../src/internal/tl_atomic.h"
#include "../src/internal/tl_defs.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))
#define TEST_ASSERT_GE(a, b) TEST_ASSERT((a) >= (b))
#define TEST_ASSERT_LE(a, b) TEST_ASSERT((a) <= (b))

/*
 * Platform-specific sleep for short yields in concurrency tests.
 */
#if defined(_WIN32)
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
static void test_sleep_ms(uint32_t ms) { Sleep(ms); }
#else
#include <unistd.h>
static void test_sleep_ms(uint32_t ms) { usleep(ms * 1000); }
#endif

typedef struct writer_ctx {
    tl_timelog_t*  tl;
    tl_atomic_u32_t stop;
    tl_atomic_u32_t error;
    uint32_t       flush_every;
    tl_ts_t        ts;
} writer_ctx_t;

static void* writer_thread_fn(void* arg) {
    writer_ctx_t* ctx = (writer_ctx_t*)arg;
    tl_ts_t ts = ctx->ts;
    uint32_t count = 0;

    while (tl_atomic_u32_load(&ctx->stop) == 0) {
        tl_status_t st = tl_append(ctx->tl, ts, (tl_handle_t)ts);
        if (st == TL_EBUSY) {
            st = tl_flush(ctx->tl);
        }
        if (st != TL_OK) {
            tl_atomic_u32_store(&ctx->error, 1);
            break;
        }

        ts++;
        count++;

        if (ctx->flush_every > 0 && (count % ctx->flush_every) == 0) {
            st = tl_flush(ctx->tl);
            if (st != TL_OK) {
                tl_atomic_u32_store(&ctx->error, 1);
                break;
            }
        }

        if ((count % 256) == 0) {
            test_sleep_ms(1);
        }
    }

    ctx->ts = ts;
    return NULL;
}

static tl_status_t snapshot_check_order(tl_timelog_t* tl, bool do_validate) {
    tl_snapshot_t* snap = NULL;
    tl_iter_t* it = NULL;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    if (st != TL_OK) return st;

    if (do_validate) {
        st = tl_validate(snap);
        if (st != TL_OK) {
            tl_snapshot_release(snap);
            return st;
        }
    }

    st = tl_iter_since(snap, TL_TS_MIN, &it);
    if (st != TL_OK) {
        tl_snapshot_release(snap);
        return st;
    }

    tl_record_t rec;
    tl_ts_t last = TL_TS_MIN;
    bool first = true;
    tl_status_t ist;
    while ((ist = tl_iter_next(it, &rec)) == TL_OK) {
        if (!first && rec.ts < last) {
            tl_iter_destroy(it);
            tl_snapshot_release(snap);
            return TL_EINTERNAL;
        }
        last = rec.ts;
        first = false;
    }

    tl_iter_destroy(it);
    tl_snapshot_release(snap);

    if (ist != TL_EOF) return ist;
    return TL_OK;
}

static tl_status_t snapshot_check_exact_once(tl_timelog_t* tl, bool do_validate) {
    tl_snapshot_t* snap = NULL;
    tl_iter_t* it = NULL;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    if (st != TL_OK) return st;

    if (do_validate) {
        st = tl_validate(snap);
        if (st != TL_OK) {
            tl_snapshot_release(snap);
            return st;
        }
    }

    st = tl_iter_since(snap, TL_TS_MIN, &it);
    if (st != TL_OK) {
        tl_snapshot_release(snap);
        return st;
    }

    tl_record_t rec;
    bool first = true;
    tl_ts_t expected = 0;
    tl_status_t ist;
    while ((ist = tl_iter_next(it, &rec)) == TL_OK) {
        if (first) {
            if (rec.ts != 1) {
                tl_iter_destroy(it);
                tl_snapshot_release(snap);
                return TL_EINTERNAL;
            }
            expected = rec.ts;
            first = false;
        } else {
            if (rec.ts != expected + 1) {
                tl_iter_destroy(it);
                tl_snapshot_release(snap);
                return TL_EINTERNAL;
            }
            expected = rec.ts;
        }
    }

    tl_iter_destroy(it);
    tl_snapshot_release(snap);

    if (ist != TL_EOF) return ist;
    return TL_OK;
}

int test_concurrency(void) {
    tl_timelog_t* tl = NULL;
    tl_status_t st;

    printf("  [concurrency] Testing snapshots vs writer thread...\n");

    tl_config_t cfg;
    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.memtable_max_bytes = 16 * 1024;
    cfg.target_page_bytes = 4096;

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(tl, NULL);

    writer_ctx_t ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.tl = tl;
    ctx.flush_every = 128;
    ctx.ts = 1;
    tl_atomic_u32_store(&ctx.stop, 0);
    tl_atomic_u32_store(&ctx.error, 0);

    tl_thread_t writer_thread;
    int rc = tl_thread_create(&writer_thread, writer_thread_fn, &ctx);
    TEST_ASSERT_EQ(rc, 0);

    for (int i = 0; i < 100; i++) {
        st = snapshot_check_exact_once(tl, (i % 10) == 0);
        TEST_ASSERT_EQ(st, TL_OK);
        if ((i % 20) == 0) {
            test_sleep_ms(1);
        }
    }

    tl_atomic_u32_store(&ctx.stop, 1);
    rc = tl_thread_join(writer_thread, NULL);
    TEST_ASSERT_EQ(rc, 0);
    TEST_ASSERT_EQ(tl_atomic_u32_load(&ctx.error), 0);

    tl_close(tl);
    tl = NULL;

    printf("  [concurrency] Testing snapshots with background maintenance...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.memtable_max_bytes = 16 * 1024;
    cfg.target_page_bytes = 4096;
    cfg.max_delta_segments = 2;
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 0; i < 2000; i++) {
        st = tl_append(tl, (tl_ts_t)i, (tl_handle_t)(i + 1000));
        if (st == TL_EBUSY) {
            st = tl_flush(tl);
        }
        TEST_ASSERT_EQ(st, TL_OK);

        if ((i % 200) == 0) {
            st = snapshot_check_order(tl, true);
            TEST_ASSERT_EQ(st, TL_OK);
            test_sleep_ms(1);
        }
    }

    st = snapshot_check_order(tl, true);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_close(tl);
    return 0;
}
