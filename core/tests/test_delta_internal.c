/*===========================================================================
 * test_delta_internal.c - Delta Layer Internal Tests
 *
 * These tests verify LLD-level invariants and internal API behavior for
 * the delta layer: memrun, memtable, merge iterator, and flush builder.
 *
 * CLASSIFICATION: Internal (LLD-Driven)
 * These are IMPLEMENTATION tests, not SPEC tests.
 *
 * If these tests fail, the cause could be:
 * 1. A bug in the implementation (likely)
 * 2. An intentional internal refactor (update test accordingly)
 *
 * These tests do NOT verify public API contracts - see test_functional.c.
 *
 * Part of Phase 10: Test Suite Reorganization
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"

/* Internal headers - NOT public API */
#include "internal/tl_alloc.h"
#include "internal/tl_atomic.h"
#include "internal/tl_sync.h"
#include "internal/tl_intervals.h"
#include "tl_memrun.h"
#include "tl_memtable.h"
#include "tl_memview.h"
#include "tl_merge_iter.h"
#include "tl_flush.h"
#include "query/tl_active_iter.h"
#include "query/tl_memrun_iter.h"

#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

typedef struct delta_fail_alloc_ctx {
    size_t fail_after_n;
    size_t alloc_count;
} delta_fail_alloc_ctx_t;

static bool delta_fail_should_fail(delta_fail_alloc_ctx_t* ctx) {
    ctx->alloc_count++;
    return ctx->fail_after_n > 0 && ctx->alloc_count == ctx->fail_after_n;
}

static void* delta_fail_malloc(void* ctx, size_t size) {
    delta_fail_alloc_ctx_t* fa = (delta_fail_alloc_ctx_t*)ctx;
    if (delta_fail_should_fail(fa)) {
        return NULL;
    }
    return malloc(size);
}

static void* delta_fail_calloc(void* ctx, size_t count, size_t size) {
    delta_fail_alloc_ctx_t* fa = (delta_fail_alloc_ctx_t*)ctx;
    if (delta_fail_should_fail(fa)) {
        return NULL;
    }
    return calloc(count, size);
}

static void* delta_fail_realloc(void* ctx, void* ptr, size_t size) {
    delta_fail_alloc_ctx_t* fa = (delta_fail_alloc_ctx_t*)ctx;
    if (delta_fail_should_fail(fa)) {
        return NULL;
    }
    return realloc(ptr, size);
}

static void delta_fail_free(void* ctx, void* ptr) {
    (void)ctx;
    free(ptr);
}

static tl_status_t make_ooo_runset(tl_alloc_ctx_t* alloc,
                                   tl_record_t* records, size_t len,
                                   tl_ooorunset_t** out) {
    TL_ASSERT(out != NULL);

    *out = NULL;
    if (len == 0) {
        return TL_OK;
    }

    tl_ooorun_t* run = NULL;
    tl_status_t st = tl_ooorun_create(alloc, records, len, 1, &run);
    if (st != TL_OK) {
        return st;
    }

    tl_ooorun_t* runs[1] = { run };
    st = tl_ooorunset_create(alloc, runs, 1, out);
    tl_ooorun_release(run);
    return st;
}

/*===========================================================================
 * OOO Run Tests (Internal API)
 *===========================================================================*/

TEST_DECLARE(delta_ooorun_create_bounds) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* recs = TL_NEW_ARRAY(&alloc, tl_record_t, 3);
    TEST_ASSERT_NOT_NULL(recs);
    recs[0] = (tl_record_t){.ts = 5, .handle = 1};
    recs[1] = (tl_record_t){.ts = 7, .handle = 2};
    recs[2] = (tl_record_t){.ts = 9, .handle = 3};

    tl_ooorun_t* run = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_ooorun_create(&alloc, recs, 3, 7, &run));
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_EQ(3, run->len);
    TEST_ASSERT_EQ(5, run->min_ts);
    TEST_ASSERT_EQ(9, run->max_ts);
    TEST_ASSERT_EQ(7, run->gen);

    tl_ooorun_release(run);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_ooorunset_create_total_len) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* recs_a = TL_NEW_ARRAY(&alloc, tl_record_t, 2);
    tl_record_t* recs_b = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    TEST_ASSERT_NOT_NULL(recs_a);
    TEST_ASSERT_NOT_NULL(recs_b);

    recs_a[0] = (tl_record_t){.ts = 10, .handle = 1};
    recs_a[1] = (tl_record_t){.ts = 20, .handle = 2};
    recs_b[0] = (tl_record_t){.ts = 30, .handle = 3};

    tl_ooorun_t* run_a = NULL;
    tl_ooorun_t* run_b = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_ooorun_create(&alloc, recs_a, 2, 1, &run_a));
    TEST_ASSERT_STATUS(TL_OK, tl_ooorun_create(&alloc, recs_b, 1, 2, &run_b));

    tl_ooorun_t* runs[2] = { run_a, run_b };
    tl_ooorunset_t* set = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_ooorunset_create(&alloc, runs, 2, &set));

    tl_ooorun_release(run_a);
    tl_ooorun_release(run_b);

    TEST_ASSERT_NOT_NULL(set);
    TEST_ASSERT_EQ(2, set->count);
    TEST_ASSERT_EQ(3, set->total_len);
    TEST_ASSERT_EQ(1, set->runs[0]->gen);
    TEST_ASSERT_EQ(2, set->runs[1]->gen);

    tl_ooorunset_release(set);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_ooorunset_append) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* recs_a = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_record_t* recs_b = TL_NEW_ARRAY(&alloc, tl_record_t, 2);
    TEST_ASSERT_NOT_NULL(recs_a);
    TEST_ASSERT_NOT_NULL(recs_b);

    recs_a[0] = (tl_record_t){.ts = 10, .handle = 1};
    recs_b[0] = (tl_record_t){.ts = 20, .handle = 2};
    recs_b[1] = (tl_record_t){.ts = 30, .handle = 3};

    tl_ooorun_t* run_a = NULL;
    tl_ooorun_t* run_b = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_ooorun_create(&alloc, recs_a, 1, 1, &run_a));
    TEST_ASSERT_STATUS(TL_OK, tl_ooorun_create(&alloc, recs_b, 2, 2, &run_b));

    tl_ooorun_t* runs[1] = { run_a };
    tl_ooorunset_t* set_a = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_ooorunset_create(&alloc, runs, 1, &set_a));
    tl_ooorun_release(run_a);

    tl_ooorunset_t* set_b = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_ooorunset_append(&alloc, set_a, run_b, &set_b));
    tl_ooorun_release(run_b);

    TEST_ASSERT_NOT_NULL(set_a);
    TEST_ASSERT_EQ(1, set_a->count);

    TEST_ASSERT_NOT_NULL(set_b);
    TEST_ASSERT_EQ(2, set_b->count);
    TEST_ASSERT_EQ(3, set_b->total_len);
    TEST_ASSERT_EQ(1, set_b->runs[0]->gen);
    TEST_ASSERT_EQ(2, set_b->runs[1]->gen);

    tl_ooorunset_release(set_a);
    tl_ooorunset_release(set_b);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Memrun Tests (Internal API)
 *
 * These test the internal memrun structure which represents a sealed,
 * immutable snapshot of memtable data. Memruns are not exposed in public API.
 *===========================================================================*/

TEST_DECLARE(delta_memrun_create_records_only) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create run array */
    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 3);
    TEST_ASSERT_NOT_NULL(run);
    run[0] = (tl_record_t){.ts = 10, .handle = 1};
    run[1] = (tl_record_t){.ts = 20, .handle = 2};
    run[2] = (tl_record_t){.ts = 30, .handle = 3};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 3, NULL, NULL, 0, &mr));
    TEST_ASSERT_NOT_NULL(mr);
    TEST_ASSERT_EQ(3, tl_memrun_run_len(mr));
    TEST_ASSERT_EQ(0, tl_memrun_ooo_len(mr));
    TEST_ASSERT_EQ(0, tl_memrun_tombs_len(mr));
    TEST_ASSERT_EQ(10, tl_memrun_min_ts(mr));
    TEST_ASSERT_EQ(30, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memrun_create_with_ooo) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create run and ooo arrays */
    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 2);
    tl_record_t* ooo = TL_NEW_ARRAY(&alloc, tl_record_t, 2);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(ooo);

    run[0] = (tl_record_t){.ts = 20, .handle = 1};
    run[1] = (tl_record_t){.ts = 40, .handle = 2};
    ooo[0] = (tl_record_t){.ts = 10, .handle = 3};
    ooo[1] = (tl_record_t){.ts = 30, .handle = 4};

    tl_ooorunset_t* ooo_runs = NULL;
    TEST_ASSERT_STATUS(TL_OK, make_ooo_runset(&alloc, ooo, 2, &ooo_runs));

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 2, ooo_runs, NULL, 0, &mr));
    TEST_ASSERT_NOT_NULL(mr);
    TEST_ASSERT_EQ(2, tl_memrun_run_len(mr));
    TEST_ASSERT_EQ(2, tl_memrun_ooo_len(mr));
    TEST_ASSERT_EQ(10, tl_memrun_min_ts(mr));
    TEST_ASSERT_EQ(40, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memrun_create_with_tombstones) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(tombs);

    run[0] = (tl_record_t){.ts = 50, .handle = 1};
    tombs[0] = (tl_interval_t){.start = 10, .end = 30, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, tombs, 1, &mr));
    TEST_ASSERT_NOT_NULL(mr);
    TEST_ASSERT_EQ(1, tl_memrun_run_len(mr));
    TEST_ASSERT_EQ(1, tl_memrun_tombs_len(mr));
    /* min_ts should include tombstone start */
    TEST_ASSERT_EQ(10, tl_memrun_min_ts(mr));
    /* max_ts is the record at 50 */
    TEST_ASSERT_EQ(50, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memrun_create_tombstone_only) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(tombs);
    tombs[0] = (tl_interval_t){.start = 100, .end = 200, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, NULL, 0, NULL, tombs, 1, &mr));
    TEST_ASSERT_NOT_NULL(mr);
    TEST_ASSERT_EQ(0, tl_memrun_run_len(mr));
    TEST_ASSERT_EQ(0, tl_memrun_ooo_len(mr));
    TEST_ASSERT_EQ(1, tl_memrun_tombs_len(mr));
    TEST_ASSERT_EQ(100, tl_memrun_min_ts(mr));
    /* max_ts = end - 1 = 199 for bounded tombstone */
    TEST_ASSERT_EQ(199, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memrun_create_empty_einval) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_memrun_create(&alloc, NULL, 0, NULL, NULL, 0, &mr));
    TEST_ASSERT_NULL(mr);

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memrun_bounds_include_tombstones) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Record at ts=50, tombstone covering [10, 30) */
    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(tombs);

    run[0] = (tl_record_t){.ts = 50, .handle = 1};
    tombs[0] = (tl_interval_t){.start = 10, .end = 30, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, tombs, 1, &mr));

    /* min_ts MUST include tombstone start (10), not just record (50) */
    TEST_ASSERT_EQ(10, tl_memrun_min_ts(mr));
    /* max_ts = max(50, 29) = 50 */
    TEST_ASSERT_EQ(50, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memrun_bounds_unbounded_tomb) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(tombs);

    run[0] = (tl_record_t){.ts = 50, .handle = 1};
    tombs[0] = (tl_interval_t){.start = 100, .end = 0, .end_unbounded = true};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, tombs, 1, &mr));

    /* min_ts = min(50, 100) = 50 */
    TEST_ASSERT_EQ(50, tl_memrun_min_ts(mr));
    /* max_ts = TL_TS_MAX due to unbounded tombstone */
    TEST_ASSERT_EQ(TL_TS_MAX, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

/**
 * Test: Tombstone AFTER records extends max_ts.
 * Record at ts=50, tombstone [100, 200) -> max_ts must be 199 (not 50).
 * This is critical for read-path: if max_ts=50, overlap checks would skip
 * this memrun when querying [150, 160), causing missed deletes.
 */
TEST_DECLARE(delta_memrun_bounds_tomb_extends_max) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(tombs);

    run[0] = (tl_record_t){.ts = 50, .handle = 1};
    tombs[0] = (tl_interval_t){.start = 100, .end = 200, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, tombs, 1, &mr));

    /* min_ts = min(50, 100) = 50 */
    TEST_ASSERT_EQ(50, tl_memrun_min_ts(mr));
    /* max_ts MUST be 199 (tomb.end - 1), NOT 50! */
    TEST_ASSERT_EQ(199, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memrun_refcnt_acquire_release) {
    /*
     * Tests internal reference counting behavior.
     * Reference counting is an implementation detail - a valid
     * implementation could use arena allocation or epoch-based reclamation.
     */
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    run[0] = (tl_record_t){.ts = 10, .handle = 1};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, NULL, 0, &mr));
    TEST_ASSERT_EQ(1, tl_memrun_refcnt(mr));

    tl_memrun_acquire(mr);
    TEST_ASSERT_EQ(2, tl_memrun_refcnt(mr));

    tl_memrun_acquire(mr);
    TEST_ASSERT_EQ(3, tl_memrun_refcnt(mr));

    tl_memrun_release(mr);
    TEST_ASSERT_EQ(2, tl_memrun_refcnt(mr));

    tl_memrun_release(mr);
    TEST_ASSERT_EQ(1, tl_memrun_refcnt(mr));

    tl_memrun_release(mr);
    /* Object destroyed, cannot check refcnt */

    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Memtable Tests (Internal API)
 *
 * These test the internal memtable structure which is the mutable ingest
 * buffer. The memtable API is not exposed publicly.
 *===========================================================================*/

TEST_DECLARE(delta_memtable_init_preallocates_sealed) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));
    TEST_ASSERT_NOT_NULL(mt.sealed);
    TEST_ASSERT_EQ(0, mt.sealed_len);
    TEST_ASSERT_EQ(4, mt.sealed_max_runs);

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_inorder) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 30, 3));

    TEST_ASSERT_EQ(3, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(0, tl_memtable_ooo_head_len(&mt));
    TEST_ASSERT_EQ(30, mt.last_inorder_ts);

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_ooo) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 30, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 2)); /* OOO */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 3)); /* OOO */

    TEST_ASSERT_EQ(1, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(2, tl_memtable_ooo_head_len(&mt));

    /* C-14: OOO is UNSORTED during append - verify insertion order preserved.
     * Records are sorted at seal/capture time, not during insert.
     * Here we inserted 10, then 20, so insertion order is [10, 20]. */
    const tl_record_t* ooo = tl_memtable_ooo_head_data(&mt);
    TEST_ASSERT_EQ(10, ooo[0].ts);  /* First OOO insert */
    TEST_ASSERT_EQ(20, ooo[1].ts);  /* Second OOO insert */

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_mixed) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 30, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 3)); /* OOO */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 40, 4)); /* In-order again */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 25, 5)); /* OOO */

    TEST_ASSERT_EQ(3, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(2, tl_memtable_ooo_head_len(&mt));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_run_limit_backpressure) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    /* Force small chunk and low run limit to trigger backpressure. */
    mt.ooo_chunk_records = 1;
    mt.ooo_run_limit = 1;

    /* Seed last_inorder_ts. */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 100, 1));

    /* First OOO insert flushes into a run. */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 50, 2));
    TEST_ASSERT_EQ(1, tl_ooorunset_count(mt.ooo_runs));
    TEST_ASSERT_EQ(0, tl_memtable_ooo_head_len(&mt));

    /* Second OOO insert cannot flush due to run limit. */
    TEST_ASSERT_STATUS(TL_EBUSY, tl_memtable_insert(&mt, 40, 3));
    TEST_ASSERT_EQ(1, tl_memtable_ooo_head_len(&mt));
    TEST_ASSERT_EQ(2, tl_memtable_ooo_total_len(&mt));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_updates_epoch) {
    /*
     * Tests internal epoch tracking behavior.
     * The epoch is an implementation detail for snapshot isolation.
     */
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));
    TEST_ASSERT_EQ(0, tl_memtable_epoch(&mt));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_EQ(1, tl_memtable_epoch(&mt));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 2));
    TEST_ASSERT_EQ(2, tl_memtable_epoch(&mt));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_updates_bytes) {
    /*
     * Tests internal byte tracking for flush trigger.
     * This is an implementation detail of the seal heuristic.
     */
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));
    TEST_ASSERT_EQ(0, mt.active_bytes_est);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_EQ(TL_RECORD_SIZE, mt.active_bytes_est);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 2));
    TEST_ASSERT_EQ(2 * TL_RECORD_SIZE, mt.active_bytes_est);

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_batch_fast_path) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 256, 4));

    tl_record_t batch[3] = {
        {.ts = 10, .handle = 1},
        {.ts = 20, .handle = 2},
        {.ts = 30, .handle = 3},
    };

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert_batch(&mt, batch, 3, TL_APPEND_HINT_MOSTLY_IN_ORDER));
    TEST_ASSERT_EQ(3, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(0, tl_memtable_ooo_head_len(&mt));
    TEST_ASSERT_EQ(30, mt.last_inorder_ts);
    TEST_ASSERT_EQ(1, tl_memtable_epoch(&mt)); /* epoch++ once for batch */

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_batch_slow_path) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 256, 4));

    /* Unsorted batch */
    tl_record_t batch[3] = {
        {.ts = 30, .handle = 1},
        {.ts = 10, .handle = 2},
        {.ts = 20, .handle = 3},
    };

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert_batch(&mt, batch, 3, 0));

    /*
     * INVARIANT CHECKS (not exact counts, to allow routing algorithm changes):
     * 1. Total records = batch size
     * 2. Epoch incremented at least once
     * 3. Active run is sorted; OOO head may be unsorted (validated invariants)
     */
    size_t total = tl_memtable_run_len(&mt) + tl_memtable_ooo_total_len(&mt);
    TEST_ASSERT_EQ(3, total);  /* All records accounted for */
    TEST_ASSERT(tl_memtable_epoch(&mt) > 0);  /* At least one epoch tick */
#ifdef TL_DEBUG
    TEST_ASSERT(tl_memtable_validate(&mt));  /* Sortedness invariants hold */
#endif

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_batch_no_double_count) {
    /*
     * Tests that batch insertion doesn't double-count in internal accounting.
     */
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 256, 4));

    tl_record_t batch[3] = {
        {.ts = 10, .handle = 1},
        {.ts = 20, .handle = 2},
        {.ts = 30, .handle = 3},
    };

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert_batch(&mt, batch, 3, 0));

    /*
     * INVARIANT: epoch should be 1 (single operation), not 3 (per-record).
     * bytes should be 3 * record size.
     */
    TEST_ASSERT_EQ(1, tl_memtable_epoch(&mt));
    TEST_ASSERT_EQ(3 * TL_RECORD_SIZE, mt.active_bytes_est);

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_batch_full_sort_check) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 256, 4));

    /* Almost sorted: unsorted pair in the middle */
    tl_record_t batch[5] = {
        {.ts = 10, .handle = 1},
        {.ts = 20, .handle = 2},
        {.ts = 25, .handle = 3}, /* Should be after 20 but... */
        {.ts = 22, .handle = 4}, /* ...this is out of order! */
        {.ts = 30, .handle = 5},
    };

    /* With MOSTLY_IN_ORDER hint, must still detect the unsorted pair */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert_batch(&mt, batch, 5, TL_APPEND_HINT_MOSTLY_IN_ORDER));

    /*
     * INVARIANT CHECKS (not exact routing behavior):
     * 1. Total records = batch size
     * 2. OOO should be non-empty (batch has out-of-order elements)
     * 3. Active run is sorted; OOO head may be unsorted (validated invariants)
     */
    size_t total = tl_memtable_run_len(&mt) + tl_memtable_ooo_total_len(&mt);
    TEST_ASSERT_EQ(5, total);  /* All records accounted for */
    TEST_ASSERT(tl_memtable_ooo_total_len(&mt) > 0);  /* OOO used because unsorted */
#ifdef TL_DEBUG
    TEST_ASSERT(tl_memtable_validate(&mt));  /* Sortedness invariants hold */
#endif

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_batch_alloc_failure_no_partial) {
    delta_fail_alloc_ctx_t fail_ctx = {0};
    tl_allocator_t user_alloc = {
        .ctx = &fail_ctx,
        .malloc_fn = delta_fail_malloc,
        .calloc_fn = delta_fail_calloc,
        .realloc_fn = delta_fail_realloc,
        .free_fn = delta_fail_free,
    };

    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, &user_alloc);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 256, 4));

    size_t init_allocs = fail_ctx.alloc_count;
    fail_ctx.fail_after_n = init_allocs + 1;  /* Fail next allocation */

    /* Unsorted batch forces slow path */
    tl_record_t batch[3] = {
        {.ts = 30, .handle = 1},
        {.ts = 10, .handle = 2},
        {.ts = 20, .handle = 3},
    };

    TEST_ASSERT_STATUS(TL_ENOMEM, tl_memtable_insert_batch(&mt, batch, 3, 0));
    TEST_ASSERT_EQ(0, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(0, tl_memtable_ooo_head_len(&mt));
    TEST_ASSERT_EQ(0, mt.active_bytes_est);
    TEST_ASSERT_EQ(0, tl_memtable_epoch(&mt));

    fail_ctx.fail_after_n = 0;
    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_flush_head_enomem_returns_ebusy) {
    delta_fail_alloc_ctx_t fail_ctx = {0};
    tl_allocator_t user_alloc = {
        .ctx = &fail_ctx,
        .malloc_fn = delta_fail_malloc,
        .calloc_fn = delta_fail_calloc,
        .realloc_fn = delta_fail_realloc,
        .free_fn = delta_fail_free,
    };

    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, &user_alloc);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 4096, 4));

    /* Force flush on first OOO insert, and pre-reserve head capacity. */
    mt.ooo_chunk_records = 1;
    TEST_ASSERT_STATUS(TL_OK, tl_recvec_reserve(&mt.ooo_head, 1));

    /* Seed last_inorder_ts. */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 100, 1));

    size_t allocs_before_flush = fail_ctx.alloc_count;
    fail_ctx.fail_after_n = allocs_before_flush + 1; /* Fail next allocation */

    /* OOO insert triggers flush; flush copy allocation should fail. */
    TEST_ASSERT_STATUS(TL_EBUSY, tl_memtable_insert(&mt, 50, 2));
    TEST_ASSERT_EQ(1, tl_memtable_ooo_head_len(&mt));
    TEST_ASSERT_EQ(1, tl_memtable_ooo_total_len(&mt));
    TEST_ASSERT_EQ(0, tl_ooorunset_count(mt.ooo_runs));

    fail_ctx.fail_after_n = 0;
    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memview_captures_head_sorted_and_pins_runs) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 4096, 4));

    /* Force a small chunk to create a runset quickly. */
    mt.ooo_chunk_records = 2;

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 50, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 30, 3)); /* Flushes head */

    TEST_ASSERT_EQ(0, tl_memtable_ooo_head_len(&mt));
    TEST_ASSERT_EQ(1, tl_ooorunset_count(mt.ooo_runs));

    /* Keep new OOO records in head (unsorted). */
    mt.ooo_chunk_records = 100;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 80, 4));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 60, 5));
    TEST_ASSERT(!mt.ooo_head_sorted);

    tl_memview_t mv;
    TEST_ASSERT_STATUS(TL_OK, tl_memview_capture(&mv, &mt, &mu, &alloc));
    tl_memview_sort_head(&mv);

    const tl_record_t* head = tl_memview_ooo_head_data(&mv);
    TEST_ASSERT_EQ(2, tl_memview_ooo_head_len(&mv));
    TEST_ASSERT_EQ(60, head[0].ts);
    TEST_ASSERT_EQ(80, head[1].ts);

    const tl_ooorunset_t* runs = tl_memview_ooo_runs(&mv);
    TEST_ASSERT(runs == mt.ooo_runs);
    TEST_ASSERT_EQ(4, tl_memview_ooo_total_len(&mv));

    tl_memview_destroy(&mv);
    tl_memtable_destroy(&mt);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memview_captures_concurrent_pins) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 4096, 4));

    /* Force OOO run creation so a runset exists. */
    mt.ooo_chunk_records = 1;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 50, 2));

    const tl_ooorunset_t* runs = mt.ooo_runs;
    TEST_ASSERT_NOT_NULL(runs);
    TEST_ASSERT_EQ(1, tl_atomic_load_relaxed_u32(&runs->refcnt));

    tl_memview_t mv_a;
    tl_memview_t mv_b;
    TEST_ASSERT_STATUS(TL_OK, tl_memview_capture(&mv_a, &mt, &mu, &alloc));
    TEST_ASSERT_STATUS(TL_OK, tl_memview_capture(&mv_b, &mt, &mu, &alloc));

    TEST_ASSERT_EQ(3, tl_atomic_load_relaxed_u32(&runs->refcnt));

    tl_memview_destroy(&mv_a);
    tl_memview_destroy(&mv_b);
    TEST_ASSERT_EQ(1, tl_atomic_load_relaxed_u32(&runs->refcnt));

    tl_memtable_destroy(&mt);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memview_capture_alloc_failure) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 256, 4));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));

    tl_mutex_t mu;
    tl_mutex_init(&mu);

    delta_fail_alloc_ctx_t fail_ctx = {0};
    tl_allocator_t user_alloc = {
        .ctx = &fail_ctx,
        .malloc_fn = delta_fail_malloc,
        .calloc_fn = delta_fail_calloc,
        .realloc_fn = delta_fail_realloc,
        .free_fn = delta_fail_free,
    };

    tl_alloc_ctx_t fail_alloc;
    tl__alloc_init(&fail_alloc, &user_alloc);
    fail_ctx.fail_after_n = 1;  /* Fail first allocation */

    tl_memview_t mv;
    tl_status_t st = tl_memview_capture(&mv, &mt, &mu, &fail_alloc);
    TEST_ASSERT_STATUS(TL_ENOMEM, st);
    TEST_ASSERT_NULL(mv.active_run);
    TEST_ASSERT_EQ(0, mv.active_run_len);
    TEST_ASSERT_EQ(0, mv.sealed_len);
    TEST_ASSERT(!mv.has_data);

    fail_ctx.fail_after_n = 0;
    tl__alloc_destroy(&fail_alloc);
    tl_mutex_destroy(&mu);
    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_tombstone) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert_tombstone(&mt, 10, 30));

    tl_intervals_imm_t imm = tl_memtable_tombs_imm(&mt);
    TEST_ASSERT_EQ(1, imm.len);
    TEST_ASSERT_EQ(10, imm.data[0].start);
    TEST_ASSERT_EQ(30, imm.data[0].end);

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_tombstone_empty) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    /* t1 == t2: empty interval, should be no-op */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert_tombstone(&mt, 10, 10));

    tl_intervals_imm_t imm = tl_memtable_tombs_imm(&mt);
    TEST_ASSERT_EQ(0, imm.len);
    /* epoch should NOT be incremented for empty interval */
    TEST_ASSERT_EQ(0, tl_memtable_epoch(&mt));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_tombstone_invalid) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    /* t1 > t2: invalid interval */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_memtable_insert_tombstone(&mt, 30, 10));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_insert_tombstone_updates_epoch) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));
    TEST_ASSERT_EQ(0, tl_memtable_epoch(&mt));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert_tombstone(&mt, 10, 30));
    TEST_ASSERT_EQ(1, tl_memtable_epoch(&mt));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_seal_empty_noop) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    /* Seal empty memtable is no-op */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_seal(&mt, &mu, NULL));
    TEST_ASSERT_EQ(0, mt.sealed_len);

    tl_memtable_destroy(&mt);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_seal_basic) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    /* Insert some records */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 2));

    /* Seal */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_seal(&mt, &mu, NULL));
    TEST_ASSERT_EQ(1, mt.sealed_len);
    TEST_ASSERT(tl_memtable_is_active_empty(&mt));

    /* Verify sealed memrun */
    TEST_ASSERT_NOT_NULL(mt.sealed[0]);
    TEST_ASSERT_EQ(2, tl_memrun_run_len(mt.sealed[0]));

    tl_memtable_destroy(&mt);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_seal_preserves_on_ebusy) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    /* Small sealed queue capacity of 1 */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 1));

    /* Insert and seal first memrun */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_seal(&mt, &mu, NULL));
    TEST_ASSERT_EQ(1, mt.sealed_len);

    /* Insert more records */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 2));
    TEST_ASSERT_EQ(1, tl_memtable_run_len(&mt));

    /* Try to seal - should fail with TL_EBUSY (queue full) */
    TEST_ASSERT_STATUS(TL_EBUSY, tl_memtable_seal(&mt, &mu, NULL));

    /* Active state should be PRESERVED */
    TEST_ASSERT_EQ(1, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(1, mt.sealed_len);

    tl_memtable_destroy(&mt);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_should_seal_bytes) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Very small threshold */
    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 2 * TL_RECORD_SIZE, 1024, 4));

    TEST_ASSERT(!tl_memtable_should_seal(&mt));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT(!tl_memtable_should_seal(&mt));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 2));
    TEST_ASSERT(tl_memtable_should_seal(&mt)); /* Threshold reached */

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_should_seal_ooo) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Small OOO budget */
    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 2 * TL_RECORD_SIZE, 4));

    /* In-order record first */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 100, 1));
    TEST_ASSERT(!tl_memtable_should_seal(&mt));

    /* OOO records */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 2));
    TEST_ASSERT(!tl_memtable_should_seal(&mt));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 3));
    TEST_ASSERT(tl_memtable_should_seal(&mt)); /* OOO budget reached */

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_sealed_queue_fifo) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    /* Seal first memrun */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_seal(&mt, &mu, NULL));

    /* Seal second memrun */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_seal(&mt, &mu, NULL));

    TEST_ASSERT_EQ(2, mt.sealed_len);

    /* Peek should return oldest (first sealed) */
    tl_memrun_t* oldest = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_peek_oldest(&mt, &oldest));
    TEST_ASSERT_NOT_NULL(oldest);
    TEST_ASSERT_EQ(10, tl_memrun_run_data(oldest)[0].ts);
    tl_memrun_release(oldest);

    tl_memtable_destroy(&mt);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_pop_releases_refcnt) {
    /*
     * Tests internal reference counting during pop.
     * Reference counting is an implementation detail.
     */
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_seal(&mt, &mu, NULL));

    /* Peek (acquires reference) */
    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_peek_oldest(&mt, &mr));
    TEST_ASSERT_NOT_NULL(mr);
    TEST_ASSERT_EQ(2, tl_memrun_refcnt(mr)); /* queue + our peek */

    /* Pop (releases queue's reference) */
    tl_memtable_pop_oldest(&mt, NULL);
    TEST_ASSERT_EQ(1, tl_memrun_refcnt(mr)); /* only our peek remains */
    TEST_ASSERT_EQ(0, mt.sealed_len);

    /* Release our reference */
    tl_memrun_release(mr);

    tl_memtable_destroy(&mt);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_wait_for_space_timeout) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_cond_t cond;
    tl_mutex_init(&mu);
    tl_cond_init(&cond);

    /* Sealed queue capacity of 1 */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 1));

    /* Insert and seal to fill the queue */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_seal(&mt, &mu, &cond));
    TEST_ASSERT_EQ(1, mt.sealed_len);

    /* Queue is full - wait_for_space should timeout */
    tl_mutex_lock(&mu);
    bool has_space = tl_memtable_wait_for_space(&mt, &mu, &cond, 10);
    tl_mutex_unlock(&mu);
    TEST_ASSERT(!has_space);

    /* Pop to free space */
    tl_memtable_pop_oldest(&mt, NULL);
    TEST_ASSERT_EQ(0, mt.sealed_len);

    /* Now wait_for_space should succeed immediately */
    tl_mutex_lock(&mu);
    has_space = tl_memtable_wait_for_space(&mt, &mu, &cond, 10);
    tl_mutex_unlock(&mu);
    TEST_ASSERT(has_space);

    tl_memtable_destroy(&mt);
    tl_cond_destroy(&cond);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_seal_transfers_multiple_runs) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 4096, 4));

    /* Force a run flush for every OOO insert. */
    mt.ooo_chunk_records = 1;

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 1000, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 900, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 800, 3));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 700, 4));

    TEST_ASSERT_EQ(0, tl_memtable_ooo_head_len(&mt));
    TEST_ASSERT_EQ(3, tl_ooorunset_count(mt.ooo_runs));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_seal(&mt, &mu, NULL));
    TEST_ASSERT_EQ(1, mt.sealed_len);
    TEST_ASSERT_NULL(mt.ooo_runs);

    tl_memrun_t* mr = mt.sealed[0];
    TEST_ASSERT_NOT_NULL(mr);
    TEST_ASSERT_EQ(3, tl_memrun_ooo_run_count(mr));
    TEST_ASSERT_EQ(3, tl_memrun_ooo_len(mr));

    tl_memtable_destroy(&mt);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Active/Memrun Iterator Tests (Internal API)
 *===========================================================================*/

TEST_DECLARE(delta_memrun_iter_merges_run_and_runs) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 2);
    tl_record_t* ooo = TL_NEW_ARRAY(&alloc, tl_record_t, 2);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(ooo);

    run[0] = (tl_record_t){.ts = 10, .handle = 1};
    run[1] = (tl_record_t){.ts = 20, .handle = 2};
    ooo[0] = (tl_record_t){.ts = 20, .handle = 99};
    ooo[1] = (tl_record_t){.ts = 30, .handle = 3};

    tl_ooorunset_t* ooo_runs = NULL;
    TEST_ASSERT_STATUS(TL_OK, make_ooo_runset(&alloc, ooo, 2, &ooo_runs));

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 2, ooo_runs, NULL, 0, &mr));

    tl_memrun_iter_t it;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_init(&it, mr, 0, 100, false, &alloc));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_next(&it, &rec));
    TEST_ASSERT_EQ(10, rec.ts);
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_next(&it, &rec));
    TEST_ASSERT_EQ(20, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_next(&it, &rec));
    TEST_ASSERT_EQ(20, rec.ts);
    TEST_ASSERT_EQ(99, rec.handle);
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_next(&it, &rec));
    TEST_ASSERT_EQ(30, rec.ts);
    TEST_ASSERT_STATUS(TL_EOF, tl_memrun_iter_next(&it, &rec));

    tl_memrun_iter_destroy(&it);
    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memrun_iter_merges_multiple_runs) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    run[0] = (tl_record_t){.ts = 15, .handle = 1};

    tl_record_t* r1 = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_record_t* r2 = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_record_t* r3 = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    TEST_ASSERT_NOT_NULL(r1);
    TEST_ASSERT_NOT_NULL(r2);
    TEST_ASSERT_NOT_NULL(r3);

    r1[0] = (tl_record_t){.ts = 5, .handle = 10};
    r2[0] = (tl_record_t){.ts = 10, .handle = 11};
    r3[0] = (tl_record_t){.ts = 20, .handle = 12};

    tl_ooorun_t* run1 = NULL;
    tl_ooorun_t* run2 = NULL;
    tl_ooorun_t* run3 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_ooorun_create(&alloc, r1, 1, 1, &run1));
    TEST_ASSERT_STATUS(TL_OK, tl_ooorun_create(&alloc, r2, 1, 2, &run2));
    TEST_ASSERT_STATUS(TL_OK, tl_ooorun_create(&alloc, r3, 1, 3, &run3));

    tl_ooorun_t* runs[3] = { run1, run2, run3 };
    tl_ooorunset_t* ooo_runs = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_ooorunset_create(&alloc, runs, 3, &ooo_runs));

    tl_ooorun_release(run1);
    tl_ooorun_release(run2);
    tl_ooorun_release(run3);

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, ooo_runs, NULL, 0, &mr));

    tl_memrun_iter_t it;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_init(&it, mr, 0, 100, false, &alloc));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_next(&it, &rec));
    TEST_ASSERT_EQ(5, rec.ts);
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_next(&it, &rec));
    TEST_ASSERT_EQ(10, rec.ts);
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_next(&it, &rec));
    TEST_ASSERT_EQ(15, rec.ts);
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_next(&it, &rec));
    TEST_ASSERT_EQ(20, rec.ts);
    TEST_ASSERT_STATUS(TL_EOF, tl_memrun_iter_next(&it, &rec));

    tl_memrun_iter_destroy(&it);
    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memrun_iter_generation_tie_break) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* r1 = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_record_t* r2 = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    TEST_ASSERT_NOT_NULL(r1);
    TEST_ASSERT_NOT_NULL(r2);

    r1[0] = (tl_record_t){.ts = 10, .handle = 1};
    r2[0] = (tl_record_t){.ts = 10, .handle = 2};

    tl_ooorun_t* run1 = NULL;
    tl_ooorun_t* run2 = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_ooorun_create(&alloc, r1, 1, 1, &run1));
    TEST_ASSERT_STATUS(TL_OK, tl_ooorun_create(&alloc, r2, 1, 2, &run2));

    tl_ooorun_t* runs[2] = { run1, run2 };
    tl_ooorunset_t* ooo_runs = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_ooorunset_create(&alloc, runs, 2, &ooo_runs));

    tl_ooorun_release(run1);
    tl_ooorun_release(run2);

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, NULL, 0, ooo_runs, NULL, 0, &mr));

    tl_memrun_iter_t it;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_init(&it, mr, 0, 100, false, &alloc));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_next(&it, &rec));
    TEST_ASSERT_EQ(10, rec.ts);
    TEST_ASSERT_EQ(1, rec.handle);
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_iter_next(&it, &rec));
    TEST_ASSERT_EQ(10, rec.ts);
    TEST_ASSERT_EQ(2, rec.handle);
    TEST_ASSERT_STATUS(TL_EOF, tl_memrun_iter_next(&it, &rec));

    tl_memrun_iter_destroy(&it);
    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_active_iter_merges_run_head_runs) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 4096, 4));

    /* Force a run flush, then keep head data for active merge. */
    mt.ooo_chunk_records = 2;

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 100, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 50, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 30, 3));

    mt.ooo_chunk_records = 100;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 80, 4));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 60, 5));

    tl_memview_t mv;
    TEST_ASSERT_STATUS(TL_OK, tl_memview_capture(&mv, &mt, &mu, &alloc));
    tl_memview_sort_head(&mv);

    tl_active_iter_t it;
    TEST_ASSERT_STATUS(TL_OK, tl_active_iter_init(&it, &mv, 0, 200, false, &alloc));

    tl_record_t rec;
    TEST_ASSERT_STATUS(TL_OK, tl_active_iter_next(&it, &rec));
    TEST_ASSERT_EQ(30, rec.ts);
    TEST_ASSERT_STATUS(TL_OK, tl_active_iter_next(&it, &rec));
    TEST_ASSERT_EQ(50, rec.ts);
    TEST_ASSERT_STATUS(TL_OK, tl_active_iter_next(&it, &rec));
    TEST_ASSERT_EQ(60, rec.ts);
    TEST_ASSERT_STATUS(TL_OK, tl_active_iter_next(&it, &rec));
    TEST_ASSERT_EQ(80, rec.ts);
    TEST_ASSERT_STATUS(TL_OK, tl_active_iter_next(&it, &rec));
    TEST_ASSERT_EQ(100, rec.ts);
    TEST_ASSERT_STATUS(TL_EOF, tl_active_iter_next(&it, &rec));

    tl_active_iter_destroy(&it);
    tl_memview_destroy(&mv);
    tl_memtable_destroy(&mt);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Merge Iterator Tests (Internal API)
 *
 * These test the internal merge iterator used for combining sorted runs.
 * The merge iterator is not exposed in the public API.
 *===========================================================================*/

TEST_DECLARE(delta_merge_iter_empty_both) {
    tl_merge_iter_t it;
    tl_merge_iter_init(&it, NULL, 0, NULL, 0);
    TEST_ASSERT(tl_merge_iter_done(&it));
    TEST_ASSERT_NULL(tl_merge_iter_next(&it));
}

TEST_DECLARE(delta_merge_iter_single_input) {
    tl_record_t a[2] = {
        {.ts = 10, .handle = 1},
        {.ts = 20, .handle = 2},
    };

    tl_merge_iter_t it;
    tl_merge_iter_init(&it, a, 2, NULL, 0);
    TEST_ASSERT(!tl_merge_iter_done(&it));
    TEST_ASSERT_EQ(2, tl_merge_iter_remaining(&it));

    const tl_record_t* r1 = tl_merge_iter_next(&it);
    TEST_ASSERT_NOT_NULL(r1);
    TEST_ASSERT_EQ(10, r1->ts);

    const tl_record_t* r2 = tl_merge_iter_next(&it);
    TEST_ASSERT_NOT_NULL(r2);
    TEST_ASSERT_EQ(20, r2->ts);

    TEST_ASSERT(tl_merge_iter_done(&it));
    TEST_ASSERT_NULL(tl_merge_iter_next(&it));
}

TEST_DECLARE(delta_merge_iter_two_inputs) {
    tl_record_t a[2] = {
        {.ts = 10, .handle = 1},
        {.ts = 30, .handle = 2},
    };
    tl_record_t b[2] = {
        {.ts = 20, .handle = 3},
        {.ts = 40, .handle = 4},
    };

    tl_merge_iter_t it;
    tl_merge_iter_init(&it, a, 2, b, 2);

    const tl_record_t* r;

    r = tl_merge_iter_next(&it);
    TEST_ASSERT_EQ(10, r->ts);

    r = tl_merge_iter_next(&it);
    TEST_ASSERT_EQ(20, r->ts);

    r = tl_merge_iter_next(&it);
    TEST_ASSERT_EQ(30, r->ts);

    r = tl_merge_iter_next(&it);
    TEST_ASSERT_EQ(40, r->ts);

    TEST_ASSERT(tl_merge_iter_done(&it));
}

/**
 * SPEC-COMPLIANT TEST: Merge iterator preserves all duplicates.
 *
 * Per timelog.h:16 and Software Design Spec Section 1:
 *   "Duplicates (same timestamp) are allowed; tie order is UNSPECIFIED"
 *
 * This test verifies:
 * 1. All 4 records are returned (2 at ts=10, 2 at ts=20)
 * 2. Records with same timestamp are grouped together
 * 3. NO assertion on which handle comes first within a group
 *
 * Previous version (func_merge_iter_stability) asserted specific tie-order
 * which was a SPEC VIOLATION. A valid implementation could return ties in
 * any order and still be correct.
 */
TEST_DECLARE(delta_merge_iter_preserves_all_duplicates) {
    tl_record_t a[2] = {
        {.ts = 10, .handle = 1},
        {.ts = 20, .handle = 2},
    };
    tl_record_t b[2] = {
        {.ts = 10, .handle = 100}, /* Same ts as a[0] */
        {.ts = 20, .handle = 200}, /* Same ts as a[1] */
    };

    tl_merge_iter_t it;
    tl_merge_iter_init(&it, a, 2, b, 2);

    /* Collect all records */
    tl_record_t results[4];
    size_t count = 0;
    while (!tl_merge_iter_done(&it) && count < 4) {
        const tl_record_t* r = tl_merge_iter_next(&it);
        if (r) results[count++] = *r;
    }

    TEST_ASSERT_EQ(4, count);

    /* Verify ts=10 group (both present, order unspecified) */
    bool found_ts10_h1 = false, found_ts10_h100 = false;
    for (size_t i = 0; i < 2; i++) {
        TEST_ASSERT_EQ(10, results[i].ts);  /* First two should be ts=10 */
        if (results[i].handle == 1) found_ts10_h1 = true;
        if (results[i].handle == 100) found_ts10_h100 = true;
    }
    TEST_ASSERT(found_ts10_h1);
    TEST_ASSERT(found_ts10_h100);

    /* Verify ts=20 group (both present, order unspecified) */
    bool found_ts20_h2 = false, found_ts20_h200 = false;
    for (size_t i = 2; i < 4; i++) {
        TEST_ASSERT_EQ(20, results[i].ts);  /* Last two should be ts=20 */
        if (results[i].handle == 2) found_ts20_h2 = true;
        if (results[i].handle == 200) found_ts20_h200 = true;
    }
    TEST_ASSERT(found_ts20_h2);
    TEST_ASSERT(found_ts20_h200);
}

/*===========================================================================
 * Flush Tests (Internal API)
 *
 * These test the internal flush builder which converts memruns to segments.
 * The flush builder is not exposed in the public API.
 *===========================================================================*/

TEST_DECLARE(delta_flush_build_records_only) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create memrun with records only */
    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 2);
    tl_record_t* ooo = TL_NEW_ARRAY(&alloc, tl_record_t, 2);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(ooo);

    run[0] = (tl_record_t){.ts = 20, .handle = 1};
    run[1] = (tl_record_t){.ts = 40, .handle = 2};
    ooo[0] = (tl_record_t){.ts = 10, .handle = 3};
    ooo[1] = (tl_record_t){.ts = 30, .handle = 4};

    tl_ooorunset_t* ooo_runs = NULL;
    TEST_ASSERT_STATUS(TL_OK, make_ooo_runset(&alloc, ooo, 2, &ooo_runs));

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 2, ooo_runs, NULL, 0, &mr));

    tl_flush_ctx_t ctx = {
        .alloc = &alloc,
        .target_page_bytes = 64 * 1024,
        .generation = 1
    };

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_flush_build(&ctx, mr, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    TEST_ASSERT_EQ(4, seg->record_count);
    TEST_ASSERT_EQ(10, seg->min_ts);
    TEST_ASSERT_EQ(40, seg->max_ts);
    TEST_ASSERT(tl_segment_is_l0(seg));

    tl_segment_release(seg);
    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_flush_build_with_tombstones) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(tombs);

    run[0] = (tl_record_t){.ts = 50, .handle = 1};
    tombs[0] = (tl_interval_t){.start = 10, .end = 30, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, tombs, 1, &mr));

    tl_flush_ctx_t ctx = {
        .alloc = &alloc,
        .target_page_bytes = 64 * 1024,
        .generation = 1
    };

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_flush_build(&ctx, mr, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    TEST_ASSERT(tl_segment_has_tombstones(seg));
    TEST_ASSERT_EQ(1, seg->record_count);

    tl_segment_release(seg);
    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_flush_build_tombstone_only) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(tombs);
    tombs[0] = (tl_interval_t){.start = 100, .end = 200, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, NULL, 0, NULL, tombs, 1, &mr));

    tl_flush_ctx_t ctx = {
        .alloc = &alloc,
        .target_page_bytes = 64 * 1024,
        .generation = 1
    };

    tl_segment_t* seg = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_flush_build(&ctx, mr, &seg));
    TEST_ASSERT_NOT_NULL(seg);
    TEST_ASSERT(tl_segment_is_tombstone_only(seg));
    TEST_ASSERT_EQ(0, seg->record_count);

    tl_segment_release(seg);
    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Debug Validation Tests (Internal API)
 *
 * These validation functions are only available in debug builds.
 * They test internal invariants that may change with implementation.
 *===========================================================================*/

#ifdef TL_DEBUG

TEST_DECLARE(delta_memrun_validate_correct) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 2);
    TEST_ASSERT_NOT_NULL(run);
    run[0] = (tl_record_t){.ts = 10, .handle = 1};
    run[1] = (tl_record_t){.ts = 20, .handle = 2};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 2, NULL, NULL, 0, &mr));
    TEST_ASSERT(tl_memrun_validate(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_validate_correct) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 2));
    TEST_ASSERT(tl_memtable_validate(&mt));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

#endif /* TL_DEBUG */

/*===========================================================================
 * C-14: Deferred OOO Sort Tests
 *
 * These tests specifically validate the C-14 fix: OOO records are unsorted
 * during append but sorted at seal time.
 *===========================================================================*/

TEST_DECLARE(delta_memtable_c14_ooo_unsorted_during_append) {
    /*
     * C-14 TEST: Verify OOO head is UNSORTED during append.
     * Insert OOO records in reverse timestamp order (worst case).
     * Verify they appear in insertion order (not sorted).
     */
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 4096, 4));

    /* First record sets last_inorder_ts = 1000 */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 1000, 1000));

    /* Insert OOO records in REVERSE order: 500, 300, 100 */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 500, 500));  /* OOO */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 300, 300));  /* OOO */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 100, 100));  /* OOO */

    TEST_ASSERT_EQ(1, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(3, tl_memtable_ooo_head_len(&mt));

    /* C-14: OOO should be in INSERTION order during append (500, 300, 100) */
    const tl_record_t* ooo = tl_memtable_ooo_head_data(&mt);
    TEST_ASSERT_EQ(500, ooo[0].ts);  /* First OOO insert */
    TEST_ASSERT_EQ(300, ooo[1].ts);  /* Second OOO insert */
    TEST_ASSERT_EQ(100, ooo[2].ts);  /* Third OOO insert */

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(delta_memtable_c14_ooo_sorted_at_seal) {
    /*
     * C-14 TEST: Verify OOO records are SORTED at seal time.
     * Insert OOO records in reverse order, seal, then verify sealed
     * memrun has them in sorted order.
     */
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 4096, 4096, 4));

    /* First record sets last_inorder_ts = 1000 */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 1000, 1000));

    /* Insert OOO records in REVERSE order: 500, 300, 100 */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 500, 500));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 300, 300));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 100, 100));

    /* Seal the memtable */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_seal(&mt, &mu, NULL));
    TEST_ASSERT_EQ(1, mt.sealed_len);
    TEST_ASSERT_NULL(mt.ooo_runs);

    /* Verify sealed memrun exists and has correct counts */
    tl_memrun_t* mr = mt.sealed[0];
    TEST_ASSERT_NOT_NULL(mr);
    TEST_ASSERT_EQ(1, tl_memrun_run_len(mr));
    TEST_ASSERT_EQ(3, tl_memrun_ooo_len(mr));

    /* C-14: Sealed memrun's OOO run should be SORTED (100, 300, 500) */
    TEST_ASSERT_EQ(1, tl_memrun_ooo_run_count(mr));
    const tl_ooorun_t* ooo_run = tl_memrun_ooo_run_at(mr, 0);
    TEST_ASSERT_EQ(3, ooo_run->len);
    TEST_ASSERT_EQ(100, ooo_run->records[0].ts);  /* Smallest */
    TEST_ASSERT_EQ(300, ooo_run->records[1].ts);  /* Middle */
    TEST_ASSERT_EQ(500, ooo_run->records[2].ts);  /* Largest */

    /* Also verify bounds are computed correctly from sorted OOO */
    TEST_ASSERT_EQ(100, tl_memrun_min_ts(mr));   /* min(run[0]=1000, ooo[0]=100) = 100 */
    TEST_ASSERT_EQ(1000, tl_memrun_max_ts(mr));  /* max(run[0]=1000, ooo[2]=500) = 1000 */

    tl_memtable_destroy(&mt);
    tl_mutex_destroy(&mu);
    tl__alloc_destroy(&alloc);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_delta_internal_tests(void) {
    /* OOO run tests (2 tests) */
    RUN_TEST(delta_ooorun_create_bounds);
    RUN_TEST(delta_ooorunset_create_total_len);
    RUN_TEST(delta_ooorunset_append);

    /* Memrun tests (9 tests) */
    RUN_TEST(delta_memrun_create_records_only);
    RUN_TEST(delta_memrun_create_with_ooo);
    RUN_TEST(delta_memrun_create_with_tombstones);
    RUN_TEST(delta_memrun_create_tombstone_only);
    RUN_TEST(delta_memrun_create_empty_einval);
    RUN_TEST(delta_memrun_bounds_include_tombstones);
    RUN_TEST(delta_memrun_bounds_unbounded_tomb);
    RUN_TEST(delta_memrun_bounds_tomb_extends_max);
    RUN_TEST(delta_memrun_refcnt_acquire_release);

    /* Memtable tests (27 tests) */
    RUN_TEST(delta_memtable_init_preallocates_sealed);
    RUN_TEST(delta_memtable_insert_inorder);
    RUN_TEST(delta_memtable_insert_ooo);
    RUN_TEST(delta_memtable_insert_mixed);
    RUN_TEST(delta_memtable_run_limit_backpressure);
    RUN_TEST(delta_memtable_insert_updates_epoch);
    RUN_TEST(delta_memtable_insert_updates_bytes);
    RUN_TEST(delta_memtable_insert_batch_fast_path);
    RUN_TEST(delta_memtable_insert_batch_slow_path);
    RUN_TEST(delta_memtable_insert_batch_no_double_count);
    RUN_TEST(delta_memtable_insert_batch_full_sort_check);
    RUN_TEST(delta_memtable_insert_batch_alloc_failure_no_partial);
    RUN_TEST(delta_memtable_flush_head_enomem_returns_ebusy);
    RUN_TEST(delta_memview_captures_head_sorted_and_pins_runs);
    RUN_TEST(delta_memview_captures_concurrent_pins);
    RUN_TEST(delta_memview_capture_alloc_failure);
    RUN_TEST(delta_memtable_insert_tombstone);
    RUN_TEST(delta_memtable_insert_tombstone_empty);
    RUN_TEST(delta_memtable_insert_tombstone_invalid);
    RUN_TEST(delta_memtable_insert_tombstone_updates_epoch);
    RUN_TEST(delta_memtable_seal_empty_noop);
    RUN_TEST(delta_memtable_seal_basic);
    RUN_TEST(delta_memtable_seal_transfers_multiple_runs);
    RUN_TEST(delta_memtable_seal_preserves_on_ebusy);
    RUN_TEST(delta_memtable_should_seal_bytes);
    RUN_TEST(delta_memtable_should_seal_ooo);
    RUN_TEST(delta_memtable_sealed_queue_fifo);
    RUN_TEST(delta_memtable_pop_releases_refcnt);
    RUN_TEST(delta_memtable_wait_for_space_timeout);

    /* Active/memrun iterator tests (2 tests) */
    RUN_TEST(delta_memrun_iter_merges_run_and_runs);
    RUN_TEST(delta_memrun_iter_merges_multiple_runs);
    RUN_TEST(delta_memrun_iter_generation_tie_break);
    RUN_TEST(delta_active_iter_merges_run_head_runs);

    /* Merge iterator tests (4 tests) */
    RUN_TEST(delta_merge_iter_empty_both);
    RUN_TEST(delta_merge_iter_single_input);
    RUN_TEST(delta_merge_iter_two_inputs);
    RUN_TEST(delta_merge_iter_preserves_all_duplicates); /* Fixed spec violation */

    /* Flush tests (3 tests) */
    RUN_TEST(delta_flush_build_records_only);
    RUN_TEST(delta_flush_build_with_tombstones);
    RUN_TEST(delta_flush_build_tombstone_only);

#ifdef TL_DEBUG
    /* Debug validation tests (2 tests) */
    RUN_TEST(delta_memrun_validate_correct);
    RUN_TEST(delta_memtable_validate_correct);
#endif

    /* C-14: Deferred OOO sort tests (2 tests) */
    RUN_TEST(delta_memtable_c14_ooo_unsorted_during_append);
    RUN_TEST(delta_memtable_c14_ooo_sorted_at_seal);
}
