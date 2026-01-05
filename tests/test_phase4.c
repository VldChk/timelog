#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_alloc.h"
#include "internal/tl_sync.h"
#include "tl_memrun.h"
#include "tl_memtable.h"
#include "tl_flush.h"

/*===========================================================================
 * Memrun Tests
 *===========================================================================*/

TEST_DECLARE(memrun_create_records_only) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    /* Create run array */
    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 3);
    TEST_ASSERT_NOT_NULL(run);
    run[0] = (tl_record_t){.ts = 10, .handle = 1};
    run[1] = (tl_record_t){.ts = 20, .handle = 2};
    run[2] = (tl_record_t){.ts = 30, .handle = 3};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 3, NULL, 0, NULL, 0, &mr));
    TEST_ASSERT_NOT_NULL(mr);
    TEST_ASSERT_EQ(3, tl_memrun_run_len(mr));
    TEST_ASSERT_EQ(0, tl_memrun_ooo_len(mr));
    TEST_ASSERT_EQ(0, tl_memrun_tombs_len(mr));
    TEST_ASSERT_EQ(10, tl_memrun_min_ts(mr));
    TEST_ASSERT_EQ(30, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memrun_create_with_ooo) {
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

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 2, ooo, 2, NULL, 0, &mr));
    TEST_ASSERT_NOT_NULL(mr);
    TEST_ASSERT_EQ(2, tl_memrun_run_len(mr));
    TEST_ASSERT_EQ(2, tl_memrun_ooo_len(mr));
    TEST_ASSERT_EQ(10, tl_memrun_min_ts(mr));
    TEST_ASSERT_EQ(40, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memrun_create_with_tombstones) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(tombs);

    run[0] = (tl_record_t){.ts = 50, .handle = 1};
    tombs[0] = (tl_interval_t){.start = 10, .end = 30, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, 0, tombs, 1, &mr));
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

TEST_DECLARE(memrun_create_tombstone_only) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(tombs);
    tombs[0] = (tl_interval_t){.start = 100, .end = 200, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, NULL, 0, NULL, 0, tombs, 1, &mr));
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

TEST_DECLARE(memrun_create_empty_einval) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_EINVAL, tl_memrun_create(&alloc, NULL, 0, NULL, 0, NULL, 0, &mr));
    TEST_ASSERT_NULL(mr);

    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memrun_bounds_include_tombstones) {
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
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, 0, tombs, 1, &mr));

    /* min_ts MUST include tombstone start (10), not just record (50) */
    TEST_ASSERT_EQ(10, tl_memrun_min_ts(mr));
    /* max_ts = max(50, 29) = 50 */
    TEST_ASSERT_EQ(50, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memrun_bounds_unbounded_tomb) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(tombs);

    run[0] = (tl_record_t){.ts = 50, .handle = 1};
    tombs[0] = (tl_interval_t){.start = 100, .end = 0, .end_unbounded = true};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, 0, tombs, 1, &mr));

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
TEST_DECLARE(memrun_bounds_tomb_extends_max) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(tombs);

    run[0] = (tl_record_t){.ts = 50, .handle = 1};
    tombs[0] = (tl_interval_t){.start = 100, .end = 200, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, 0, tombs, 1, &mr));

    /* min_ts = min(50, 100) = 50 */
    TEST_ASSERT_EQ(50, tl_memrun_min_ts(mr));
    /* max_ts MUST be 199 (tomb.end - 1), NOT 50! */
    TEST_ASSERT_EQ(199, tl_memrun_max_ts(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memrun_refcnt_acquire_release) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    run[0] = (tl_record_t){.ts = 10, .handle = 1};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, 0, NULL, 0, &mr));
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
 * Memtable Tests
 *===========================================================================*/

TEST_DECLARE(memtable_init_preallocates_sealed) {
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

TEST_DECLARE(memtable_insert_inorder) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 2));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 30, 3));

    TEST_ASSERT_EQ(3, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(0, tl_memtable_ooo_len(&mt));
    TEST_ASSERT_EQ(30, mt.last_inorder_ts);

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memtable_insert_ooo) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 30, 1));
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 10, 2)); /* OOO */
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_insert(&mt, 20, 3)); /* OOO */

    TEST_ASSERT_EQ(1, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(2, tl_memtable_ooo_len(&mt));

    /* Verify OOO is sorted */
    const tl_record_t* ooo = tl_memtable_ooo_data(&mt);
    TEST_ASSERT_EQ(10, ooo[0].ts);
    TEST_ASSERT_EQ(20, ooo[1].ts);

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memtable_insert_mixed) {
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
    TEST_ASSERT_EQ(2, tl_memtable_ooo_len(&mt));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memtable_insert_updates_epoch) {
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

TEST_DECLARE(memtable_insert_updates_bytes) {
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

TEST_DECLARE(memtable_insert_batch_fast_path) {
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
    TEST_ASSERT_EQ(0, tl_memtable_ooo_len(&mt));
    TEST_ASSERT_EQ(30, mt.last_inorder_ts);
    TEST_ASSERT_EQ(1, tl_memtable_epoch(&mt)); /* epoch++ once for batch */

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memtable_insert_batch_slow_path) {
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
    /* First record goes to run, rest go to OOO */
    TEST_ASSERT_EQ(1, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(2, tl_memtable_ooo_len(&mt));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memtable_insert_batch_no_double_count) {
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
    /* epoch should be 1, not 3 */
    TEST_ASSERT_EQ(1, tl_memtable_epoch(&mt));
    /* bytes should be 3 * record size */
    TEST_ASSERT_EQ(3 * TL_RECORD_SIZE, mt.active_bytes_est);

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memtable_insert_batch_full_sort_check) {
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

    /* Should NOT use fast path because batch is not fully sorted */
    /* Fast path would have all in run; slow path routes some to OOO */
    /* First 3 elements (10, 20, 25) go to run, 22 goes to OOO, 30 to run */
    TEST_ASSERT_EQ(4, tl_memtable_run_len(&mt));
    TEST_ASSERT_EQ(1, tl_memtable_ooo_len(&mt));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memtable_insert_tombstone) {
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

TEST_DECLARE(memtable_insert_tombstone_empty) {
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

TEST_DECLARE(memtable_insert_tombstone_invalid) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_memtable_t mt;
    TEST_ASSERT_STATUS(TL_OK, tl_memtable_init(&mt, &alloc, 1024, 256, 4));

    /* t1 > t2: invalid interval */
    TEST_ASSERT_STATUS(TL_EINVAL, tl_memtable_insert_tombstone(&mt, 30, 10));

    tl_memtable_destroy(&mt);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memtable_insert_tombstone_updates_epoch) {
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

TEST_DECLARE(memtable_seal_empty_noop) {
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

TEST_DECLARE(memtable_seal_basic) {
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

TEST_DECLARE(memtable_seal_preserves_on_ebusy) {
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

TEST_DECLARE(memtable_should_seal_bytes) {
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

TEST_DECLARE(memtable_should_seal_ooo) {
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

TEST_DECLARE(memtable_sealed_queue_fifo) {
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

TEST_DECLARE(memtable_pop_releases_refcnt) {
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

TEST_DECLARE(memtable_wait_for_space_timeout) {
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

/*===========================================================================
 * Flush Tests
 *===========================================================================*/

TEST_DECLARE(merge_iter_empty_both) {
    tl_merge_iter_t it;
    tl_merge_iter_init(&it, NULL, 0, NULL, 0);
    TEST_ASSERT(tl_merge_iter_done(&it));
    TEST_ASSERT_NULL(tl_merge_iter_next(&it));
}

TEST_DECLARE(merge_iter_single_input) {
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

TEST_DECLARE(merge_iter_two_inputs) {
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

TEST_DECLARE(merge_iter_stability) {
    /* Test that equal timestamps prefer first input (a) */
    tl_record_t a[2] = {
        {.ts = 10, .handle = 1}, /* From run */
        {.ts = 20, .handle = 2},
    };
    tl_record_t b[2] = {
        {.ts = 10, .handle = 100}, /* From OOO - same ts */
        {.ts = 20, .handle = 200},
    };

    tl_merge_iter_t it;
    tl_merge_iter_init(&it, a, 2, b, 2);

    const tl_record_t* r;

    /* ts=10 from 'a' should come first (stable) */
    r = tl_merge_iter_next(&it);
    TEST_ASSERT_EQ(10, r->ts);
    TEST_ASSERT_EQ(1, r->handle); /* from 'a' */

    r = tl_merge_iter_next(&it);
    TEST_ASSERT_EQ(10, r->ts);
    TEST_ASSERT_EQ(100, r->handle); /* from 'b' */

    r = tl_merge_iter_next(&it);
    TEST_ASSERT_EQ(20, r->ts);
    TEST_ASSERT_EQ(2, r->handle); /* from 'a' */

    r = tl_merge_iter_next(&it);
    TEST_ASSERT_EQ(20, r->ts);
    TEST_ASSERT_EQ(200, r->handle); /* from 'b' */
}

TEST_DECLARE(flush_build_records_only) {
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

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 2, ooo, 2, NULL, 0, &mr));

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

TEST_DECLARE(flush_build_with_tombstones) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 1);
    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(run);
    TEST_ASSERT_NOT_NULL(tombs);

    run[0] = (tl_record_t){.ts = 50, .handle = 1};
    tombs[0] = (tl_interval_t){.start = 10, .end = 30, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 1, NULL, 0, tombs, 1, &mr));

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

TEST_DECLARE(flush_build_tombstone_only) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_interval_t* tombs = TL_NEW_ARRAY(&alloc, tl_interval_t, 1);
    TEST_ASSERT_NOT_NULL(tombs);
    tombs[0] = (tl_interval_t){.start = 100, .end = 200, .end_unbounded = false};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, NULL, 0, NULL, 0, tombs, 1, &mr));

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

#ifdef TL_DEBUG
TEST_DECLARE(memrun_validate_correct) {
    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_record_t* run = TL_NEW_ARRAY(&alloc, tl_record_t, 2);
    TEST_ASSERT_NOT_NULL(run);
    run[0] = (tl_record_t){.ts = 10, .handle = 1};
    run[1] = (tl_record_t){.ts = 20, .handle = 2};

    tl_memrun_t* mr = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_memrun_create(&alloc, run, 2, NULL, 0, NULL, 0, &mr));
    TEST_ASSERT(tl_memrun_validate(mr));

    tl_memrun_release(mr);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(memtable_validate_correct) {
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
#endif

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_phase4_tests(void) {
    /* Memrun tests */
    RUN_TEST(memrun_create_records_only);
    RUN_TEST(memrun_create_with_ooo);
    RUN_TEST(memrun_create_with_tombstones);
    RUN_TEST(memrun_create_tombstone_only);
    RUN_TEST(memrun_create_empty_einval);
    RUN_TEST(memrun_bounds_include_tombstones);
    RUN_TEST(memrun_bounds_unbounded_tomb);
    RUN_TEST(memrun_bounds_tomb_extends_max);
    RUN_TEST(memrun_refcnt_acquire_release);

    /* Memtable tests */
    RUN_TEST(memtable_init_preallocates_sealed);
    RUN_TEST(memtable_insert_inorder);
    RUN_TEST(memtable_insert_ooo);
    RUN_TEST(memtable_insert_mixed);
    RUN_TEST(memtable_insert_updates_epoch);
    RUN_TEST(memtable_insert_updates_bytes);
    RUN_TEST(memtable_insert_batch_fast_path);
    RUN_TEST(memtable_insert_batch_slow_path);
    RUN_TEST(memtable_insert_batch_no_double_count);
    RUN_TEST(memtable_insert_batch_full_sort_check);
    RUN_TEST(memtable_insert_tombstone);
    RUN_TEST(memtable_insert_tombstone_empty);
    RUN_TEST(memtable_insert_tombstone_invalid);
    RUN_TEST(memtable_insert_tombstone_updates_epoch);
    RUN_TEST(memtable_seal_empty_noop);
    RUN_TEST(memtable_seal_basic);
    RUN_TEST(memtable_seal_preserves_on_ebusy);
    RUN_TEST(memtable_should_seal_bytes);
    RUN_TEST(memtable_should_seal_ooo);
    RUN_TEST(memtable_sealed_queue_fifo);
    RUN_TEST(memtable_pop_releases_refcnt);
    RUN_TEST(memtable_wait_for_space_timeout);

    /* Flush tests */
    RUN_TEST(merge_iter_empty_both);
    RUN_TEST(merge_iter_single_input);
    RUN_TEST(merge_iter_two_inputs);
    RUN_TEST(merge_iter_stability);
    RUN_TEST(flush_build_records_only);
    RUN_TEST(flush_build_with_tombstones);
    RUN_TEST(flush_build_tombstone_only);

#ifdef TL_DEBUG
    RUN_TEST(memrun_validate_correct);
    RUN_TEST(memtable_validate_correct);
#endif
}
