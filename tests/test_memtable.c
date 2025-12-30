#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../src/internal/tl_memtable.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))

int test_memtable(void) {
    tl_allocator_t alloc;
    tl_allocator_init_default(&alloc);
    tl_status_t st;
    tl_memtable_t* mt = NULL;

    /* Test: Memtable creation */
    st = tl_memtable_create(&alloc, 1024 * 1024, 64 * 1024, &mt);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(mt, NULL);
    TEST_ASSERT_EQ(mt->memtable_max_bytes, 1024 * 1024);
    TEST_ASSERT_EQ(mt->target_page_bytes, 64 * 1024);
    TEST_ASSERT_EQ(mt->sealed_len, 0);

    /* Test: Single record insertion (first record, in-order) */
    st = tl_memtable_insert(mt, 100, 1001);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_run), 1);
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_ooo), 0);
    TEST_ASSERT(mt->active_has_inorder);
    TEST_ASSERT_EQ(mt->active_last_inorder_ts, 100);

    /* Test: In-order insertion (ts >= last) */
    st = tl_memtable_insert(mt, 200, 1002);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_memtable_insert(mt, 200, 1003);  /* Same timestamp is in-order */
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_memtable_insert(mt, 300, 1004);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_run), 4);
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_ooo), 0);
    TEST_ASSERT_EQ(mt->active_last_inorder_ts, 300);

    /* Test: Out-of-order insertion (ts < last) */
    st = tl_memtable_insert(mt, 150, 1005);  /* Between 100 and 200 */
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_run), 4);
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_ooo), 1);
    TEST_ASSERT(mt->active_ooo_has_data);
    TEST_ASSERT_EQ(mt->active_ooo_min, 150);
    TEST_ASSERT_EQ(mt->active_ooo_max, 150);

    /* More OOO insertions */
    st = tl_memtable_insert(mt, 50, 1006);   /* Before first */
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_memtable_insert(mt, 250, 1007);  /* Between 200 and 300 */
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_ooo), 3);
    TEST_ASSERT_EQ(mt->active_ooo_min, 50);
    TEST_ASSERT_EQ(mt->active_ooo_max, 250);

    /* Test: Tombstone insertion */
    st = tl_memtable_add_tombstone(mt, 400, 500);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&mt->active_tombs), 1);

    st = tl_memtable_add_tombstone(mt, 450, 550);  /* Overlapping - should coalesce */
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&mt->active_tombs), 1);  /* Coalesced */
    TEST_ASSERT(tl_intervals_contains(&mt->active_tombs, 520));

    st = tl_memtable_add_tombstone(mt, 600, 700);  /* Disjoint */
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&mt->active_tombs), 2);

    /* Test: Empty tombstone range is no-op */
    st = tl_memtable_add_tombstone(mt, 800, 800);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&mt->active_tombs), 2);  /* Unchanged */

    /* Test: Invalid tombstone range */
    st = tl_memtable_add_tombstone(mt, 900, 800);  /* t2 < t1 */
    TEST_ASSERT_EQ(st, TL_EINVAL);

    /* Test: Sealing active buffers */
    TEST_ASSERT(tl_memtable_can_seal(mt));
    st = tl_memtable_seal_active(mt);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(mt->sealed_len, 1);
    TEST_ASSERT_EQ(tl_memtable_sealed_count(mt), 1);

    /* Active buffers should be reset */
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_run), 0);
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_ooo), 0);
    TEST_ASSERT_EQ(tl_intervals_len(&mt->active_tombs), 0);
    TEST_ASSERT(!mt->active_has_inorder);
    TEST_ASSERT(!mt->active_ooo_has_data);

    /* Check sealed memrun */
    tl_memrun_t* mr = tl_memtable_peek_oldest_sealed(mt);
    TEST_ASSERT_NE(mr, NULL);
    TEST_ASSERT_EQ(mr->run_len, 4);
    TEST_ASSERT_EQ(mr->ooo_len, 3);
    TEST_ASSERT_EQ(mr->tombs_len, 2);
    TEST_ASSERT_EQ(tl_memrun_record_count(mr), 7);
    TEST_ASSERT(!tl_memrun_empty(mr));

    /* OOO should be sorted after seal */
    TEST_ASSERT_EQ(mr->ooo[0].ts, 50);
    TEST_ASSERT_EQ(mr->ooo[1].ts, 150);
    TEST_ASSERT_EQ(mr->ooo[2].ts, 250);

    /* Bounds should be computed from records */
    TEST_ASSERT_EQ(mr->min_ts, 50);   /* Smallest OOO */
    TEST_ASSERT_EQ(mr->max_ts, 300);  /* Largest in-order */

    /* Test: Sealing empty active returns TL_EOF */
    st = tl_memtable_seal_active(mt);
    TEST_ASSERT_EQ(st, TL_EOF);

    /* Test: Memrun reference counting */
    TEST_ASSERT_EQ(tl_atomic_u32_load(&mr->refcnt), 1);
    uint32_t rc = tl_memrun_acquire(mr);
    TEST_ASSERT_EQ(rc, 2);
    rc = tl_memrun_release(mr);
    TEST_ASSERT_EQ(rc, 1);

    /* Test: Multiple seals and FIFO ordering */
    st = tl_memtable_insert(mt, 1000, 2001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_memtable_seal_active(mt);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(mt->sealed_len, 2);

    st = tl_memtable_insert(mt, 2000, 2002);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_memtable_seal_active(mt);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(mt->sealed_len, 3);

    /* Oldest should still be the first memrun */
    tl_memrun_t* oldest = tl_memtable_peek_oldest_sealed(mt);
    TEST_ASSERT_EQ(oldest, mr);

    /* Pop oldest */
    oldest = tl_memtable_pop_oldest_sealed(mt);
    TEST_ASSERT_EQ(oldest, mr);
    TEST_ASSERT(oldest->is_published);
    TEST_ASSERT_EQ(mt->sealed_len, 2);

    /* Next oldest should be different */
    tl_memrun_t* next = tl_memtable_peek_oldest_sealed(mt);
    TEST_ASSERT_NE(next, oldest);
    TEST_ASSERT_EQ(next->run_len, 1);
    TEST_ASSERT_EQ(next->run[0].ts, 1000);

    /* Release the popped memrun */
    tl_memrun_release(oldest);

    /* Test: Backpressure when sealed queue is full */
    /* We have 2 sealed, need 2 more to reach TL_SEALED_MAX_RUNS (4) */
    st = tl_memtable_insert(mt, 3000, 3001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_memtable_seal_active(mt);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(mt->sealed_len, 3);

    st = tl_memtable_insert(mt, 4000, 4001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_memtable_seal_active(mt);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(mt->sealed_len, 4);

    /* Now sealed queue is full */
    TEST_ASSERT(!tl_memtable_can_seal(mt));

    st = tl_memtable_insert(mt, 5000, 5001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_memtable_seal_active(mt);
    TEST_ASSERT_EQ(st, TL_EBUSY);

    /* Pop one to make room */
    tl_memrun_t* popped = tl_memtable_pop_oldest_sealed(mt);
    TEST_ASSERT_NE(popped, NULL);
    tl_memrun_release(popped);
    TEST_ASSERT(tl_memtable_can_seal(mt));

    /* Now seal should work */
    st = tl_memtable_seal_active(mt);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Test: Memview snapshot */
    tl_memview_t* mv = NULL;
    st = tl_memtable_snapshot(mt, &mv);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(mv, NULL);

    /* Memview should capture sealed memruns (non-published ones) */
    TEST_ASSERT_EQ(mv->sealed_len, 4);  /* 3 old + 1 new sealed */

    /* Active should be empty (we sealed everything) */
    TEST_ASSERT_EQ(mv->active_run_len, 0);
    TEST_ASSERT_EQ(mv->active_ooo_len, 0);
    TEST_ASSERT_EQ(mv->active_tombs_len, 0);

    tl_memview_release(mv);

    /* Add some active data and take snapshot again */
    st = tl_memtable_insert(mt, 6000, 6001);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_memtable_insert(mt, 5500, 6002);  /* OOO */
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_memtable_add_tombstone(mt, 7000, 8000);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_memtable_snapshot(mt, &mv);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(mv->sealed_len, 4);
    TEST_ASSERT_EQ(mv->active_run_len, 1);
    TEST_ASSERT_EQ(mv->active_ooo_len, 1);
    TEST_ASSERT_EQ(mv->active_tombs_len, 1);

    /* OOO should be sorted in memview */
    TEST_ASSERT_EQ(mv->active_ooo[0].ts, 5500);

    /* Total record count */
    size_t total = tl_memview_record_count(mv);
    TEST_ASSERT(total > 0);

    TEST_ASSERT(!tl_memview_empty(mv));

    tl_memview_release(mv);

    /* Cleanup: destroy memtable */
    tl_memtable_destroy(mt);

    /* Test: Batch insertion with sorted hint */
    st = tl_memtable_create(&alloc, 1024 * 1024, 64 * 1024, &mt);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_record_t batch[] = {
        {100, 1}, {200, 2}, {300, 3}, {400, 4}, {500, 5}
    };

    st = tl_memtable_insert_batch(mt, batch, 5, TL_APPEND_HINT_MOSTLY_ORDER);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_run), 5);
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_ooo), 0);

    /* Fast path should have been used (all in-order) */
    TEST_ASSERT_EQ(mt->active_last_inorder_ts, 500);
    TEST_ASSERT_EQ(mt->write_count, 5);

    /* Test: Batch insertion without hint (mixed order) */
    tl_record_t mixed[] = {
        {600, 6}, {550, 7}, {700, 8}
    };

    st = tl_memtable_insert_batch(mt, mixed, 3, 0);  /* No hint */
    TEST_ASSERT_EQ(st, TL_OK);
    /* 600 goes to run (in-order), 550 to ooo, 700 to run */
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_run), 7);  /* 5 + 2 */
    TEST_ASSERT_EQ(tl_recvec_len(&mt->active_ooo), 1);

    tl_memtable_destroy(mt);

    /* Test: Memtable should_seal thresholds */
    st = tl_memtable_create(&alloc, 100, 64 * 1024, &mt);  /* Very small threshold */
    TEST_ASSERT_EQ(st, TL_OK);

    /* Initially should not seal */
    TEST_ASSERT(!tl_memtable_should_seal(mt));

    /* Add enough records to exceed threshold */
    for (int i = 0; i < 10; i++) {
        st = tl_memtable_insert(mt, i * 10, i);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    /* Now should trigger seal */
    TEST_ASSERT(tl_memtable_should_seal(mt));

    tl_memtable_destroy(mt);

    /* Test: Null safety */
    TEST_ASSERT_EQ(tl_memtable_insert(NULL, 100, 1), TL_EINVAL);
    TEST_ASSERT_EQ(tl_memtable_insert_batch(NULL, batch, 5, 0), TL_EINVAL);
    TEST_ASSERT_EQ(tl_memtable_add_tombstone(NULL, 100, 200), TL_EINVAL);
    TEST_ASSERT(!tl_memtable_should_seal(NULL));
    TEST_ASSERT(!tl_memtable_can_seal(NULL));
    TEST_ASSERT_EQ(tl_memtable_seal_active(NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_memtable_sealed_count(NULL), 0);
    TEST_ASSERT_EQ(tl_memtable_peek_oldest_sealed(NULL), NULL);
    TEST_ASSERT_EQ(tl_memtable_pop_oldest_sealed(NULL), NULL);
    TEST_ASSERT_EQ(tl_memrun_acquire(NULL), 0);
    TEST_ASSERT_EQ(tl_memrun_release(NULL), 0);
    TEST_ASSERT_EQ(tl_memrun_record_count(NULL), 0);
    TEST_ASSERT(tl_memrun_empty(NULL));
    TEST_ASSERT(tl_memview_empty(NULL));
    TEST_ASSERT_EQ(tl_memview_record_count(NULL), 0);

    return 0;
}
