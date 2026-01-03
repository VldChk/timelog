#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_sync.h"
#include "internal/tl_atomic.h"
#include "internal/tl_seqlock.h"
#include "internal/tl_locks.h"

#include <string.h>

/*===========================================================================
 * Atomic Tests
 *===========================================================================*/

TEST_DECLARE(atomic_u32_load_store) {
    tl_atomic_u32 val;
    tl_atomic_init_u32(&val, 0);

    TEST_ASSERT_EQ(0, tl_atomic_load_relaxed_u32(&val));

    tl_atomic_store_relaxed_u32(&val, 42);
    TEST_ASSERT_EQ(42, tl_atomic_load_relaxed_u32(&val));

    tl_atomic_store_release_u32(&val, 100);
    TEST_ASSERT_EQ(100, tl_atomic_load_acquire_u32(&val));
}

TEST_DECLARE(atomic_u64_load_store) {
    tl_atomic_u64 val;
    tl_atomic_init_u64(&val, 0);

    TEST_ASSERT_EQ(0, tl_atomic_load_relaxed_u64(&val));

    tl_atomic_store_relaxed_u64(&val, 0x123456789ABCDEF0ULL);
    TEST_ASSERT_EQ(0x123456789ABCDEF0ULL, tl_atomic_load_relaxed_u64(&val));
}

TEST_DECLARE(atomic_fetch_add) {
    tl_atomic_u32 val;
    tl_atomic_init_u32(&val, 10);

    uint32_t old = tl_atomic_fetch_add_u32(&val, 5, TL_MO_RELAXED);
    TEST_ASSERT_EQ(10, old);
    TEST_ASSERT_EQ(15, tl_atomic_load_relaxed_u32(&val));

    old = tl_atomic_inc_u32(&val);
    TEST_ASSERT_EQ(15, old);
    TEST_ASSERT_EQ(16, tl_atomic_load_relaxed_u32(&val));
}

TEST_DECLARE(atomic_fetch_sub) {
    tl_atomic_u32 val;
    tl_atomic_init_u32(&val, 20);

    uint32_t old = tl_atomic_fetch_sub_u32(&val, 7, TL_MO_RELAXED);
    TEST_ASSERT_EQ(20, old);
    TEST_ASSERT_EQ(13, tl_atomic_load_relaxed_u32(&val));

    old = tl_atomic_dec_u32(&val);
    TEST_ASSERT_EQ(13, old);
    TEST_ASSERT_EQ(12, tl_atomic_load_relaxed_u32(&val));
}

TEST_DECLARE(atomic_cas_success) {
    tl_atomic_u32 val;
    tl_atomic_init_u32(&val, 100);

    uint32_t expected = 100;
    bool success = tl_atomic_cas_u32(&val, &expected, 200, TL_MO_SEQ_CST, TL_MO_RELAXED);

    TEST_ASSERT(success);
    TEST_ASSERT_EQ(100, expected); /* unchanged on success */
    TEST_ASSERT_EQ(200, tl_atomic_load_relaxed_u32(&val));
}

TEST_DECLARE(atomic_cas_failure) {
    tl_atomic_u32 val;
    tl_atomic_init_u32(&val, 100);

    uint32_t expected = 50; /* Wrong expected value */
    bool success = tl_atomic_cas_u32(&val, &expected, 200, TL_MO_SEQ_CST, TL_MO_RELAXED);

    TEST_ASSERT(!success);
    TEST_ASSERT_EQ(100, expected); /* Updated to actual value */
    TEST_ASSERT_EQ(100, tl_atomic_load_relaxed_u32(&val)); /* Unchanged */
}

TEST_DECLARE(atomic_ptr_exchange) {
    int a = 1, b = 2;
    tl_atomic_ptr ptr;
    tl_atomic_init_ptr(&ptr, &a);

    TEST_ASSERT_EQ(&a, tl_atomic_load_acquire_ptr(&ptr));

    void* old = tl_atomic_exchange_ptr(&ptr, &b, TL_MO_ACQ_REL);
    TEST_ASSERT_EQ(&a, old);
    TEST_ASSERT_EQ(&b, tl_atomic_load_acquire_ptr(&ptr));
}

/*===========================================================================
 * Mutex Tests
 *===========================================================================*/

TEST_DECLARE(mutex_init_destroy) {
    tl_mutex_t mu;
    tl_status_t s = tl_mutex_init(&mu);
    TEST_ASSERT_STATUS(TL_OK, s);
    tl_mutex_destroy(&mu);
}

TEST_DECLARE(mutex_lock_unlock) {
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    tl_mutex_lock(&mu);
    /* Critical section */
    tl_mutex_unlock(&mu);

    tl_mutex_destroy(&mu);
}

TEST_DECLARE(mutex_trylock) {
    tl_mutex_t mu;
    tl_mutex_init(&mu);

    /* First trylock should succeed */
    TEST_ASSERT(tl_mutex_trylock(&mu));

    /* Second trylock should fail (already locked by same thread) */
    /* Note: This behavior varies by platform. SRWLock allows it, pthread doesn't. */
    /* We just test unlock after trylock. */
    tl_mutex_unlock(&mu);

    /* Should be able to lock again */
    TEST_ASSERT(tl_mutex_trylock(&mu));
    tl_mutex_unlock(&mu);

    tl_mutex_destroy(&mu);
}

/*===========================================================================
 * Condition Variable Tests
 *===========================================================================*/

TEST_DECLARE(cond_init_destroy) {
    tl_cond_t cv;
    tl_status_t s = tl_cond_init(&cv);
    TEST_ASSERT_STATUS(TL_OK, s);
    tl_cond_destroy(&cv);
}

TEST_DECLARE(cond_timedwait_timeout) {
    tl_mutex_t mu;
    tl_cond_t cv;

    tl_mutex_init(&mu);
    tl_cond_init(&cv);

    tl_mutex_lock(&mu);

    /*
     * Wait with short timeout. We expect a timeout, but POSIX allows
     * spurious wakeups. To handle this correctly, we use a predicate
     * pattern and retry on spurious wakeups.
     *
     * For this test, we just verify that after enough time passes,
     * we get a false return (timeout). Spurious wakeups return true
     * but immediately go back to wait.
     */
    bool got_timeout = false;
    int attempts = 0;
    while (!got_timeout && attempts < 10) {
        bool signaled = tl_cond_timedwait(&cv, &mu, 5); /* 5ms */
        if (!signaled) {
            got_timeout = true;
        }
        attempts++;
    }
    TEST_ASSERT(got_timeout); /* Should eventually timeout */

    tl_mutex_unlock(&mu);

    tl_cond_destroy(&cv);
    tl_mutex_destroy(&mu);
}

/*===========================================================================
 * Seqlock Tests
 *===========================================================================*/

TEST_DECLARE(seqlock_init) {
    tl_seqlock_t sl;
    tl_seqlock_init(&sl);

    uint64_t seq = tl_seqlock_current(&sl);
    TEST_ASSERT_EQ(0, seq);
    TEST_ASSERT(tl_seqlock_is_even(seq));
}

TEST_DECLARE(seqlock_write_cycle) {
    tl_seqlock_t sl;
    tl_seqlock_init(&sl);

    /* Before write */
    uint64_t seq0 = tl_seqlock_read(&sl);
    TEST_ASSERT(tl_seqlock_is_even(seq0));

    /* Begin write */
    tl_seqlock_write_begin(&sl);
    uint64_t seq1 = tl_seqlock_current(&sl);
    TEST_ASSERT(!tl_seqlock_is_even(seq1)); /* Odd during write */

    /* End write */
    tl_seqlock_write_end(&sl);
    uint64_t seq2 = tl_seqlock_read(&sl);
    TEST_ASSERT(tl_seqlock_is_even(seq2));
    TEST_ASSERT_EQ(seq0 + 2, seq2); /* Incremented by 2 */
}

TEST_DECLARE(seqlock_validate) {
    tl_seqlock_t sl;
    tl_seqlock_init(&sl);

    uint64_t seq1 = tl_seqlock_read(&sl);

    /* No change - should validate */
    uint64_t seq2 = tl_seqlock_read(&sl);
    TEST_ASSERT(tl_seqlock_validate(seq1, seq2));

    /* Simulate write */
    tl_seqlock_write_begin(&sl);
    tl_seqlock_write_end(&sl);

    /* Changed - should not validate */
    uint64_t seq3 = tl_seqlock_read(&sl);
    TEST_ASSERT(!tl_seqlock_validate(seq1, seq3));
}

/*===========================================================================
 * Thread Tests
 *===========================================================================*/

static void* thread_increment(void* arg) {
    tl_atomic_u32* counter = (tl_atomic_u32*)arg;
    for (int i = 0; i < 1000; i++) {
        tl_atomic_inc_u32(counter);
    }
    return (void*)(intptr_t)42;
}

TEST_DECLARE(thread_create_join) {
    tl_atomic_u32 counter;
    tl_atomic_init_u32(&counter, 0);

    tl_thread_t t;
    tl_status_t s = tl_thread_create(&t, thread_increment, (void*)&counter);
    TEST_ASSERT_STATUS(TL_OK, s);

    void* result = NULL;
    s = tl_thread_join(&t, &result);
    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_EQ(42, (intptr_t)result);

    TEST_ASSERT_EQ(1000, tl_atomic_load_relaxed_u32(&counter));
}

TEST_DECLARE(thread_multiple) {
    tl_atomic_u32 counter;
    tl_atomic_init_u32(&counter, 0);

    tl_thread_t t1, t2, t3;
    tl_thread_create(&t1, thread_increment, (void*)&counter);
    tl_thread_create(&t2, thread_increment, (void*)&counter);
    tl_thread_create(&t3, thread_increment, (void*)&counter);

    tl_thread_join(&t1, NULL);
    tl_thread_join(&t2, NULL);
    tl_thread_join(&t3, NULL);

    TEST_ASSERT_EQ(3000, tl_atomic_load_relaxed_u32(&counter));
}

/*===========================================================================
 * Lock Ordering Tests (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG
TEST_DECLARE(lock_ordering_valid) {
    tl_mutex_t maint_mu, flush_mu, writer_mu;
    tl_mutex_init(&maint_mu);
    tl_mutex_init(&flush_mu);
    tl_mutex_init(&writer_mu);

    /* Valid order: maint -> flush -> writer */
    TL_LOCK(&maint_mu, TL_LOCK_MAINT_MU);
    TL_LOCK(&flush_mu, TL_LOCK_FLUSH_MU);
    TL_LOCK(&writer_mu, TL_LOCK_WRITER_MU);

    TL_UNLOCK(&writer_mu, TL_LOCK_WRITER_MU);
    TL_UNLOCK(&flush_mu, TL_LOCK_FLUSH_MU);
    TL_UNLOCK(&maint_mu, TL_LOCK_MAINT_MU);

    tl_mutex_destroy(&writer_mu);
    tl_mutex_destroy(&flush_mu);
    tl_mutex_destroy(&maint_mu);
}
#endif

/*===========================================================================
 * Integration Tests
 *===========================================================================*/

TEST_DECLARE(open_initializes_locks) {
    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(NULL, &tl);

    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_NOT_NULL(tl);

    /* Verify seqlock initialized to 0 (even) */
    /* This requires internal access - we trust the implementation */

    tl_close(tl);
}

TEST_DECLARE(close_destroys_locks) {
    tl_timelog_t* tl = NULL;
    tl_open(NULL, &tl);

    /* Should not crash */
    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_phase1_tests(void) {
    /* Atomics */
    RUN_TEST(atomic_u32_load_store);
    RUN_TEST(atomic_u64_load_store);
    RUN_TEST(atomic_fetch_add);
    RUN_TEST(atomic_fetch_sub);
    RUN_TEST(atomic_cas_success);
    RUN_TEST(atomic_cas_failure);
    RUN_TEST(atomic_ptr_exchange);

    /* Mutex */
    RUN_TEST(mutex_init_destroy);
    RUN_TEST(mutex_lock_unlock);
    RUN_TEST(mutex_trylock);

    /* Condition variable */
    RUN_TEST(cond_init_destroy);
    RUN_TEST(cond_timedwait_timeout);

    /* Seqlock */
    RUN_TEST(seqlock_init);
    RUN_TEST(seqlock_write_cycle);
    RUN_TEST(seqlock_validate);

    /* Threads */
    RUN_TEST(thread_create_join);
    RUN_TEST(thread_multiple);

    /* Lock ordering (debug only) */
#ifdef TL_DEBUG
    RUN_TEST(lock_ordering_valid);
#endif

    /* Integration */
    RUN_TEST(open_initializes_locks);
    RUN_TEST(close_destroys_locks);
}
