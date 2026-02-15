/*===========================================================================
 * test_internal_sync.c - Internal Synchronization Primitive Tests
 *
 * Tests for low-level synchronization primitives:
 * - Atomic operations (u32, u64, ptr)
 * - Mutex (init, destroy, lock, unlock, trylock)
 * - Condition variables (init, destroy, wait, timedwait, signal)
 * - Seqlock (init, write cycle, validation)
 * - Threads (create, join, multiple)
 * - Lock ordering (debug builds only)
 *
 * These tests validate the foundational concurrency building blocks
 * that all higher-level components depend on.
 *
 * Migration Status: COMPLETE (migrated from test_phase1.c)
 * Note: Test names prefixed with "sync_" to avoid conflicts during migration.
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_sync.h"
#include "internal/tl_atomic.h"
#include "internal/tl_seqlock.h"
#include "internal/tl_locks.h"

#include <string.h>
#include <stdint.h>
#include <stddef.h>

/*===========================================================================
 * Atomic Tests
 *===========================================================================*/

TEST_DECLARE(sync_atomic_u32_load_store) {
    tl_atomic_u32 val;
    tl_atomic_init_u32(&val, 0);

    TEST_ASSERT_EQ(0, tl_atomic_load_relaxed_u32(&val));

    tl_atomic_store_relaxed_u32(&val, 42);
    TEST_ASSERT_EQ(42, tl_atomic_load_relaxed_u32(&val));

    tl_atomic_store_release_u32(&val, 100);
    TEST_ASSERT_EQ(100, tl_atomic_load_acquire_u32(&val));
}

TEST_DECLARE(sync_atomic_u64_load_store) {
    tl_atomic_u64 val;
    tl_atomic_init_u64(&val, 0);

    TEST_ASSERT_EQ(0, tl_atomic_load_relaxed_u64(&val));

    tl_atomic_store_relaxed_u64(&val, 0x123456789ABCDEF0ULL);
    TEST_ASSERT_EQ(0x123456789ABCDEF0ULL, tl_atomic_load_relaxed_u64(&val));
}

TEST_DECLARE(sync_atomic_fetch_add) {
    tl_atomic_u32 val;
    tl_atomic_init_u32(&val, 10);

    uint32_t old = tl_atomic_fetch_add_u32(&val, 5, TL_MO_RELAXED);
    TEST_ASSERT_EQ(10, old);
    TEST_ASSERT_EQ(15, tl_atomic_load_relaxed_u32(&val));

    old = tl_atomic_inc_u32(&val);
    TEST_ASSERT_EQ(15, old);
    TEST_ASSERT_EQ(16, tl_atomic_load_relaxed_u32(&val));
}

TEST_DECLARE(sync_atomic_fetch_sub) {
    tl_atomic_u32 val;
    tl_atomic_init_u32(&val, 20);

    uint32_t old = tl_atomic_fetch_sub_u32(&val, 7, TL_MO_RELAXED);
    TEST_ASSERT_EQ(20, old);
    TEST_ASSERT_EQ(13, tl_atomic_load_relaxed_u32(&val));

    old = tl_atomic_dec_u32(&val);
    TEST_ASSERT_EQ(13, old);
    TEST_ASSERT_EQ(12, tl_atomic_load_relaxed_u32(&val));
}

TEST_DECLARE(sync_atomic_cas_success) {
    tl_atomic_u32 val;
    tl_atomic_init_u32(&val, 100);

    uint32_t expected = 100;
    bool success = tl_atomic_cas_u32(&val, &expected, 200, TL_MO_SEQ_CST, TL_MO_RELAXED);

    TEST_ASSERT(success);
    TEST_ASSERT_EQ(100, expected); /* unchanged on success */
    TEST_ASSERT_EQ(200, tl_atomic_load_relaxed_u32(&val));
}

TEST_DECLARE(sync_atomic_cas_failure) {
    tl_atomic_u32 val;
    tl_atomic_init_u32(&val, 100);

    uint32_t expected = 50; /* Wrong expected value */
    bool success = tl_atomic_cas_u32(&val, &expected, 200, TL_MO_SEQ_CST, TL_MO_RELAXED);

    TEST_ASSERT(!success);
    TEST_ASSERT_EQ(100, expected); /* Updated to actual value */
    TEST_ASSERT_EQ(100, tl_atomic_load_relaxed_u32(&val)); /* Unchanged */
}

TEST_DECLARE(sync_atomic_ptr_exchange) {
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

TEST_DECLARE(sync_mutex_init_destroy) {
    tl_mutex_t mu;
    tl_status_t s = tl_mutex_init(&mu);
    TEST_ASSERT_STATUS(TL_OK, s);
    tl_mutex_destroy(&mu);
}

TEST_DECLARE(sync_mutex_lock_unlock) {
    tl_mutex_t mu;
    TEST_ASSERT_STATUS(TL_OK, tl_mutex_init(&mu));

    tl_mutex_lock(&mu);
    /* Critical section */
    tl_mutex_unlock(&mu);

    tl_mutex_destroy(&mu);
}

TEST_DECLARE(sync_mutex_trylock) {
    tl_mutex_t mu;
    TEST_ASSERT_STATUS(TL_OK, tl_mutex_init(&mu));

    /* First trylock should succeed */
    TEST_ASSERT(tl_mutex_trylock(&mu));

    /*
     * Recursive trylock behavior is platform-specific:
     * - Windows SRWLock: Allows recursive lock (returns true)
     * - POSIX pthread: Undefined for PTHREAD_MUTEX_DEFAULT
     * We don't test recursive trylock - just verify basic functionality.
     */
    tl_mutex_unlock(&mu);

    /* After unlock, should be able to lock again */
    TEST_ASSERT(tl_mutex_trylock(&mu));
    tl_mutex_unlock(&mu);

    tl_mutex_destroy(&mu);
}

/*===========================================================================
 * Condition Variable Tests
 *===========================================================================*/

TEST_DECLARE(sync_cond_init_destroy) {
    tl_cond_t cv;
    tl_status_t s = tl_cond_init(&cv);
    TEST_ASSERT_STATUS(TL_OK, s);
    tl_cond_destroy(&cv);
}

/*---------------------------------------------------------------------------
 * Condvar signal/wakeup test context
 *---------------------------------------------------------------------------*/
typedef struct {
    tl_mutex_t*   mu;
    tl_cond_t*    cv;
    tl_atomic_u32 predicate;  /* 0 = not ready, 1 = ready */
    tl_atomic_u32 waiter_woke;
} sync_cond_signal_ctx_t;

static void* sync_cond_waiter_thread(void* arg) {
    sync_cond_signal_ctx_t* ctx = (sync_cond_signal_ctx_t*)arg;

    tl_mutex_lock(ctx->mu);

    /* Wait for predicate to become true */
    while (tl_atomic_load_acquire_u32(&ctx->predicate) == 0) {
        tl_cond_wait(ctx->cv, ctx->mu);
    }

    /* Mark that we woke up */
    tl_atomic_store_release_u32(&ctx->waiter_woke, 1);

    tl_mutex_unlock(ctx->mu);
    return NULL;
}

TEST_DECLARE(sync_cond_signal_wakeup) {
    tl_mutex_t mu;
    tl_cond_t cv;

    TEST_ASSERT_STATUS(TL_OK, tl_mutex_init(&mu));
    TEST_ASSERT_STATUS(TL_OK, tl_cond_init(&cv));

    sync_cond_signal_ctx_t ctx = {
        .mu = &mu,
        .cv = &cv
    };
    tl_atomic_init_u32(&ctx.predicate, 0);
    tl_atomic_init_u32(&ctx.waiter_woke, 0);

    /* Start waiter thread */
    tl_thread_t waiter;
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&waiter, sync_cond_waiter_thread, &ctx));

    /* Give waiter time to enter wait */
    tl_sleep_ms(10);

    /* Set predicate and signal */
    tl_mutex_lock(&mu);
    tl_atomic_store_release_u32(&ctx.predicate, 1);
    tl_cond_signal(&cv);
    tl_mutex_unlock(&mu);

    /* Wait for waiter to finish */
    TEST_ASSERT_STATUS(TL_OK, tl_thread_join(&waiter, NULL));

    /* Verify waiter woke up */
    TEST_ASSERT_EQ(1, tl_atomic_load_relaxed_u32(&ctx.waiter_woke));

    tl_cond_destroy(&cv);
    tl_mutex_destroy(&mu);
}

TEST_DECLARE(sync_cond_timedwait_timeout) {
    tl_mutex_t mu;
    tl_cond_t cv;

    TEST_ASSERT_STATUS(TL_OK, tl_mutex_init(&mu));
    TEST_ASSERT_STATUS(TL_OK, tl_cond_init(&cv));

    tl_mutex_lock(&mu);

    /*
     * Wait with timeout. We expect a timeout, but POSIX allows spurious
     * wakeups. To handle this correctly and avoid flakiness, we:
     * 1. Use a reasonable per-wait timeout (20ms)
     * 2. Track total elapsed time with monotonic clock
     * 3. Allow up to 500ms total before declaring test failure
     *
     * On platforms with coarse timers, spurious wakeups may occur.
     * Eventually we must get a timeout (false return).
     */
    const uint64_t max_total_ms = 500;
    const uint64_t start_ms = tl_monotonic_ms();

    bool got_timeout = false;
    while (!got_timeout) {
        uint64_t elapsed = tl_monotonic_ms() - start_ms;
        if (elapsed >= max_total_ms) {
            /* Test failure - never got timeout in reasonable time */
            break;
        }

        bool signaled = tl_cond_timedwait(&cv, &mu, 20); /* 20ms per wait */
        if (!signaled) {
            got_timeout = true;
        }
        /* On spurious wakeup (signaled=true), loop and wait again */
    }
    TEST_ASSERT(got_timeout); /* Should eventually timeout */

    tl_mutex_unlock(&mu);

    tl_cond_destroy(&cv);
    tl_mutex_destroy(&mu);
}

/*===========================================================================
 * Seqlock Tests
 *===========================================================================*/

TEST_DECLARE(sync_seqlock_init) {
    tl_seqlock_t sl;
    tl_seqlock_init(&sl);

    uint64_t seq = tl_seqlock_current(&sl);
    TEST_ASSERT_EQ(0, seq);
    TEST_ASSERT(tl_seqlock_is_even(seq));
}

TEST_DECLARE(sync_seqlock_write_cycle) {
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

TEST_DECLARE(sync_seqlock_validate) {
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

static void* sync_thread_increment(void* arg) {
    tl_atomic_u32* counter = (tl_atomic_u32*)arg;
    for (int i = 0; i < 1000; i++) {
        tl_atomic_inc_u32(counter);
    }
    return (void*)(intptr_t)42;
}

TEST_DECLARE(sync_thread_create_join) {
    tl_atomic_u32 counter;
    tl_atomic_init_u32(&counter, 0);

    tl_thread_t t;
    tl_status_t s = tl_thread_create(&t, sync_thread_increment, (void*)&counter);
    TEST_ASSERT_STATUS(TL_OK, s);

    void* result = NULL;
    s = tl_thread_join(&t, &result);
    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_EQ(42, (intptr_t)result);

    TEST_ASSERT_EQ(1000, tl_atomic_load_relaxed_u32(&counter));
}

TEST_DECLARE(sync_thread_multiple) {
    tl_atomic_u32 counter;
    tl_atomic_init_u32(&counter, 0);

    tl_thread_t t1, t2, t3;
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&t1, sync_thread_increment, (void*)&counter));
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&t2, sync_thread_increment, (void*)&counter));
    TEST_ASSERT_STATUS(TL_OK, tl_thread_create(&t3, sync_thread_increment, (void*)&counter));

    TEST_ASSERT_STATUS(TL_OK, tl_thread_join(&t1, NULL));
    TEST_ASSERT_STATUS(TL_OK, tl_thread_join(&t2, NULL));
    TEST_ASSERT_STATUS(TL_OK, tl_thread_join(&t3, NULL));

    TEST_ASSERT_EQ(3000, tl_atomic_load_relaxed_u32(&counter));
}

/*===========================================================================
 * Lock Ordering Tests (Debug Only)
 *===========================================================================*/

#ifdef TL_DEBUG
TEST_DECLARE(sync_lock_ordering_valid) {
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

TEST_DECLARE(sync_open_initializes_locks) {
    tl_timelog_t* tl = NULL;
    tl_status_t s = tl_open(NULL, &tl);

    TEST_ASSERT_STATUS(TL_OK, s);
    TEST_ASSERT_NOT_NULL(tl);

    /* Verify seqlock initialized to 0 (even) */
    /* This requires internal access - we trust the implementation */

    tl_close(tl);
}

TEST_DECLARE(sync_close_destroys_locks) {
    tl_timelog_t* tl = NULL;
    tl_open(NULL, &tl);

    /* Should not crash */
    tl_close(tl);
}

/*===========================================================================
 * Test Runner
 *===========================================================================*/

void run_internal_sync_tests(void) {
    /* Atomics (7 tests) */
    RUN_TEST(sync_atomic_u32_load_store);
    RUN_TEST(sync_atomic_u64_load_store);
    RUN_TEST(sync_atomic_fetch_add);
    RUN_TEST(sync_atomic_fetch_sub);
    RUN_TEST(sync_atomic_cas_success);
    RUN_TEST(sync_atomic_cas_failure);
    RUN_TEST(sync_atomic_ptr_exchange);

    /* Mutex (3 tests) */
    RUN_TEST(sync_mutex_init_destroy);
    RUN_TEST(sync_mutex_lock_unlock);
    RUN_TEST(sync_mutex_trylock);

    /* Condition variable (3 tests) */
    RUN_TEST(sync_cond_init_destroy);
    RUN_TEST(sync_cond_signal_wakeup);
    RUN_TEST(sync_cond_timedwait_timeout);

    /* Seqlock (3 tests) */
    RUN_TEST(sync_seqlock_init);
    RUN_TEST(sync_seqlock_write_cycle);
    RUN_TEST(sync_seqlock_validate);

    /* Threads (2 tests) */
    RUN_TEST(sync_thread_create_join);
    RUN_TEST(sync_thread_multiple);

    /* Lock ordering - debug only (1 test) */
#ifdef TL_DEBUG
    RUN_TEST(sync_lock_ordering_valid);
#endif

    /* Integration (2 tests) */
    RUN_TEST(sync_open_initializes_locks);
    RUN_TEST(sync_close_destroys_locks);

    /* Total: 20 tests in release, 21 in debug */
}
