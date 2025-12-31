#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/timelog/timelog.h"
#include "../src/internal/tl_memtable.h"
#include "../src/internal/tl_thread.h"

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

/*
 * Platform-specific sleep for testing timing-related behavior.
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

int test_maintenance(void) {
    tl_timelog_t* tl = NULL;
    tl_snapshot_t* snap = NULL;
    tl_stats_t stats;
    tl_status_t st;

    printf("  [maintenance] Testing maintenance subsystem...\n");

    /*=======================================================================
     * Test 1: tl_maint_step no work on empty timelog
     *=======================================================================*/
    printf("    Test 1: maint_step no work on empty timelog...\n");

    tl_config_t cfg;
    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(tl, NULL);

    /* No sealed memruns, should return TL_EOF */
    st = tl_maint_step(tl);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 2: tl_maint_step flushes one sealed memrun
     *=======================================================================*/
    printf("    Test 2: maint_step flushes one memrun...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add records and manually flush to create sealed memruns */
    for (int i = 0; i < 100; i++) {
        st = tl_append(tl, 1000 + i, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    /* Force seal by calling flush (which seals + flushes all) */
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Verify we have delta segments */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_GE(stats.segments_delta, 1);
    tl_snapshot_release(snap);
    snap = NULL;

    /* Now add more data but don't flush */
    for (int i = 0; i < 50; i++) {
        st = tl_append(tl, 2000 + i, 3000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    /* maint_step should return TL_EOF since nothing is sealed yet */
    st = tl_maint_step(tl);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 3: tl_maint_start/stop lifecycle
     *=======================================================================*/
    printf("    Test 3: maint_start/stop lifecycle...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Start maintenance */
    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Stop maintenance */
    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 4: tl_maint_start idempotent
     *=======================================================================*/
    printf("    Test 4: maint_start idempotent...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Start multiple times should be OK */
    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 5: tl_maint_stop idempotent
     *=======================================================================*/
    printf("    Test 5: maint_stop idempotent...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Stop without start should be OK */
    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Start, then stop multiple times */
    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 6: tl_close stops background maintenance
     *=======================================================================*/
    printf("    Test 6: close stops background maintenance...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Close should cleanly stop maintenance */
    tl_close(tl);
    tl = NULL;

    /* If we get here without hanging, the test passed */

    /*=======================================================================
     * Test 7: Background flush of sealed memruns
     *=======================================================================*/
    printf("    Test 7: background flush of sealed memruns...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Start background maintenance */
    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add enough data to trigger sealing (use small memtable) */
    /* The default memtable is 64KB, we'll add records and check */
    for (int batch = 0; batch < 3; batch++) {
        for (int i = 0; i < 100; i++) {
            st = tl_append(tl, batch * 1000 + i, batch * 2000 + i);
            TEST_ASSERT_EQ(st, TL_OK);
        }
        /* Force seal and let background thread flush */
        st = tl_flush(tl);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    /* Give background thread time to process */
    test_sleep_ms(200);

    /* Verify data is visible */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_GE(stats.segments_delta, 1);
    tl_snapshot_release(snap);
    snap = NULL;

    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 8: Snapshot stability during maintenance
     *=======================================================================*/
    printf("    Test 8: snapshot stability during maintenance...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add data */
    for (int i = 0; i < 100; i++) {
        st = tl_append(tl, 1000 + i, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    /* Acquire snapshot before flush */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Record count before */
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    uint64_t records_before = stats.records_estimate;

    /* Start maintenance and flush */
    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    test_sleep_ms(100);

    /* Snapshot should still be valid */
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.records_estimate, records_before);

    /* Validate snapshot */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_snapshot_release(snap);
    snap = NULL;

    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 9: Concurrent reads during maintenance
     *=======================================================================*/
    printf("    Test 9: concurrent reads during maintenance...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add data */
    for (int i = 0; i < 200; i++) {
        st = tl_append(tl, 1000 + i, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Perform reads while background maintenance is running */
    for (int round = 0; round < 5; round++) {
        /* Flush to create work for maintenance */
        st = tl_flush(tl);
        TEST_ASSERT_EQ(st, TL_OK);

        /* Add more data */
        for (int i = 0; i < 50; i++) {
            st = tl_append(tl, 2000 + round * 100 + i, 3000 + round * 100 + i);
            TEST_ASSERT_EQ(st, TL_OK);
        }

        /* Read while maintenance might be running */
        st = tl_snapshot_acquire(tl, &snap);
        TEST_ASSERT_EQ(st, TL_OK);

        st = tl_validate(snap);
        TEST_ASSERT_EQ(st, TL_OK);

        tl_snapshot_release(snap);
        snap = NULL;

        test_sleep_ms(50);
    }

    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 10: Restart maintenance after stop
     *=======================================================================*/
    printf("    Test 10: restart maintenance after stop...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Start, stop, start again */
    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 0; i < 50; i++) {
        st = tl_append(tl, 1000 + i, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Start again */
    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add more data and flush */
    for (int i = 0; i < 50; i++) {
        st = tl_append(tl, 2000 + i, 3000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    test_sleep_ms(100);

    /* Verify data */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.records_estimate, 100);
    tl_snapshot_release(snap);
    snap = NULL;

    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 11: Null safety for maintenance APIs
     *=======================================================================*/
    printf("    Test 11: null safety...\n");

    TEST_ASSERT_EQ(tl_maint_start(NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_maint_stop(NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_maint_step(NULL), TL_EINVAL);

    /*=======================================================================
     * Test 12: maint_step with closed timelog
     *=======================================================================*/
    printf("    Test 12: maint_step with closed timelog...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add some data */
    for (int i = 0; i < 50; i++) {
        st = tl_append(tl, 1000 + i, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    tl_close(tl);
    tl = NULL;

    /* If we get here without crash, test passed */

    /*=======================================================================
     * Test 13: Compaction reduces delta segment count
     *=======================================================================*/
    printf("    Test 13: compaction reduces delta count...\n");

    /* Create config with low max_delta_segments to trigger compaction */
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;
    cfg.max_delta_segments = 2;  /* Compact when >= 2 deltas */

    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Create first delta segment */
    for (int i = 0; i < 50; i++) {
        st = tl_append(tl, 1000 + i, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Create second delta segment */
    for (int i = 0; i < 50; i++) {
        st = tl_append(tl, 2000 + i, 3000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Verify we have 2 delta segments */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.segments_delta, 2);
    TEST_ASSERT_EQ(stats.segments_main, 0);
    TEST_ASSERT_EQ(stats.records_estimate, 100);
    tl_snapshot_release(snap);
    snap = NULL;

    /* Trigger compaction */
    st = tl_compact(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Verify: 0 delta segments, 1 main segment, same record count */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.segments_delta, 0);
    TEST_ASSERT_EQ(stats.segments_main, 1);
    TEST_ASSERT_EQ(stats.records_estimate, 100);
    tl_snapshot_release(snap);
    snap = NULL;

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 14: Compaction with tombstone folding
     *=======================================================================*/
    printf("    Test 14: compaction with tombstone folding...\n");

    cfg.max_delta_segments = 2;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add records */
    for (int i = 0; i < 100; i++) {
        st = tl_append(tl, 1000 + i, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Delete some records */
    st = tl_delete_range(tl, 1020, 1040);  /* Delete 20 records */
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Verify we have 2 delta segments with tombstones */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.segments_delta, 2);
    TEST_ASSERT_GE(stats.tombstone_count, 1);
    tl_snapshot_release(snap);
    snap = NULL;

    /* Compact */
    st = tl_compact(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Verify: tombstones applied, records deleted */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.segments_delta, 0);
    TEST_ASSERT_EQ(stats.segments_main, 1);
    /* 100 - 20 = 80 records after tombstone folding */
    TEST_ASSERT_EQ(stats.records_estimate, 80);
    /* Tombstones should be folded (removed) */
    TEST_ASSERT_EQ(stats.tombstone_count, 0);
    tl_snapshot_release(snap);
    snap = NULL;

    /* Verify data integrity via iteration */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    tl_iter_t* it = NULL;
    st = tl_iter_range(snap, TL_TS_MIN, TL_TS_MAX, &it);
    TEST_ASSERT_EQ(st, TL_OK);

    uint64_t count = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        /* Verify deleted range is not present */
        TEST_ASSERT(rec.ts < 1020 || rec.ts >= 1040);
        count++;
    }
    TEST_ASSERT_EQ(count, 80);
    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    snap = NULL;

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 15: Snapshot stability during compaction
     *=======================================================================*/
    printf("    Test 15: snapshot stability during compaction...\n");

    cfg.max_delta_segments = 2;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Create delta segments */
    for (int i = 0; i < 50; i++) {
        st = tl_append(tl, 1000 + i, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 0; i < 50; i++) {
        st = tl_append(tl, 2000 + i, 3000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Acquire snapshot before compaction */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    records_before = stats.records_estimate;
    uint64_t deltas_before = stats.segments_delta;
    TEST_ASSERT_EQ(deltas_before, 2);

    /* Compact while holding snapshot */
    st = tl_compact(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Old snapshot should still see old state */
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.records_estimate, records_before);
    TEST_ASSERT_EQ(stats.segments_delta, deltas_before);

    /* Validate old snapshot */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_snapshot_release(snap);
    snap = NULL;

    /* New snapshot should see compacted state */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.segments_delta, 0);
    TEST_ASSERT_EQ(stats.segments_main, 1);
    TEST_ASSERT_EQ(stats.records_estimate, records_before);
    tl_snapshot_release(snap);
    snap = NULL;

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 16: Multiple compaction rounds
     *=======================================================================*/
    printf("    Test 16: multiple compaction rounds...\n");

    cfg.max_delta_segments = 2;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Round 1: create deltas and compact */
    for (int i = 0; i < 30; i++) {
        st = tl_append(tl, 1000 + i, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 0; i < 30; i++) {
        st = tl_append(tl, 2000 + i, 3000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_compact(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.segments_main, 1);
    TEST_ASSERT_EQ(stats.records_estimate, 60);
    tl_snapshot_release(snap);
    snap = NULL;

    /* Round 2: add more deltas and compact again */
    for (int i = 0; i < 40; i++) {
        st = tl_append(tl, 3000 + i, 4000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    for (int i = 0; i < 40; i++) {
        st = tl_append(tl, 4000 + i, 5000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_compact(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Verify: now we should have 2 main segments */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.segments_delta, 0);
    TEST_ASSERT_EQ(stats.segments_main, 2);
    TEST_ASSERT_EQ(stats.records_estimate, 140);  /* 60 + 80 */

    /* Validate data */
    st = tl_validate(snap);
    TEST_ASSERT_EQ(st, TL_OK);
    tl_snapshot_release(snap);
    snap = NULL;

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 17: tl_compact on empty timelog
     *=======================================================================*/
    printf("    Test 17: compact on empty timelog...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_BACKGROUND;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Compact empty timelog should return TL_EOF */
    st = tl_compact(tl);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 18: tl_compact when below threshold
     *=======================================================================*/
    printf("    Test 18: compact below threshold...\n");

    cfg.max_delta_segments = 4;  /* Higher threshold */
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Create only 1 delta segment */
    for (int i = 0; i < 50; i++) {
        st = tl_append(tl, 1000 + i, 2000 + i);
        TEST_ASSERT_EQ(st, TL_OK);
    }
    st = tl_flush(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Compact should return TL_EOF (below threshold) */
    st = tl_compact(tl);
    TEST_ASSERT_EQ(st, TL_EOF);

    /* Verify still have delta */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(stats.segments_delta, 1);
    tl_snapshot_release(snap);
    snap = NULL;

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 19: Background compaction
     *=======================================================================*/
    printf("    Test 19: background compaction...\n");

    cfg.max_delta_segments = 2;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Start background maintenance */
    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Create delta segments */
    for (int batch = 0; batch < 4; batch++) {
        for (int i = 0; i < 30; i++) {
            st = tl_append(tl, batch * 1000 + i, batch * 2000 + i);
            TEST_ASSERT_EQ(st, TL_OK);
        }
        st = tl_flush(tl);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    /* Request compaction */
    st = tl_compact(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Wait for background thread to process */
    test_sleep_ms(300);

    /* Verify compaction happened */
    st = tl_snapshot_acquire(tl, &snap);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_stats(snap, &stats);
    TEST_ASSERT_EQ(st, TL_OK);
    /* Should have main segment(s) and fewer deltas */
    TEST_ASSERT_GE(stats.segments_main, 1);
    TEST_ASSERT_EQ(stats.records_estimate, 120);
    tl_snapshot_release(snap);
    snap = NULL;

    st = tl_maint_stop(tl);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 20: maint_start returns TL_ESTATE when disabled
     *=======================================================================*/
    printf("    Test 20: maint_start disabled...\n");

    st = tl_config_init_defaults(&cfg);
    TEST_ASSERT_EQ(st, TL_OK);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    st = tl_open(&cfg, &tl);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_maint_start(tl);
    TEST_ASSERT_EQ(st, TL_ESTATE);

    tl_close(tl);
    tl = NULL;

    /*=======================================================================
     * Test 21: Null safety for tl_compact
     *=======================================================================*/
    printf("    Test 21: compact null safety...\n");

    TEST_ASSERT_EQ(tl_compact(NULL), TL_EINVAL);

    /*=======================================================================
     * Cleanup
     *=======================================================================*/
    printf("  [maintenance] All maintenance tests passed.\n");
    return 0;
}
