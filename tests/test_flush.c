#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../src/internal/tl_flush.h"
#include "../src/internal/tl_segment.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))

/* Helper to create a memrun with in-order records only */
static tl_memrun_t* create_memrun_inorder(const tl_allocator_t* alloc,
                                           const tl_record_t* records, size_t n) {
    tl_memrun_t* mr = tl__calloc(alloc, 1, sizeof(tl_memrun_t));
    if (mr == NULL) return NULL;

    mr->alloc = alloc;
    tl_atomic_u32_store(&mr->refcnt, 1);
    mr->is_published = false;

    if (n > 0) {
        mr->run = tl__malloc(alloc, n * sizeof(tl_record_t));
        if (mr->run == NULL) {
            tl__free(alloc, mr);
            return NULL;
        }
        memcpy(mr->run, records, n * sizeof(tl_record_t));
        mr->run_len = n;
        mr->min_ts = records[0].ts;
        mr->max_ts = records[n - 1].ts;
    } else {
        mr->min_ts = TL_TS_MAX;
        mr->max_ts = TL_TS_MIN;
    }

    return mr;
}

/* Helper to create a memrun with both run and ooo parts */
static tl_memrun_t* create_memrun_mixed(const tl_allocator_t* alloc,
                                         const tl_record_t* run, size_t run_n,
                                         const tl_record_t* ooo, size_t ooo_n) {
    tl_memrun_t* mr = tl__calloc(alloc, 1, sizeof(tl_memrun_t));
    if (mr == NULL) return NULL;

    mr->alloc = alloc;
    tl_atomic_u32_store(&mr->refcnt, 1);
    mr->is_published = false;
    mr->min_ts = TL_TS_MAX;
    mr->max_ts = TL_TS_MIN;

    if (run_n > 0) {
        mr->run = tl__malloc(alloc, run_n * sizeof(tl_record_t));
        if (mr->run == NULL) {
            tl__free(alloc, mr);
            return NULL;
        }
        memcpy(mr->run, run, run_n * sizeof(tl_record_t));
        mr->run_len = run_n;

        if (mr->run[0].ts < mr->min_ts) mr->min_ts = mr->run[0].ts;
        if (mr->run[run_n - 1].ts > mr->max_ts) mr->max_ts = mr->run[run_n - 1].ts;
    }

    if (ooo_n > 0) {
        mr->ooo = tl__malloc(alloc, ooo_n * sizeof(tl_record_t));
        if (mr->ooo == NULL) {
            if (mr->run) tl__free(alloc, mr->run);
            tl__free(alloc, mr);
            return NULL;
        }
        memcpy(mr->ooo, ooo, ooo_n * sizeof(tl_record_t));
        mr->ooo_len = ooo_n;

        /* OOO should be sorted already for flush */
        if (mr->ooo[0].ts < mr->min_ts) mr->min_ts = mr->ooo[0].ts;
        if (mr->ooo[ooo_n - 1].ts > mr->max_ts) mr->max_ts = mr->ooo[ooo_n - 1].ts;
    }

    return mr;
}

/* Helper to add tombstones to a memrun */
static void memrun_add_tombstones(const tl_allocator_t* alloc, tl_memrun_t* mr,
                                   const tl_interval_t* tombs, size_t n) {
    if (n == 0) return;

    mr->tombs = tl__malloc(alloc, n * sizeof(tl_interval_t));
    if (mr->tombs == NULL) return;

    memcpy(mr->tombs, tombs, n * sizeof(tl_interval_t));
    mr->tombs_len = n;
}

int test_flush(void) {
    tl_allocator_t alloc;
    tl_allocator_init_default(&alloc);
    tl_status_t st;
    tl_segment_t* seg = NULL;

    /* Test: Flush memrun with in-order records only */
    {
        tl_record_t records[] = {
            {100, 1001}, {200, 1002}, {300, 1003}, {400, 1004}, {500, 1005}
        };
        tl_memrun_t* mr = create_memrun_inorder(&alloc, records, 5);
        TEST_ASSERT_NE(mr, NULL);

        st = tl_flush_memrun(&alloc, mr, 64 * 1024, 1, &seg);
        TEST_ASSERT_EQ(st, TL_OK);
        TEST_ASSERT_NE(seg, NULL);
        TEST_ASSERT_EQ(seg->record_count, 5);
        TEST_ASSERT_EQ(seg->min_ts, 100);
        TEST_ASSERT_EQ(seg->max_ts, 500);
        TEST_ASSERT_EQ(seg->kind, TL_SEG_DELTA);
        TEST_ASSERT_EQ(seg->generation, 1);
        TEST_ASSERT_EQ(seg->tombstones, NULL);
        TEST_ASSERT_EQ(tl_segment_validate(seg), TL_OK);

        tl_segment_release(seg);
        seg = NULL;
        tl_memrun_release(mr);
    }

    /* Test: Flush memrun with both run + ooo (2-way merge) */
    {
        /* Run: 100, 300, 500 */
        /* OOO: 50, 200, 400 (already sorted) */
        /* Expected merge: 50, 100, 200, 300, 400, 500 */
        tl_record_t run[] = {{100, 1}, {300, 3}, {500, 5}};
        tl_record_t ooo[] = {{50, 0}, {200, 2}, {400, 4}};

        tl_memrun_t* mr = create_memrun_mixed(&alloc, run, 3, ooo, 3);
        TEST_ASSERT_NE(mr, NULL);

        st = tl_flush_memrun(&alloc, mr, 64 * 1024, 2, &seg);
        TEST_ASSERT_EQ(st, TL_OK);
        TEST_ASSERT_NE(seg, NULL);
        TEST_ASSERT_EQ(seg->record_count, 6);
        TEST_ASSERT_EQ(seg->min_ts, 50);
        TEST_ASSERT_EQ(seg->max_ts, 500);

        /* Validate segment structure */
        TEST_ASSERT_EQ(tl_segment_validate(seg), TL_OK);

        /* Check that records are in sorted order in pages */
        if (seg->page_count > 0) {
            tl_page_t* p = seg->catalog.pages[0].page;
            for (uint32_t i = 1; i < p->count; i++) {
                TEST_ASSERT(p->ts[i] >= p->ts[i - 1]);
            }
        }

        tl_segment_release(seg);
        seg = NULL;
        tl_memrun_release(mr);
    }

    /* Test: Flush memrun with tombstones */
    {
        tl_record_t records[] = {{100, 1}, {200, 2}};
        tl_memrun_t* mr = create_memrun_inorder(&alloc, records, 2);
        TEST_ASSERT_NE(mr, NULL);

        tl_interval_t tombs[] = {{150, 180, false}, {250, 300, false}};
        memrun_add_tombstones(&alloc, mr, tombs, 2);
        TEST_ASSERT_EQ(mr->tombs_len, 2);

        st = tl_flush_memrun(&alloc, mr, 64 * 1024, 3, &seg);
        TEST_ASSERT_EQ(st, TL_OK);
        TEST_ASSERT_NE(seg, NULL);
        TEST_ASSERT_EQ(seg->record_count, 2);
        TEST_ASSERT_NE(seg->tombstones, NULL);
        TEST_ASSERT_EQ(tl_tombstones_len(seg->tombstones), 2);
        TEST_ASSERT(tl_tombstones_contains(seg->tombstones, 160));
        TEST_ASSERT(tl_tombstones_contains(seg->tombstones, 275));
        TEST_ASSERT(!tl_tombstones_contains(seg->tombstones, 100));

        tl_segment_release(seg);
        seg = NULL;
        tl_memrun_release(mr);
    }

    /* Test: Flush tombstone-only memrun */
    {
        tl_memrun_t* mr = tl__calloc(&alloc, 1, sizeof(tl_memrun_t));
        TEST_ASSERT_NE(mr, NULL);
        mr->alloc = &alloc;
        tl_atomic_u32_store(&mr->refcnt, 1);
        mr->min_ts = TL_TS_MAX;
        mr->max_ts = TL_TS_MIN;

        tl_interval_t tombs[] = {{100, 200, false}, {300, 400, false}};
        memrun_add_tombstones(&alloc, mr, tombs, 2);

        st = tl_flush_memrun(&alloc, mr, 64 * 1024, 4, &seg);
        TEST_ASSERT_EQ(st, TL_OK);
        TEST_ASSERT_NE(seg, NULL);
        TEST_ASSERT_EQ(seg->record_count, 0);
        TEST_ASSERT_EQ(seg->page_count, 0);
        TEST_ASSERT_NE(seg->tombstones, NULL);
        TEST_ASSERT_EQ(seg->min_ts, 100);
        TEST_ASSERT_EQ(seg->max_ts, 400);

        tl_segment_release(seg);
        seg = NULL;
        tl_memrun_release(mr);
    }

    /* Test: Empty memrun returns TL_EOF */
    {
        tl_memrun_t* mr = tl__calloc(&alloc, 1, sizeof(tl_memrun_t));
        TEST_ASSERT_NE(mr, NULL);
        mr->alloc = &alloc;
        tl_atomic_u32_store(&mr->refcnt, 1);
        mr->min_ts = TL_TS_MAX;
        mr->max_ts = TL_TS_MIN;

        st = tl_flush_memrun(&alloc, mr, 64 * 1024, 5, &seg);
        TEST_ASSERT_EQ(st, TL_EOF);
        TEST_ASSERT_EQ(seg, NULL);

        tl_memrun_release(mr);
    }

    /* Test: Multiple pages created from large memrun */
    {
        /* Create memrun with enough records to span multiple pages */
        const size_t N = 500;  /* Should create at least 2 pages with small capacity */
        tl_record_t* records = tl__malloc(&alloc, N * sizeof(tl_record_t));
        TEST_ASSERT_NE(records, NULL);

        for (size_t i = 0; i < N; i++) {
            records[i].ts = i * 10;
            records[i].handle = i + 1;
        }

        tl_memrun_t* mr = create_memrun_inorder(&alloc, records, N);
        TEST_ASSERT_NE(mr, NULL);
        tl__free(&alloc, records);

        /* Use small page size to force multiple pages */
        st = tl_flush_memrun(&alloc, mr, 1024, 6, &seg);  /* ~1KB pages */
        TEST_ASSERT_EQ(st, TL_OK);
        TEST_ASSERT_NE(seg, NULL);
        TEST_ASSERT_EQ(seg->record_count, N);
        TEST_ASSERT(seg->page_count >= 2);  /* Should have multiple pages */
        TEST_ASSERT_EQ(seg->min_ts, 0);
        TEST_ASSERT_EQ(seg->max_ts, (tl_ts_t)((N - 1) * 10));
        TEST_ASSERT_EQ(tl_segment_validate(seg), TL_OK);

        tl_segment_release(seg);
        seg = NULL;
        tl_memrun_release(mr);
    }

    /* Test: 2-way merge correctness with interleaved timestamps */
    {
        /* Run: 10, 30, 50, 70, 90 */
        /* OOO: 5, 25, 45, 65, 85 (sorted) */
        /* Expected: 5, 10, 25, 30, 45, 50, 65, 70, 85, 90 */
        tl_record_t run[] = {{10, 10}, {30, 30}, {50, 50}, {70, 70}, {90, 90}};
        tl_record_t ooo[] = {{5, 5}, {25, 25}, {45, 45}, {65, 65}, {85, 85}};

        tl_memrun_t* mr = create_memrun_mixed(&alloc, run, 5, ooo, 5);
        TEST_ASSERT_NE(mr, NULL);

        st = tl_flush_memrun(&alloc, mr, 64 * 1024, 7, &seg);
        TEST_ASSERT_EQ(st, TL_OK);
        TEST_ASSERT_NE(seg, NULL);
        TEST_ASSERT_EQ(seg->record_count, 10);

        /* Verify sorted order in segment */
        tl_page_t* p = seg->catalog.pages[0].page;
        tl_ts_t prev_ts = 0;
        for (uint32_t i = 0; i < p->count; i++) {
            TEST_ASSERT(p->ts[i] >= prev_ts);
            prev_ts = p->ts[i];
        }

        /* Check specific values */
        TEST_ASSERT_EQ(p->ts[0], 5);
        TEST_ASSERT_EQ(p->ts[1], 10);
        TEST_ASSERT_EQ(p->ts[9], 90);

        tl_segment_release(seg);
        seg = NULL;
        tl_memrun_release(mr);
    }

    /* Test: Null safety */
    TEST_ASSERT_EQ(tl_flush_memrun(&alloc, NULL, 64 * 1024, 0, &seg), TL_EINVAL);
    TEST_ASSERT_EQ(tl_flush_memrun(&alloc, NULL, 64 * 1024, 0, NULL), TL_EINVAL);

    return 0;
}
