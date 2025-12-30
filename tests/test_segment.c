#include <stdio.h>
#include <stdlib.h>
#include <string.h>
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

int test_segment(void) {
    tl_allocator_t alloc;
    tl_allocator_init_default(&alloc);
    tl_status_t st;

    /* Create some test pages */
    tl_ts_t ts1[] = {100, 200, 300};
    tl_handle_t h1[] = {1, 2, 3};
    tl_ts_t ts2[] = {400, 500};
    tl_handle_t h2[] = {4, 5};

    tl_page_t* p1 = NULL;
    tl_page_t* p2 = NULL;
    st = tl_page_create_soa(&alloc, ts1, h1, 3, &p1);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_page_create_soa(&alloc, ts2, h2, 2, &p2);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Test: Segment creation with pages */
    tl_page_t* pages[] = {p1, p2};
    tl_segment_t* seg = NULL;
    st = tl_segment_create(&alloc, pages, 2, NULL, TL_SEG_DELTA, 1, &seg);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(seg, NULL);
    TEST_ASSERT_EQ(seg->page_count, 2);
    TEST_ASSERT_EQ(seg->record_count, 5);
    TEST_ASSERT_EQ(seg->min_ts, 100);
    TEST_ASSERT_EQ(seg->max_ts, 500);
    TEST_ASSERT_EQ(seg->kind, TL_SEG_DELTA);
    TEST_ASSERT_EQ(seg->generation, 1);
    TEST_ASSERT_EQ(seg->catalog.n_pages, 2);
    TEST_ASSERT_EQ(seg->catalog.pages[0].min_ts, 100);
    TEST_ASSERT_EQ(seg->catalog.pages[1].min_ts, 400);
    TEST_ASSERT_EQ(tl_segment_validate(seg), TL_OK);

    /* Test: Segment overlap */
    TEST_ASSERT(tl_segment_overlaps(seg, 0, 1000));    /* Fully covers */
    TEST_ASSERT(tl_segment_overlaps(seg, 100, 200));   /* Partial */
    TEST_ASSERT(tl_segment_overlaps(seg, 450, 550));   /* Inside last page */
    TEST_ASSERT(!tl_segment_overlaps(seg, 0, 100));    /* Before (exclusive end) */
    TEST_ASSERT(!tl_segment_overlaps(seg, 501, 1000)); /* After */
    TEST_ASSERT(tl_segment_overlaps(seg, 500, 600));   /* Touches end */

    /* Test: Reference counting */
    TEST_ASSERT_EQ(tl_atomic_u32_load(&seg->refcnt), 1);

    uint32_t rc = tl_segment_acquire(seg);
    TEST_ASSERT_EQ(rc, 2);
    TEST_ASSERT_EQ(tl_atomic_u32_load(&seg->refcnt), 2);

    rc = tl_segment_acquire(seg);
    TEST_ASSERT_EQ(rc, 3);

    rc = tl_segment_release(seg);
    TEST_ASSERT_EQ(rc, 2);

    rc = tl_segment_release(seg);
    TEST_ASSERT_EQ(rc, 1);

    /* Release last reference - segment is destroyed */
    rc = tl_segment_release(seg);
    TEST_ASSERT_EQ(rc, 0);
    seg = NULL;

    /* Test: Segment with tombstones only */
    tl_intervals_t iset;
    tl_intervals_init(&iset, &alloc);
    st = tl_intervals_insert(&iset, 100, 200);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_intervals_insert(&iset, 300, 400);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_tombstones_t* tombs = NULL;
    st = tl_tombstones_create(&alloc, &iset, &tombs);
    TEST_ASSERT_EQ(st, TL_OK);
    tl_intervals_destroy(&iset);

    st = tl_segment_create_tombstone_only(&alloc, tombs, TL_SEG_DELTA, 2, &seg);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(seg, NULL);
    TEST_ASSERT_EQ(seg->page_count, 0);
    TEST_ASSERT_EQ(seg->record_count, 0);
    TEST_ASSERT_EQ(seg->min_ts, 100);  /* From tombstones */
    TEST_ASSERT_EQ(seg->max_ts, 400);  /* From tombstones */
    TEST_ASSERT_NE(seg->tombstones, NULL);
    TEST_ASSERT_EQ(tl_segment_validate(seg), TL_OK);

    tl_segment_release(seg);
    seg = NULL;

    /* Test: Segment with pages and tombstones */
    st = tl_page_create_soa(&alloc, ts1, h1, 3, &p1);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_intervals_init(&iset, &alloc);
    st = tl_intervals_insert(&iset, 50, 80);  /* Before page range */
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_intervals_insert(&iset, 350, 500); /* Extends past page range */
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_tombstones_create(&alloc, &iset, &tombs);
    TEST_ASSERT_EQ(st, TL_OK);
    tl_intervals_destroy(&iset);

    tl_page_t* single_page[] = {p1};
    st = tl_segment_create(&alloc, single_page, 1, tombs, TL_SEG_MAIN, 3, &seg);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(seg->min_ts, 50);   /* Extended by tombstones */
    TEST_ASSERT_EQ(seg->max_ts, 500);  /* Extended by tombstones */
    TEST_ASSERT_EQ(seg->page_count, 1);
    TEST_ASSERT_NE(seg->tombstones, NULL);

    tl_segment_release(seg);
    seg = NULL;

    /* Test: Empty segment rejected */
    st = tl_segment_create(&alloc, NULL, 0, NULL, TL_SEG_DELTA, 0, &seg);
    TEST_ASSERT_EQ(st, TL_EINVAL);

    /* Test: Tombstone-only with empty tombstones rejected */
    st = tl_segment_create_tombstone_only(&alloc, NULL, TL_SEG_DELTA, 0, &seg);
    TEST_ASSERT_EQ(st, TL_EINVAL);

    /* Test: Segment builder */
    tl_segment_builder_t builder;
    st = tl_segment_builder_init(&builder, &alloc, 3, TL_SEG_DELTA, 10);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add records - will auto-split into pages */
    st = tl_segment_builder_add(&builder, 100, 1);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_segment_builder_add(&builder, 200, 2);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_segment_builder_add(&builder, 300, 3);
    TEST_ASSERT_EQ(st, TL_OK);
    /* Now page is full, next add will trigger new page */
    st = tl_segment_builder_add(&builder, 400, 4);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_segment_builder_add(&builder, 500, 5);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Finish without tombstones */
    st = tl_segment_builder_finish(&builder, &seg);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(seg, NULL);
    TEST_ASSERT_EQ(seg->page_count, 2);  /* 3 + 2 records split into two pages */
    TEST_ASSERT_EQ(seg->record_count, 5);
    TEST_ASSERT_EQ(seg->min_ts, 100);
    TEST_ASSERT_EQ(seg->max_ts, 500);
    TEST_ASSERT_EQ(seg->generation, 10);
    TEST_ASSERT_EQ(tl_segment_validate(seg), TL_OK);

    tl_segment_release(seg);
    seg = NULL;
    tl_segment_builder_destroy(&builder);

    /* Test: Segment builder with tombstones */
    st = tl_segment_builder_init(&builder, &alloc, 5, TL_SEG_MAIN, 20);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_segment_builder_add(&builder, 100, 1);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_segment_builder_add(&builder, 200, 2);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add tombstones */
    tl_intervals_init(&iset, &alloc);
    st = tl_intervals_insert(&iset, 150, 180);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_tombstones_create(&alloc, &iset, &tombs);
    TEST_ASSERT_EQ(st, TL_OK);
    tl_intervals_destroy(&iset);

    tl_segment_builder_set_tombstones(&builder, tombs);

    st = tl_segment_builder_finish(&builder, &seg);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(seg, NULL);
    TEST_ASSERT_EQ(seg->page_count, 1);
    TEST_ASSERT_NE(seg->tombstones, NULL);
    TEST_ASSERT(tl_tombstones_contains(seg->tombstones, 160));

    tl_segment_release(seg);
    seg = NULL;
    tl_segment_builder_destroy(&builder);

    /* Test: Empty builder returns TL_EOF */
    st = tl_segment_builder_init(&builder, &alloc, 5, TL_SEG_DELTA, 0);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_segment_builder_finish(&builder, &seg);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_segment_builder_destroy(&builder);

    /* Test: Null safety */
    TEST_ASSERT(!tl_segment_overlaps(NULL, 0, 100));
    TEST_ASSERT_EQ(tl_segment_acquire(NULL), 0);
    TEST_ASSERT_EQ(tl_segment_release(NULL), 0);
    TEST_ASSERT_EQ(tl_segment_validate(NULL), TL_OK);

    return 0;
}
