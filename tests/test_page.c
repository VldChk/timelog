#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../src/internal/tl_page.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))

int test_page(void) {
    tl_allocator_t alloc;
    tl_allocator_init_default(&alloc);
    tl_page_t* page = NULL;
    tl_status_t st;

    /* Test: Empty page creation */
    st = tl_page_create(&alloc, NULL, 0, &page);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(page, NULL);
    TEST_ASSERT_EQ(page->count, 0);
    TEST_ASSERT_EQ(page->flags, TL_PAGE_FULLY_LIVE);
    TEST_ASSERT_EQ(tl_page_validate(page), TL_OK);
    tl_page_destroy(&alloc, page);
    page = NULL;

    /* Test: Page creation from records */
    tl_record_t records[] = {
        {100, 1001},
        {200, 1002},
        {200, 1003},  /* Duplicate timestamp */
        {300, 1004},
        {500, 1005}
    };
    st = tl_page_create(&alloc, records, 5, &page);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(page, NULL);
    TEST_ASSERT_EQ(page->count, 5);
    TEST_ASSERT_EQ(page->min_ts, 100);
    TEST_ASSERT_EQ(page->max_ts, 500);
    TEST_ASSERT_EQ(page->flags, TL_PAGE_FULLY_LIVE);
    TEST_ASSERT_EQ(page->ts[0], 100);
    TEST_ASSERT_EQ(page->ts[4], 500);
    TEST_ASSERT_EQ(page->h[0], 1001);
    TEST_ASSERT_EQ(page->h[4], 1005);
    TEST_ASSERT_EQ(tl_page_validate(page), TL_OK);
    tl_page_destroy(&alloc, page);
    page = NULL;

    /* Test: Page creation from SoA arrays */
    tl_ts_t ts_arr[] = {10, 20, 30, 40, 50};
    tl_handle_t h_arr[] = {101, 102, 103, 104, 105};
    st = tl_page_create_soa(&alloc, ts_arr, h_arr, 5, &page);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(page, NULL);
    TEST_ASSERT_EQ(page->count, 5);
    TEST_ASSERT_EQ(page->min_ts, 10);
    TEST_ASSERT_EQ(page->max_ts, 50);
    TEST_ASSERT_EQ(page->ts[2], 30);
    TEST_ASSERT_EQ(page->h[2], 103);
    TEST_ASSERT_EQ(tl_page_validate(page), TL_OK);

    /* Test: Lower bound search */
    /* Find first ts >= target */
    TEST_ASSERT_EQ(tl_page_lower_bound(page, 0), 0);    /* Before all */
    TEST_ASSERT_EQ(tl_page_lower_bound(page, 10), 0);   /* Exact first */
    TEST_ASSERT_EQ(tl_page_lower_bound(page, 15), 1);   /* Between 10 and 20 */
    TEST_ASSERT_EQ(tl_page_lower_bound(page, 20), 1);   /* Exact match */
    TEST_ASSERT_EQ(tl_page_lower_bound(page, 50), 4);   /* Exact last */
    TEST_ASSERT_EQ(tl_page_lower_bound(page, 51), 5);   /* After all */
    TEST_ASSERT_EQ(tl_page_lower_bound(page, 100), 5);  /* Way after */

    /* Test: Upper bound search */
    /* Find first ts > target */
    TEST_ASSERT_EQ(tl_page_upper_bound(page, 0), 0);    /* Before all */
    TEST_ASSERT_EQ(tl_page_upper_bound(page, 10), 1);   /* Exact first */
    TEST_ASSERT_EQ(tl_page_upper_bound(page, 15), 1);   /* Between */
    TEST_ASSERT_EQ(tl_page_upper_bound(page, 20), 2);   /* Exact match */
    TEST_ASSERT_EQ(tl_page_upper_bound(page, 50), 5);   /* Exact last */
    TEST_ASSERT_EQ(tl_page_upper_bound(page, 100), 5);  /* Way after */

    /* Test: Page overlap predicate */
    TEST_ASSERT(tl_page_overlaps(page, 0, 100, false));    /* Fully covers */
    TEST_ASSERT(tl_page_overlaps(page, 10, 20, false));    /* Partial start */
    TEST_ASSERT(tl_page_overlaps(page, 40, 60, false));    /* Partial end */
    TEST_ASSERT(tl_page_overlaps(page, 25, 35, false));    /* Inside */
    TEST_ASSERT(!tl_page_overlaps(page, 0, 10, false));    /* Before (exclusive end) */
    TEST_ASSERT(!tl_page_overlaps(page, 51, 100, false));  /* After */
    TEST_ASSERT(tl_page_overlaps(page, 50, 100, false));   /* Touches end */
    TEST_ASSERT(tl_page_overlaps(page, 0, 11, false));     /* Touches start */

    /* Test: Row deleted check (for FULLY_LIVE page) */
    TEST_ASSERT(!tl_page_row_deleted(page, 0));
    TEST_ASSERT(!tl_page_row_deleted(page, 4));
    TEST_ASSERT(!tl_page_row_deleted(page, 5));  /* Out of bounds */

    tl_page_destroy(&alloc, page);
    page = NULL;

    /* Test: Page catalog */
    tl_page_catalog_t cat;
    tl_page_catalog_init(&cat);
    TEST_ASSERT_EQ(cat.n_pages, 0);
    TEST_ASSERT_EQ(cat.pages, NULL);

    /* Create some pages for catalog */
    tl_page_t* p1 = NULL;
    tl_page_t* p2 = NULL;
    tl_page_t* p3 = NULL;

    tl_ts_t ts1[] = {10, 20};
    tl_handle_t h1[] = {1, 2};
    tl_ts_t ts2[] = {30, 40};
    tl_handle_t h2[] = {3, 4};
    tl_ts_t ts3[] = {50, 60, 70};
    tl_handle_t h3[] = {5, 6, 7};

    st = tl_page_create_soa(&alloc, ts1, h1, 2, &p1);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_page_create_soa(&alloc, ts2, h2, 2, &p2);
    TEST_ASSERT_EQ(st, TL_OK);
    st = tl_page_create_soa(&alloc, ts3, h3, 3, &p3);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Build catalog manually */
    cat.n_pages = 3;
    cat.pages = tl__malloc(&alloc, 3 * sizeof(tl_page_meta_t));
    TEST_ASSERT_NE(cat.pages, NULL);

    cat.pages[0] = (tl_page_meta_t){.min_ts = 10, .max_ts = 20, .count = 2, .flags = 0, .page = p1};
    cat.pages[1] = (tl_page_meta_t){.min_ts = 30, .max_ts = 40, .count = 2, .flags = 0, .page = p2};
    cat.pages[2] = (tl_page_meta_t){.min_ts = 50, .max_ts = 70, .count = 3, .flags = 0, .page = p3};

    /* Test: find_first - first page with max_ts >= t1 */
    TEST_ASSERT_EQ(tl_page_catalog_find_first(&cat, 0), 0);   /* Before all */
    TEST_ASSERT_EQ(tl_page_catalog_find_first(&cat, 10), 0);  /* Start of first */
    TEST_ASSERT_EQ(tl_page_catalog_find_first(&cat, 20), 0);  /* End of first */
    TEST_ASSERT_EQ(tl_page_catalog_find_first(&cat, 21), 1);  /* After first */
    TEST_ASSERT_EQ(tl_page_catalog_find_first(&cat, 40), 1);  /* End of second */
    TEST_ASSERT_EQ(tl_page_catalog_find_first(&cat, 41), 2);  /* After second */
    TEST_ASSERT_EQ(tl_page_catalog_find_first(&cat, 70), 2);  /* End of third */
    TEST_ASSERT_EQ(tl_page_catalog_find_first(&cat, 71), 3);  /* After all */

    /* Test: find_last - first page with min_ts >= t2, returns end of usable range */
    TEST_ASSERT_EQ(tl_page_catalog_find_last(&cat, 0, false), 0);    /* Before all */
    TEST_ASSERT_EQ(tl_page_catalog_find_last(&cat, 10, false), 0);   /* At first start */
    TEST_ASSERT_EQ(tl_page_catalog_find_last(&cat, 11, false), 1);   /* Inside first */
    TEST_ASSERT_EQ(tl_page_catalog_find_last(&cat, 30, false), 1);   /* At second start */
    TEST_ASSERT_EQ(tl_page_catalog_find_last(&cat, 50, false), 2);   /* At third start */
    TEST_ASSERT_EQ(tl_page_catalog_find_last(&cat, 51, false), 3);   /* Inside third */
    TEST_ASSERT_EQ(tl_page_catalog_find_last(&cat, 100, false), 3);  /* After all */

    /* Cleanup pages */
    tl_page_destroy(&alloc, p1);
    tl_page_destroy(&alloc, p2);
    tl_page_destroy(&alloc, p3);
    tl_page_catalog_destroy(&alloc, &cat);

    /* Test: Page builder */
    tl_page_builder_t builder;
    st = tl_page_builder_init(&builder, &alloc, 3);  /* Capacity of 3 */
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT(tl_page_builder_empty(&builder));
    TEST_ASSERT(tl_page_builder_has_room(&builder));
    TEST_ASSERT_EQ(tl_page_builder_count(&builder), 0);

    /* Add records */
    st = tl_page_builder_add(&builder, 100, 1001);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_page_builder_count(&builder), 1);
    TEST_ASSERT(!tl_page_builder_empty(&builder));

    st = tl_page_builder_add(&builder, 200, 1002);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_page_builder_add(&builder, 300, 1003);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT(!tl_page_builder_has_room(&builder));

    /* Try to add when full */
    st = tl_page_builder_add(&builder, 400, 1004);
    TEST_ASSERT_EQ(st, TL_EBUSY);

    /* Finish and create page */
    st = tl_page_builder_finish(&builder, &page);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(page, NULL);
    TEST_ASSERT_EQ(page->count, 3);
    TEST_ASSERT_EQ(page->min_ts, 100);
    TEST_ASSERT_EQ(page->max_ts, 300);
    TEST_ASSERT_EQ(tl_page_validate(page), TL_OK);
    tl_page_destroy(&alloc, page);
    page = NULL;

    /* Builder should be reset after finish */
    TEST_ASSERT(tl_page_builder_empty(&builder));

    /* Test finish on empty builder returns TL_EOF */
    st = tl_page_builder_finish(&builder, &page);
    TEST_ASSERT_EQ(st, TL_EOF);
    TEST_ASSERT_EQ(page, NULL);

    /* Test reset */
    st = tl_page_builder_add(&builder, 500, 1005);
    TEST_ASSERT_EQ(st, TL_OK);
    tl_page_builder_reset(&builder);
    TEST_ASSERT(tl_page_builder_empty(&builder));

    tl_page_builder_destroy(&builder);

    /* Test: Null safety */
    TEST_ASSERT_EQ(tl_page_lower_bound(NULL, 100), 0);
    TEST_ASSERT_EQ(tl_page_upper_bound(NULL, 100), 0);
    TEST_ASSERT(!tl_page_overlaps(NULL, 0, 100, false));
    TEST_ASSERT(!tl_page_row_deleted(NULL, 0));
    TEST_ASSERT_EQ(tl_page_validate(NULL), TL_OK);

    /* Test: tl_page_alloc_size */
    size_t sz = tl_page_alloc_size(100, false);
    TEST_ASSERT(sz >= sizeof(tl_page_t) + 100 * sizeof(tl_ts_t) + 100 * sizeof(tl_handle_t));

    sz = tl_page_alloc_size(100, true);
    TEST_ASSERT(sz > tl_page_alloc_size(100, false));  /* Should include bitset */

    return 0;
}
