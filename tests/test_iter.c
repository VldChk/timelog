#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../src/internal/tl_iter.h"
#include "../src/internal/tl_segment.h"
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

int test_iter(void) {
    tl_allocator_t alloc;
    tl_allocator_init_default(&alloc);
    tl_status_t st;

    /*=======================================================================
     * Array Iterator Tests
     *=======================================================================*/

    /* Test: Empty array iterator */
    tl_array_iter_t* ait = NULL;
    st = tl_array_iter_create(&alloc, NULL, 0, 0, 100, false, &ait);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(ait, NULL);
    TEST_ASSERT_EQ(tl_array_iter_state(ait), TL_ITER_EOF);
    TEST_ASSERT_EQ(tl_array_iter_peek(ait), NULL);
    tl_array_iter_destroy(ait);

    /* Test: Array iterator with data */
    tl_record_t records[] = {
        {100, 1001}, {200, 1002}, {300, 1003}, {400, 1004}, {500, 1005}
    };

    st = tl_array_iter_create(&alloc, records, 5, 0, 1000, false, &ait);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_array_iter_state(ait), TL_ITER_READY);

    /* Read all records */
    const tl_record_t* rec = tl_array_iter_peek(ait);
    TEST_ASSERT_NE(rec, NULL);
    TEST_ASSERT_EQ(rec->ts, 100);
    TEST_ASSERT_EQ(rec->handle, 1001);

    st = tl_array_iter_advance(ait);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_array_iter_peek(ait);
    TEST_ASSERT_EQ(rec->ts, 200);

    st = tl_array_iter_advance(ait);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_array_iter_peek(ait);
    TEST_ASSERT_EQ(rec->ts, 300);

    st = tl_array_iter_advance(ait);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_array_iter_peek(ait);
    TEST_ASSERT_EQ(rec->ts, 400);

    st = tl_array_iter_advance(ait);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_array_iter_peek(ait);
    TEST_ASSERT_EQ(rec->ts, 500);

    st = tl_array_iter_advance(ait);
    TEST_ASSERT_EQ(st, TL_EOF);
    TEST_ASSERT_EQ(tl_array_iter_state(ait), TL_ITER_EOF);

    tl_array_iter_destroy(ait);

    /* Test: Array iterator with range filter */
    st = tl_array_iter_create(&alloc, records, 5, 200, 400, false, &ait);
    TEST_ASSERT_EQ(st, TL_OK);

    rec = tl_array_iter_peek(ait);
    TEST_ASSERT_EQ(rec->ts, 200);  /* First in range */

    st = tl_array_iter_advance(ait);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_array_iter_peek(ait);
    TEST_ASSERT_EQ(rec->ts, 300);

    st = tl_array_iter_advance(ait);
    TEST_ASSERT_EQ(st, TL_EOF);  /* 400 is excluded (half-open range) */

    tl_array_iter_destroy(ait);

    /* Test: Array iterator seek */
    st = tl_array_iter_create(&alloc, records, 5, 0, 1000, false, &ait);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_array_iter_seek(ait, 250);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_array_iter_peek(ait);
    TEST_ASSERT_EQ(rec->ts, 300);  /* First >= 250 */

    st = tl_array_iter_seek(ait, 500);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_array_iter_peek(ait);
    TEST_ASSERT_EQ(rec->ts, 500);

    st = tl_array_iter_seek(ait, 600);
    TEST_ASSERT_EQ(st, TL_EOF);  /* Beyond range */

    tl_array_iter_destroy(ait);

    /*=======================================================================
     * Two-Way Merge Iterator Tests
     *=======================================================================*/

    /* Test: Empty two-way iterator */
    tl_twoway_iter_t* twit = NULL;
    st = tl_twoway_iter_create(&alloc, NULL, 0, NULL, 0, 0, 100, false, &twit);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_twoway_iter_state(twit), TL_ITER_EOF);
    tl_twoway_iter_destroy(twit);

    /* Test: Two-way merge with run only */
    tl_record_t run[] = {{100, 1}, {200, 2}, {300, 3}};
    st = tl_twoway_iter_create(&alloc, run, 3, NULL, 0, 0, 1000, false, &twit);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_twoway_iter_state(twit), TL_ITER_READY);

    rec = tl_twoway_iter_peek(twit);
    TEST_ASSERT_EQ(rec->ts, 100);
    st = tl_twoway_iter_advance(twit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_twoway_iter_peek(twit);
    TEST_ASSERT_EQ(rec->ts, 200);

    tl_twoway_iter_destroy(twit);

    /* Test: Two-way merge with ooo only */
    tl_record_t ooo[] = {{150, 4}, {250, 5}};
    st = tl_twoway_iter_create(&alloc, NULL, 0, ooo, 2, 0, 1000, false, &twit);
    TEST_ASSERT_EQ(st, TL_OK);

    rec = tl_twoway_iter_peek(twit);
    TEST_ASSERT_EQ(rec->ts, 150);
    st = tl_twoway_iter_advance(twit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_twoway_iter_peek(twit);
    TEST_ASSERT_EQ(rec->ts, 250);

    tl_twoway_iter_destroy(twit);

    /* Test: Two-way merge interleaved */
    st = tl_twoway_iter_create(&alloc, run, 3, ooo, 2, 0, 1000, false, &twit);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Expected order: 100, 150, 200, 250, 300 */
    tl_ts_t expected_ts[] = {100, 150, 200, 250, 300};
    for (int i = 0; i < 5; i++) {
        TEST_ASSERT_EQ(tl_twoway_iter_state(twit), TL_ITER_READY);
        rec = tl_twoway_iter_peek(twit);
        TEST_ASSERT_NE(rec, NULL);
        TEST_ASSERT_EQ(rec->ts, expected_ts[i]);
        if (i < 4) {
            st = tl_twoway_iter_advance(twit);
            TEST_ASSERT_EQ(st, TL_OK);
        }
    }

    st = tl_twoway_iter_advance(twit);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_twoway_iter_destroy(twit);

    /* Test: Two-way merge with range filter */
    st = tl_twoway_iter_create(&alloc, run, 3, ooo, 2, 150, 260, false, &twit);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Expected order in range [150, 260): 150, 200, 250 */
    rec = tl_twoway_iter_peek(twit);
    TEST_ASSERT_EQ(rec->ts, 150);
    st = tl_twoway_iter_advance(twit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_twoway_iter_peek(twit);
    TEST_ASSERT_EQ(rec->ts, 200);
    st = tl_twoway_iter_advance(twit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_twoway_iter_peek(twit);
    TEST_ASSERT_EQ(rec->ts, 250);
    st = tl_twoway_iter_advance(twit);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_twoway_iter_destroy(twit);

    /* Test: Two-way merge seek */
    st = tl_twoway_iter_create(&alloc, run, 3, ooo, 2, 0, 1000, false, &twit);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_twoway_iter_seek(twit, 175);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_twoway_iter_peek(twit);
    TEST_ASSERT_EQ(rec->ts, 200);  /* First >= 175 */

    tl_twoway_iter_destroy(twit);

    /*=======================================================================
     * Segment Iterator Tests
     *=======================================================================*/

    /* Test: Empty segment iterator */
    tl_segment_iter_t* sit = NULL;
    st = tl_segment_iter_create(&alloc, NULL, 0, 1000, false, &sit);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_segment_iter_state(sit), TL_ITER_EOF);
    tl_segment_iter_destroy(sit);

    /* Test: Segment iterator with real segment */
    /* Create a segment with some pages */
    tl_segment_builder_t builder;
    st = tl_segment_builder_init(&builder, &alloc, 3, TL_SEG_DELTA, 1);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Add records: 100, 200, 300, 400, 500, 600 (will create 2 pages of 3 each) */
    for (int i = 1; i <= 6; i++) {
        st = tl_segment_builder_add(&builder, i * 100, i * 1000);
        TEST_ASSERT_EQ(st, TL_OK);
    }

    tl_segment_t* seg = NULL;
    st = tl_segment_builder_finish(&builder, &seg);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(seg, NULL);
    TEST_ASSERT_EQ(seg->page_count, 2);
    TEST_ASSERT_EQ(seg->record_count, 6);

    tl_segment_builder_destroy(&builder);

    /* Iterate entire segment */
    st = tl_segment_iter_create(&alloc, seg, 0, 1000, false, &sit);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_segment_iter_state(sit), TL_ITER_READY);

    int count = 0;
    while (tl_segment_iter_state(sit) == TL_ITER_READY) {
        rec = tl_segment_iter_peek(sit);
        TEST_ASSERT_NE(rec, NULL);
        count++;
        TEST_ASSERT_EQ(rec->ts, count * 100);
        TEST_ASSERT_EQ(rec->handle, count * 1000);
        tl_segment_iter_advance(sit);
    }
    TEST_ASSERT_EQ(count, 6);

    tl_segment_iter_destroy(sit);

    /* Test: Segment iterator with range */
    st = tl_segment_iter_create(&alloc, seg, 250, 450, false, &sit);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Should get 300, 400 */
    rec = tl_segment_iter_peek(sit);
    TEST_ASSERT_EQ(rec->ts, 300);
    st = tl_segment_iter_advance(sit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_segment_iter_peek(sit);
    TEST_ASSERT_EQ(rec->ts, 400);
    st = tl_segment_iter_advance(sit);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_segment_iter_destroy(sit);

    /* Test: Segment iterator seek */
    st = tl_segment_iter_create(&alloc, seg, 0, 1000, false, &sit);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_segment_iter_seek(sit, 350);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_segment_iter_peek(sit);
    TEST_ASSERT_EQ(rec->ts, 400);  /* First >= 350 */

    tl_segment_iter_destroy(sit);

    /* Test: Segment iterator with non-overlapping range */
    st = tl_segment_iter_create(&alloc, seg, 700, 800, false, &sit);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_segment_iter_state(sit), TL_ITER_EOF);
    tl_segment_iter_destroy(sit);

    /* Cleanup segment */
    tl_segment_release(seg);

    /*=======================================================================
     * Null Safety Tests
     *=======================================================================*/

    TEST_ASSERT_EQ(tl_array_iter_state(NULL), TL_ITER_EOF);
    TEST_ASSERT_EQ(tl_array_iter_peek(NULL), NULL);
    TEST_ASSERT_EQ(tl_array_iter_advance(NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_array_iter_seek(NULL, 100), TL_EINVAL);
    tl_array_iter_destroy(NULL);  /* Should not crash */

    TEST_ASSERT_EQ(tl_twoway_iter_state(NULL), TL_ITER_EOF);
    TEST_ASSERT_EQ(tl_twoway_iter_peek(NULL), NULL);
    TEST_ASSERT_EQ(tl_twoway_iter_advance(NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_twoway_iter_seek(NULL, 100), TL_EINVAL);
    tl_twoway_iter_destroy(NULL);

    TEST_ASSERT_EQ(tl_segment_iter_state(NULL), TL_ITER_EOF);
    TEST_ASSERT_EQ(tl_segment_iter_peek(NULL), NULL);
    TEST_ASSERT_EQ(tl_segment_iter_advance(NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_segment_iter_seek(NULL, 100), TL_EINVAL);
    tl_segment_iter_destroy(NULL);

    return 0;
}
