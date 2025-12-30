#include <stdio.h>
#include "../src/internal/tl_intervals.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))

int test_intervals(void) {
    tl_intervals_t iset;
    tl_allocator_t alloc;
    tl_allocator_init_default(&alloc);

    /* Test init */
    tl_intervals_init(&iset, &alloc);
    TEST_ASSERT_EQ(tl_intervals_len(&iset), 0);
    TEST_ASSERT(tl_intervals_empty(&iset));
    TEST_ASSERT_EQ(tl_intervals_validate(&iset), TL_OK);

    /* Test insert single interval */
    TEST_ASSERT_EQ(tl_intervals_insert(&iset, 10, 20), TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&iset), 1);
    TEST_ASSERT_EQ(tl_intervals_validate(&iset), TL_OK);

    const tl_interval_t* iv = tl_intervals_at(&iset, 0);
    TEST_ASSERT_NE(iv, NULL);
    TEST_ASSERT_EQ(iv->start, 10);
    TEST_ASSERT_EQ(iv->end, 20);

    /* Test invalid interval (start >= end) */
    TEST_ASSERT_EQ(tl_intervals_insert(&iset, 50, 50), TL_EINVAL);
    TEST_ASSERT_EQ(tl_intervals_insert(&iset, 60, 50), TL_EINVAL);

    /* Test contains */
    TEST_ASSERT(tl_intervals_contains(&iset, 10));
    TEST_ASSERT(tl_intervals_contains(&iset, 15));
    TEST_ASSERT(tl_intervals_contains(&iset, 19));
    TEST_ASSERT(!tl_intervals_contains(&iset, 9));
    TEST_ASSERT(!tl_intervals_contains(&iset, 20));  /* half-open */
    TEST_ASSERT(!tl_intervals_contains(&iset, 25));

    /* Test insert disjoint interval (after) */
    TEST_ASSERT_EQ(tl_intervals_insert(&iset, 30, 40), TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&iset), 2);
    TEST_ASSERT_EQ(tl_intervals_validate(&iset), TL_OK);

    /* Test insert disjoint interval (before) */
    TEST_ASSERT_EQ(tl_intervals_insert(&iset, 0, 5), TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&iset), 3);
    TEST_ASSERT_EQ(tl_intervals_validate(&iset), TL_OK);

    /* Verify ordering */
    const tl_interval_t* data = tl_intervals_data(&iset);
    TEST_ASSERT_EQ(data[0].start, 0);
    TEST_ASSERT_EQ(data[1].start, 10);
    TEST_ASSERT_EQ(data[2].start, 30);

    /* Test coalescing overlapping intervals */
    TEST_ASSERT_EQ(tl_intervals_insert(&iset, 15, 25), TL_OK);  /* overlaps [10,20) */
    TEST_ASSERT_EQ(tl_intervals_len(&iset), 3);  /* merged with [10,20) -> [10,25) */
    TEST_ASSERT_EQ(tl_intervals_validate(&iset), TL_OK);
    TEST_ASSERT(tl_intervals_contains(&iset, 22));

    /* Test coalescing adjacent intervals */
    TEST_ASSERT_EQ(tl_intervals_insert(&iset, 25, 30), TL_OK);  /* touches [10,25) and [30,40) */
    TEST_ASSERT_EQ(tl_intervals_len(&iset), 2);  /* merged into [10,40) */
    TEST_ASSERT_EQ(tl_intervals_validate(&iset), TL_OK);

    /* Verify merged result */
    data = tl_intervals_data(&iset);
    TEST_ASSERT_EQ(data[0].start, 0);
    TEST_ASSERT_EQ(data[0].end, 5);
    TEST_ASSERT_EQ(data[1].start, 10);
    TEST_ASSERT_EQ(data[1].end, 40);

    /* Test find */
    size_t idx = tl_intervals_find(&iset, 3);
    TEST_ASSERT_EQ(idx, 0);  /* in [0,5) */

    idx = tl_intervals_find(&iset, 7);
    TEST_ASSERT_EQ(idx, 1);  /* first with start > 7 or containing 7 */

    idx = tl_intervals_find(&iset, 50);
    TEST_ASSERT_EQ(idx, 2);  /* past end */

    /* Test clear */
    tl_intervals_clear(&iset);
    TEST_ASSERT_EQ(tl_intervals_len(&iset), 0);
    TEST_ASSERT(tl_intervals_empty(&iset));

    /* Test clip */
    tl_intervals_insert(&iset, 0, 100);
    TEST_ASSERT_EQ(tl_intervals_clip(&iset, 20, 80), TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&iset), 1);
    iv = tl_intervals_at(&iset, 0);
    TEST_ASSERT_EQ(iv->start, 20);
    TEST_ASSERT_EQ(iv->end, 80);
    TEST_ASSERT_EQ(tl_intervals_validate(&iset), TL_OK);

    /* Test clip with multiple intervals */
    tl_intervals_clear(&iset);
    tl_intervals_insert(&iset, 0, 10);
    tl_intervals_insert(&iset, 20, 30);
    tl_intervals_insert(&iset, 40, 50);
    tl_intervals_insert(&iset, 60, 70);
    TEST_ASSERT_EQ(tl_intervals_clip(&iset, 25, 55), TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&iset), 2);
    data = tl_intervals_data(&iset);
    TEST_ASSERT_EQ(data[0].start, 25);
    TEST_ASSERT_EQ(data[0].end, 30);
    TEST_ASSERT_EQ(data[1].start, 40);
    TEST_ASSERT_EQ(data[1].end, 50);

    /* Test union */
    tl_intervals_t a, b, c;
    tl_intervals_init(&a, &alloc);
    tl_intervals_init(&b, &alloc);
    tl_intervals_init(&c, &alloc);

    tl_intervals_insert(&a, 0, 10);
    tl_intervals_insert(&a, 20, 30);

    tl_intervals_insert(&b, 5, 25);
    tl_intervals_insert(&b, 40, 50);

    TEST_ASSERT_EQ(tl_intervals_union(&c, &a, &b), TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&c), 2);  /* [0,30) and [40,50) */
    TEST_ASSERT_EQ(tl_intervals_validate(&c), TL_OK);
    data = tl_intervals_data(&c);
    TEST_ASSERT_EQ(data[0].start, 0);
    TEST_ASSERT_EQ(data[0].end, 30);
    TEST_ASSERT_EQ(data[1].start, 40);
    TEST_ASSERT_EQ(data[1].end, 50);

    /* Test copy */
    tl_intervals_t copy;
    tl_intervals_init(&copy, &alloc);
    TEST_ASSERT_EQ(tl_intervals_copy(&copy, &c), TL_OK);
    TEST_ASSERT_EQ(tl_intervals_len(&copy), tl_intervals_len(&c));
    TEST_ASSERT_EQ(tl_intervals_validate(&copy), TL_OK);

    /* Test move */
    tl_intervals_t moved;
    tl_intervals_init(&moved, &alloc);
    size_t c_len = tl_intervals_len(&c);
    tl_intervals_move(&moved, &c);
    TEST_ASSERT_EQ(tl_intervals_len(&moved), c_len);
    TEST_ASSERT_EQ(tl_intervals_len(&c), 0);
    TEST_ASSERT_EQ(c.data, NULL);

    /* Test init with capacity */
    tl_intervals_t cap;
    TEST_ASSERT_EQ(tl_intervals_init_cap(&cap, &alloc, 10), TL_OK);
    TEST_ASSERT_EQ(cap.cap, 10);
    TEST_ASSERT_EQ(cap.len, 0);
    tl_intervals_destroy(&cap);

    /* Test edge cases: empty interval set */
    tl_intervals_t empty;
    tl_intervals_init(&empty, &alloc);
    TEST_ASSERT(!tl_intervals_contains(&empty, 0));
    TEST_ASSERT_EQ(tl_intervals_find(&empty, 0), 0);
    tl_intervals_destroy(&empty);

    /* Cleanup */
    tl_intervals_destroy(&iset);
    tl_intervals_destroy(&a);
    tl_intervals_destroy(&b);
    tl_intervals_destroy(&c);
    tl_intervals_destroy(&copy);
    tl_intervals_destroy(&moved);

    return 0;
}
