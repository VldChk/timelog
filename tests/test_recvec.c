#include <stdio.h>
#include "../src/internal/tl_recvec.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))

int test_recvec(void) {
    tl_recvec_t vec;
    tl_allocator_t alloc;
    tl_allocator_init_default(&alloc);

    /* Test init */
    tl_recvec_init(&vec, &alloc);
    TEST_ASSERT_EQ(tl_recvec_len(&vec), 0);
    TEST_ASSERT_EQ(tl_recvec_cap(&vec), 0);
    TEST_ASSERT(tl_recvec_empty(&vec));

    /* Test push */
    TEST_ASSERT_EQ(tl_recvec_push(&vec, 100, 1), TL_OK);
    TEST_ASSERT_EQ(tl_recvec_len(&vec), 1);
    TEST_ASSERT(!tl_recvec_empty(&vec));

    /* Test element access */
    tl_record_t* r = tl_recvec_at(&vec, 0);
    TEST_ASSERT_NE(r, NULL);
    TEST_ASSERT_EQ(r->ts, 100);
    TEST_ASSERT_EQ(r->handle, 1);

    /* Test push more elements */
    TEST_ASSERT_EQ(tl_recvec_push(&vec, 200, 2), TL_OK);
    TEST_ASSERT_EQ(tl_recvec_push(&vec, 50, 3), TL_OK);
    TEST_ASSERT_EQ(tl_recvec_len(&vec), 3);

    /* Test capacity growth */
    size_t cap = tl_recvec_cap(&vec);
    TEST_ASSERT(cap >= 3);

    /* Test batch push */
    tl_record_t batch[5] = {
        {300, 4}, {400, 5}, {150, 6}, {250, 7}, {350, 8}
    };
    TEST_ASSERT_EQ(tl_recvec_push_n(&vec, batch, 5), TL_OK);
    TEST_ASSERT_EQ(tl_recvec_len(&vec), 8);

    /* Test sort */
    tl_recvec_sort_by_ts(&vec);
    const tl_record_t* data = tl_recvec_data_const(&vec);
    for (size_t i = 1; i < vec.len; i++) {
        TEST_ASSERT(data[i-1].ts <= data[i].ts);
    }

    /* Test lower_bound */
    size_t idx = tl_recvec_lower_bound(&vec, 50);
    TEST_ASSERT_EQ(idx, 0);

    idx = tl_recvec_lower_bound(&vec, 150);
    TEST_ASSERT(idx < vec.len);
    TEST_ASSERT(data[idx].ts >= 150);
    if (idx > 0) {
        TEST_ASSERT(data[idx-1].ts < 150);
    }

    idx = tl_recvec_lower_bound(&vec, 500);
    TEST_ASSERT_EQ(idx, vec.len);

    /* Test empty lower_bound */
    tl_recvec_t empty;
    tl_recvec_init(&empty, &alloc);
    TEST_ASSERT_EQ(tl_recvec_lower_bound(&empty, 100), 0);
    tl_recvec_destroy(&empty);

    /* Test reserve */
    TEST_ASSERT_EQ(tl_recvec_reserve(&vec, 100), TL_OK);
    TEST_ASSERT(tl_recvec_cap(&vec) >= 100);
    TEST_ASSERT_EQ(tl_recvec_len(&vec), 8);  /* len unchanged */

    /* Test pin/unpin */
    TEST_ASSERT(!tl_recvec_is_pinned(&vec));
    tl_recvec_pin(&vec);
    TEST_ASSERT(tl_recvec_is_pinned(&vec));
    tl_recvec_unpin(&vec);
    TEST_ASSERT(!tl_recvec_is_pinned(&vec));

    /* Test shrink_to_fit */
    TEST_ASSERT_EQ(tl_recvec_shrink_to_fit(&vec), TL_OK);
    TEST_ASSERT_EQ(tl_recvec_cap(&vec), tl_recvec_len(&vec));

    /* Test shrink while pinned fails - need cap > len first */
    TEST_ASSERT_EQ(tl_recvec_reserve(&vec, tl_recvec_len(&vec) + 10), TL_OK);
    TEST_ASSERT(tl_recvec_cap(&vec) > tl_recvec_len(&vec));
    tl_recvec_pin(&vec);
    TEST_ASSERT_EQ(tl_recvec_shrink_to_fit(&vec), TL_EBUSY);
    tl_recvec_unpin(&vec);

    /* Test clear */
    tl_recvec_clear(&vec);
    TEST_ASSERT_EQ(tl_recvec_len(&vec), 0);
    TEST_ASSERT(tl_recvec_cap(&vec) > 0);  /* capacity preserved */

    /* Test move */
    tl_recvec_push(&vec, 999, 99);
    tl_recvec_t dst;
    tl_recvec_init(&dst, &alloc);
    tl_recvec_move(&dst, &vec);
    TEST_ASSERT_EQ(tl_recvec_len(&dst), 1);
    TEST_ASSERT_EQ(tl_recvec_len(&vec), 0);
    TEST_ASSERT_EQ(vec.data, NULL);

    /* Cleanup */
    tl_recvec_destroy(&dst);
    tl_recvec_destroy(&vec);

    /* Test init with capacity */
    tl_recvec_t vec2;
    TEST_ASSERT_EQ(tl_recvec_init_cap(&vec2, &alloc, 50), TL_OK);
    TEST_ASSERT_EQ(tl_recvec_cap(&vec2), 50);
    TEST_ASSERT_EQ(tl_recvec_len(&vec2), 0);
    tl_recvec_destroy(&vec2);

    /* Test out of bounds access */
    tl_recvec_t vec3;
    tl_recvec_init(&vec3, &alloc);
    tl_recvec_push(&vec3, 1, 1);
    TEST_ASSERT_EQ(tl_recvec_at(&vec3, 1), NULL);
    TEST_ASSERT_EQ(tl_recvec_at(&vec3, 100), NULL);
    tl_recvec_destroy(&vec3);

    return 0;
}
