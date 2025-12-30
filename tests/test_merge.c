#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../src/internal/tl_merge.h"
#include "../src/internal/tl_filter.h"
#include "../src/internal/tl_iter.h"
#include "../src/internal/tl_plan.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))

/*
 * Array iterator vtable adapters for testing.
 */
static const tl_record_t* array_iter_peek_adapter(void* self) {
    return tl_array_iter_peek((tl_array_iter_t*)self);
}

static tl_status_t array_iter_advance_adapter(void* self) {
    return tl_array_iter_advance((tl_array_iter_t*)self);
}

static tl_status_t array_iter_seek_adapter(void* self, tl_ts_t ts) {
    return tl_array_iter_seek((tl_array_iter_t*)self, ts);
}

static tl_iter_state_t array_iter_state_adapter(void* self) {
    return tl_array_iter_state((tl_array_iter_t*)self);
}

static void array_iter_destroy_adapter(void* self) {
    tl_array_iter_destroy((tl_array_iter_t*)self);
}

static const tl_iter_vtable_t array_vtable = {
    .peek = array_iter_peek_adapter,
    .advance = array_iter_advance_adapter,
    .seek = array_iter_seek_adapter,
    .state = array_iter_state_adapter,
    .destroy = array_iter_destroy_adapter
};

/*
 * Helper: create a qplan with array iterators for testing.
 */
static tl_status_t create_test_plan(const tl_allocator_t* alloc,
                                     const tl_record_t** arrays,
                                     const size_t* lengths,
                                     uint32_t n_arrays,
                                     tl_ts_t t1,
                                     tl_ts_t t2,
                                     tl_qplan_t** out) {
    tl_qplan_t* plan = tl__calloc(alloc, 1, sizeof(tl_qplan_t));
    if (plan == NULL) return TL_ENOMEM;

    plan->alloc = alloc;
    plan->t1 = t1;
    plan->t2 = t2;

    if (n_arrays > 0) {
        plan->iters = tl__malloc(alloc, n_arrays * sizeof(tl_component_iter_t));
        if (plan->iters == NULL) {
            tl__free(alloc, plan);
            return TL_ENOMEM;
        }
        plan->iters_cap = n_arrays;

        for (uint32_t i = 0; i < n_arrays; i++) {
            tl_array_iter_t* ait = NULL;
            tl_status_t st = tl_array_iter_create(alloc, arrays[i], lengths[i], t1, t2, &ait);
            if (st != TL_OK) {
                /* Cleanup on failure */
                for (uint32_t j = 0; j < i; j++) {
                    array_vtable.destroy(plan->iters[j].impl);
                }
                tl__free(alloc, plan->iters);
                tl__free(alloc, plan);
                return st;
            }

            /* Only add if iterator has data */
            if (tl_array_iter_state(ait) == TL_ITER_READY) {
                plan->iters[plan->n_iters].vtable = &array_vtable;
                plan->iters[plan->n_iters].impl = ait;
                plan->iters[plan->n_iters].component_id = i;
                plan->n_iters++;
            } else {
                tl_array_iter_destroy(ait);
            }
        }
    }

    *out = plan;
    return TL_OK;
}

int test_merge(void) {
    tl_allocator_t alloc;
    tl_allocator_init_default(&alloc);
    tl_status_t st;

    /*=======================================================================
     * Merge Iterator Tests
     *=======================================================================*/

    /* Test: Empty merge iterator (no plan) */
    tl_merge_iter_t* mit = NULL;
    st = tl_merge_iter_create(&alloc, NULL, &mit);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(mit, NULL);
    TEST_ASSERT_EQ(tl_merge_iter_state(mit), TL_ITER_EOF);
    TEST_ASSERT_EQ(tl_merge_iter_peek(mit), NULL);
    tl_merge_iter_destroy(mit);

    /* Test: Empty merge iterator (empty plan) */
    tl_qplan_t* plan = NULL;
    st = create_test_plan(&alloc, NULL, NULL, 0, 0, 1000, &plan);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_merge_iter_create(&alloc, plan, &mit);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_merge_iter_state(mit), TL_ITER_EOF);
    tl_merge_iter_destroy(mit);
    tl_qplan_destroy(plan);

    /* Test: Single source merge */
    tl_record_t arr1[] = {{100, 1001}, {200, 1002}, {300, 1003}};
    const tl_record_t* arrays1[] = {arr1};
    size_t lengths1[] = {3};

    st = create_test_plan(&alloc, arrays1, lengths1, 1, 0, 1000, &plan);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(plan->n_iters, 1);

    st = tl_merge_iter_create(&alloc, plan, &mit);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_merge_iter_state(mit), TL_ITER_READY);

    const tl_record_t* rec = tl_merge_iter_peek(mit);
    TEST_ASSERT_NE(rec, NULL);
    TEST_ASSERT_EQ(rec->ts, 100);
    TEST_ASSERT_EQ(rec->handle, 1001);

    st = tl_merge_iter_advance(mit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_merge_iter_peek(mit);
    TEST_ASSERT_EQ(rec->ts, 200);

    st = tl_merge_iter_advance(mit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_merge_iter_peek(mit);
    TEST_ASSERT_EQ(rec->ts, 300);

    st = tl_merge_iter_advance(mit);
    TEST_ASSERT_EQ(st, TL_EOF);
    TEST_ASSERT_EQ(tl_merge_iter_state(mit), TL_ITER_EOF);

    tl_merge_iter_destroy(mit);
    tl_qplan_destroy(plan);

    /* Test: Two-source merge (non-overlapping) */
    tl_record_t arr2a[] = {{100, 1}, {200, 2}, {300, 3}};
    tl_record_t arr2b[] = {{400, 4}, {500, 5}, {600, 6}};
    const tl_record_t* arrays2[] = {arr2a, arr2b};
    size_t lengths2[] = {3, 3};

    st = create_test_plan(&alloc, arrays2, lengths2, 2, 0, 1000, &plan);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(plan->n_iters, 2);

    st = tl_merge_iter_create(&alloc, plan, &mit);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Expected: 100, 200, 300, 400, 500, 600 */
    tl_ts_t expected2[] = {100, 200, 300, 400, 500, 600};
    for (int i = 0; i < 6; i++) {
        TEST_ASSERT_EQ(tl_merge_iter_state(mit), TL_ITER_READY);
        rec = tl_merge_iter_peek(mit);
        TEST_ASSERT_NE(rec, NULL);
        TEST_ASSERT_EQ(rec->ts, expected2[i]);
        if (i < 5) {
            st = tl_merge_iter_advance(mit);
            TEST_ASSERT_EQ(st, TL_OK);
        }
    }

    st = tl_merge_iter_advance(mit);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_merge_iter_destroy(mit);
    tl_qplan_destroy(plan);

    /* Test: Two-source merge (interleaved) */
    tl_record_t arr3a[] = {{100, 1}, {300, 3}, {500, 5}};
    tl_record_t arr3b[] = {{200, 2}, {400, 4}, {600, 6}};
    const tl_record_t* arrays3[] = {arr3a, arr3b};
    size_t lengths3[] = {3, 3};

    st = create_test_plan(&alloc, arrays3, lengths3, 2, 0, 1000, &plan);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_merge_iter_create(&alloc, plan, &mit);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Expected: 100, 200, 300, 400, 500, 600 */
    tl_ts_t expected3[] = {100, 200, 300, 400, 500, 600};
    for (int i = 0; i < 6; i++) {
        TEST_ASSERT_EQ(tl_merge_iter_state(mit), TL_ITER_READY);
        rec = tl_merge_iter_peek(mit);
        TEST_ASSERT_NE(rec, NULL);
        TEST_ASSERT_EQ(rec->ts, expected3[i]);
        if (i < 5) {
            st = tl_merge_iter_advance(mit);
            TEST_ASSERT_EQ(st, TL_OK);
        }
    }

    tl_merge_iter_destroy(mit);
    tl_qplan_destroy(plan);

    /* Test: Three-source merge (k=3) */
    tl_record_t arr4a[] = {{100, 1}, {400, 4}};
    tl_record_t arr4b[] = {{200, 2}, {500, 5}};
    tl_record_t arr4c[] = {{300, 3}, {600, 6}};
    const tl_record_t* arrays4[] = {arr4a, arr4b, arr4c};
    size_t lengths4[] = {2, 2, 2};

    st = create_test_plan(&alloc, arrays4, lengths4, 3, 0, 1000, &plan);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(plan->n_iters, 3);

    st = tl_merge_iter_create(&alloc, plan, &mit);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Expected: 100, 200, 300, 400, 500, 600 */
    tl_ts_t expected4[] = {100, 200, 300, 400, 500, 600};
    for (int i = 0; i < 6; i++) {
        TEST_ASSERT_EQ(tl_merge_iter_state(mit), TL_ITER_READY);
        rec = tl_merge_iter_peek(mit);
        TEST_ASSERT_NE(rec, NULL);
        TEST_ASSERT_EQ(rec->ts, expected4[i]);
        if (i < 5) {
            st = tl_merge_iter_advance(mit);
            TEST_ASSERT_EQ(st, TL_OK);
        }
    }

    tl_merge_iter_destroy(mit);
    tl_qplan_destroy(plan);

    /* Test: Merge with duplicate timestamps (deterministic ordering by component_id) */
    tl_record_t arr5a[] = {{100, 1}, {200, 2}};
    tl_record_t arr5b[] = {{100, 3}, {200, 4}};
    const tl_record_t* arrays5[] = {arr5a, arr5b};
    size_t lengths5[] = {2, 2};

    st = create_test_plan(&alloc, arrays5, lengths5, 2, 0, 1000, &plan);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_merge_iter_create(&alloc, plan, &mit);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Expected: (100, id=0), (100, id=1), (200, id=0), (200, id=1) */
    rec = tl_merge_iter_peek(mit);
    TEST_ASSERT_EQ(rec->ts, 100);
    TEST_ASSERT_EQ(rec->handle, 1);  /* From component 0 */

    st = tl_merge_iter_advance(mit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_merge_iter_peek(mit);
    TEST_ASSERT_EQ(rec->ts, 100);
    TEST_ASSERT_EQ(rec->handle, 3);  /* From component 1 */

    st = tl_merge_iter_advance(mit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_merge_iter_peek(mit);
    TEST_ASSERT_EQ(rec->ts, 200);
    TEST_ASSERT_EQ(rec->handle, 2);  /* From component 0 */

    st = tl_merge_iter_advance(mit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_merge_iter_peek(mit);
    TEST_ASSERT_EQ(rec->ts, 200);
    TEST_ASSERT_EQ(rec->handle, 4);  /* From component 1 */

    tl_merge_iter_destroy(mit);
    tl_qplan_destroy(plan);

    /* Test: Merge seek */
    st = create_test_plan(&alloc, arrays3, lengths3, 2, 0, 1000, &plan);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_merge_iter_create(&alloc, plan, &mit);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_merge_iter_seek(mit, 250);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_merge_iter_peek(mit);
    TEST_ASSERT_EQ(rec->ts, 300);  /* First >= 250 */

    st = tl_merge_iter_seek(mit, 500);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_merge_iter_peek(mit);
    TEST_ASSERT_EQ(rec->ts, 500);

    st = tl_merge_iter_seek(mit, 700);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_merge_iter_destroy(mit);
    tl_qplan_destroy(plan);

    /*=======================================================================
     * Tombstone Cursor Tests
     *=======================================================================*/

    /* Test: Empty tombstones */
    tl_tomb_cursor_t cursor;
    tl_tomb_cursor_init(&cursor, NULL);
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 100), false);
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 200), false);

    /* Test: With tombstones */
    tl_intervals_t intervals;
    tl_intervals_init(&intervals, &alloc);
    tl_intervals_insert(&intervals, 100, 200);  /* Delete [100, 200) */
    tl_intervals_insert(&intervals, 300, 400);  /* Delete [300, 400) */

    tl_tombstones_t* tombs = NULL;
    st = tl_tombstones_create(&alloc, &intervals, &tombs);
    TEST_ASSERT_EQ(st, TL_OK);
    tl_intervals_destroy(&intervals);

    tl_tomb_cursor_init(&cursor, tombs);

    /* Test various timestamps (must be non-decreasing for cursor) */
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 50), false);
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 100), true);
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 150), true);
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 199), true);
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 200), false);  /* End exclusive */
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 250), false);
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 300), true);
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 350), true);
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 400), false);
    TEST_ASSERT_EQ(tl_tomb_cursor_is_deleted(&cursor, 500), false);

    tl_tombstones_destroy(&alloc, tombs);

    /*=======================================================================
     * Filtered Iterator Tests
     *=======================================================================*/

    /* Test: Filtered iterator with no tombstones */
    st = create_test_plan(&alloc, arrays1, lengths1, 1, 0, 1000, &plan);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_merge_iter_create(&alloc, plan, &mit);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_filtered_iter_t* fit = NULL;
    st = tl_filtered_iter_create(&alloc, mit, NULL, &fit);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_filtered_iter_state(fit), TL_ITER_READY);

    /* Should return all records */
    rec = tl_filtered_iter_peek(fit);
    TEST_ASSERT_EQ(rec->ts, 100);
    st = tl_filtered_iter_advance(fit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_filtered_iter_peek(fit);
    TEST_ASSERT_EQ(rec->ts, 200);
    st = tl_filtered_iter_advance(fit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_filtered_iter_peek(fit);
    TEST_ASSERT_EQ(rec->ts, 300);
    st = tl_filtered_iter_advance(fit);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_filtered_iter_destroy(fit);
    tl_merge_iter_destroy(mit);
    tl_qplan_destroy(plan);

    /* Test: Filtered iterator with tombstones */
    tl_record_t arr6[] = {{100, 1}, {150, 2}, {200, 3}, {250, 4}, {300, 5}};
    const tl_record_t* arrays6[] = {arr6};
    size_t lengths6[] = {5};

    st = create_test_plan(&alloc, arrays6, lengths6, 1, 0, 1000, &plan);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_merge_iter_create(&alloc, plan, &mit);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Create tombstones: delete [150, 250) */
    tl_intervals_init(&intervals, &alloc);
    tl_intervals_insert(&intervals, 150, 250);
    st = tl_tombstones_create(&alloc, &intervals, &tombs);
    TEST_ASSERT_EQ(st, TL_OK);
    tl_intervals_destroy(&intervals);

    st = tl_filtered_iter_create(&alloc, mit, tombs, &fit);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Expected: 100, 250, 300 (150 and 200 are deleted) */
    rec = tl_filtered_iter_peek(fit);
    TEST_ASSERT_EQ(rec->ts, 100);

    st = tl_filtered_iter_advance(fit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_filtered_iter_peek(fit);
    TEST_ASSERT_EQ(rec->ts, 250);  /* 150 and 200 skipped */

    st = tl_filtered_iter_advance(fit);
    TEST_ASSERT_EQ(st, TL_OK);
    rec = tl_filtered_iter_peek(fit);
    TEST_ASSERT_EQ(rec->ts, 300);

    st = tl_filtered_iter_advance(fit);
    TEST_ASSERT_EQ(st, TL_EOF);

    tl_filtered_iter_destroy(fit);
    tl_merge_iter_destroy(mit);
    tl_tombstones_destroy(&alloc, tombs);
    tl_qplan_destroy(plan);

    /* Test: Filtered iterator with all records deleted */
    st = create_test_plan(&alloc, arrays6, lengths6, 1, 0, 1000, &plan);
    TEST_ASSERT_EQ(st, TL_OK);

    st = tl_merge_iter_create(&alloc, plan, &mit);
    TEST_ASSERT_EQ(st, TL_OK);

    /* Create tombstones: delete [0, 1000) - all records */
    tl_intervals_init(&intervals, &alloc);
    tl_intervals_insert(&intervals, 0, 1000);
    st = tl_tombstones_create(&alloc, &intervals, &tombs);
    TEST_ASSERT_EQ(st, TL_OK);
    tl_intervals_destroy(&intervals);

    st = tl_filtered_iter_create(&alloc, mit, tombs, &fit);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(tl_filtered_iter_state(fit), TL_ITER_EOF);  /* All deleted */

    tl_filtered_iter_destroy(fit);
    tl_merge_iter_destroy(mit);
    tl_tombstones_destroy(&alloc, tombs);
    tl_qplan_destroy(plan);

    /*=======================================================================
     * Null Safety Tests
     *=======================================================================*/

    TEST_ASSERT_EQ(tl_merge_iter_state(NULL), TL_ITER_EOF);
    TEST_ASSERT_EQ(tl_merge_iter_peek(NULL), NULL);
    TEST_ASSERT_EQ(tl_merge_iter_advance(NULL), TL_EINVAL);
    TEST_ASSERT_EQ(tl_merge_iter_seek(NULL, 100), TL_EINVAL);
    tl_merge_iter_destroy(NULL);  /* Should not crash */

    TEST_ASSERT_EQ(tl_filtered_iter_state(NULL), TL_ITER_EOF);
    TEST_ASSERT_EQ(tl_filtered_iter_peek(NULL), NULL);
    TEST_ASSERT_EQ(tl_filtered_iter_advance(NULL), TL_EINVAL);
    tl_filtered_iter_destroy(NULL);

    return 0;
}
