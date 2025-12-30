#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../src/internal/tl_manifest.h"

/* Test macros */
#define TEST_ASSERT(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond); \
        return 1; \
    } \
} while(0)

#define TEST_ASSERT_EQ(a, b) TEST_ASSERT((a) == (b))
#define TEST_ASSERT_NE(a, b) TEST_ASSERT((a) != (b))

/* Helper to create a test segment */
static tl_segment_t* create_test_segment(const tl_allocator_t* alloc,
                                          tl_ts_t min_ts, tl_ts_t max_ts,
                                          tl_segment_kind_t kind, uint32_t gen) {
    tl_ts_t ts[] = {min_ts, max_ts};
    tl_handle_t h[] = {1, 2};
    tl_page_t* page = NULL;

    if (tl_page_create_soa(alloc, ts, h, 2, &page) != TL_OK) {
        return NULL;
    }

    tl_page_t* pages[] = {page};
    tl_segment_t* seg = NULL;
    if (tl_segment_create(alloc, pages, 1, NULL, kind, gen, &seg) != TL_OK) {
        tl_page_destroy(alloc, page);
        return NULL;
    }

    return seg;
}

int test_manifest(void) {
    tl_allocator_t alloc;
    tl_allocator_init_default(&alloc);
    tl_status_t st;
    tl_manifest_t* m = NULL;

    /* Test: Empty manifest creation */
    st = tl_manifest_create_empty(&alloc, 0, &m);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(m, NULL);
    TEST_ASSERT_EQ(m->version, 0);
    TEST_ASSERT_EQ(m->n_main, 0);
    TEST_ASSERT_EQ(m->n_delta, 0);
    TEST_ASSERT_EQ(m->main, NULL);
    TEST_ASSERT_EQ(m->delta, NULL);
    TEST_ASSERT(!m->has_bounds);
    TEST_ASSERT_EQ(tl_manifest_segment_count(m), 0);
    TEST_ASSERT_EQ(tl_manifest_validate(m), TL_OK);

    tl_manifest_release(m);
    m = NULL;

    /* Create test segments */
    tl_segment_t* seg1 = create_test_segment(&alloc, 100, 200, TL_SEG_MAIN, 1);
    TEST_ASSERT_NE(seg1, NULL);
    tl_segment_t* seg2 = create_test_segment(&alloc, 300, 400, TL_SEG_MAIN, 2);
    TEST_ASSERT_NE(seg2, NULL);
    tl_segment_t* delta1 = create_test_segment(&alloc, 150, 250, TL_SEG_DELTA, 3);
    TEST_ASSERT_NE(delta1, NULL);
    tl_segment_t* delta2 = create_test_segment(&alloc, 350, 450, TL_SEG_DELTA, 4);
    TEST_ASSERT_NE(delta2, NULL);

    /* Test: Build manifest with delta segment */
    st = tl_manifest_create_empty(&alloc, 0, &m);
    TEST_ASSERT_EQ(st, TL_OK);

    tl_manifest_t* m2 = NULL;
    st = tl_manifest_build(&alloc, m, delta1, NULL, NULL, 0, NULL, 0, &m2);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_NE(m2, NULL);
    TEST_ASSERT_EQ(m2->version, 1);  /* Incremented from 0 */
    TEST_ASSERT_EQ(m2->n_delta, 1);
    TEST_ASSERT_EQ(m2->n_main, 0);
    TEST_ASSERT_EQ(m2->delta[0], delta1);
    TEST_ASSERT(m2->has_bounds);
    TEST_ASSERT_EQ(m2->min_ts, 150);
    TEST_ASSERT_EQ(m2->max_ts, 250);
    TEST_ASSERT_EQ(tl_manifest_validate(m2), TL_OK);

    /* delta1 should have refcnt incremented */
    TEST_ASSERT_EQ(tl_atomic_u32_load(&delta1->refcnt), 2);  /* Original + manifest */

    tl_manifest_release(m);
    m = m2;
    m2 = NULL;

    /* Test: Build manifest with main segment */
    st = tl_manifest_build(&alloc, m, NULL, seg1, NULL, 0, NULL, 0, &m2);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(m2->version, 2);
    TEST_ASSERT_EQ(m2->n_delta, 1);  /* Still has delta1 */
    TEST_ASSERT_EQ(m2->n_main, 1);
    TEST_ASSERT_EQ(m2->main[0], seg1);
    TEST_ASSERT_EQ(m2->min_ts, 100);  /* Extended by main segment */
    TEST_ASSERT_EQ(m2->max_ts, 250);
    TEST_ASSERT_EQ(tl_manifest_validate(m2), TL_OK);

    tl_manifest_release(m);
    m = m2;
    m2 = NULL;

    /* Test: Build manifest adding both delta and main */
    st = tl_manifest_build(&alloc, m, delta2, seg2, NULL, 0, NULL, 0, &m2);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(m2->version, 3);
    TEST_ASSERT_EQ(m2->n_delta, 2);
    TEST_ASSERT_EQ(m2->n_main, 2);
    TEST_ASSERT_EQ(tl_manifest_segment_count(m2), 4);
    TEST_ASSERT_EQ(m2->min_ts, 100);
    TEST_ASSERT_EQ(m2->max_ts, 450);
    TEST_ASSERT_EQ(tl_manifest_validate(m2), TL_OK);

    tl_manifest_release(m);
    m = m2;
    m2 = NULL;

    /* Test: Build manifest with removal */
    tl_segment_t* remove_delta[] = {delta1};
    tl_segment_t* remove_main[] = {seg1};

    st = tl_manifest_build(&alloc, m, NULL, NULL, remove_delta, 1, remove_main, 1, &m2);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(m2->version, 4);
    TEST_ASSERT_EQ(m2->n_delta, 1);  /* Only delta2 remains */
    TEST_ASSERT_EQ(m2->n_main, 1);   /* Only seg2 remains */
    TEST_ASSERT_EQ(m2->delta[0], delta2);
    TEST_ASSERT_EQ(m2->main[0], seg2);
    TEST_ASSERT_EQ(m2->min_ts, 300);  /* Updated bounds */
    TEST_ASSERT_EQ(m2->max_ts, 450);
    TEST_ASSERT_EQ(tl_manifest_validate(m2), TL_OK);

    tl_manifest_release(m);
    m = m2;
    m2 = NULL;

    /* Test: Reference counting */
    TEST_ASSERT_EQ(tl_atomic_u32_load(&m->refcnt), 1);

    uint32_t rc = tl_manifest_acquire(m);
    TEST_ASSERT_EQ(rc, 2);

    rc = tl_manifest_acquire(m);
    TEST_ASSERT_EQ(rc, 3);

    rc = tl_manifest_release(m);
    TEST_ASSERT_EQ(rc, 2);

    rc = tl_manifest_release(m);
    TEST_ASSERT_EQ(rc, 1);

    /* Test: Segments survive manifest destruction */
    /* Before releasing manifest, acquire segments */
    tl_segment_acquire(seg2);
    tl_segment_acquire(delta2);

    uint32_t seg2_rc_before = tl_atomic_u32_load(&seg2->refcnt);
    uint32_t delta2_rc_before = tl_atomic_u32_load(&delta2->refcnt);

    /* Release manifest - should decrement segment refcounts */
    tl_manifest_release(m);
    m = NULL;

    /* Segments should still exist (we acquired them) */
    TEST_ASSERT_EQ(tl_atomic_u32_load(&seg2->refcnt), seg2_rc_before - 1);
    TEST_ASSERT_EQ(tl_atomic_u32_load(&delta2->refcnt), delta2_rc_before - 1);

    /* Release our segment references */
    tl_segment_release(seg2);
    tl_segment_release(delta2);

    /* Clean up remaining original segment references */
    tl_segment_release(seg1);
    tl_segment_release(delta1);

    /* Test: Build from NULL old manifest */
    tl_segment_t* new_seg = create_test_segment(&alloc, 500, 600, TL_SEG_DELTA, 5);
    TEST_ASSERT_NE(new_seg, NULL);

    st = tl_manifest_build(&alloc, NULL, new_seg, NULL, NULL, 0, NULL, 0, &m);
    TEST_ASSERT_EQ(st, TL_OK);
    TEST_ASSERT_EQ(m->version, 1);
    TEST_ASSERT_EQ(m->n_delta, 1);
    TEST_ASSERT_EQ(m->n_main, 0);

    tl_manifest_release(m);
    m = NULL;
    tl_segment_release(new_seg);

    /* Test: Null safety */
    TEST_ASSERT_EQ(tl_manifest_segment_count(NULL), 0);
    TEST_ASSERT_EQ(tl_manifest_acquire(NULL), 0);
    TEST_ASSERT_EQ(tl_manifest_release(NULL), 0);
    TEST_ASSERT_EQ(tl_manifest_validate(NULL), TL_OK);

    return 0;
}
