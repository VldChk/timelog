/*===========================================================================
 * test_search_branchless.c - Branchless lower-bound differential tests
 *
 * Validates that the size-gated branchless (cmov) search forms in
 *   tl_record_lower_bound        (internal/tl_search.h, AoS)
 *   tl_page_lower_bound          (storage/tl_page.c, SoA)
 * are BIT-IDENTICAL to a reference branchy binary search, across sizes that
 * span the branchless<->branchy gate (TL_LOWER_BOUND_BRANCHLESS_MAX = 262144),
 * duplicate/equality runs, signed timestamp extremes, and boundary targets
 * around the branchless gate.
 *
 * Symbols prefixed "blq_" to stay unique.
 *===========================================================================*/

#include "test_harness.h"
#include "timelog/timelog.h"
#include "internal/tl_alloc.h"
#include "internal/tl_search.h"
#include "internal/tl_defs.h"
#include "storage/tl_page.h"

#include <stdlib.h>

/* ---- reference (oracle) branchy searches over a plain int64 key array ---- */
static size_t blq_ref_lower(const tl_ts_t* k, size_t n, tl_ts_t target) {
    size_t lo = 0, hi = n;
    while (lo < hi) { size_t mid = lo + (hi - lo) / 2;
        if (k[mid] < target) lo = mid + 1; else hi = mid; }
    return lo;
}
/* Build the target sweep for a sorted key array keys[i] = 2*i (gaps so
 * "between" targets exist). Returns count; fills out[] (cap >= 16). */
static size_t blq_targets(size_t n, tl_ts_t* out) {
    size_t c = 0;
    out[c++] = -1;                 /* below min */
    if (n > 0) {
        out[c++] = 0;              /* exact first */
        out[c++] = 1;              /* between 0 and 2 */
        out[c++] = (tl_ts_t)(n);   /* mid-ish: exact key when n even, between when odd */
        out[c++] = (tl_ts_t)(n) + 1;
        out[c++] = (tl_ts_t)(2 * (n - 1));      /* exact last */
        out[c++] = (tl_ts_t)(2 * (n - 1)) + 1;  /* above max */
        out[c++] = (tl_ts_t)(2 * n);            /* above max */
    } else {
        out[c++] = 0;
        out[c++] = 1000;
    }
    return c;
}

/* sizes spanning the gate; GATE = TL_LOWER_BOUND_BRANCHLESS_MAX */
#define BLQ_GATE ((size_t)TL_LOWER_BOUND_BRANCHLESS_MAX)
static const size_t blq_sizes[] = {
    0, 1, 2, 3, 4, 7, 8, 9, 15, 16, 17, 255, 256, 257, 4095, 4096, 4097, 65535,
    BLQ_GATE - 1, BLQ_GATE, BLQ_GATE + 1, BLQ_GATE + 33
};
#define BLQ_NSIZES (sizeof(blq_sizes) / sizeof(blq_sizes[0]))

TEST_DECLARE(blq_record_lower_differential) {
    tl_ts_t targets[16];
    for (size_t si = 0; si < BLQ_NSIZES; si++) {
        size_t n = blq_sizes[si];
        tl_record_t* recs = (tl_record_t*)malloc((n ? n : 1) * sizeof(tl_record_t));
        tl_ts_t* keys = (tl_ts_t*)malloc((n ? n : 1) * sizeof(tl_ts_t));
        TEST_ASSERT(recs != NULL && keys != NULL);
        for (size_t i = 0; i < n; i++) { recs[i].ts = (tl_ts_t)(2 * i); recs[i].handle = i; keys[i] = (tl_ts_t)(2 * i); }
        size_t tc = blq_targets(n, targets);
        for (size_t t = 0; t < tc; t++) {
            size_t got = tl_record_lower_bound(recs, n, targets[t]);
            size_t exp = blq_ref_lower(keys, n, targets[t]);
            TEST_ASSERT_EQ_SIZE(exp, got);
        }
        free(recs); free(keys);
    }
}

/* Page differential: build real pages and compare lower bound. Includes a
 * size above the branchless gate (all records land in one page). */
TEST_DECLARE(blq_page_lower_differential) {
    tl_alloc_ctx_t alloc; tl__alloc_init(&alloc, NULL);
    tl_ts_t targets[16];
    const size_t page_sizes[] = { 1, 2, 3, 255, 256, 4096, BLQ_GATE + 1 };
    for (size_t si = 0; si < sizeof(page_sizes) / sizeof(page_sizes[0]); si++) {
        size_t n = page_sizes[si];
        tl_record_t* recs = (tl_record_t*)malloc(n * sizeof(tl_record_t));
        tl_ts_t* keys = (tl_ts_t*)malloc(n * sizeof(tl_ts_t));
        TEST_ASSERT(recs != NULL && keys != NULL);
        for (size_t i = 0; i < n; i++) { recs[i].ts = (tl_ts_t)(2 * i); recs[i].handle = i; keys[i] = (tl_ts_t)(2 * i); }
        tl_page_t* page = NULL;
        TEST_ASSERT_STATUS(TL_OK, tl_page_build(&alloc, recs, n, &page));
        TEST_ASSERT(page != NULL);
        size_t tc = blq_targets(n, targets);
        for (size_t t = 0; t < tc; t++) {
            TEST_ASSERT_EQ_SIZE(blq_ref_lower(keys, n, targets[t]), tl_page_lower_bound(page, targets[t]));
        }
        tl_page_destroy(page, &alloc);
        free(recs); free(keys);
    }
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(blq_duplicate_extreme_differential) {
    const tl_ts_t keys[] = {
        TL_TS_MIN, -5, -5, 0, 0, 0, 7, TL_TS_MAX
    };
    const tl_ts_t targets[] = {
        TL_TS_MIN, TL_TS_MIN + 1, -6, -5, -4, 0, 1, 7, 8,
        TL_TS_MAX - 1, TL_TS_MAX
    };
    const size_t n = sizeof(keys) / sizeof(keys[0]);

    tl_record_t recs[sizeof(keys) / sizeof(keys[0])];
    for (size_t i = 0; i < n; i++) {
        recs[i].ts = keys[i];
        recs[i].handle = i;
    }

    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_t* page = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_page_build(&alloc, recs, n, &page));
    TEST_ASSERT(page != NULL);

    for (size_t i = 0; i < sizeof(targets) / sizeof(targets[0]); i++) {
        tl_ts_t target = targets[i];
        TEST_ASSERT_EQ_SIZE(blq_ref_lower(keys, n, target),
                            tl_record_lower_bound(recs, n, target));
        TEST_ASSERT_EQ_SIZE(blq_ref_lower(keys, n, target),
                            tl_page_lower_bound(page, target));
    }

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
}

TEST_DECLARE(blq_gate_duplicate_differential) {
    const size_t n = BLQ_GATE;
    tl_record_t* recs = (tl_record_t*)malloc(n * sizeof(tl_record_t));
    tl_ts_t* keys = (tl_ts_t*)malloc(n * sizeof(tl_ts_t));
    TEST_ASSERT(recs != NULL && keys != NULL);

    for (size_t i = 0; i < n; i++) {
        keys[i] = (tl_ts_t)((long long)(i / 4) - 32768LL);
        recs[i].ts = keys[i];
        recs[i].handle = i;
    }

    tl_alloc_ctx_t alloc;
    tl__alloc_init(&alloc, NULL);

    tl_page_t* page = NULL;
    TEST_ASSERT_STATUS(TL_OK, tl_page_build(&alloc, recs, n, &page));
    TEST_ASSERT(page != NULL);

    const tl_ts_t targets[] = {
        keys[0] - 1, keys[0], keys[0] + 1,
        keys[n / 2] - 1, keys[n / 2], keys[n / 2] + 1,
        keys[n - 1] - 1, keys[n - 1], keys[n - 1] + 1,
    };
    for (size_t i = 0; i < sizeof(targets) / sizeof(targets[0]); i++) {
        tl_ts_t target = targets[i];
        TEST_ASSERT_EQ_SIZE(blq_ref_lower(keys, n, target),
                            tl_record_lower_bound(recs, n, target));
        TEST_ASSERT_EQ_SIZE(blq_ref_lower(keys, n, target),
                            tl_page_lower_bound(page, target));
    }

    tl_page_destroy(page, &alloc);
    tl__alloc_destroy(&alloc);
    free(recs);
    free(keys);
}

void run_search_branchless_tests(void) {
    RUN_TEST(blq_record_lower_differential);
    RUN_TEST(blq_page_lower_differential);
    RUN_TEST(blq_duplicate_extreme_differential);
    RUN_TEST(blq_gate_duplicate_differential);
}
