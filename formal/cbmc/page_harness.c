#include <stdlib.h>
#include <stdint.h>
#include "../../core/src/storage/tl_page.h"

extern size_t nondet_size_t(void);
extern int64_t nondet_i64(void);
void __CPROVER_assume(_Bool);
void __CPROVER_assert(_Bool, const char *);

#include "../../core/src/storage/tl_page.c"

void harness_page_search_boundaries(void) {
    tl_page_t page = {0};

    size_t n = nondet_size_t();
    __CPROVER_assume(n <= 16);
    page.count = (uint32_t)n;

    tl_ts_t* ts = NULL;
    tl_handle_t* h = NULL;
    if (n > 0) {
        ts = (tl_ts_t*)malloc(sizeof(tl_ts_t) * n);
        h = (tl_handle_t*)malloc(sizeof(tl_handle_t) * n);
        __CPROVER_assume(ts != NULL && h != NULL);

        for (size_t i = 0; i < n; ++i) {
            ts[i] = nondet_i64();
            h[i] = (tl_handle_t)i;
            if (i > 0) {
                __CPROVER_assume(ts[i - 1] <= ts[i]);
            }
        }
        page.min_ts = ts[0];
        page.max_ts = ts[n - 1];
    }

    page.ts = ts;
    page.h = h;

    tl_ts_t target = nondet_i64();
    size_t lb = tl_page_lower_bound(&page, target);
    size_t ub = tl_page_upper_bound(&page, target);

    __CPROVER_assert(lb <= ub, "lower_bound is never after upper_bound");
    __CPROVER_assert(ub <= page.count, "search bounds stay within page count");

    for (size_t i = 0; i < lb; ++i) {
        __CPROVER_assert(page.ts[i] < target,
                         "all indices before lower_bound are < target");
    }
    for (size_t i = lb; i < page.count; ++i) {
        __CPROVER_assert(page.ts[i] >= target,
                         "all indices at/after lower_bound are >= target");
    }
    for (size_t i = 0; i < ub; ++i) {
        __CPROVER_assert(page.ts[i] <= target,
                         "all indices before upper_bound are <= target");
    }
    for (size_t i = ub; i < page.count; ++i) {
        __CPROVER_assert(page.ts[i] > target,
                         "all indices at/after upper_bound are > target");
    }

    /* Boundary-specific checks around min/max timestamp extremes. */
    size_t lb_min = tl_page_lower_bound(&page, TL_TS_MIN);
    size_t ub_max = tl_page_upper_bound(&page, TL_TS_MAX);
    __CPROVER_assert(lb_min == 0, "lower_bound(TL_TS_MIN) starts at index 0");
    __CPROVER_assert(ub_max == page.count,
                     "upper_bound(TL_TS_MAX) is at end of page");

    free(ts);
    free(h);
}
