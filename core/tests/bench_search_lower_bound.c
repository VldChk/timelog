/*===========================================================================
 * bench_search_lower_bound.c - advisory microbench (NOT part of test_timelog)
 *
 * Repeatable seam evidence for the size-gated branchless search. This bench
 * calls both production seams and imports the production
 * TL_LOWER_BOUND_BRANCHLESS_MAX constant:
 *   - tl_record_lower_bound()
 *   - tl_page_lower_bound()
 *
 * Build & run:
 *   cmake --build build-rel --target bench_search_lower_bound
 *   taskset -c 0 build-rel/bench_search_lower_bound
 *
 * Typical (GCC 13, x86-64): small/medium arrays win materially, while above the
 * gate the production helper uses the branchy fallback so timing should be near
 * the reference loop. Performance is advisory: this program prints a warning
 * for >5% slowdown, but exits non-zero only on correctness mismatch because
 * unpinned/shared-runner timing noise is too high for a hard CI gate.
 *===========================================================================*/
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "internal/tl_alloc.h"
#include "internal/tl_search.h"
#include "storage/tl_page.h"

static inline size_t branchy_record(const tl_record_t* a, size_t n, tl_ts_t x) {
    size_t lo = 0, hi = n;
    while (lo < hi) { size_t m = lo + (hi - lo) / 2; if (a[m].ts < x) lo = m + 1; else hi = m; }
    return lo;
}
static inline size_t branchy_ts_lower(const tl_ts_t* a, size_t n, tl_ts_t x) {
    size_t lo = 0, hi = n;
    while (lo < hi) { size_t m = lo + (hi - lo) / 2; if (a[m] < x) lo = m + 1; else hi = m; }
    return lo;
}
static long ns(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return (long)t.tv_sec * 1000000000L + t.tv_nsec; }
static uint64_t xr(uint64_t* s) { uint64_t x = *s; x ^= x << 13; x ^= x >> 7; x ^= x << 17; return (*s = x); }

static void warn_if_slow(int* warnings, const char* seam, size_t n, double branchy, double gated) {
    if (gated > branchy * 1.05) {
        (*warnings)++;
        fprintf(stderr,
            "WARNING: %s gated search %.2f ns is >5%% slower than branchy %.2f ns at n=%zu\n",
            seam, gated, branchy, n);
    }
}

static int fill_queries(tl_ts_t* q, size_t count, size_t n, uint64_t* seed) {
    if (q == NULL || n > (size_t)(INT64_MAX / 2)) {
        return -1;
    }
    for (size_t i = 0; i < count; i++) {
        q[i] = (tl_ts_t)(xr(seed) % (2 * n));
    }
    return 0;
}

int main(void) {
    const size_t gate = TL_LOWER_BOUND_BRANCHLESS_MAX;
    size_t sizes[] = { 256, 4096, 65535, gate, gate + 1, 1048576, 2097152, 8388608 };
    uint64_t sd = 99; size_t M = 1u << 20;
    tl_ts_t* q = malloc(M * sizeof(tl_ts_t));
    volatile size_t sink = 0;
    int warnings = 0;
    if (q == NULL) {
        fprintf(stderr, "failed to allocate query buffer\n");
        return 2;
    }
    printf("%-22s %-10s %12s %12s %9s\n", "seam", "n", "branchy_ns", "gated_ns", "gated/by");
    for (size_t si = 0; si < sizeof(sizes) / sizeof(sizes[0]); si++) {
        size_t n = sizes[si];
        tl_record_t* a = malloc(n * sizeof(tl_record_t));
        if (a == NULL) {
            fprintf(stderr, "failed to allocate records n=%zu\n", n);
            free(q);
            return 2;
        }
        for (size_t i = 0; i < n; i++) { a[i].ts = (tl_ts_t)(2 * i); a[i].handle = i; }
        if (fill_queries(q, M, n, &sd) != 0) {
            fprintf(stderr, "failed to fill queries n=%zu\n", n);
            free(a);
            free(q);
            return 2;
        }
        /* correctness cross-check */
        for (size_t i = 0; i < 4096; i++) if (branchy_record(a, n, q[i]) != tl_record_lower_bound(a, n, q[i])) {
            fprintf(stderr, "MISMATCH record_lower n=%zu\n", n); return 2; }
        double bb = 1e30, bg = 1e30;
        for (int r = 0; r < 7; r++) {
            long t = ns();
            size_t ac = 0;
            for (size_t i = 0; i < M; i++) {
                ac += branchy_record(a, n, q[i]);
            }
            sink ^= ac;
            double d = (double)(ns() - t) / (double)M;
            if (d < bb) {
                bb = d;
            }
        }
        for (int r = 0; r < 7; r++) {
            long t = ns();
            size_t ac = 0;
            for (size_t i = 0; i < M; i++) {
                ac += tl_record_lower_bound(a, n, q[i]);
            }
            sink ^= ac;
            double d = (double)(ns() - t) / (double)M;
            if (d < bg) {
                bg = d;
            }
        }
        printf("%-22s %-10zu %12.2f %12.2f %8.2fx\n", "record_lower", n, bb, bg, bb / bg);
        warn_if_slow(&warnings, "record_lower", n, bb, bg);

        tl_alloc_ctx_t alloc;
        tl__alloc_init(&alloc, NULL);

        tl_page_t* page = NULL;
        if (tl_page_build(&alloc, a, n, &page) != TL_OK || page == NULL) {
            fprintf(stderr, "failed to build page n=%zu\n", n);
            tl__alloc_destroy(&alloc);
            free(a);
            free(q);
            return 2;
        }
        for (size_t i = 0; i < 4096; i++) {
            if (branchy_ts_lower(page->ts, page->count, q[i]) != tl_page_lower_bound(page, q[i])) {
                fprintf(stderr, "MISMATCH page_lower n=%zu\n", n);
                return 2;
            }
        }

        bb = 1e30; bg = 1e30;
        for (int r = 0; r < 7; r++) {
            long t = ns();
            size_t ac = 0;
            for (size_t i = 0; i < M; i++) {
                ac += branchy_ts_lower(page->ts, page->count, q[i]);
            }
            sink ^= ac;
            double d = (double)(ns() - t) / (double)M;
            if (d < bb) { bb = d; }
        }
        for (int r = 0; r < 7; r++) {
            long t = ns();
            size_t ac = 0;
            for (size_t i = 0; i < M; i++) {
                ac += tl_page_lower_bound(page, q[i]);
            }
            sink ^= ac;
            double d = (double)(ns() - t) / (double)M;
            if (d < bg) { bg = d; }
        }
        printf("%-22s %-10zu %12.2f %12.2f %8.2fx\n", "page_lower", n, bb, bg, bb / bg);
        warn_if_slow(&warnings, "page_lower", n, bb, bg);

        tl_page_destroy(page, &alloc);
        tl__alloc_destroy(&alloc);
        free(a);
    }
    free(q);
    fprintf(stderr, "sink=%zu warnings=%d\n", (size_t)sink, warnings);
    return 0;
}
