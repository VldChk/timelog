/*===========================================================================
 * bench_search_lower_bound.c - STANDALONE microbench (NOT part of test_timelog)
 *
 * Repeatable evidence for the size-gated branchless search
 * (TL_LOWER_BOUND_BRANCHLESS_MAX = 262144 in core/src/internal/tl_defs.h):
 * confirms the branchless form wins below the gate and is NEVER slower than the
 * branchy form at any size (the gated function falls back to branchy above the
 * gate, so it cannot regress). Mirrors the exact gated logic.
 *
 * Build & run (shipped-flags equivalent):
 *   gcc -O3 -flto -std=c17 -D_POSIX_C_SOURCE=199309L \
 *       core/tests/bench_search_lower_bound.c -o /tmp/bench_search && taskset -c 0 /tmp/bench_search
 *
 * Expected (GCC 13, x86-64): ~4-5x at 256-4096, ~3x at 65535, ~2.4x at the gate,
 * ~1.0x (no regression) at 262145+.
 *===========================================================================*/
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef int64_t ts_t;
#define GATE ((size_t)1 << 18)   /* must match TL_LOWER_BOUND_BRANCHLESS_MAX */

static inline size_t branchy(const ts_t* a, size_t n, ts_t x) {
    size_t lo = 0, hi = n;
    while (lo < hi) { size_t m = lo + (hi - lo) / 2; if (a[m] < x) lo = m + 1; else hi = m; }
    return lo;
}
static inline size_t gated(const ts_t* a, size_t n, ts_t x) {
    if (n <= GATE) {
        size_t b = 0, L = n;
        while (L > 0) { size_t h = L / 2; b += (size_t)(a[b + h] < x) * (L - h); L = h; }
        return b;
    }
    size_t lo = 0, hi = n;
    while (lo < hi) { size_t m = lo + (hi - lo) / 2; if (a[m] < x) lo = m + 1; else hi = m; }
    return lo;
}
static long ns(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return (long)t.tv_sec * 1000000000L + t.tv_nsec; }
static uint64_t xr(uint64_t* s) { uint64_t x = *s; x ^= x << 13; x ^= x >> 7; x ^= x << 17; return (*s = x); }

int main(void) {
    size_t sizes[] = { 256, 4096, 65535, 262144, 262145, 1048576, 2097152, 8388608 };
    uint64_t sd = 99; size_t M = 1u << 20;
    ts_t* q = malloc(M * sizeof(ts_t));
    volatile size_t sink = 0;
    int regressed = 0;
    printf("%-10s %12s %12s %9s\n", "n", "branchy_ns", "gated_ns", "gated/by");
    for (size_t si = 0; si < sizeof(sizes) / sizeof(sizes[0]); si++) {
        size_t n = sizes[si];
        ts_t* a = malloc(n * sizeof(ts_t));
        for (size_t i = 0; i < n; i++) a[i] = (ts_t)(2 * i);
        for (size_t i = 0; i < M; i++) q[i] = (ts_t)(xr(&sd) % (2 * n));
        /* correctness cross-check */
        for (size_t i = 0; i < 4096; i++) if (branchy(a, n, q[i]) != gated(a, n, q[i])) {
            fprintf(stderr, "MISMATCH n=%zu\n", n); return 2; }
        double bb = 1e30, bg = 1e30;
        for (int r = 0; r < 7; r++) { long t = ns(); size_t ac = 0;
            for (size_t i = 0; i < M; i++) ac += branchy(a, n, q[i]); sink ^= ac;
            double d = (double)(ns() - t) / (double)M; if (d < bb) bb = d; }
        for (int r = 0; r < 7; r++) { long t = ns(); size_t ac = 0;
            for (size_t i = 0; i < M; i++) ac += gated(a, n, q[i]); sink ^= ac;
            double d = (double)(ns() - t) / (double)M; if (d < bg) bg = d; }
        printf("%-10zu %12.2f %12.2f %8.2fx\n", n, bb, bg, bb / bg);
        if (bg > bb * 1.05) regressed = 1;   /* >5% slower would be a regression */
        free(a);
    }
    free(q);
    fprintf(stderr, "sink=%zu\n", (size_t)sink);
    return regressed ? 1 : 0;
}
