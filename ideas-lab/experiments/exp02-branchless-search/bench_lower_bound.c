#define _POSIX_C_SOURCE 200809L

/* exp02 — branchless vs branchy lower_bound over tl_record_t[] (AoS, 16B/elem).
 *
 * Isolates N17: does a branchless (cmov / arithmetic) lower_bound beat the
 * current branchy loop in tl_search.h, and in which cache regimes?
 * Standalone C harness (T8.5) — no Python, no interpreter noise.
 *
 * Build: gcc -O3 -march=native bench_lower_bound.c -o bench && ./bench
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef int64_t tl_ts_t;
typedef uint64_t tl_handle_t;
typedef struct { tl_ts_t ts; tl_handle_t handle; } tl_record_t;

/* ---- baseline: exact copy of current tl_search.h ---- */
static inline size_t lb_branchy(const tl_record_t* data, size_t len, tl_ts_t target) {
    size_t lo = 0, hi = len;
    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (data[mid].ts < target) lo = mid + 1;
        else hi = mid;
    }
    return lo;
}

/* ---- candidate: branchless power-of-two-step, arithmetic (cmov-friendly) ---- */
static inline size_t lb_branchless(const tl_record_t* data, size_t len, tl_ts_t target) {
    const tl_record_t* first = data;
    size_t length = len;
    while (length > 0) {
        size_t half = length / 2;
        /* pure arithmetic: no data-dependent branch -> compiler emits cmov */
        first += (size_t)(first[half].ts < target) * (length - half);
        length = half;
    }
    return (size_t)(first - data);
}

/* ---- candidate+prefetch: same, with explicit prefetch of both children ---- */
static inline size_t lb_branchless_pf(const tl_record_t* data, size_t len, tl_ts_t target) {
    const tl_record_t* first = data;
    size_t length = len;
    while (length > 0) {
        size_t half = length / 2;
        /* prefetch the two possible next probe locations one step ahead */
        __builtin_prefetch(&first[half / 2]);
        __builtin_prefetch(&first[half + half / 2]);
        first += (size_t)(first[half].ts < target) * (length - half);
        length = half;
    }
    return (size_t)(first - data);
}

static long now_ns(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
    return (long)t.tv_sec*1000000000L + t.tv_nsec; }

static uint64_t xrand(uint64_t* s){ /* xorshift64 */
    uint64_t x=*s; x^=x<<13; x^=x>>7; x^=x<<17; return (*s=x); }

typedef size_t (*lb_fn)(const tl_record_t*, size_t, tl_ts_t);

static double bench(lb_fn fn, const tl_record_t* a, size_t n,
                    const tl_ts_t* q, size_t m, volatile size_t* sink) {
    /* warmup */
    size_t acc=0;
    for (size_t i=0;i<m/8;i++) acc += fn(a, n, q[i & (m-1)]);
    *sink ^= acc;
    long best = 0;
    for (int rep=0; rep<7; rep++) {
        long t0 = now_ns();
        size_t s=0;
        for (size_t i=0;i<m;i++) s += fn(a, n, q[i]);
        long dt = now_ns()-t0;
        *sink ^= s;
        if (rep==0 || dt < best) best = dt;
    }
    return (double)best / (double)m;
}

int main(void){
    size_t sizes[] = {256, 1024, 4096, 16384, 65536, 1u<<20};
    size_t nsizes = sizeof(sizes)/sizeof(sizes[0]);
    size_t M = 1u<<20;           /* queries per measurement (power of two) */
    volatile size_t sink = 0;
    uint64_t seed = 0x9e3779b97f4a7c15ULL;

    tl_ts_t* q = malloc(M*sizeof(tl_ts_t));

    printf("%-10s %12s %12s %12s   %8s %8s\n",
           "n", "branchy", "branchless", "bl+prefetch", "bl/by", "pf/by");
    printf("%-10s %12s %12s %12s   %8s %8s\n",
           "(records)", "ns/search", "ns/search", "ns/search", "speedup", "speedup");

    for (size_t si=0; si<nsizes; si++) {
        size_t n = sizes[si];
        tl_record_t* a = malloc(n*sizeof(tl_record_t));
        /* sorted ts = 2*i (gaps so queries land between elements too) */
        for (size_t i=0;i<n;i++){ a[i].ts=(tl_ts_t)(2*i); a[i].handle=i; }
        /* random query targets in [0, 2n) */
        for (size_t i=0;i<M;i++) q[i] = (tl_ts_t)(xrand(&seed) % (2*n));

        /* correctness: all three must agree on every query */
        for (size_t i=0;i<4096;i++){
            size_t r0=lb_branchy(a,n,q[i]), r1=lb_branchless(a,n,q[i]), r2=lb_branchless_pf(a,n,q[i]);
            if (r0!=r1 || r0!=r2){ fprintf(stderr,"MISMATCH n=%zu q=%lld by=%zu bl=%zu pf=%zu\n",
                                            n,(long long)q[i],r0,r1,r2); return 1; }
        }

        double by = bench(lb_branchy, a, n, q, M, &sink);
        double bl = bench(lb_branchless, a, n, q, M, &sink);
        double pf = bench(lb_branchless_pf, a, n, q, M, &sink);
        printf("%-10zu %12.2f %12.2f %12.2f   %7.2fx %7.2fx\n",
               n, by, bl, pf, by/bl, by/pf);
        free(a);
    }
    free(q);
    fprintf(stderr, "sink=%zu\n", (size_t)sink);
    return 0;
}
