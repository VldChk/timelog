#define _POSIX_C_SOURCE 200809L

/* exp05 — k-way merge: binary min-heap (replace_top) vs tournament/winner tree (N20).
 *
 * Timelog's read path merges K sources (memtable + L0 + L1 segments) with a binary min-heap whose
 * sift_down does ~2*log2(K) comparisons per emitted record. A tournament (winner/loser) tree does
 * ~log2(K) comparisons per record along a fixed leaf->root path. This isolates that constant-factor
 * win across K — directly relevant to the OOO read-amp case (exp04) where K (overlapping segments)
 * is large. Standalone C, no interpreter noise.
 *
 * Build: gcc -O3 -march=native bench_kmerge.c -o bench && ./bench
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef int64_t  tl_ts_t;
typedef uint64_t tl_handle_t;
/* mirror tl_heap_entry_t's comparison-relevant fields */
typedef struct { tl_ts_t ts; uint32_t tie; tl_handle_t handle; } entry_t;

/* entry comparison: (ts, tie) ascending. returns <0 if a<b. */
static inline int ekey_lt(const entry_t* a, const entry_t* b) {
    if (a->ts != b->ts) return a->ts < b->ts;
    return a->tie < b->tie;
}

/* ---- a source = sorted array of entries + cursor ---- */
typedef struct { const entry_t* rec; size_t len, pos; } source_t;

/* ===== Binary min-heap with replace_top + sift_down (copy of tl_heap structure) ===== */
typedef struct { entry_t e; int src; } heap_node_t;
static int hnode_lt(const heap_node_t* a, const heap_node_t* b) { return ekey_lt(&a->e, &b->e); }

static void heap_sift_down(heap_node_t* h, size_t n, size_t i) {
    for (;;) {
        size_t l = 2*i+1, r = 2*i+2, m = i;
        if (l < n && hnode_lt(&h[l], &h[m])) m = l;   /* compare child */
        if (r < n && hnode_lt(&h[r], &h[m])) m = r;   /* compare other child */
        if (m == i) break;
        heap_node_t t = h[i]; h[i] = h[m]; h[m] = t;
        i = m;
    }
}
static size_t merge_heap(source_t* srcs, size_t K, entry_t* out) {
    heap_node_t* h = malloc(K * sizeof(heap_node_t));
    size_t n = 0;
    for (size_t k = 0; k < K; k++)
        if (srcs[k].len > 0) { h[n].e = srcs[k].rec[0]; h[n].src = (int)k; srcs[k].pos = 1; n++; }
    for (size_t i = n/2; i-- > 0; ) heap_sift_down(h, n, i);
    size_t outn = 0;
    while (n > 0) {
        out[outn++] = h[0].e;
        int s = h[0].src;
        if (srcs[s].pos < srcs[s].len) { h[0].e = srcs[s].rec[srcs[s].pos++]; heap_sift_down(h, n, 0); }
        else { h[0] = h[--n]; heap_sift_down(h, n, 0); }   /* remove exhausted */
    }
    free(h);
    return outn;
}

/* ===== Tournament (winner) tree: ~log2(M) comparisons per emitted record ===== */
#define SENT_TS INT64_MAX
static size_t merge_winner(source_t* srcs, size_t K, entry_t* out) {
    size_t M = 1; while (M < K) M <<= 1;          /* pad leaves to power of two */
    entry_t* leafkey = malloc(M * sizeof(entry_t));/* current head of each leaf */
    int* leafsrc = malloc(M * sizeof(int));
    int* tree = malloc(2*M * sizeof(int));         /* internal[1..M); leaves at [M,2M): hold leaf idx */
    for (size_t k = 0; k < M; k++) {
        leafsrc[k] = (k < K && srcs[k].len > 0) ? (int)k : -1;
        if (leafsrc[k] >= 0) { leafkey[k] = srcs[k].rec[0]; srcs[k].pos = 1; }
        else { leafkey[k].ts = SENT_TS; leafkey[k].tie = 0; }
        tree[M + k] = (int)k;                       /* leaf node holds its own leaf index */
    }
    /* better(a,b): leaf index with smaller key (a wins ties to keep determinism) */
    #define BETTER(a,b) ( ekey_lt(&leafkey[(b)], &leafkey[(a)]) ? (b) : (a) )
    for (size_t i = M; i-- > 1; ) tree[i] = BETTER(tree[2*i], tree[2*i+1]);
    size_t outn = 0;
    for (;;) {
        int w = tree[1];                            /* winner leaf */
        if (leafkey[w].ts == SENT_TS) break;        /* all exhausted */
        out[outn++] = leafkey[w];
        int s = leafsrc[w];
        if (s >= 0 && srcs[s].pos < srcs[s].len) leafkey[w] = srcs[s].rec[srcs[s].pos++];
        else { leafkey[w].ts = SENT_TS; leafkey[w].tie = 0; leafsrc[w] = -1; }
        /* replay leaf w to root: ONE comparison per level */
        for (int i = (int)((M + w) / 2); i >= 1; i /= 2)
            tree[i] = BETTER(tree[2*i], tree[2*i+1]);
    }
    #undef BETTER
    free(leafkey); free(leafsrc); free(tree);
    return outn;
}

static long now_ns(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
    return (long)t.tv_sec*1000000000L + t.tv_nsec; }
static uint64_t xr(uint64_t* s){ uint64_t x=*s; x^=x<<13; x^=x>>7; x^=x<<17; return (*s=x); }

int main(void){
    size_t Ks[] = {2, 4, 8, 16, 32, 64};
    size_t total = 1u<<20;                  /* total records merged */
    uint64_t seed = 0xabcdef1234567ULL;
    printf("%-5s %14s %14s %9s   (total=%zu records)\n", "K", "heap ns/rec", "winner ns/rec", "speedup", total);
    for (size_t ki = 0; ki < sizeof(Ks)/sizeof(Ks[0]); ki++) {
        size_t K = Ks[ki];
        /* K sorted sources, interleaved ts so merge actually alternates sources */
        source_t* srcs = malloc(K * sizeof(source_t));
        entry_t** bufs = malloc(K * sizeof(entry_t*));
        size_t per = total / K;
        for (size_t k = 0; k < K; k++) {
            bufs[k] = malloc(per * sizeof(entry_t));
            tl_ts_t t = (tl_ts_t)(xr(&seed) % 100);
            for (size_t i = 0; i < per; i++) {
                t += (tl_ts_t)(xr(&seed) % (2*K));    /* sorted, ranges overlap across sources */
                bufs[k][i].ts = t; bufs[k][i].tie = (uint32_t)k; bufs[k][i].handle = i;
            }
            srcs[k].rec = bufs[k]; srcs[k].len = per; srcs[k].pos = 0;
        }
        entry_t* o1 = malloc(total * sizeof(entry_t));
        entry_t* o2 = malloc(total * sizeof(entry_t));
        double bh = 1e30, bw = 1e30;
        size_t n1=0, n2=0;
        for (int rep = 0; rep < 5; rep++) {
            for (size_t k=0;k<K;k++) srcs[k].pos=0;
            long t0=now_ns(); n1=merge_heap(srcs, K, o1); long d=now_ns()-t0;
            if ((double)d/n1 < bh) bh=(double)d/n1;
            for (size_t k=0;k<K;k++) srcs[k].pos=0;
            t0=now_ns(); n2=merge_winner(srcs, K, o2); d=now_ns()-t0;
            if ((double)d/n2 < bw) bw=(double)d/n2;
        }
        /* correctness: identical merged output */
        int ok = (n1==n2);
        for (size_t i=0; ok && i<n1; i++) if (o1[i].ts!=o2[i].ts || o1[i].tie!=o2[i].tie) ok=0;
        printf("%-5zu %14.2f %14.2f %8.2fx   %s\n", K, bh, bw, bh/bw, ok?"ok":"MISMATCH!");
        for (size_t k=0;k<K;k++) free(bufs[k]);
        free(bufs); free(srcs); free(o1); free(o2);
    }
    return 0;
}
