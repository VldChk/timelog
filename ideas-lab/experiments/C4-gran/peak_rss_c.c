#define _POSIX_C_SOURCE 200809L

/* peak_rss_c — C-level peak-RSS measurement for the max_compaction_windows cap.
 *
 * EXPID=C4-gran. Removes ALL Python-object baseline noise: the handle is just a
 * uint64 counter, so RSS reflects ONLY the engine's page/segment memory. We
 * build a wide L1 grid (wave 1), then ingest a wide bulk batch overlapping every
 * window (wave 2), then drive tl_maint_step() to drain wave 2 while a sampler
 * thread tracks /proc/self/statm RSS high-water.
 *
 * Output: one JSON line per invocation. Usage:
 *   peak_rss_c <cap> <N> <n_windows> <seed>
 */
#include "timelog/timelog.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>
#include <time.h>
#include <malloc.h>
#include <stdatomic.h>

static long page_kb(void) { return sysconf(_SC_PAGESIZE) / 1024; }

static long rss_kb(void) {
    FILE* f = fopen("/proc/self/statm", "r");
    if (!f) return -1;
    long total = 0, resident = 0;
    if (fscanf(f, "%ld %ld", &total, &resident) != 2) { fclose(f); return -1; }
    fclose(f);
    return resident * page_kb();
}

/* ---- background RSS peak sampler ---- */
typedef struct { atomic_int stop; long peak_kb; } sampler_t;

static void* sampler_run(void* arg) {
    sampler_t* s = (sampler_t*)arg;
    struct timespec ts = {0, 200 * 1000}; /* 200us */
    while (!atomic_load_explicit(&s->stop, memory_order_acquire)) {
        long r = rss_kb();
        if (r > s->peak_kb) s->peak_kb = r;
        nanosleep(&ts, NULL);
    }
    long r = rss_kb();
    if (r > s->peak_kb) s->peak_kb = r;
    return NULL;
}

/* ---- deterministic LCG for reproducible workload ---- */
static uint64_t lcg_state;
static uint64_t lcg(void) {
    lcg_state = lcg_state * 6364136223846793005ULL + 1442695040888963407ULL;
    return lcg_state >> 16;
}
static uint64_t lcg_range(uint64_t n) { return lcg() % n; }

static uint64_t mix64(uint64_t x) {
    x ^= x >> 30;
    x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27;
    x *= 0x94d049bb133111ebULL;
    x ^= x >> 31;
    return x;
}

#define WINDOW_MS 3600000LL

/* Ingest n records spread across n_windows windows with ~30% OOO arrivals. */
static void ingest_wave(tl_timelog_t* tl, long n, long n_windows, uint64_t seed,
                        long flush_every) {
    lcg_state = seed;
    long long span = (long long)n_windows * WINDOW_MS;
    long long cur_max = 0;
    for (long i = 0; i < n; i++) {
        long long ts;
        long long base = (long long)lcg_range((uint64_t)span);
        if ((lcg() % 100) < 30 && cur_max > WINDOW_MS) {
            long long back = (long long)lcg_range((uint64_t)(span / 2) + 1) + 1;
            ts = cur_max - back;
            if (ts < 0) ts = 0;
        } else {
            ts = base;
            if (ts > cur_max) cur_max = ts;
        }
        tl_append(tl, (tl_ts_t)ts, (tl_handle_t)(uint64_t)(i + 1));
        if ((i + 1) % flush_every == 0) tl_flush(tl);
    }
    tl_flush(tl);
}

static void get_layout(tl_timelog_t* tl, tl_stats_t* out) {
    tl_snapshot_t* snap = NULL;
    tl_snapshot_acquire(tl, &snap);
    tl_stats(snap, out);
    tl_snapshot_release(snap);
}

/* checksum of a fixed set of range queries via scan iterator */
static uint64_t query_fingerprint(tl_timelog_t* tl, long n_windows, long* out_total,
                                  uint64_t* out_multiset_hash) {
    lcg_state = 0xC4C4;
    long long span = (long long)n_windows * WINDOW_MS;
    long long w = span / 500; if (w < 1) w = 1;
    uint64_t h = 1469598103934665603ULL; /* FNV offset */
    uint64_t mh = 0xcbf29ce484222325ULL;
    long total = 0;
    tl_snapshot_t* snap = NULL;
    tl_snapshot_acquire(tl, &snap);
    for (int q = 0; q < 400; q++) {
        long long lo = (long long)lcg_range((uint64_t)span);
        long long hi = lo + w;
        tl_iter_t* it = NULL;
        if (tl_iter_range(snap, (tl_ts_t)lo, (tl_ts_t)hi, &it) != TL_OK) continue;
        long cnt = 0;
        uint64_t qsum1 = 0;
        uint64_t qsum2 = 0;
        tl_record_t rec;
        while (tl_iter_next(it, &rec) == TL_OK) {
            cnt++;
            uint64_t item = mix64((uint64_t)rec.ts ^ mix64(rec.handle));
            qsum1 += item;
            qsum2 += mix64(item + 0x9e3779b97f4a7c15ULL);
            h ^= item;
            h *= 1099511628211ULL;
        }
        tl_iter_destroy(it);
        total += cnt;
        h ^= (uint64_t)cnt; h *= 1099511628211ULL;
        mh ^= mix64(qsum1 ^ (qsum2 << 1) ^ (uint64_t)cnt);
        mh *= 1099511628211ULL;
    }
    tl_snapshot_release(snap);
    *out_total = total;
    *out_multiset_hash = mh;
    return h;
}

int main(int argc, char** argv) {
    long cap = argc > 1 ? atol(argv[1]) : 0;
    long N = argc > 2 ? atol(argv[2]) : 2000000;
    long n_windows = argc > 3 ? atol(argv[3]) : 300;
    uint64_t seed = argc > 4 ? (uint64_t)atol(argv[4]) : 7;
    long flush_every = 25000;

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.target_page_bytes = 4096;
    if (cap > 0) cfg.max_compaction_windows = (uint32_t)cap;

    tl_timelog_t* tl = NULL;
    if (tl_open(&cfg, &tl) != TL_OK) { fprintf(stderr, "open failed\n"); return 1; }

    long wave1 = N / 2;
    long wave2 = N - wave1;

    /* wave 1: build the L1 grid, drain fully */
    ingest_wave(tl, wave1, n_windows, seed, flush_every);
    tl_compact(tl);
    while (tl_maint_step(tl) == TL_OK) {}

    tl_stats_t st_base; get_layout(tl, &st_base);
    long base_l1 = (long)st_base.segments_l1;

    /* wave 2: wide bulk batch overlapping every window */
    ingest_wave(tl, wave2, n_windows, seed + 1, flush_every);

    long rss_before = rss_kb();

    /* drive compaction; sample RSS during drain */
    tl_compact(tl);
    sampler_t samp;
    atomic_init(&samp.stop, 0);
    samp.peak_kb = rss_before;
    pthread_t th;
    if (pthread_create(&th, NULL, sampler_run, &samp) != 0) {
        fprintf(stderr, "sampler thread creation failed\n");
        tl_close(tl);
        return 1;
    }

    /* peak_live_kb: high-water of the post-trim RSS, i.e. the TRUE live working
     * set the cap is supposed to bound (glibc retains freed pages in-arena, so
     * the raw RSS high-water is dominated by the final dataset size, not the
     * per-pass transient). We malloc_trim() after each step and record the max
     * trimmed RSS reached at any pass boundary -- this isolates the transient
     * each pass holds beyond the resident dataset at that point. We also record
     * the single largest one-step RSS jump (per-pass transient delta). */
    struct timespec c0, c1;
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &c0);
    long steps = 0;
    long peak_live = rss_before;       /* max RSS observed right after trim */
    long max_step_delta = 0;           /* largest single-pass transient jump */
    long pre = rss_before;
    while (tl_maint_step(tl) == TL_OK) {
        steps++;
        long mid = rss_kb();
        long delta = mid - pre;
        if (delta > max_step_delta) max_step_delta = delta;
        malloc_trim(0);
        long after = rss_kb();
        if (after > peak_live) peak_live = after;
        pre = after;
    }
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &c1);

    atomic_store_explicit(&samp.stop, 1, memory_order_release);
    pthread_join(th, NULL);
    long peak = samp.peak_kb;
    double drain_ms = (c1.tv_sec - c0.tv_sec) * 1000.0 +
                      (c1.tv_nsec - c0.tv_nsec) / 1e6;

    long rss_after = rss_kb();
    tl_stats_t st_final; get_layout(tl, &st_final);

    long qtotal = 0;
    uint64_t qmultihash = 0;
    uint64_t qhash = query_fingerprint(tl, n_windows, &qtotal, &qmultihash);

    printf("{\"cap\": %ld, \"N\": %ld, \"base_l1_windows\": %ld, "
           "\"rss_before_drain_mb\": %.1f, \"peak_rss_mb\": %.1f, "
           "\"rss_after_drain_mb\": %.1f, \"rss_spike_mb\": %.1f, "
           "\"peak_live_mb\": %.1f, \"live_spike_mb\": %.1f, "
           "\"max_step_transient_mb\": %.1f, "
           "\"maint_steps\": %ld, \"drain_cpu_ms\": %.1f, "
           "\"segments_l0\": %llu, \"segments_l1\": %llu, "
           "\"pages_total\": %llu, \"tombstone_count\": %llu, "
           "\"compactions_total\": %llu, \"select_l0_inputs\": %llu, "
           "\"select_l1_inputs\": %llu, \"records_estimate\": %llu, "
           "\"query_total\": %ld, \"query_hash\": \"%016llx\", "
           "\"query_multiset_hash\": \"%016llx\"}\n",
           cap, N, base_l1,
           rss_before / 1024.0, peak / 1024.0, rss_after / 1024.0,
           (peak - rss_before) / 1024.0,
           peak_live / 1024.0, (peak_live - rss_before) / 1024.0,
           max_step_delta / 1024.0,
           steps, drain_ms,
           (unsigned long long)st_final.segments_l0,
           (unsigned long long)st_final.segments_l1,
           (unsigned long long)st_final.pages_total,
           (unsigned long long)st_final.tombstone_count,
           (unsigned long long)st_final.compactions_total,
           (unsigned long long)st_final.compaction_select_l0_inputs,
           (unsigned long long)st_final.compaction_select_l1_inputs,
           (unsigned long long)st_final.records_estimate,
           qtotal, (unsigned long long)qhash,
           (unsigned long long)qmultihash);

    tl_close(tl);
    return 0;
}
