/* C4-wwd pure-C benchmark.
 *
 * on_drop_handle == NULL, so whole-window-dropped L1 segments are removed
 * with NO record scan at all (true O(1) drop). Measures the post-delete
 * compaction CPU and validates query results identical to baseline.
 *
 * Build (linked against the build's libtimelog.a):
 *   cc -O2 -I core/include bench_wwd.c <build>/libtimelog.a -lpthread -lm -o bench
 * Run: ./bench <n_windows> <per_window> <drop_frac_pct> <window_size>
 */
#define _POSIX_C_SOURCE 200809L

#include "timelog/timelog.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static long long now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts);
    return (long long)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

static int drain(tl_timelog_t* tl) {
    int n = 0;
    while (1) {
        tl_status_t st = tl_maint_step(tl);
        if (st != TL_OK) break;   /* TL_EOF => no more work */
        n++;
        if (n > 5000000) break;
    }
    return n;
}

static unsigned long long fingerprint(tl_timelog_t* tl, long long lo, long long hi,
                                       unsigned long long* out_count) {
    tl_snapshot_t* snap = NULL;
    if (tl_snapshot_acquire(tl, &snap) != TL_OK) { *out_count = 0; return 0; }
    tl_iter_t* it = NULL;
    if (tl_iter_range(snap, lo, hi, &it) != TL_OK) {
        tl_snapshot_release(snap); *out_count = 0; return 0;
    }
    unsigned long long sum = 0, cnt = 0;
    tl_record_t rec;
    while (tl_iter_next(it, &rec) == TL_OK) {
        sum = (sum + (unsigned long long)rec.ts);
        cnt++;
    }
    tl_iter_destroy(it);
    tl_snapshot_release(snap);
    *out_count = cnt;
    return sum;
}

static void get_stats(tl_timelog_t* tl, tl_stats_t* s) {
    tl_snapshot_t* snap = NULL;
    tl_snapshot_acquire(tl, &snap);
    tl_stats(snap, s);
    tl_snapshot_release(snap);
}

int main(int argc, char** argv) {
    long long n_windows = argc > 1 ? atoll(argv[1]) : 600;
    long long per_window = argc > 2 ? atoll(argv[2]) : 300;
    long long drop_pct = argc > 3 ? atoll(argv[3]) : 70;
    long long window_size = argc > 4 ? atoll(argv[4]) : 1000;
    long long n_drop = n_windows * drop_pct / 100;

    tl_config_t cfg;
    tl_config_init_defaults(&cfg);
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.window_size = window_size;
    cfg.max_delta_segments = 2;
    cfg.on_drop_handle = NULL;   /* pure-C: true O(1) whole-window drop */

    tl_timelog_t* tl = NULL;
    if (tl_open(&cfg, &tl) != TL_OK) { fprintf(stderr, "open failed\n"); return 1; }

    /* Phase 1: build one L1 per window. */
    for (long long w = 0; w < n_windows; w++) {
        long long base = w * window_size;
        for (long long j = 0; j < per_window; j++) {
            tl_append(tl, base + j, (tl_handle_t)(base + j));
        }
        tl_flush(tl);
        drain(tl);
    }

    tl_stats_t s0; get_stats(tl, &s0);

    /* Phase 2: delete whole windows + churn surviving windows. */
    for (long long w = 0; w < n_drop; w++) {
        long long base = w * window_size;
        tl_delete_range(tl, base, base + window_size);
    }
    for (long long w = n_drop; w < n_windows; w++) {
        long long base = w * window_size;
        tl_append(tl, base + 1, (tl_handle_t)(base + 1));
    }
    tl_flush(tl);

    /* MEASURED: post-delete compaction drain. */
    long long t0 = now_ns();
    tl_compact(tl);
    int steps = drain(tl);
    for (int i = 0; i < 6; i++) { tl_compact(tl); steps += drain(tl); }
    long long cpu_ns = now_ns() - t0;

    tl_stats_t s1; get_stats(tl, &s1);

    unsigned long long cnt = 0;
    unsigned long long fp = fingerprint(tl, 0, n_windows * window_size, &cnt);

    printf("{\"on_drop\":null,\"n_windows\":%lld,\"per_window\":%lld,\"drop_pct\":%lld,"
           "\"n_drop\":%lld,\"l1_built\":%llu,\"l1_after\":%llu,"
           "\"l1_merged_phase2\":%llu,\"pages_built\":%llu,\"pages_after\":%llu,"
           "\"compact_cpu_ms\":%.3f,\"maint_steps_phase2\":%d,\"compactions_total\":%llu,"
           "\"query_count\":%llu,\"query_checksum\":%llu}\n",
           n_windows, per_window, drop_pct, n_drop,
           (unsigned long long)s0.segments_l1, (unsigned long long)s1.segments_l1,
           (unsigned long long)(s1.compaction_select_l1_inputs - s0.compaction_select_l1_inputs),
           (unsigned long long)s0.pages_total, (unsigned long long)s1.pages_total,
           cpu_ns / 1e6, steps, (unsigned long long)s1.compactions_total,
           cnt, fp);

    tl_close(tl);
    return 0;
}
