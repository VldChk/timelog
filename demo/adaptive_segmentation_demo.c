/*===========================================================================
 * adaptive_segmentation_demo.c - Adaptive Segmentation Demo (Native C)
 *
 * Demonstrates adaptive L1 window sizing by applying step changes in data
 * density and observing adaptive_window + EWMA density via tl_stats().
 *
 * Usage:
 *   adaptive_segmentation_demo [--short]
 *
 * Notes:
 * - Runs in manual maintenance mode to control flush/compaction timing.
 * - Prints adaptive window after each phase.
 *===========================================================================*/

#include "timelog/timelog.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    const char* name;
    tl_ts_t step;
} phase_t;

typedef struct {
    size_t records_per_batch;
    size_t flushes_per_phase;
    size_t memtable_max_bytes;
    size_t sealed_max_runs;
} demo_sizes_t;

static void print_usage(const char* exe) {
    printf("Usage: %s [--short]\n", exe);
}

static demo_sizes_t choose_sizes(int short_mode) {
    demo_sizes_t sizes;
    if (short_mode) {
        sizes.records_per_batch = 5000;
        sizes.flushes_per_phase = 2;
        sizes.memtable_max_bytes = 64 * 1024;
        sizes.sealed_max_runs = 8;
    } else {
        sizes.records_per_batch = 50000;
        sizes.flushes_per_phase = 3;
        sizes.memtable_max_bytes = 512 * 1024;
        sizes.sealed_max_runs = 8;
    }
    return sizes;
}

static tl_status_t drain_maintenance(tl_timelog_t* tl, int max_steps);

static tl_status_t append_records(tl_timelog_t* tl,
                                  tl_ts_t* ts_cursor,
                                  tl_handle_t* handle_cursor,
                                  size_t count,
                                  tl_ts_t step) {
    for (size_t i = 0; i < count; i++) {
        tl_status_t st = tl_append(tl, *ts_cursor, *handle_cursor);
        if (st != TL_OK && st != TL_EBUSY) {
            return st;
        }
        (*ts_cursor) += step;
        (*handle_cursor)++;
        if (st == TL_EBUSY) {
            tl_status_t drain_st = drain_maintenance(tl, 1024);
            if (drain_st != TL_OK) {
                return drain_st;
            }
        }
    }
    return TL_OK;
}

static tl_status_t drain_maintenance(tl_timelog_t* tl, int max_steps) {
    for (int i = 0; i < max_steps; i++) {
        tl_status_t st = tl_maint_step(tl);
        if (st == TL_OK) {
            continue;
        }
        if (st == TL_EOF) {
            return TL_OK;
        }
        return st;
    }
    return TL_EINTERNAL;
}

static tl_status_t print_stats(tl_timelog_t* tl, const char* label) {
    tl_snapshot_t* snap = NULL;
    tl_stats_t stats;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    if (st != TL_OK) {
        return st;
    }
    st = tl_stats(snap, &stats);
    if (st != TL_OK) {
        tl_snapshot_release(snap);
        return st;
    }

    printf("  [%s]\n", label);
    printf("    adaptive_window: %" PRId64 "\n", (int64_t)stats.adaptive_window);
    printf("    ewma_density:    %.9f\n", stats.adaptive_ewma_density);
    printf("    flushes:         %" PRIu64 "\n", stats.adaptive_flush_count);
    printf("    segments L0/L1:  %" PRIu64 "/%" PRIu64 "\n",
           stats.segments_l0, stats.segments_l1);
    printf("    records_est:     %" PRIu64 "\n", stats.records_estimate);

    tl_snapshot_release(snap);
    return TL_OK;
}

static tl_status_t get_flush_count(tl_timelog_t* tl, uint64_t* out) {
    tl_snapshot_t* snap = NULL;
    tl_stats_t stats;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    if (st != TL_OK) {
        return st;
    }
    st = tl_stats(snap, &stats);
    tl_snapshot_release(snap);
    if (st != TL_OK) {
        return st;
    }
    *out = stats.adaptive_flush_count;
    return TL_OK;
}

static double expected_density(size_t records_per_batch, tl_ts_t step) {
    if (records_per_batch == 0) {
        return 0.0;
    }
    /* span = (n - 1) * step + 1 */
    double span = (double)(records_per_batch - 1) * (double)step + 1.0;
    if (span <= 0.0) {
        return 0.0;
    }
    return (double)records_per_batch / span;
}

static tl_status_t run_phase(tl_timelog_t* tl,
                             const char* name,
                             tl_ts_t step,
                             const demo_sizes_t* sizes,
                             const tl_adaptive_config_t* adaptive,
                             tl_ts_t* ts_cursor,
                             tl_handle_t* handle_cursor) {
    printf("\nPhase: %s\n", name);
    printf("  step: %" PRId64 "\n", (int64_t)step);

    double density = expected_density(sizes->records_per_batch, step);
    if (density > 0.0) {
        double expected = (double)adaptive->target_records / density;
        printf("  expected candidate (approx): %.0f\n", expected);
    }

    uint64_t start_flushes = 0;
    tl_status_t st = get_flush_count(tl, &start_flushes);
    if (st != TL_OK) {
        return st;
    }
    uint64_t target_flushes = start_flushes + sizes->flushes_per_phase;

    while (1) {
        st = append_records(
            tl, ts_cursor, handle_cursor, sizes->records_per_batch, step);
        if (st != TL_OK) {
            return st;
        }

        st = drain_maintenance(tl, 4096);
        if (st != TL_OK) {
            return st;
        }

        uint64_t current_flushes = 0;
        st = get_flush_count(tl, &current_flushes);
        if (st != TL_OK) {
            return st;
        }
        if (current_flushes >= target_flushes) {
            break;
        }
    }

    st = tl_compact(tl);
    if (st != TL_OK) {
        return st;
    }
    st = drain_maintenance(tl, 1024);
    if (st != TL_OK) {
        return st;
    }

    return print_stats(tl, name);
}

int main(int argc, char** argv) {
    int short_mode = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--short") == 0) {
            short_mode = 1;
        } else if (strcmp(argv[i], "--help") == 0 ||
                   strcmp(argv[i], "-h") == 0) {
            print_usage(argv[0]);
            return 0;
        } else {
            print_usage(argv[0]);
            return 1;
        }
    }

    demo_sizes_t sizes = choose_sizes(short_mode);

    tl_config_t cfg;
    tl_status_t st = tl_config_init_defaults(&cfg);
    if (st != TL_OK) {
        printf("config_init_defaults failed: %s\n", tl_strerror(st));
        return 1;
    }

    cfg.time_unit = TL_TIME_NS;
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.window_size = 1000000;
    cfg.memtable_max_bytes = sizes.memtable_max_bytes;
    cfg.sealed_max_runs = sizes.sealed_max_runs;

    cfg.adaptive.target_records = 50000;
    cfg.adaptive.min_window = 10000;
    cfg.adaptive.max_window = 100000000;
    cfg.adaptive.window_quantum = 1000;
    cfg.adaptive.hysteresis_pct = 5;
    cfg.adaptive.alpha = 0.5;
    cfg.adaptive.warmup_flushes = 1;
    cfg.adaptive.stale_flushes = 0;
    cfg.adaptive.failure_backoff_threshold = 0;
    cfg.adaptive.failure_backoff_pct = 0;

    tl_timelog_t* tl = NULL;
    st = tl_open(&cfg, &tl);
    if (st != TL_OK) {
        printf("tl_open failed: %s\n", tl_strerror(st));
        return 1;
    }

    printf("Adaptive Segmentation Demo (manual maintenance)\n");
    printf("  target_records: %" PRIu64 "\n", cfg.adaptive.target_records);
    printf("  min_window:     %" PRId64 "\n", (int64_t)cfg.adaptive.min_window);
    printf("  max_window:     %" PRId64 "\n", (int64_t)cfg.adaptive.max_window);
    printf("  window_quantum: %" PRId64 "\n", (int64_t)cfg.adaptive.window_quantum);
    printf("  alpha:          %.2f\n", cfg.adaptive.alpha);
    printf("  hysteresis:     %u%%\n", cfg.adaptive.hysteresis_pct);
    printf("  flushes/phase:  %zu\n", sizes.flushes_per_phase);
    printf("  records/batch:  %zu\n", sizes.records_per_batch);
    printf("  memtable bytes: %zu\n", sizes.memtable_max_bytes);
    printf("  sealed runs:    %zu\n", sizes.sealed_max_runs);

    tl_ts_t ts_cursor = 0;
    tl_handle_t handle_cursor = 1;

    phase_t phases[] = {
        {"dense (step=1)", 1},
        {"sparse (step=1000)", 1000},
        {"dense (step=1)", 1},
    };

    for (size_t i = 0; i < sizeof(phases) / sizeof(phases[0]); i++) {
        st = run_phase(tl, phases[i].name, phases[i].step, &sizes,
                       &cfg.adaptive, &ts_cursor, &handle_cursor);
        if (st != TL_OK) {
            printf("phase '%s' failed: %s\n", phases[i].name, tl_strerror(st));
            tl_close(tl);
            return 1;
        }
    }

    tl_snapshot_t* snap = NULL;
    st = tl_snapshot_acquire(tl, &snap);
    if (st == TL_OK) {
        st = tl_validate(snap);
        if (st != TL_OK) {
            printf("validation failed: %s\n", tl_strerror(st));
            tl_snapshot_release(snap);
            tl_close(tl);
            return 1;
        }
        tl_snapshot_release(snap);
    }

    tl_close(tl);
    printf("\nDone.\n");
    return 0;
}
