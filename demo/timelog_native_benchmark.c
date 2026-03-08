#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "timelog/timelog.h"

typedef struct benchmark_options {
    size_t records;
    size_t batch_size;
    double ooo_rate;
    uint64_t seed;
    size_t scan_loops;
} benchmark_options_t;

static uint64_t xorshift64(uint64_t* state) {
    uint64_t x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    return x;
}

static double uniform01(uint64_t* state) {
    /* 53-bit mantissa for stable [0, 1) floating-point generation */
    return (double)(xorshift64(state) >> 11) * (1.0 / 9007199254740992.0);
}

static int64_t monotonic_ns(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) {
        return -1;
    }
    return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}

static void print_usage(const char* prog) {
    fprintf(stderr,
            "Usage: %s [--records N] [--batch-size N] [--ooo-rate R] [--seed N] "
            "[--scan-loops N]\n",
            prog);
    fprintf(stderr, "Defaults: --records 5000000 --batch-size 4096 "
                    "--ooo-rate 0.05 --seed 12345 --scan-loops 1\n");
}

static bool parse_size(const char* s, size_t* out) {
    char* end = NULL;
    unsigned long long v = strtoull(s, &end, 10);
    if (end == s || *end != '\0') {
        return false;
    }
    *out = (size_t)v;
    return true;
}

static bool parse_u64(const char* s, uint64_t* out) {
    char* end = NULL;
    unsigned long long v = strtoull(s, &end, 10);
    if (end == s || *end != '\0') {
        return false;
    }
    *out = (uint64_t)v;
    return true;
}

static bool parse_double(const char* s, double* out) {
    char* end = NULL;
    double v = strtod(s, &end);
    if (end == s || *end != '\0') {
        return false;
    }
    *out = v;
    return true;
}

static bool parse_args(int argc, char** argv, benchmark_options_t* opts) {
    opts->records = 5000000;
    opts->batch_size = 4096;
    opts->ooo_rate = 0.05;
    opts->seed = 12345;
    opts->scan_loops = 1;

    for (int i = 1; i < argc; ++i) {
        const char* arg = argv[i];
        if (strcmp(arg, "--help") == 0 || strcmp(arg, "-h") == 0) {
            print_usage(argv[0]);
            return false;
        }
        if (i + 1 >= argc) {
            fprintf(stderr, "Missing value for %s\n", arg);
            return false;
        }
        const char* value = argv[++i];
        if (strcmp(arg, "--records") == 0) {
            if (!parse_size(value, &opts->records) || opts->records == 0) {
                fprintf(stderr, "Invalid --records value: %s\n", value);
                return false;
            }
        } else if (strcmp(arg, "--batch-size") == 0) {
            if (!parse_size(value, &opts->batch_size) || opts->batch_size == 0) {
                fprintf(stderr, "Invalid --batch-size value: %s\n", value);
                return false;
            }
        } else if (strcmp(arg, "--ooo-rate") == 0) {
            if (!parse_double(value, &opts->ooo_rate) ||
                opts->ooo_rate < 0.0 || opts->ooo_rate > 1.0) {
                fprintf(stderr, "Invalid --ooo-rate value: %s (expected 0.0..1.0)\n", value);
                return false;
            }
        } else if (strcmp(arg, "--seed") == 0) {
            if (!parse_u64(value, &opts->seed)) {
                fprintf(stderr, "Invalid --seed value: %s\n", value);
                return false;
            }
        } else if (strcmp(arg, "--scan-loops") == 0) {
            if (!parse_size(value, &opts->scan_loops) || opts->scan_loops == 0) {
                fprintf(stderr, "Invalid --scan-loops value: %s\n", value);
                return false;
            }
        } else {
            fprintf(stderr, "Unknown argument: %s\n", arg);
            return false;
        }
    }
    return true;
}

static tl_status_t flush_until_published(tl_timelog_t* tl) {
    for (int i = 0; i < 8; ++i) {
        tl_status_t st = tl_flush(tl);
        if (st == TL_OK || st == TL_EOF) {
            return TL_OK;
        }
        if (st != TL_EBUSY) {
            return st;
        }
    }
    return TL_EBUSY;
}

static int run_benchmark(const benchmark_options_t* opts) {
    tl_config_t cfg;
    tl_status_t st = tl_config_init_defaults(&cfg);
    if (st != TL_OK) {
        fprintf(stderr, "tl_config_init_defaults failed: %s\n", tl_strerror(st));
        return 1;
    }
    cfg.maintenance_mode = TL_MAINT_DISABLED;
    cfg.memtable_max_bytes = 16 * 1024 * 1024;
    cfg.log_level = TL_LOG_NONE;

    tl_timelog_t* tl = NULL;
    st = tl_open(&cfg, &tl);
    if (st != TL_OK) {
        fprintf(stderr, "tl_open failed: %s\n", tl_strerror(st));
        return 1;
    }

    tl_record_t* batch = calloc(opts->batch_size, sizeof(*batch));
    if (batch == NULL) {
        fprintf(stderr, "Allocation failed for batch buffer\n");
        tl_close(tl);
        return 1;
    }

    uint64_t rng = opts->seed == 0 ? 1 : opts->seed;
    tl_ts_t ts_cursor = 0;
    size_t emitted = 0;
    size_t busy_events = 0;
    const uint32_t append_flags =
        (opts->ooo_rate <= 0.30) ? TL_APPEND_HINT_MOSTLY_IN_ORDER : TL_APPEND_NONE;

    int64_t ingest_start_ns = monotonic_ns();
    if (ingest_start_ns < 0) {
        fprintf(stderr, "clock_gettime failed before ingest\n");
        free(batch);
        tl_close(tl);
        return 1;
    }

    while (emitted < opts->records) {
        size_t n = opts->batch_size;
        if (n > opts->records - emitted) {
            n = opts->records - emitted;
        }

        for (size_t i = 0; i < n; ++i) {
            ts_cursor += 1;
            tl_ts_t ts = ts_cursor;
            if (emitted + i > 1024 && opts->ooo_rate > 0.0 && uniform01(&rng) < opts->ooo_rate) {
                uint64_t back = 1 + (xorshift64(&rng) % 1024);
                if ((uint64_t)ts > back) {
                    ts -= (tl_ts_t)back;
                }
            }
            batch[i].ts = ts;
            batch[i].handle = (tl_handle_t)(emitted + i + 1);
        }

        st = tl_append_batch(tl, batch, n, append_flags);
        if (st == TL_EBUSY) {
            /* TL_EBUSY on append means records are already accepted. */
            busy_events += 1;
            st = flush_until_published(tl);
        }
        if (st != TL_OK) {
            fprintf(stderr, "append batch failed at emitted=%zu: %s\n", emitted, tl_strerror(st));
            free(batch);
            tl_close(tl);
            return 1;
        }

        emitted += n;
    }

    st = flush_until_published(tl);
    if (st != TL_OK) {
        fprintf(stderr, "final flush failed: %s\n", tl_strerror(st));
        free(batch);
        tl_close(tl);
        return 1;
    }

    int64_t ingest_end_ns = monotonic_ns();
    if (ingest_end_ns < 0) {
        fprintf(stderr, "clock_gettime failed after ingest\n");
        free(batch);
        tl_close(tl);
        return 1;
    }

    tl_snapshot_t* snap = NULL;
    st = tl_snapshot_acquire(tl, &snap);
    if (st != TL_OK) {
        fprintf(stderr, "tl_snapshot_acquire failed: %s\n", tl_strerror(st));
        free(batch);
        tl_close(tl);
        return 1;
    }

    uint64_t scanned = 0;
    int64_t scan_start_ns = monotonic_ns();
    if (scan_start_ns < 0) {
        fprintf(stderr, "clock_gettime failed before scan\n");
        tl_snapshot_release(snap);
        free(batch);
        tl_close(tl);
        return 1;
    }

    for (size_t loop = 0; loop < opts->scan_loops; ++loop) {
        tl_iter_t* it = NULL;
        st = tl_iter_since(snap, TL_TS_MIN, &it);
        if (st != TL_OK) {
            fprintf(stderr, "tl_iter_since failed: %s\n", tl_strerror(st));
            tl_snapshot_release(snap);
            free(batch);
            tl_close(tl);
            return 1;
        }

        tl_record_t rec;
        for (;;) {
            st = tl_iter_next(it, &rec);
            if (st == TL_EOF) {
                break;
            }
            if (st != TL_OK) {
                fprintf(stderr, "tl_iter_next failed: %s\n", tl_strerror(st));
                tl_iter_destroy(it);
                tl_snapshot_release(snap);
                free(batch);
                tl_close(tl);
                return 1;
            }
            scanned += 1;
        }
        tl_iter_destroy(it);
    }

    int64_t scan_end_ns = monotonic_ns();
    if (scan_end_ns < 0) {
        fprintf(stderr, "clock_gettime failed after scan\n");
        tl_snapshot_release(snap);
        free(batch);
        tl_close(tl);
        return 1;
    }

    tl_snapshot_release(snap);
    free(batch);
    tl_close(tl);

    double ingest_s = (double)(ingest_end_ns - ingest_start_ns) / 1e9;
    double scan_s = (double)(scan_end_ns - scan_start_ns) / 1e9;

    if (ingest_s <= 0.0 || scan_s <= 0.0) {
        fprintf(stderr, "Invalid timing window\n");
        return 1;
    }

    double ingest_rps = (double)opts->records / ingest_s;
    double scan_rps = (double)scanned / scan_s;

    printf("timelog_native_benchmark\n");
    printf("records=%zu batch_size=%zu ooo_rate=%.4f scan_loops=%zu seed=%" PRIu64 "\n",
           opts->records, opts->batch_size, opts->ooo_rate, opts->scan_loops, opts->seed);
    printf("ingest_seconds=%.6f ingest_records_per_sec=%.2f\n", ingest_s, ingest_rps);
    printf("scan_seconds=%.6f scan_records=%" PRIu64 " scan_records_per_sec=%.2f\n",
           scan_s, scanned, scan_rps);
    printf("append_busy_events=%zu\n", busy_events);
    return 0;
}

int main(int argc, char** argv) {
    benchmark_options_t opts;
    if (!parse_args(argc, argv, &opts)) {
        if (argc > 1 && (strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "-h") == 0)) {
            return 0;
        }
        print_usage(argv[0]);
        return 2;
    }
    return run_benchmark(&opts);
}
