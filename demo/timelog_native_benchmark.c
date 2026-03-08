/*===========================================================================
 * timelog_native_benchmark.c - Native C benchmark harness for Timelog.
 *
 * Purpose:
 * - Measure core engine performance without Python wrapper/runtime overhead.
 * - Provide ingest, full-range scan, and point-query throughput numbers.
 *
 * Usage example:
 *   timelog_native_benchmark --records 5000000 --batch-size 4096 \
 *     --ooo-rate 0.05 --point-queries 100000
 *===========================================================================*/

#include "timelog/timelog.h"

#include <errno.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#else
#include <time.h>
#endif

typedef struct {
    uint64_t records;
    uint32_t batch_size;
    double ooo_rate;
    uint32_t ooo_lag;
    uint32_t point_queries;
    uint64_t seed;
    size_t memtable_max_bytes;
    size_t sealed_max_runs;
    int use_batch_append;
} bench_options_t;

typedef struct {
    double ingest_seconds;
    double flush_seconds;
    double scan_seconds;
    double point_seconds;
    uint64_t scan_records;
    uint64_t point_hits;
    uint64_t busy_returns;
    uint64_t flush_ebusy_retries;
} bench_metrics_t;

static double now_seconds(void) {
#ifdef _WIN32
    static LARGE_INTEGER freq = {0};
    LARGE_INTEGER counter;
    if (freq.QuadPart == 0) {
        QueryPerformanceFrequency(&freq);
    }
    QueryPerformanceCounter(&counter);
    return (double)counter.QuadPart / (double)freq.QuadPart;
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
#endif
}

static uint64_t rng_next(uint64_t* state) {
    uint64_t x = (*state == 0) ? 0x9E3779B97F4A7C15ULL : *state;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    *state = x;
    return x * 0x2545F4914F6CDD1DULL;
}

static uint64_t rng_bounded(uint64_t* state, uint64_t bound) {
    if (bound == 0) {
        return 0;
    }
    return rng_next(state) % bound;
}

static int rng_hit_probability(uint64_t* state, double probability) {
    const double denom = 9007199254740992.0; /* 2^53 */
    double u;
    if (probability <= 0.0) {
        return 0;
    }
    if (probability >= 1.0) {
        return 1;
    }
    u = (double)(rng_next(state) >> 11) / denom;
    return u < probability;
}

static int parse_u64(const char* s, uint64_t* out) {
    unsigned long long v;
    char* end = NULL;
    if (s == NULL || out == NULL) {
        return 0;
    }
    errno = 0;
    v = strtoull(s, &end, 10);
    if (errno != 0 || end == s || *end != '\0') {
        return 0;
    }
    *out = (uint64_t)v;
    return 1;
}

static int parse_u32(const char* s, uint32_t* out) {
    uint64_t v = 0;
    if (!parse_u64(s, &v) || v > UINT32_MAX) {
        return 0;
    }
    *out = (uint32_t)v;
    return 1;
}

static int parse_size(const char* s, size_t* out) {
    uint64_t v = 0;
    if (!parse_u64(s, &v) || v > (uint64_t)SIZE_MAX) {
        return 0;
    }
    *out = (size_t)v;
    return 1;
}

static int parse_double_value(const char* s, double* out) {
    double v;
    char* end = NULL;
    if (s == NULL || out == NULL) {
        return 0;
    }
    errno = 0;
    v = strtod(s, &end);
    if (errno != 0 || end == s || *end != '\0' || !isfinite(v)) {
        return 0;
    }
    *out = v;
    return 1;
}

static void print_usage(const char* exe) {
    printf("Usage: %s [options]\n", exe);
    printf("\n");
    printf("Native C benchmark (no Python wrapper overhead).\n");
    printf("\n");
    printf("Options:\n");
    printf("  --records N           Total records to ingest (default: 5000000)\n");
    printf("  --batch-size N        Records per tl_append_batch call (default: 4096)\n");
    printf("  --single-append       Use tl_append per record (disable batch mode)\n");
    printf("  --ooo-rate R          Out-of-order probability [0..1] (default: 0.05)\n");
    printf("  --ooo-lag N           Max OOO lag in timestamps (default: 1000)\n");
    printf("  --point-queries N     Random point queries after ingest (default: 100000)\n");
    printf("  --seed N              RNG seed (default: 12345)\n");
    printf("  --memtable-mb N       memtable_max_bytes in MiB (default: 64)\n");
    printf("  --sealed-runs N       sealed_max_runs (default: 64)\n");
    printf("  -h, --help            Show this help\n");
}

static int parse_args(int argc, char** argv, bench_options_t* opts) {
    int i;
    if (opts == NULL) {
        return 0;
    }
    for (i = 1; i < argc; i++) {
        const char* arg = argv[i];
        if (strcmp(arg, "-h") == 0 || strcmp(arg, "--help") == 0) {
            print_usage(argv[0]);
            return 2;
        }
        if (strcmp(arg, "--single-append") == 0) {
            opts->use_batch_append = 0;
            continue;
        }
        if (i + 1 >= argc) {
            fprintf(stderr, "Missing value for argument: %s\n", arg);
            return 0;
        }
        if (strcmp(arg, "--records") == 0) {
            if (!parse_u64(argv[++i], &opts->records) || opts->records == 0) {
                fprintf(stderr, "Invalid --records value\n");
                return 0;
            }
        } else if (strcmp(arg, "--batch-size") == 0) {
            if (!parse_u32(argv[++i], &opts->batch_size) || opts->batch_size == 0) {
                fprintf(stderr, "Invalid --batch-size value\n");
                return 0;
            }
        } else if (strcmp(arg, "--ooo-rate") == 0) {
            if (!parse_double_value(argv[++i], &opts->ooo_rate) ||
                opts->ooo_rate < 0.0 || opts->ooo_rate > 1.0) {
                fprintf(stderr, "Invalid --ooo-rate value\n");
                return 0;
            }
        } else if (strcmp(arg, "--ooo-lag") == 0) {
            if (!parse_u32(argv[++i], &opts->ooo_lag) || opts->ooo_lag == 0) {
                fprintf(stderr, "Invalid --ooo-lag value\n");
                return 0;
            }
        } else if (strcmp(arg, "--point-queries") == 0) {
            if (!parse_u32(argv[++i], &opts->point_queries)) {
                fprintf(stderr, "Invalid --point-queries value\n");
                return 0;
            }
        } else if (strcmp(arg, "--seed") == 0) {
            if (!parse_u64(argv[++i], &opts->seed)) {
                fprintf(stderr, "Invalid --seed value\n");
                return 0;
            }
        } else if (strcmp(arg, "--memtable-mb") == 0) {
            size_t mib = 0;
            if (!parse_size(argv[++i], &mib) || mib == 0) {
                fprintf(stderr, "Invalid --memtable-mb value\n");
                return 0;
            }
            if (mib > SIZE_MAX / (1024U * 1024U)) {
                fprintf(stderr, "--memtable-mb value too large\n");
                return 0;
            }
            opts->memtable_max_bytes = mib * 1024U * 1024U;
        } else if (strcmp(arg, "--sealed-runs") == 0) {
            if (!parse_size(argv[++i], &opts->sealed_max_runs) ||
                opts->sealed_max_runs == 0) {
                fprintf(stderr, "Invalid --sealed-runs value\n");
                return 0;
            }
        } else {
            fprintf(stderr, "Unknown argument: %s\n", arg);
            return 0;
        }
    }
    return 1;
}

static tl_ts_t generate_timestamp(const bench_options_t* opts, uint64_t* rng_state,
                                  tl_ts_t cursor) {
    tl_ts_t ts = cursor;
    if (cursor > (tl_ts_t)opts->ooo_lag && rng_hit_probability(rng_state, opts->ooo_rate)) {
        uint32_t lag = (uint32_t)(rng_bounded(rng_state, (uint64_t)opts->ooo_lag) + 1U);
        ts -= (tl_ts_t)lag;
    }
    return ts;
}

static tl_status_t run_ingest(tl_timelog_t* tl, const bench_options_t* opts,
                              tl_ts_t* timestamps, bench_metrics_t* metrics) {
    uint64_t rng_state = (opts->seed == 0) ? 12345ULL : opts->seed;
    uint64_t produced = 0;
    tl_ts_t cursor = 0;
    tl_handle_t next_handle = 1;
    double t0 = now_seconds();
    tl_status_t st = TL_OK;

    if (opts->use_batch_append) {
        tl_record_t* batch = (tl_record_t*)calloc(opts->batch_size, sizeof(tl_record_t));
        uint32_t flags =
            (opts->ooo_rate <= 0.20) ? TL_APPEND_HINT_MOSTLY_IN_ORDER : TL_APPEND_NONE;
        if (batch == NULL) {
            return TL_ENOMEM;
        }
        while (produced < opts->records) {
            uint64_t remaining = opts->records - produced;
            size_t n = (size_t)((remaining < (uint64_t)opts->batch_size)
                                    ? remaining
                                    : (uint64_t)opts->batch_size);
            size_t i;
            for (i = 0; i < n; i++) {
                tl_ts_t ts;
                cursor += 1;
                ts = generate_timestamp(opts, &rng_state, cursor);
                timestamps[produced + i] = ts;
                batch[i].ts = ts;
                batch[i].handle = next_handle++;
            }
            st = tl_append_batch(tl, batch, n, flags);
            if (st != TL_OK && st != TL_EBUSY) {
                free(batch);
                return st;
            }
            if (st == TL_EBUSY) {
                metrics->busy_returns += 1;
            }
            produced += (uint64_t)n;
        }
        free(batch);
    } else {
        while (produced < opts->records) {
            tl_ts_t ts;
            cursor += 1;
            ts = generate_timestamp(opts, &rng_state, cursor);
            timestamps[produced] = ts;
            st = tl_append(tl, ts, next_handle++);
            if (st != TL_OK && st != TL_EBUSY) {
                return st;
            }
            if (st == TL_EBUSY) {
                metrics->busy_returns += 1;
            }
            produced += 1;
        }
    }

    metrics->ingest_seconds = now_seconds() - t0;
    return TL_OK;
}

static tl_status_t flush_with_retry(tl_timelog_t* tl, uint32_t max_attempts,
                                    bench_metrics_t* metrics) {
    uint32_t attempt;
    for (attempt = 0; attempt < max_attempts; attempt++) {
        tl_status_t st = tl_flush(tl);
        if (st == TL_OK || st == TL_EOF) {
            return TL_OK;
        }
        if (st == TL_EBUSY) {
            metrics->flush_ebusy_retries += 1;
            continue;
        }
        return st;
    }
    return TL_EBUSY;
}

static tl_status_t run_full_scan(const tl_timelog_t* tl, bench_metrics_t* metrics) {
    tl_snapshot_t* snap = NULL;
    tl_iter_t* it = NULL;
    tl_record_t rec;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    double t0;
    double t1;
    uint64_t count = 0;
    if (st != TL_OK) {
        return st;
    }

    st = tl_iter_since(snap, TL_TS_MIN, &it);
    if (st != TL_OK) {
        tl_snapshot_release(snap);
        return st;
    }

    t0 = now_seconds();
    while ((st = tl_iter_next(it, &rec)) == TL_OK) {
        count += 1;
    }
    t1 = now_seconds();

    tl_iter_destroy(it);
    tl_snapshot_release(snap);

    if (st != TL_EOF) {
        return st;
    }

    metrics->scan_records = count;
    metrics->scan_seconds = t1 - t0;
    return TL_OK;
}

static tl_status_t run_point_queries(const tl_timelog_t* tl, const bench_options_t* opts,
                                     const tl_ts_t* timestamps, bench_metrics_t* metrics) {
    tl_snapshot_t* snap = NULL;
    tl_record_t rec;
    tl_status_t st = tl_snapshot_acquire(tl, &snap);
    uint64_t rng_state = (opts->seed == 0) ? 67890ULL : (opts->seed ^ 0xA5A5A5A5ULL);
    uint64_t total_hits = 0;
    uint32_t q;
    double t0;
    double t1;
    if (st != TL_OK) {
        return st;
    }

    t0 = now_seconds();
    for (q = 0; q < opts->point_queries; q++) {
        uint64_t idx = rng_bounded(&rng_state, opts->records);
        tl_iter_t* it = NULL;
        st = tl_iter_point(snap, timestamps[idx], &it);
        if (st != TL_OK) {
            tl_snapshot_release(snap);
            return st;
        }
        while ((st = tl_iter_next(it, &rec)) == TL_OK) {
            total_hits += 1;
        }
        tl_iter_destroy(it);
        if (st != TL_EOF) {
            tl_snapshot_release(snap);
            return st;
        }
    }
    t1 = now_seconds();

    tl_snapshot_release(snap);
    metrics->point_seconds = t1 - t0;
    metrics->point_hits = total_hits;
    return TL_OK;
}

int main(int argc, char** argv) {
    bench_options_t opts;
    bench_metrics_t metrics;
    tl_config_t cfg;
    tl_timelog_t* tl = NULL;
    tl_ts_t* timestamps = NULL;
    tl_status_t st;
    double t0;
    double t1;

    memset(&metrics, 0, sizeof(metrics));
    memset(&opts, 0, sizeof(opts));
    opts.records = 5000000ULL;
    opts.batch_size = 4096U;
    opts.ooo_rate = 0.05;
    opts.ooo_lag = 1000U;
    opts.point_queries = 100000U;
    opts.seed = 12345ULL;
    opts.memtable_max_bytes = 64U * 1024U * 1024U;
    opts.sealed_max_runs = 64U;
    opts.use_batch_append = 1;

    {
        int parse_rc = parse_args(argc, argv, &opts);
        if (parse_rc == 2) {
            return 0;
        }
        if (parse_rc != 1) {
            print_usage(argv[0]);
            return 1;
        }
    }

    if (opts.records > (uint64_t)SIZE_MAX / sizeof(tl_ts_t)) {
        fprintf(stderr, "records value too large for this platform\n");
        return 1;
    }

    timestamps = (tl_ts_t*)malloc((size_t)opts.records * sizeof(tl_ts_t));
    if (timestamps == NULL) {
        fprintf(stderr, "Failed to allocate timestamp buffer for %" PRIu64 " records\n",
                opts.records);
        return 1;
    }

    st = tl_config_init_defaults(&cfg);
    if (st != TL_OK) {
        fprintf(stderr, "tl_config_init_defaults failed: %s\n", tl_strerror(st));
        free(timestamps);
        return 1;
    }

    cfg.maintenance_mode = TL_MAINT_BACKGROUND;
    cfg.memtable_max_bytes = opts.memtable_max_bytes;
    cfg.sealed_max_runs = opts.sealed_max_runs;
    cfg.log_level = TL_LOG_NONE;

    st = tl_open(&cfg, &tl);
    if (st != TL_OK) {
        fprintf(stderr, "tl_open failed: %s\n", tl_strerror(st));
        free(timestamps);
        return 1;
    }

    printf("Timelog Native C Benchmark\n");
    printf("  records:            %" PRIu64 "\n", opts.records);
    printf("  append mode:        %s\n", opts.use_batch_append ? "batch" : "single");
    printf("  batch_size:         %u\n", opts.batch_size);
    printf("  ooo_rate:           %.3f\n", opts.ooo_rate);
    printf("  ooo_lag:            %u\n", opts.ooo_lag);
    printf("  point_queries:      %u\n", opts.point_queries);
    printf("  memtable_max_bytes: %zu\n", opts.memtable_max_bytes);
    printf("  sealed_max_runs:    %zu\n", opts.sealed_max_runs);
    printf("  seed:               %" PRIu64 "\n", opts.seed);

    st = run_ingest(tl, &opts, timestamps, &metrics);
    if (st != TL_OK) {
        fprintf(stderr, "Ingest failed: %s\n", tl_strerror(st));
        tl_close(tl);
        free(timestamps);
        return 1;
    }

    t0 = now_seconds();
    st = flush_with_retry(tl, 128U, &metrics);
    t1 = now_seconds();
    if (st != TL_OK) {
        fprintf(stderr, "Flush failed: %s\n", tl_strerror(st));
        tl_close(tl);
        free(timestamps);
        return 1;
    }
    metrics.flush_seconds = t1 - t0;

    st = run_full_scan(tl, &metrics);
    if (st != TL_OK) {
        fprintf(stderr, "Full scan failed: %s\n", tl_strerror(st));
        tl_close(tl);
        free(timestamps);
        return 1;
    }

    st = run_point_queries(tl, &opts, timestamps, &metrics);
    if (st != TL_OK) {
        fprintf(stderr, "Point queries failed: %s\n", tl_strerror(st));
        tl_close(tl);
        free(timestamps);
        return 1;
    }

    printf("\nResults\n");
    printf("  ingest_seconds:     %.6f s\n", metrics.ingest_seconds);
    printf("  ingest_throughput:  %.3f M rec/s\n",
           ((double)opts.records / metrics.ingest_seconds) / 1e6);
    printf("  ingest_ns_per_rec:  %.1f ns\n",
           (metrics.ingest_seconds * 1e9) / (double)opts.records);
    printf("  ingest_ebusy:       %" PRIu64 " (accepted writes)\n", metrics.busy_returns);
    printf("  flush_seconds:      %.6f s\n", metrics.flush_seconds);
    printf("  flush_ebusy_retries:%" PRIu64 "\n", metrics.flush_ebusy_retries);
    printf("  scan_seconds:       %.6f s\n", metrics.scan_seconds);
    printf("  scan_records:       %" PRIu64 "\n", metrics.scan_records);
    printf("  scan_throughput:    %.3f M rec/s\n",
           ((double)metrics.scan_records / metrics.scan_seconds) / 1e6);
    printf("  point_seconds:      %.6f s\n", metrics.point_seconds);
    printf("  point_qps:          %.3f M q/s\n",
           ((double)opts.point_queries / metrics.point_seconds) / 1e6);
    printf("  point_hits_total:   %" PRIu64 "\n", metrics.point_hits);
    printf("  avg_hits_per_query: %.3f\n",
           (opts.point_queries == 0U)
               ? 0.0
               : ((double)metrics.point_hits / (double)opts.point_queries));

    if (metrics.scan_records != opts.records) {
        printf("  WARNING: scan_records != inserted_records (%" PRIu64 " vs %" PRIu64 ")\n",
               metrics.scan_records, opts.records);
    }

    tl_close(tl);
    free(timestamps);
    return 0;
}
