"""Shared microbench harness for the ideas-lab experiments.

Measures per-call latency of Timelog's *raw C* methods (timelog._timelog.Timelog)
to isolate binding-layer (calling-convention) overhead from the Python facade.

Hygiene: pin to one CPU, disable maintenance to avoid background-thread jitter,
warm up, take the median of R reps, report ns/op. Designed to run identically on
the baseline build and on an experiment build so the delta is the signal.
"""
from __future__ import annotations
import os, sys, time, json, statistics, random

def pin_cpu(cpu: int = 0) -> bool:
    try:
        os.sched_setaffinity(0, {cpu})
        return True
    except (AttributeError, OSError):
        return False

def _median_ns_per_op(fn, iters: int, reps: int = 5) -> dict:
    # warmup
    fn(max(1, iters // 10))
    samples = []
    for _ in range(reps):
        t0 = time.perf_counter_ns()
        fn(iters)
        t1 = time.perf_counter_ns()
        samples.append((t1 - t0) / iters)
    samples.sort()
    return {
        "ns_per_op_median": statistics.median(samples),
        "ns_per_op_min": samples[0],
        "ns_per_op_p50": statistics.median(samples),
        "reps": reps,
        "iters": iters,
    }

def bench_raw_c(iters_append=1_000_000, iters_query=1_000_000, reps=5):
    from timelog import _timelog as C
    pinned = pin_cpu(0)

    results = {"pinned_cpu": pinned, "python": sys.version.split()[0],
               "module": C.__file__, "ops": {}}

    # --- append(ts, obj): METH_VARARGS, 2 positional args ---
    obj = object()  # one shared handle object; engine INCREFs it
    def run_append(n):
        tl = C.Timelog()
        a = tl.append
        for i in range(n):
            a(i, obj)
        tl.close()
    results["ops"]["append_ts_obj"] = _median_ns_per_op(run_append, iters_append, reps)

    # --- point(ts): METH_VARARGS, 1 positional arg, cheap C body on small log ---
    tl = C.Timelog()
    for i in range(1000):
        tl.append(i, obj)
    rng = random.Random(42)
    pts = [rng.randrange(1000) for _ in range(iters_query)]
    def run_point(n):
        p = tl.point
        for i in range(n):
            p(pts[i])
    results["ops"]["point_ts"] = _median_ns_per_op(run_point, iters_query, reps)

    # --- next_ts(ts): METH_VARARGS, 1 positional arg ---
    def run_next(n):
        f = tl.next_ts
        for i in range(n):
            f(pts[i])
    results["ops"]["next_ts"] = _median_ns_per_op(run_next, iters_query, reps)
    tl.close()

    return results

def bench_facade_append(iters=1_000_000, reps=5):
    from timelog import Timelog, TimelogBusyError
    pin_cpu(0)
    obj = object()
    def run(n):
        # Default maintenance (background worker on), matching the raw-C default
        # so the comparison isolates the Python-wrapper cost, not maintenance mode.
        tl = Timelog()
        a = tl.append
        for i in range(n):
            try:
                a(obj, ts=i)
            except TimelogBusyError:
                pass  # TL_EBUSY: record IS inserted; do not retry
        tl.close()
    return _median_ns_per_op(run, iters, reps)

if __name__ == "__main__":
    out = bench_raw_c()
    out["facade_append_obj_ts"] = bench_facade_append()
    print(json.dumps(out, indent=2))
