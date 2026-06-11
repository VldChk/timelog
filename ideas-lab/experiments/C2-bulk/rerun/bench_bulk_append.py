#!/usr/bin/env python3
"""Rerun probe for C2-bulk.

Run with PYTHONPATH pointing at a build where C2-bulk/prototype.patch is applied.
Emits JSON with per-record timings and endian behavior.
"""
from __future__ import annotations

import json
import statistics
import time

import numpy as np
from timelog import Timelog


def median_ns_per_record(fn, n: int, repeats: int = 5) -> float:
    samples: list[float] = []
    for _ in range(repeats):
        t0 = time.perf_counter_ns()
        fn()
        samples.append((time.perf_counter_ns() - t0) / n)
    return statistics.median(samples)


def main() -> None:
    n = 200_000
    timestamps = np.arange(n, dtype=np.int64)
    objects = list(range(n))

    def per_append() -> None:
        log = Timelog(maintenance="disabled")
        for ts, obj in zip(timestamps, objects, strict=True):
            log.append(int(ts), obj)
        log.close()

    def extend_pairs() -> None:
        log = Timelog(maintenance="disabled")
        log.extend(zip(timestamps.tolist(), objects, strict=True))
        log.close()

    def bulk_append() -> None:
        log = Timelog(maintenance="disabled")
        log.bulk_append(timestamps, objects)
        log.close()

    endian_behavior = {}
    big_endian = timestamps.astype(">i8")
    try:
        log = Timelog(maintenance="disabled")
        log.bulk_append(big_endian, objects)
        rows = list(log.range(0, 10))
        log.close()
        endian_behavior = {"accepted": True, "rows_head": rows[:3]}
    except Exception as exc:  # noqa: BLE001 - experiment records exact behavior.
        endian_behavior = {
            "accepted": False,
            "error_type": type(exc).__name__,
            "error": str(exc),
        }

    per_ns = median_ns_per_record(per_append, n, repeats=3)
    extend_ns = median_ns_per_record(extend_pairs, n)
    bulk_ns = median_ns_per_record(bulk_append, n)
    print(json.dumps({
        "n": n,
        "per_append_ns_per_record": round(per_ns, 3),
        "extend_ns_per_record": round(extend_ns, 3),
        "bulk_append_ns_per_record": round(bulk_ns, 3),
        "bulk_vs_per_append": round(per_ns / bulk_ns, 3),
        "bulk_vs_extend": round(extend_ns / bulk_ns, 3),
        "non_native_endian_behavior": endian_behavior,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
