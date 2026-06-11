"""C4-wwd measurement: TTL/retention whole-window-drop benchmark.

Builds a large number of small time windows (window_size=1000, ts spread over
several hundred windows), compacts each window into its own L1 segment, then
deletes a large fraction of ENTIRE windows (TTL/retention shape). Finally it
adds an L0 churn record into every window so a compaction pass selects every
window's L1 segment -- the deleted windows are fully covered and become
whole-window drops on the variant.

Measures, BASELINE vs VARIANT, the second (post-delete) compaction phase only:
  - compact_cpu_ms : thread_time_ns spent in the maint_step drain loop
  - l1_merged      : delta(select_l1_inputs) -- L1 segments fed to selection
  - pages_after    : storage pages at quiescence
  - l1_after       : L1 segment count at quiescence
Also captures a query fingerprint (sum + count over the whole live range and
per-window point probes) so baseline and variant can be proven identical.

Run on the build whose _timelog.so is on PYTHONPATH; emits one JSON line.
Config (optional JSON arg): {"n_windows":..., "per_window":..., "drop_frac":...}
"""
from __future__ import annotations
import gc
import json
import sys
import time

import timelog

WINDOW_SIZE = 1000


def drain(tl, limit=5_000_000):
    n = 0
    while n < limit and tl.maint_step():
        n += 1
    if n >= limit and tl.maint_step():
        raise RuntimeError(f"maintenance drain exceeded cap ({limit})")
    return n


def run(cfg):
    n_windows = cfg.get("n_windows", 400)
    per_window = cfg.get("per_window", 200)
    drop_frac = cfg.get("drop_frac", 0.6)
    # Drop the first drop_frac fraction of windows entirely (contiguous TTL tail).
    n_drop = int(n_windows * drop_frac)
    drop_windows = set(range(n_drop))

    gc.disable()
    tl = timelog.Timelog(
        maintenance="disabled",
        busy_policy="flush",
        window_size=WINDOW_SIZE,
        max_delta_segments=2,
    )

    # Phase 1: build one L1 segment per window (flush + compact incrementally).
    for w in range(n_windows):
        base = w * WINDOW_SIZE
        for j in range(per_window):
            tl.append(base + j, base + j)  # payload == ts (pure-int handle)
        tl.flush()
        drain(tl)

    s0 = tl.stats()
    l1_built = s0["storage"]["segments_l1"]
    l1in_0 = s0["compaction_selection"]["select_l1_inputs"]
    pages_0 = s0["storage"]["pages_total"]

    # Phase 2: delete whole windows (TTL/retention), then flush the
    # tombstones into L0 so a compaction pass folds them into the overlapping
    # L1 windows. The deleted windows become fully covered.
    for w in drop_windows:
        base = w * WINDOW_SIZE
        tl.delete_range(base, base + WINDOW_SIZE)
    # Add an L0 churn record into every SURVIVING window so the merged output
    # is non-trivial and selection spans the whole timeline.
    for w in range(n_drop, n_windows):
        base = w * WINDOW_SIZE
        tl.append(base + 1, base + 1)
    tl.flush()  # seal tombstones + churn into L0

    # ---- MEASURED REGION: post-delete compaction drain --------------------
    cpu0 = time.thread_time_ns()
    tl.compact()           # request compaction over the deleted span
    steps = drain(tl)
    # extra settling passes (counted) so all deleted windows reconcile
    for _ in range(6):
        tl.compact()
        steps += drain(tl)
    compact_cpu_ns = time.thread_time_ns() - cpu0
    # -----------------------------------------------------------------------

    gc.collect()
    s1 = tl.stats()
    l1in_1 = s1["compaction_selection"]["select_l1_inputs"]
    pages_1 = s1["storage"]["pages_total"]
    l1_after = s1["storage"]["segments_l1"]

    # Query fingerprint over the whole range: count + checksum of timestamps.
    lo, hi = 0, n_windows * WINDOW_SIZE
    cnt = 0
    checksum = 0
    for ts, payload in tl.range(lo, hi):
        cnt += 1
        checksum = (checksum + ts) & 0xFFFFFFFFFFFFFFFF
    # Per-window probe: deleted windows must be empty, surviving windows must
    # still hold their records. Count windows that return any record.
    point_hits = 0
    for w in range(n_windows):
        base = w * WINDOW_SIZE
        if any(True for _ in tl.range(base, base + WINDOW_SIZE)):
            point_hits += 1

    tl.close()
    gc.enable()

    return {
        "module": timelog._timelog.__file__,
        "n_windows": n_windows,
        "per_window": per_window,
        "drop_frac": drop_frac,
        "n_drop": n_drop,
        "l1_built": l1_built,
        "l1_after": l1_after,
        "l1_merged_phase2": l1in_1 - l1in_0,
        "pages_built": pages_0,
        "pages_after": pages_1,
        "compact_cpu_ms": round(compact_cpu_ns / 1e6, 2),
        "maint_steps_phase2": steps,
        "compactions_total": s1["operational"]["compactions_total"],
        # query fingerprint (must be identical baseline vs variant)
        "query_count": cnt,
        "query_checksum": checksum,
        "point_hits": point_hits,
    }


if __name__ == "__main__":
    cfg = json.loads(sys.argv[1]) if len(sys.argv) > 1 else {}
    print(json.dumps(run(cfg)))
