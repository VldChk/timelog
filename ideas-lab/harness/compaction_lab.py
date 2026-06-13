"""compaction_lab — the real, reusable compaction-experiment harness.

Runs ONE (build, workload, config, seed) cell and emits a full metrics JSON. A build is selected by the
PYTHONPATH the caller sets, so the SAME harness measures the baseline .so or any variant .so identically.
A driver (run_matrix.py) invokes this as a subprocess per cell -> build-isolation + process-isolation.

Metrics (methodology-review protocol, _data/compaction-study.json):
  write_amp   : 1 + delta(select_l0_inputs + select_l1_inputs)*avg_seg_records / records_flushed
  space_amp   : pages_total*target_page_bytes / (live_records*16)
  read_amp    : point/range p50/p99 at quiescence (K = l0+l1 segments)
  compact_cpu : thread_time_ns spent in the maint_step() drain loop (attributable, race-free)
  rss_mb      : /proc/self/statm resident at quiescence after gc.collect()
  layout      : segments_l0, segments_l1, pages_total, tombstone_count, compactions_total

Usage (single cell): python compaction_lab.py '<json-config>'
  config = {"workload": "...", "N": ..., "seed": ..., "page_bytes": ..., "tl_kwargs": {...},
            "query_shapes": [...], "queries": ...}
"""
from __future__ import annotations
import importlib, os, sys, gc, json, time, random

PAGE_BYTES_DEFAULT = 64 * 1024
REC_BYTES = 16  # sizeof(int64 ts) + sizeof(uint64 handle)

def _pin():
    try: os.sched_setaffinity(0, {0})
    except Exception:
        pass  # CPU affinity is optional outside Linux benchmark hosts.

def _rss_mb():
    try:
        with open("/proc/self/statm") as f:
            resident_pages = int(f.read().split()[1])
        return resident_pages * os.sysconf("SC_PAGE_SIZE") / (1024 * 1024)
    except Exception:
        return None

# ---------------- deterministic workload generators ----------------
def gen_workload(kind, N, seed, window_ms=3_600_000):
    """Return (events, deletes). events = list of (ts, payload_id). deletes = list of (t1,t2)."""
    rng = random.Random(seed)
    deletes = []
    if kind == "steady":            # monotonically increasing across ~N/density windows
        events = [(i, i) for i in range(N)]
    elif kind == "ooo":             # 20% backward (late) arrivals
        events = []
        cur = 0
        for i in range(N):
            if rng.random() < 0.20 and cur > 1000:
                events.append((cur - rng.randint(1, 1000), i))   # late
            else:
                cur += rng.randint(1, 3); events.append((cur, i))
    elif kind == "bursty":          # bursts of 5000 then time jump
        events = []; t = 0
        for b in range(N // 5000):
            for _ in range(5000):
                t += rng.randint(0, 2); events.append((t, len(events)))
            t += window_ms // 4                                   # idle gap
    elif kind == "delete_storm":    # steady append, then delete half the span in chunks
        events = [(i, i) for i in range(N)]
        span = N
        # delete 40% of the timeline in 1/20-span chunks (TTL/retention shape)
        chunk = max(1, span // 20)
        t = 0
        while t < int(span * 0.40):
            deletes.append((t, t + chunk)); t += chunk
    else:
        raise ValueError(f"unknown workload {kind}")
    return events, deletes

# ---------------- the cell runner ----------------
def _drain(tl, limit=2_000_000):
    n = 0
    while n < limit and tl.maint_step():
        n += 1
    if n >= limit and tl.maint_step():
        raise RuntimeError(f"maintenance drain exceeded cap ({limit})")
    return n

def _counters(tl):
    s = tl.stats()
    return {
        "l0in": s["compaction_selection"]["select_l0_inputs"],
        "l1in": s["compaction_selection"]["select_l1_inputs"],
        "comp": s["operational"]["compactions_total"],
        "seals": s["operational"]["seals_total"],
        "l0": s["storage"]["segments_l0"], "l1": s["storage"]["segments_l1"],
        "pages": s["storage"]["pages_total"], "tomb": s["storage"]["tombstone_count"],
        "records_est": s["storage"]["records_estimate"],
    }

def _query_latency(tl, lo, hi, shapes, queries):
    rng = random.Random(0xBEEF)
    out = {}
    pts = [rng.randrange(lo, hi) for _ in range(queries)]
    if "point" in shapes:
        p = tl.point
        for q in pts[:200]: p(q)
        lat = []
        for q in pts:
            t0 = time.perf_counter_ns(); p(q); lat.append(time.perf_counter_ns() - t0)
        lat.sort()
        out["point_p50"] = lat[len(lat)//2]; out["point_p99"] = lat[int(0.99*len(lat))]
    if "range" in shapes:
        r = tl.range; w = max(1, (hi - lo) // 1000)
        for q in pts[:200]:
            for _ in r(q, q+w): pass
        lat = []
        for q in pts:
            t0 = time.perf_counter_ns(); c = 0
            for _ in r(q, q+w): c += 1
            lat.append(time.perf_counter_ns() - t0)
        lat.sort()
        out["range_p50"] = lat[len(lat)//2]; out["range_p99"] = lat[int(0.99*len(lat))]
    return out

def run_cell(cfg):
    from timelog import Timelog, TimelogBusyError
    timelog_module = importlib.import_module("timelog")
    _pin()
    N = cfg["N"]; seed = cfg.get("seed", 1)
    page_bytes = cfg.get("page_bytes", PAGE_BYTES_DEFAULT)
    tl_kwargs = dict(cfg.get("tl_kwargs", {}))
    tl_kwargs.setdefault("maintenance", "disabled")
    tl_kwargs.setdefault("busy_policy", "flush")
    tl_kwargs.setdefault("target_page_bytes", page_bytes)
    events, deletes = gen_workload(cfg["workload"], N, seed)

    gc.disable()
    tl = Timelog(**tl_kwargs)
    c0 = _counters(tl)
    # ingest (flush every flush_every to create L0; drive compaction when trigger met)
    flush_every = cfg.get("flush_every", 25_000)
    trig = tl_kwargs.get("max_delta_segments", 8) or 8
    compact_cpu_ns = 0           # accumulate attributable compaction CPU across ALL drains
    steps = 0
    for idx, (ts, pid) in enumerate(events):
        try:
            tl.append(ts, pid)
        except TimelogBusyError:
            pass  # TL_EBUSY means the record was committed.
        if (idx + 1) % flush_every == 0:
            tl.flush()
            if tl.stats()["storage"]["segments_l0"] >= trig:
                cpu0 = time.thread_time_ns(); steps += _drain(tl); compact_cpu_ns += time.thread_time_ns() - cpu0
    tl.flush()
    for (t1, t2) in deletes:
        tl.delete_range(t1, t2)
    if deletes:
        # Tombstones are not visible to delete-debt compaction until sealed.
        tl.flush()
    cpu0 = time.thread_time_ns()
    steps += _drain(tl)
    compact_cpu_ns += time.thread_time_ns() - cpu0
    gc.collect()
    c1 = _counters(tl)
    rss = _rss_mb()

    # derive metrics
    live = N - sum(min(t2, N) - max(t1, 0) for (t1, t2) in deletes if t1 < N)
    live = max(1, live)
    segs = c1["l0"] + c1["l1"]
    avg_seg_records = (c1["records_est"] / segs) if segs else 0
    merged = (c1["l0in"] - c0["l0in"]) + (c1["l1in"] - c0["l1in"])
    records_flushed = N
    write_amp = 1.0 + (merged * avg_seg_records) / records_flushed if records_flushed else 0
    space_amp = (c1["pages"] * page_bytes) / (live * REC_BYTES)

    lat = _query_latency(tl, 0, max(2, N), cfg.get("query_shapes", ["point", "range"]),
                         cfg.get("queries", 20000))
    tl.close()
    gc.enable()
    return {
        "workload": cfg["workload"], "N": N, "seed": seed, "tl_kwargs": cfg.get("tl_kwargs", {}),
        "module": timelog_module._timelog.__file__ if hasattr(timelog_module, "_timelog") else timelog_module.__file__,
        "layout": {k: c1[k] for k in ("l0", "l1", "pages", "tomb", "comp")},
        "segments_merged": merged, "maint_steps": steps,
        "write_amp": round(write_amp, 3), "space_amp": round(space_amp, 3),
        "compact_cpu_ms": round(compact_cpu_ns / 1e6, 2), "rss_mb": round(rss, 1) if rss else None,
        "read_amp": lat,
    }

if __name__ == "__main__":
    cfg = json.loads(sys.argv[1])
    print(json.dumps(run_cell(cfg)))
