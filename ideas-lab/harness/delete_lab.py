"""delete_lab — focused measurement of tombstone canonicalization + delete-debt sweep.

Experiment C5-canon. BASELINE build, no core change. Measures whether enabling
`delete_debt_threshold` meaningfully reduces space_amp / reclaim-lag on
delete-heavy workloads, and at what read/CPU cost.

Mechanism recap (from core/src/maint/tl_compaction.c):
  - delete_range() inserts a tombstone into the memtable.
  - flush() carries tombstones into L0 segments (and applies them to records
    flushed in the same memrun).
  - tl_compact_needed() fires when EITHER L0 count >= max_delta_segments OR
    (delete_debt_threshold > 0 AND max per-window covered-fraction of L0
    tombstones >= threshold).
  - delete-debt only scans L0 tombstones. A tombstone in the memtable is
    invisible to the heuristic until flushed.
  - compaction physically drops covered records, emits non-overlapping L1, and
    preserves residual tombstones; THIS is what reclaims physical pages.

To ISOLATE the delete-debt trigger from the L0-count trigger, the protocol
drains compaction to quiescence BEFORE deleting (L0 below trigger), then issues
a delete + flush, then counts maint_steps until physical pages stop dropping.
With debt disabled (0.0) and L0 below the segment trigger, NO compaction fires
on its own -> the deleted data stays resident (reclaim-lag = unbounded until an
unrelated trigger). With debt enabled, compaction fires within a maint_step or
two once the flushed tombstone's per-window coverage crosses the threshold.

Usage (single cell): python3 delete_lab.py '<json-config>'
  cfg = {"N":..., "seed":..., "page_bytes":..., "del_frac":..., "n_chunks":...,
         "delete_debt_threshold":..., "max_delta_segments":..., "flush_every":...,
         "queries":..., "window_size":...}
"""
from __future__ import annotations
import os, sys, gc, json, time, random

PAGE_BYTES_DEFAULT = 64 * 1024
REC_BYTES = 16  # int64 ts + uint64 handle


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


def _counters(tl):
    s = tl.stats()
    return {
        "l0": s["storage"]["segments_l0"], "l1": s["storage"]["segments_l1"],
        "pages": s["storage"]["pages_total"], "tomb": s["storage"]["tombstone_count"],
        "comp": s["operational"]["compactions_total"],
        "records_est": s["storage"]["records_estimate"],
        "l0in": s["compaction_selection"]["select_l0_inputs"],
        "l1in": s["compaction_selection"]["select_l1_inputs"],
    }


def _drain(tl, limit=2_000_000):
    n = 0
    while n < limit and tl.maint_step():
        n += 1
    if n >= limit and tl.maint_step():
        raise RuntimeError(f"maintenance drain exceeded cap ({limit})")
    return n


def _drain_one(tl):
    """Advance maintenance by exactly one step; return True if work was done."""
    return bool(tl.maint_step())


def _point_range_lat(tl, lo, hi, queries, width):
    rng = random.Random(0xBEEF)
    pts = [rng.randrange(lo, max(lo + 1, hi)) for _ in range(queries)]
    out = {}
    p = tl.point
    for q in pts[:200]: p(q)
    lat = []
    for q in pts:
        t0 = time.perf_counter_ns(); p(q); lat.append(time.perf_counter_ns() - t0)
    lat.sort()
    out["point_p50"] = lat[len(lat) // 2]; out["point_p99"] = lat[int(0.99 * len(lat))]
    r = tl.range
    for q in pts[:200]:
        for _ in r(q, q + width): pass
    lat = []
    for q in pts:
        t0 = time.perf_counter_ns(); c = 0
        for _ in r(q, q + width): c += 1
        lat.append(time.perf_counter_ns() - t0)
    lat.sort()
    out["range_p50"] = lat[len(lat) // 2]; out["range_p99"] = lat[int(0.99 * len(lat))]
    return out


def run_cell(cfg):
    from timelog import Timelog
    _pin()
    N = cfg["N"]
    page_bytes = cfg.get("page_bytes", PAGE_BYTES_DEFAULT)
    del_frac = cfg.get("del_frac", 0.40)
    n_chunks = cfg.get("n_chunks", 8)
    flush_every = cfg.get("flush_every", 25_000)
    queries = cfg.get("queries", 20_000)
    ddt = cfg.get("delete_debt_threshold", 0.0)
    max_delta = cfg.get("max_delta_segments", 8)

    tl_kwargs = {
        "maintenance": "disabled",
        "busy_policy": "flush",
        "target_page_bytes": page_bytes,
        "max_delta_segments": max_delta,
        "delete_debt_threshold": ddt,
    }
    if "window_size" in cfg and cfg["window_size"]:
        tl_kwargs["window_size"] = cfg["window_size"]

    gc.disable()
    tl = Timelog(**tl_kwargs)

    # ---- Phase 1: steady ingest, periodic flush, drain compaction so we reach
    # a clean baseline with data laid out into L1 (non-overlapping windows). ----
    for i in range(N):
        tl.append(i, i)
        if (i + 1) % flush_every == 0:
            tl.flush()
            if tl.stats()["storage"]["segments_l0"] >= max_delta:
                _drain(tl)
    tl.flush()
    tl.compact()
    _drain(tl)  # force a clean L1 baseline before measuring delete debt
    gc.collect()

    base = _counters(tl)
    if base["l0"] != 0 or base["l1"] == 0:
        tl.close()
        gc.enable()
        raise RuntimeError(
            f"delete_lab failed to build a clean L1 baseline: "
            f"l0={base['l0']} l1={base['l1']}"
        )
    base_rss = _rss_mb()
    # ---- Phase 2: delete a contiguous chunk of the timeline near the front.
    # Front placement guarantees window-dense coverage so a window's covered
    # fraction is ~1.0 (well above any threshold) -> isolates debt trigger. ----
    del_span = int(N * del_frac)
    chunk = max(1, del_span // n_chunks)
    t = 0
    deletes = []
    while t < del_span:
        end = min(t + chunk, del_span)
        deletes.append((t, end)); t = end
    for (t1, t2) in deletes:
        tl.delete_range(t1, t2)
    # Flush so the tombstone lands in L0 and becomes visible to delete-debt.
    tl.flush()
    gc.collect()

    after_delete = _counters(tl)
    after_delete_rss = _rss_mb()

    # ---- Phase 3: RECLAIM-LAG measurement. After the delete+flush, drive
    # maintenance ONE step at a time and watch when pages_total actually drops
    # below the pre-delete baseline (deleted data no longer resident). We do NOT
    # call compact() explicitly -> this measures whether the configured trigger
    # fires on its own. Cap steps to avoid an infinite loop when debt=off. ----
    LAG_CAP = cfg.get("lag_cap", 200)
    reclaim_steps = None         # maint_steps until pages first drop materially
    compactions_at_reclaim = None
    cpu_ns = 0
    pages_trace = [after_delete["pages"]]
    # "Reclaimed" = pages dropped by >2% of the deleted fraction's page share,
    # i.e. physical pages fell meaningfully below the post-delete count.
    target_drop = max(1, int(after_delete["pages"] * del_frac * 0.5))
    step = 0
    while step < LAG_CAP:
        cpu0 = time.thread_time_ns()
        did = _drain_one(tl)
        cpu_ns += time.thread_time_ns() - cpu0
        step += 1
        cur = tl.stats()["storage"]["pages_total"]
        pages_trace.append(cur)
        if reclaim_steps is None and (after_delete["pages"] - cur) >= target_drop:
            reclaim_steps = step
            compactions_at_reclaim = tl.stats()["operational"]["compactions_total"]
        if not did:
            # No more maintenance work pending and trigger not (re)armed.
            break

    # Drain anything left so we measure a stable quiescent state.
    cpu0 = time.thread_time_ns()
    _drain(tl)
    cpu_ns += time.thread_time_ns() - cpu0
    gc.collect()

    final = _counters(tl)
    final_rss = _rss_mb()

    # ---- live records after deletes (for space_amp denominator) ----
    deleted = sum(min(t2, N) - max(t1, 0) for (t1, t2) in deletes if t1 < N)
    live = max(1, N - deleted)

    def space_amp(pages):
        return round((pages * page_bytes) / (live * REC_BYTES), 3)

    lat = _point_range_lat(tl, 0, N, queries, max(1, N // 1000))
    tl.close()
    gc.enable()

    return {
        "cfg": {k: cfg.get(k) for k in
                ("N", "seed", "del_frac", "n_chunks", "delete_debt_threshold",
                 "max_delta_segments", "flush_every", "window_size")},
        "module": timelog._timelog.__file__ if hasattr(timelog, "_timelog") else "?",
        "delete_debt_threshold": ddt,
        "live_records": live,
        # layout snapshots
        "base":   {"pages": base["pages"], "l0": base["l0"], "l1": base["l1"],
                   "tomb": base["tomb"], "comp": base["comp"],
                   "space_amp": space_amp(base["pages"]), "rss_mb": round(base_rss, 1) if base_rss else None},
        "after_delete": {"pages": after_delete["pages"], "l0": after_delete["l0"],
                         "l1": after_delete["l1"], "tomb": after_delete["tomb"],
                         "comp": after_delete["comp"],
                         "space_amp": space_amp(after_delete["pages"]),
                         "rss_mb": round(after_delete_rss, 1) if after_delete_rss else None},
        "final":  {"pages": final["pages"], "l0": final["l0"], "l1": final["l1"],
                   "tomb": final["tomb"], "comp": final["comp"],
                   "space_amp": space_amp(final["pages"]),
                   "rss_mb": round(final_rss, 1) if final_rss else None},
        # reclaim-lag
        "reclaim_steps": reclaim_steps,          # None => never reclaimed within LAG_CAP
        "reclaim_lag_steps": reclaim_steps if reclaim_steps is not None else f">{LAG_CAP}(cap)",
        "compactions_during_reclaim": (compactions_at_reclaim - after_delete["comp"])
                                       if compactions_at_reclaim is not None else 0,
        "pages_trace_head": pages_trace[:12],
        # reclaim effectiveness
        "pages_reclaimed": after_delete["pages"] - final["pages"],
        "space_amp_reduction": round(after_delete["pages"] and
                                     (1.0 - final["pages"] / after_delete["pages"]) or 0.0, 3),
        # cost
        "reclaim_cpu_ms": round(cpu_ns / 1e6, 2),
        "compactions_total_final": final["comp"],
        "tombstone_count_quiescent": final["tomb"],
        # read-amp at quiescence (tombstones residual in final)
        "read_amp": lat,
    }


if __name__ == "__main__":
    cfg = json.loads(sys.argv[1])
    print(json.dumps(run_cell(cfg)))
