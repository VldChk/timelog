"""exp04 — Compaction strategy measurement (theme T4).

Timelog implements ONE policy: leveled compaction with time-windowed L1 (each window -> one
non-overlapping L1 segment). The classic STCS<->LCS (tiering<->leveling) axis is the single knob
`max_delta_segments` (the L0 trigger). This harness measures the two faces of that tradeoff:

  Exp1 READ AMP   : query latency (point/range) vs L0 segment depth (more overlap = slower reads).
  Exp2 WRITE AMP  : compactions performed vs max_delta_segments, for a fixed ingest.
  Exp3 SPACE/DELETE: pages reclaimed by compaction; delete_debt-driven reclaim.

Methodology: maintenance='disabled' for a deterministic layout; maint_step() drives compaction
explicitly; pinned core; p50/p99 over many random queries. Exp1 uses dense in-order timestamps in
one coarse time window but disjoint per-segment ranges, so it measures clean L0-depth overhead rather
than the maximum-overlap OOO case. Exp4/5 provide the wide-overlap OOO signal.

Run: PYTHONPATH=python taskset -c 0 python3 compaction_bench.py
"""
from __future__ import annotations
import os, sys, time, json, statistics, random

def pin():
    try: os.sched_setaffinity(0, {0})
    except Exception: pass

def _seg(tl):
    s = tl.stats(); st = s["storage"]; op = s["operational"]
    return {"l0": st["segments_l0"], "l1": st["segments_l1"], "pages": st["pages_total"],
            "compactions": op["compactions_total"], "seals": op["seals_total"]}

def _drain_compaction(tl, limit=10000):
    n = 0
    while n < limit and tl.maint_step():
        n += 1
    if n >= limit and tl.maint_step():
        raise RuntimeError(f"maintenance drain exceeded cap ({limit})")
    return n

def _query_latency(tl, n_ts, queries=20000, width=50):
    """p50/p99 ns for point and narrow-range queries over random timestamps."""
    rng = random.Random(99)
    pts = [rng.randrange(n_ts) for _ in range(queries)]
    # point
    pt = []
    p = tl.point
    for q in pts:
        t0 = time.perf_counter_ns(); _ = p(q); pt.append(time.perf_counter_ns() - t0)
    # narrow range (materialize via iteration -> realistic read-amp signal)
    rg = []
    r = tl.range
    for q in pts:
        t0 = time.perf_counter_ns()
        c = 0
        for _ in r(q, q + width): c += 1
        rg.append(time.perf_counter_ns() - t0)
    pt.sort(); rg.sort()
    pct = lambda a, q: a[min(len(a) - 1, int(q * len(a)))]
    return {"point_p50": pct(pt, .50), "point_p99": pct(pt, .99),
            "range_p50": pct(rg, .50), "range_p99": pct(rg, .99)}

# ---------- Exp1: READ AMP vs L0 depth (CLEAN: large memtable so flush==exactly 1 L0) ----------
def exp1_read_amp(N=262_144, depths=(1, 2, 4, 8, 16, 32, 64, 128)):
    import timelog
    BIG_MEMTABLE = 256 * 1024 * 1024   # 256 MiB: prevents auto-seal mid-batch -> controlled depth
    rows = []
    for d in depths:
        tl = timelog.Timelog(maintenance="disabled", busy_policy="flush",
                             max_delta_segments=10**9, memtable_max_bytes=BIG_MEMTABLE)
        per = N // d
        for b in range(d):
            for i in range(b * per, (b + 1) * per):
                tl.append(i, i)          # dense, in-order ts -> one coarse window, disjoint ranges
            tl.flush()                    # -> EXACTLY one L0 segment (no auto-seal)
        seg = _seg(tl)
        lat = _query_latency(tl, N, queries=30000)
        rows.append({"target_depth": d, **seg, **lat})
        tl.close()
    # compacted-to-L1 baseline (leveled): build d=128 L0 then compact to 1 L1
    tl = timelog.Timelog(maintenance="disabled", busy_policy="flush",
                         max_delta_segments=2, memtable_max_bytes=BIG_MEMTABLE)
    per = N // 128
    for b in range(128):
        for i in range(b * per, (b + 1) * per): tl.append(i, i)
        tl.flush()
    _drain_compaction(tl)
    seg = _seg(tl); lat = _query_latency(tl, N, queries=30000)
    rows.append({"target_depth": "compacted_L1", **seg, **lat})
    tl.close()
    return rows

# ---------- Exp4: OOO workload — does out-of-order ingest worsen the layout/read-amp? ----------
def exp4_ooo(N=200_000):
    import timelog, random
    BIG = 256 * 1024 * 1024
    out = {}
    for label, order in [("in_order", False), ("out_of_order", True)]:
        seq = list(range(N))
        if order: random.Random(13).shuffle(seq)
        tl = timelog.Timelog(maintenance="disabled", busy_policy="flush",
                             max_delta_segments=10**9, memtable_max_bytes=BIG)
        # 16 flushes -> 16 L0 segments; OOO spreads each segment's ts range -> more overlap
        per = N // 16
        for b in range(16):
            for ts in seq[b*per:(b+1)*per]: tl.append(ts, ts)
            tl.flush()
        seg = _seg(tl); lat = _query_latency(tl, N, queries=20000)
        out[label] = {**seg, **lat}
        tl.close()
    return out

# ---------- Exp2: WRITE AMP vs max_delta_segments (trigger sweep) ----------
def exp2_write_amp(N=400_000, triggers=(2, 4, 8, 16, 32, 64)):
    import timelog
    from timelog import TimelogBusyError
    rows = []
    for trig in triggers:
        tl = timelog.Timelog(maintenance="disabled", busy_policy="flush",
                             max_delta_segments=trig)
        # ingest with periodic flush; whenever L0 hits the trigger, drive compaction
        # (this mimics what the background worker does, but deterministically)
        FLUSH_EVERY = 25_000
        compactions_driven = 0
        for i in range(N):
            try:
                tl.append(i, i)
            except TimelogBusyError:
                pass  # TL_EBUSY means the record was committed.
            if (i + 1) % FLUSH_EVERY == 0:
                tl.flush()
                if tl.stats()["storage"]["segments_l0"] >= trig:
                    compactions_driven += _drain_compaction(tl)
        tl.flush(); compactions_driven += _drain_compaction(tl)
        seg = _seg(tl)
        lat = _query_latency(tl, N, queries=10000)
        rows.append({"max_delta_segments": trig, "compactions_run": seg["compactions"],
                     "maint_steps": compactions_driven, **seg, **lat})
        tl.close()
    return rows

# ---------- Exp3: SPACE / delete reclaim ----------
def exp3_space_delete(N=200_000):
    import timelog
    out = {}
    # space: pages before vs after compaction (dense, overlapping L0)
    tl = timelog.Timelog(maintenance="disabled", busy_policy="flush", max_delta_segments=10_000)
    per = N // 8
    for b in range(8):
        for i in range(b * per, (b + 1) * per): tl.append(i, i)
        tl.flush()
    before = _seg(tl)
    _drain_compaction(tl)  # won't trigger (trigger huge) -> force via maint? trigger huge so no-op
    # force compaction by lowering not possible at runtime; instead measure on a low-trigger twin
    tl.close()
    tl = timelog.Timelog(maintenance="disabled", busy_policy="flush", max_delta_segments=2)
    for b in range(8):
        for i in range(b * per, (b + 1) * per): tl.append(i, i)
        tl.flush()
    _drain_compaction(tl)
    after = _seg(tl)
    out["space"] = {"l0_overlapping": before, "after_compaction_L1": after,
                    "pages_reclaimed_pct": round((before["pages"] - after["pages"]) / before["pages"] * 100, 1)}
    tl.close()
    return out

# ---------- Exp5: the actionable one — OOO ingest + trigger sweep (read-latency knob) ----------
def exp5_ooo_trigger(N=200_000, triggers=(2, 4, 8, 16, 32, 1_000_000_000)):
    """Out-of-order ingest under different max_delta_segments. Lower trigger compacts the
    overlapping L0 sooner -> faster reads; a huge trigger never compacts -> read-amp explodes.
    This is the concrete tuning lever the notes only hand-waved at."""
    import timelog, random
    BIG = 256 * 1024 * 1024
    seq = list(range(N)); random.Random(13).shuffle(seq)
    rows = []
    for trig in triggers:
        tl = timelog.Timelog(maintenance="disabled", busy_policy="flush",
                             max_delta_segments=trig, memtable_max_bytes=BIG)
        per = N // 16
        for b in range(16):
            for ts in seq[b*per:(b+1)*per]: tl.append(ts, ts)
            tl.flush()
            if tl.stats()["storage"]["segments_l0"] >= trig:
                _drain_compaction(tl)
        _drain_compaction(tl)
        seg = _seg(tl); lat = _query_latency(tl, N, queries=20000)
        label = "no_compaction" if trig > 1_000_000 else trig
        rows.append({"max_delta_segments": label, **seg, **lat})
        tl.close()
    return rows

if __name__ == "__main__":
    pin()
    out = {"python": sys.version.split()[0]}
    out["exp1_read_amp"] = exp1_read_amp()
    out["exp2_write_amp"] = exp2_write_amp()
    out["exp3_space_delete"] = exp3_space_delete()
    out["exp4_ooo"] = exp4_ooo()
    out["exp5_ooo_trigger"] = exp5_ooo_trigger()
    print(json.dumps(out, indent=2))
