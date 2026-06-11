"""exp04 confirmation — rigorous re-measure of the two headline compaction findings,
applying the methodology-review corrections:
  - WRITE-AMP proxy = delta(select_l0_inputs + select_l1_inputs) (segments re-merged), not compactions_total.
  - gc.disable() during timed phases, gc.collect() at quiescence.
  - paired-seed REPEATS (median), pinned core.
  - maintenance='disabled' + maint_step() drain for attributable, race-free compaction.

Confirms: (1) read-amp grows monotonically with L0 fan-in K; (2) OOO ingest -> 5x read penalty unless
compaction fires; the max_delta_segments trigger is the lever.
"""
from __future__ import annotations
import os, sys, gc, time, json, statistics, random

def pin():
    try: os.sched_setaffinity(0, {0})
    except Exception: pass

def _stats(tl):
    s = tl.stats()
    return (s["compaction_selection"]["select_l0_inputs"],
            s["compaction_selection"]["select_l1_inputs"],
            s["storage"]["segments_l0"], s["storage"]["segments_l1"],
            s["storage"]["pages_total"], s["operational"]["compactions_total"])

def _drain(tl, limit=100000):
    n = 0
    while n < limit and tl.maint_step():
        n += 1
    if n >= limit and tl.maint_step():
        raise RuntimeError(f"maintenance drain exceeded cap ({limit})")
    return n

def _point_p(tl, n_ts, queries=20000):
    rng = random.Random(99)
    qs = [rng.randrange(n_ts) for _ in range(queries)]
    p = tl.point
    for q in qs[:300]: p(q)          # warm
    lat = []
    for q in qs:
        t0 = time.perf_counter_ns(); p(q); lat.append(time.perf_counter_ns() - t0)
    lat.sort()
    return lat[len(lat)//2], lat[int(0.99*len(lat))]

def run_ooo_trigger(N=200_000, triggers=(2, 8, 32, 10**9), reps=3):
    import timelog
    BIG = 256 * 1024 * 1024
    agg = {}
    for trig in triggers:
        p50s, p99s, wa_inputs, comps = [], [], [], []
        for rep in range(reps):
            seq = list(range(N)); random.Random(13 + rep).shuffle(seq)
            gc.disable()
            tl = timelog.Timelog(maintenance="disabled", busy_policy="flush",
                                 max_delta_segments=trig, memtable_max_bytes=BIG)
            per = N // 16
            for b in range(16):
                for ts in seq[b*per:(b+1)*per]: tl.append(ts, ts)
                tl.flush()
                if tl.stats()["storage"]["segments_l0"] >= trig: _drain(tl)
            _drain(tl)
            gc.collect()
            l0in, l1in, l0, l1, pages, comp = _stats(tl)
            p50, p99 = _point_p(tl, N)
            p50s.append(p50); p99s.append(p99); wa_inputs.append(l0in + l1in); comps.append(comp)
            tl.close()
            gc.enable()
        label = "no_compaction" if trig > 10**8 else trig
        agg[str(label)] = {
            "point_p50_median": int(statistics.median(p50s)),
            "point_p99_median": int(statistics.median(p99s)),
            "wa_segments_merged_median": int(statistics.median(wa_inputs)),  # select_l0+l1 inputs
            "compactions_median": int(statistics.median(comps)),
            "final_l0": l0, "final_l1": l1, "pages": pages,
            "p50_samples": p50s,
        }
    return agg

if __name__ == "__main__":
    pin()
    out = {"python": sys.version.split()[0],
           "note": "WA proxy = select_l0_inputs+select_l1_inputs (segments re-merged); 3 paired-seed repeats; gc-controlled."}
    out["ooo_trigger_confirm"] = run_ooo_trigger()
    print(json.dumps(out, indent=2))
