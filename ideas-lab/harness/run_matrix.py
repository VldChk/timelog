"""run_matrix — drive compaction_lab.py as a SUBPROCESS per (build, workload, knob, seed) cell.

Subprocess-per-cell gives build-isolation (PYTHONPATH chooses the .so) AND process-isolation (no allocator
fragmentation / handle-table carryover between cells). Aggregates fixed-seed repeats -> median; a cell fails
closed if any seed run fails.

Usage: python run_matrix.py <pythonpath_to_build> [out.json]
"""
from __future__ import annotations
import os, sys, json, subprocess, statistics

HARNESS = os.path.join(os.path.dirname(__file__), "compaction_lab.py")
SEEDS = [1, 2, 3]

def run_cell(pythonpath, cfg):
    env = dict(os.environ, PYTHONPATH=pythonpath)
    out = subprocess.run(["taskset", "-c", "0", sys.executable, HARNESS, json.dumps(cfg)],
                         env=env, capture_output=True, text=True)
    if out.returncode != 0:
        return {"error": out.stderr.strip()[-300:]}
    return json.loads(out.stdout)

def matrix(pythonpath):
    workloads = ["steady", "ooo", "delete_storm"]
    triggers = [2, 4, 8, 16, 32]
    N = 400_000
    rows = []
    for wl in workloads:
        for trig in triggers:
            cells = []
            for sd in SEEDS:
                cfg = {"workload": wl, "N": N, "seed": sd, "flush_every": 8000, "queries": 6000,
                       "tl_kwargs": {"max_delta_segments": trig}}
                cells.append(run_cell(pythonpath, cfg))
            good = [c for c in cells if "error" not in c]
            bad = [c for c in cells if "error" in c]
            if bad:
                rows.append({
                    "workload": wl,
                    "trigger": trig,
                    "error": "one or more seed runs failed",
                    "failed_seeds": len(bad),
                    "expected_seeds": len(SEEDS),
                    "sample_error": bad[0].get("error"),
                    "cells": cells,
                })
                continue
            def med(path):
                vals = []
                for c in good:
                    o = c
                    for k in path: o = o.get(k) if isinstance(o, dict) else None
                    if isinstance(o, (int, float)): vals.append(o)
                return round(statistics.median(vals), 2) if vals else None
            rows.append({
                "workload": wl, "trigger": trig,
                "seeds": len(good),
                "WA": med(["write_amp"]), "SA": med(["space_amp"]),
                "compact_cpu_ms": med(["compact_cpu_ms"]), "rss_mb": med(["rss_mb"]),
                "comp": med(["layout", "comp"]), "l0": med(["layout", "l0"]), "l1": med(["layout", "l1"]),
                "point_p50": med(["read_amp", "point_p50"]), "point_p99": med(["read_amp", "point_p99"]),
                "range_p50": med(["read_amp", "range_p50"]), "range_p99": med(["read_amp", "range_p99"]),
            })
    return rows

if __name__ == "__main__":
    pp = sys.argv[1] if len(sys.argv) > 1 else "python"
    rows = matrix(pp)
    failed = [r for r in rows if "error" in r]
    out = {"pythonpath": pp, "expected_seeds": SEEDS, "rows": rows, "failed_cells": len(failed)}
    if len(sys.argv) > 2:
        with open(sys.argv[2], "w") as f: json.dump(out, f, indent=2)
    # pretty table
    print(f"{'workload':13s} {'trig':>4} {'WA':>7} {'SA':>6} {'cpu_ms':>7} {'rss':>6} {'comp':>4} {'l0':>3} {'l1':>3} {'pt50':>6} {'pt99':>6} {'rg50':>6} {'rg99':>6}")
    for r in rows:
        if "error" in r:
            print(f"{r['workload']:13s} {r['trigger']:>4}  ERROR {r['error'][:40]} {str(r.get('sample_error',''))[:60]}")
            continue
        print(f"{r['workload']:13s} {r['trigger']:>4} {r['WA']:>7} {r['SA']:>6} {r['compact_cpu_ms']:>7} {str(r['rss_mb']):>6} {r['comp']:>4} {r['l0']:>3} {r['l1']:>3} {r['point_p50']:>6} {r['point_p99']:>6} {r['range_p50']:>6} {r['range_p99']:>6}")
    if failed:
        raise SystemExit(1)
