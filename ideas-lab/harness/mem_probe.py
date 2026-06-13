#!/usr/bin/env python3
"""mem_probe — two-process RSS + tracemalloc memory probe for Timelog (EXP C7-mem).

WHAT IT DOES
------------
A *monitor* process forks a *worker* process. The worker runs a sustained Timelog
workload (millions of appends with periodic compaction, then a delete-storm phase)
under Python `tracemalloc`. The monitor samples the worker's resident set size (RSS)
from /proc/<pid>/statm at a fixed cadence and merges it with the worker's own
tracemalloc samples (passed back over a pipe) into a single CSV time-series.

After the run it fits slopes to the steady-state region to distinguish:
  * Python-level growth  -> tracemalloc slope > 0   (live Python objects accumulating)
  * Native fragmentation -> RSS slope > 0 while tracemalloc slope ~ 0
                            (C allocator holds pages the Python heap no longer needs)

ALLOCATOR A/B
-------------
`--ab` reruns the SAME worker (same workload + seed) under several allocator settings
by re-exec'ing this script as a fresh subprocess with a different environment:
  glibc        : stock glibc malloc (baseline)
  arena2       : glibc with MALLOC_ARENA_MAX=2 (fewer per-thread arenas -> less RSS)
  mimalloc     : mimalloc via LD_PRELOAD (if a usable libmimalloc.so is found)
  jemalloc     : jemalloc via LD_PRELOAD (if a usable libjemalloc.so is found)
It reports peak RSS and RSS-after-workload (a fragmentation proxy) for each.

USAGE
-----
  # single run, default allocator, write CSV:
  python3 mem_probe.py --n 3000000 --csv /tmp/mem.csv

  # allocator A/B (this is the headline experiment):
  python3 mem_probe.py --ab --n 3000000 --csv-dir /tmp/memab

The worker uses the build selected by PYTHONPATH (set PYTHONPATH=.../python for the
baseline staged module). The monitor re-exports the same PYTHONPATH to children.
"""
from __future__ import annotations
import argparse, csv, gc, json, os, subprocess, sys, time, traceback, tracemalloc

PAGE = os.sysconf("SC_PAGE_SIZE")
MB = 1024 * 1024


def drain_maintenance(tl, limit: int = 2_000_000) -> int:
    """Drive maintenance to quiescence and fail closed if the cap is reached."""
    steps = 0
    while steps < limit and tl.maint_step():
        steps += 1
    if steps >= limit and tl.maint_step():
        raise RuntimeError(f"maintenance drain exceeded cap ({limit})")
    return steps


# ----------------------------------------------------------------------------- RSS
def rss_bytes(pid: int) -> int:
    """Resident bytes of <pid> from /proc/<pid>/statm (field 2 = resident pages)."""
    with open(f"/proc/{pid}/statm") as f:
        return int(f.read().split()[1]) * PAGE


def slope_per_sec(ts, ys):
    """Least-squares slope (units of y per second). ts seconds, ys same length."""
    n = len(ts)
    if n < 3:
        return 0.0
    mt = sum(ts) / n
    my = sum(ys) / n
    num = sum((t - mt) * (y - my) for t, y in zip(ts, ys))
    den = sum((t - mt) ** 2 for t in ts)
    return num / den if den else 0.0


# ----------------------------------------------------------------------------- worker
def run_worker(n: int, seed: int, sample_pipe_fd: int, sample_period_s: float,
               flush_every: int, compact_trigger: int) -> None:
    """Sustained workload. Emits 'tracemalloc' samples on the pipe; monitor pairs them with RSS."""
    import random
    from timelog import Timelog, TimelogBusyError

    try:
        os.sched_setaffinity(0, {0})
    except Exception:
        pass  # CPU affinity is optional outside Linux benchmark hosts.

    pipe = os.fdopen(sample_pipe_fd, "w", buffering=1)

    def emit(phase: str):
        cur, peak = tracemalloc.get_traced_memory()
        # the worker reads its OWN rss too, so landmark-phase RSS is never lost to a
        # race with process exit (the monitor's /proc sampling can miss the last phase).
        try:
            self_rss = rss_bytes(os.getpid())
        except Exception:
            # The monitor still samples RSS; this worker-side landmark is best effort.
            self_rss = 0
        pipe.write(json.dumps({
            "t": time.monotonic(),
            "phase": phase,
            "tm_cur": cur,
            "tm_peak": peak,
            "self_rss": self_rss,
        }) + "\n")

    rng = random.Random(seed)
    gc.disable()  # match production hot-path; we still collect explicitly at boundaries
    tracemalloc.start()

    tl = Timelog(maintenance="disabled", busy_policy="flush",
                 target_page_bytes=64 * 1024)

    # ---- PHASE 1: ingest with periodic flush + compaction drain ----
    last_emit = 0.0
    cur_ts = 0
    for i in range(n):
        # ~12% out-of-order to exercise the OOO mini-LSM and OOO-run allocations
        if rng.random() < 0.12 and cur_ts > 2000:
            ts = cur_ts - rng.randint(1, 2000)
        else:
            cur_ts += rng.randint(1, 3)
            ts = cur_ts
        try:
            tl.append(ts, i)
        except TimelogBusyError:
            pass  # TL_EBUSY means the record was committed.

        if (i + 1) % flush_every == 0:
            tl.flush()
            if tl.stats()["storage"]["segments_l0"] >= compact_trigger:
                drain_maintenance(tl)
        now = time.monotonic()
        if now - last_emit >= sample_period_s:
            emit("ingest")
            last_emit = now

    tl.flush()
    drain_maintenance(tl)
    gc.collect()
    emit("ingest_done")

    # ---- PHASE 2: delete-storm (retention/TTL shape) then physical-delete via compaction ----
    span = max(2, cur_ts)
    chunk = max(1, span // 40)
    t = 0
    di = 0
    while t < int(span * 0.50):
        tl.delete_range(t, t + chunk)
        t += chunk
        di += 1
        if di % 4 == 0:
            # drive compaction so tombstones physically drop records (frees handle storage)
            tl.flush()
            drain_maintenance(tl)
            now = time.monotonic()
            if now - last_emit >= sample_period_s:
                emit("delete")
                last_emit = now
    tl.flush()
    drain_maintenance(tl)
    gc.collect()
    emit("delete_done")

    # ---- PHASE 3: settle / quiescence (watch for native pages NOT returned to OS) ----
    settle_until = time.monotonic() + 2.0
    while time.monotonic() < settle_until:
        time.sleep(0.05)
        now = time.monotonic()
        if now - last_emit >= sample_period_s:
            emit("settle")
            last_emit = now

    # try to coerce glibc to return free arenas to the OS so the fragmentation
    # number reflects what the *allocator* chooses to hold, not lazy un-trimmed pages.
    try:
        import ctypes
        ctypes.CDLL("libc.so.6").malloc_trim(0)
    except Exception:
        pass  # Non-glibc hosts or restricted runtimes may not expose malloc_trim.
    gc.collect()
    emit("trimmed")

    tl.close()
    del tl
    gc.collect()
    emit("closed")
    tracemalloc.stop()
    pipe.flush()
    pipe.close()


# ----------------------------------------------------------------------------- monitor
def run_monitored(args, csv_path: str) -> dict:
    """Fork worker, sample its RSS, merge with its tracemalloc samples, write CSV, compute slopes."""
    r_fd, w_fd = os.pipe()
    pid = os.fork()
    if pid == 0:
        # child = worker
        os.close(r_fd)
        try:
            run_worker(args.n, args.seed, w_fd, args.period, args.flush_every, args.trigger)
        except Exception:
            traceback.print_exc()
            os._exit(1)
        else:
            os._exit(0)

    # parent = monitor
    os.close(w_fd)
    pipe = os.fdopen(r_fd, "r")
    samples = []          # (t_rel, rss_bytes, phase, tm_cur, tm_peak)
    t0 = time.monotonic()
    last_worker = None    # most recent tracemalloc sample seen on the pipe
    landmark_self_rss = {}  # phase -> worker-reported own RSS bytes (race-proof landmarks)

    import select
    poller = select.poll()
    poller.register(pipe.fileno(), select.POLLIN)
    peak_rss = 0
    buf = ""
    worker_status = None

    def drain_pipe():
        nonlocal buf, last_worker
        for _ in poller.poll(0):
            chunk = os.read(pipe.fileno(), 65536).decode()
            if not chunk:
                return
            buf += chunk
            while "\n" in buf:
                line, buf = buf.split("\n", 1)
                if not line.strip():
                    continue
                try:
                    rec = json.loads(line)
                except Exception:
                    continue
                last_worker = rec
                ph = rec.get("phase")
                if ph and ph not in landmark_self_rss:
                    landmark_self_rss[ph] = rec.get("self_rss", 0)

    while True:
        # is the worker still alive?
        try:
            wpid, status = os.waitpid(pid, os.WNOHANG)
            dead = wpid == pid
            if dead:
                worker_status = status
        except ChildProcessError:
            dead = True

        drain_pipe()

        # sample RSS while the proc dir still exists
        try:
            rb = rss_bytes(pid)
            peak_rss = max(peak_rss, rb)
            tr = time.monotonic() - t0
            tw = last_worker or {}
            samples.append((tr, rb, tw.get("phase", "?"),
                            tw.get("tm_cur", 0), tw.get("tm_peak", 0)))
        except (FileNotFoundError, ProcessLookupError):
            # The worker can exit between waitpid polling and /proc sampling.
            pass

        if dead:
            break
        time.sleep(args.period)

    drain_pipe()  # final flush: catch trimmed/closed landmarks emitted just before exit
    pipe.close()

    if worker_status is not None and worker_status != 0:
        if os.WIFSIGNALED(worker_status):
            raise RuntimeError(
                f"mem_probe worker died from signal {os.WTERMSIG(worker_status)}"
            )
        if os.WIFEXITED(worker_status):
            raise RuntimeError(
                f"mem_probe worker exited with status {os.WEXITSTATUS(worker_status)}"
            )
        raise RuntimeError(f"mem_probe worker failed with wait status {worker_status}")

    # write CSV time-series
    os.makedirs(os.path.dirname(csv_path) or ".", exist_ok=True)
    with open(csv_path, "w", newline="") as f:
        wr = csv.writer(f)
        wr.writerow(["t_s", "rss_mb", "phase", "tracemalloc_cur_mb", "tracemalloc_peak_mb"])
        for tr, rb, ph, tmc, tmp in samples:
            wr.writerow([f"{tr:.3f}", f"{rb/MB:.2f}", ph, f"{tmc/MB:.3f}", f"{tmp/MB:.3f}"])

    # slope analysis over the steady ingest region (drop first 15% warmup)
    ing = [(t, rb, tmc) for (t, rb, ph, tmc, tmp) in samples if ph == "ingest"]
    rss_slope = tm_slope = 0.0
    if len(ing) >= 5:
        k = max(1, int(len(ing) * 0.15))
        ing = ing[k:]
        ts = [t for (t, _, _) in ing]
        rss_slope = slope_per_sec(ts, [rb / MB for (_, rb, _) in ing])     # MB/s
        tm_slope = slope_per_sec(ts, [tmc / MB for (_, _, tmc) in ing])    # MB/s

    # phase landmark RSS values: prefer the worker-reported self_rss (race-proof),
    # fall back to the monitor's first /proc sample tagged with that phase.
    def first_rss(phase):
        if phase in landmark_self_rss and landmark_self_rss[phase]:
            return landmark_self_rss[phase] / MB
        for (t, rb, ph, *_2) in samples:
            if ph == phase:
                return rb / MB
        return None

    final_rss = samples[-1][1] / MB if samples else None
    return {
        "csv": csv_path,
        "n_samples": len(samples),
        "peak_rss_mb": round(peak_rss / MB, 2),
        "final_rss_mb": round(final_rss, 2) if final_rss else None,
        "rss_at_ingest_done_mb": round(first_rss("ingest_done"), 2) if first_rss("ingest_done") else None,
        "rss_at_delete_done_mb": round(first_rss("delete_done"), 2) if first_rss("delete_done") else None,
        "rss_after_trim_mb": round(first_rss("trimmed"), 2) if first_rss("trimmed") else None,
        "rss_after_close_mb": round(first_rss("closed"), 2) if first_rss("closed") else None,
        "ingest_rss_slope_mb_per_s": round(rss_slope, 4),
        "ingest_tracemalloc_slope_mb_per_s": round(tm_slope, 4),
    }


# ----------------------------------------------------------------------------- A/B driver
def find_lib(names):
    """Find a preload library in system paths or explicit opt-in directories.

    Do not search the repository or /tmp implicitly: LD_PRELOAD executes native
    code before Python starts, so allocator experiments must not accidentally
    run an unaudited local ELF just because it is present in the checkout.
    """
    search = [
        "/usr/lib/x86_64-linux-gnu",
        "/usr/local/lib",
        "/usr/lib",
        "/lib/x86_64-linux-gnu",
        "/lib",
    ]
    extra = os.environ.get("TIMELOG_MEM_PROBE_PRELOAD_DIRS")
    if extra:
        search.extend(p for p in extra.split(os.pathsep) if p)
    for base in names:
        for d in search:
            p = os.path.join(d, base)
            if os.path.exists(p):
                return p
    return None


def discover_allocators():
    """Return list of (label, env_overrides, note)."""
    out = [("glibc", {}, "stock glibc malloc"),
           ("arena2", {"MALLOC_ARENA_MAX": "2"}, "glibc, MALLOC_ARENA_MAX=2")]
    mim = find_lib(["libmimalloc.so", "libmimalloc.so.2", "libmimalloc.so.2.1"])
    if mim:
        out.append(("mimalloc", {"LD_PRELOAD": mim}, f"mimalloc preload {mim}"))
    else:
        out.append(("mimalloc", None, "UNAVAILABLE: no libmimalloc.so found"))
    jem = find_lib(["libjemalloc.so", "libjemalloc.so.2"])
    if jem:
        out.append(("jemalloc", {"LD_PRELOAD": jem}, f"jemalloc preload {jem}"))
    else:
        out.append(("jemalloc", None, "UNAVAILABLE: no shared libjemalloc.so found"))
    return out


def run_ab(args):
    allocs = discover_allocators()
    results = []
    os.makedirs(args.csv_dir, exist_ok=True)
    for label, env_over, note in allocs:
        if env_over is None:
            print(f"[{label}] SKIP - {note}", file=sys.stderr)
            results.append({"alloc": label, "note": note, "skipped": True})
            continue
        csv_path = os.path.join(args.csv_dir, f"{label}.csv")
        env = dict(os.environ)
        env.update(env_over)
        # re-exec a single-run child so the allocator env is applied to a *fresh* process
        cmd = [sys.executable, os.path.abspath(__file__), "--single",
               "--n", str(args.n), "--seed", str(args.seed),
               "--period", str(args.period), "--flush-every", str(args.flush_every),
               "--trigger", str(args.trigger), "--csv", csv_path]
        print(f"[{label}] {note}  -> {csv_path}", file=sys.stderr)
        t0 = time.time()
        proc = subprocess.run(cmd, env=env, capture_output=True, text=True)
        dur = time.time() - t0
        if proc.returncode != 0:
            print(f"[{label}] FAILED rc={proc.returncode}\n{proc.stderr[-2000:]}", file=sys.stderr)
            results.append({"alloc": label, "note": note, "error": proc.stderr[-500:]})
            continue
        try:
            metrics = json.loads(proc.stdout.strip().splitlines()[-1])
        except Exception as e:
            print(f"[{label}] parse error: {e}\nSTDOUT:{proc.stdout[-1000:]}", file=sys.stderr)
            results.append({"alloc": label, "note": note, "error": f"parse: {e}"})
            continue
        metrics.update({"alloc": label, "note": note, "wall_s": round(dur, 1)})
        results.append(metrics)

    # summary table
    base = next((r for r in results if r.get("alloc") == "glibc" and "peak_rss_mb" in r), None)
    print("\n==================== ALLOCATOR A/B (EXP C7-mem) ====================")
    hdr = f"{'alloc':<10} {'peak_RSS':>9} {'ingest_done':>12} {'delete_done':>12} {'after_trim':>11} {'after_close':>12} {'wall_s':>7}"
    print(hdr)
    print("-" * len(hdr))
    for r in results:
        if r.get("skipped") or "peak_rss_mb" not in r:
            print(f"{r['alloc']:<10} {'-- ' + r.get('note',''):>0}")
            continue
        print(f"{r['alloc']:<10} {r['peak_rss_mb']:>9} {str(r.get('rss_at_ingest_done_mb')):>12} "
              f"{str(r.get('rss_at_delete_done_mb')):>12} {str(r.get('rss_after_trim_mb')):>11} "
              f"{str(r.get('rss_after_close_mb')):>12} {r.get('wall_s'):>7}")
    if base:
        print("\nDelta vs glibc (peak RSS / after-trim RSS):")
        for r in results:
            if r.get("alloc") == "glibc" or "peak_rss_mb" not in r:
                continue
            dpeak = r["peak_rss_mb"] - base["peak_rss_mb"]
            ppeak = 100 * dpeak / base["peak_rss_mb"]
            bt = base.get("rss_after_trim_mb") or 0
            rt = r.get("rss_after_trim_mb") or 0
            dtrim = rt - bt
            ptrim = (100 * dtrim / bt) if bt else 0.0
            print(f"  {r['alloc']:<10} peak {dpeak:+.2f} MB ({ppeak:+.1f}%)   "
                  f"after-trim {dtrim:+.2f} MB ({ptrim:+.1f}%)")
    print("====================================================================\n")

    summary = {"config": {"n": args.n, "seed": args.seed, "period": args.period,
                          "flush_every": args.flush_every, "trigger": args.trigger,
                          "python": sys.version.split()[0]},
               "results": results}
    with open(os.path.join(args.csv_dir, "summary.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print(json.dumps(summary))
    return summary


def ab_has_failures(summary: dict) -> bool:
    """True when a configured allocator run failed.

    Unavailable optional allocators are represented as skipped rows and do not
    invalidate the A/B run. A row with an error means the allocator was selected
    and executed but failed or produced unparsable output, so the comparison is
    not reproducible.
    """
    return any("error" in row for row in summary.get("results", []))


# ----------------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(description="Timelog two-process memory probe + allocator A/B")
    ap.add_argument("--n", type=int, default=3_000_000, help="appends in ingest phase")
    ap.add_argument("--seed", type=int, default=1234)
    ap.add_argument("--period", type=float, default=0.1, help="sampling period seconds")
    ap.add_argument("--flush-every", type=int, default=25_000)
    ap.add_argument("--trigger", type=int, default=8, help="L0 segs before compaction drain")
    ap.add_argument("--csv", default="/tmp/mem_probe.csv", help="single-run CSV path")
    ap.add_argument("--single", action="store_true", help="(internal) one monitored run, print JSON")
    ap.add_argument("--ab", action="store_true", help="allocator A/B across glibc/arena2/mimalloc/jemalloc")
    ap.add_argument("--csv-dir", default="/tmp/mem_probe_ab", help="A/B output dir")
    args = ap.parse_args()

    if args.ab:
        summary = run_ab(args)
        if ab_has_failures(summary):
            raise SystemExit(1)
    else:
        # default + --single both do exactly one monitored run
        metrics = run_monitored(args, args.csv)
        print(json.dumps(metrics))


if __name__ == "__main__":
    main()
