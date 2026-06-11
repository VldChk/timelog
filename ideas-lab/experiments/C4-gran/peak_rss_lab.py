"""peak_rss_lab — measure PEAK RSS during the compaction drain for a sweep of
max_compaction_windows.

EXPID=C4-gran. Tests whether the EXISTING max_compaction_windows cap is enough
to behave like granular per-window compaction for a wide L0/OOO spread. The
current verdict is negative for wide-OOO RSS: the cap splits the drain into
smaller passes, but still repeatedly pulls overlapping L1 windows and does not
meaningfully bound the transient. We sample /proc/self/statm in a background
thread WHILE maint_step() runs the drain loop, so quiesced-RSS sampling does not
hide the old+new copy spike.

Workload: wide-OOO bulk. ~1-2M records spread across MANY windows with a high
OOO rate, all ingested in maintenance='disabled' (compaction only requested),
then drained. With cap=0 the drain merges the whole spread at once; with a small
cap it should converge to equivalent query results in more, smaller passes. The
final layout may differ because bounded drains can leave some L0 work resident.

Per cap we report:
  peak_rss_mb        : RSS high-water observed by the sampler during the drain
  rss_delta_mb       : peak_rss - rss_just_before_drain (the transient spike)
  compactions_total  : number of compaction passes (more = more granular)
  maint_steps        : maint_step() iterations consumed by the drain
  layout             : final segments_l0/l1, pages_total, tombstone_count
  query_fingerprint  : checksum over a fixed set of range queries (correctness)

Usage: python3 peak_rss_lab.py            # full sweep, default workload
       python3 peak_rss_lab.py '<json>'   # override cfg
"""
from __future__ import annotations
import os, sys, gc, json, time, threading, random, hashlib


def _rss_kb():
    with open("/proc/self/statm") as f:
        resident_pages = int(f.read().split()[1])
    return resident_pages * os.sysconf("SC_PAGE_SIZE") // 1024


class RSSPeakSampler:
    """Background thread sampling /proc/self/statm; tracks high-water mark."""
    def __init__(self, interval_s=0.0005):
        self.interval = interval_s
        self.peak_kb = 0
        self._stop = threading.Event()
        self._t = None

    def _run(self):
        while not self._stop.is_set():
            r = _rss_kb()
            if r > self.peak_kb:
                self.peak_kb = r
            time.sleep(self.interval)

    def start(self):
        self.peak_kb = _rss_kb()
        self._stop.clear()
        self._t = threading.Thread(target=self._run, daemon=True)
        self._t.start()

    def stop(self):
        self._stop.set()
        self._t.join()
        r = _rss_kb()
        if r > self.peak_kb:
            self.peak_kb = r
        return self.peak_kb


def gen_wide_ooo(N, seed, n_windows, ooo_rate, window_ms=3_600_000):
    """Spread N records across n_windows windows. Each record lands in a random
    window (wide spread). Within the stream, ooo_rate fraction arrive 'late'
    (timestamp below the running max) to exercise the OOO mini-LSM."""
    rng = random.Random(seed)
    span = n_windows * window_ms
    events = []
    cur_max = 0
    for i in range(N):
        base = rng.randrange(0, span)
        if rng.random() < ooo_rate and cur_max > window_ms:
            # late arrival: pull below current max
            ts = max(0, cur_max - rng.randrange(1, span // 2 + 1))
        else:
            ts = base
            if ts > cur_max:
                cur_max = ts
        events.append((ts, i))
    return events


def _drain_with_peak(tl, sampler, limit=5_000_000):
    """Run the maint_step drain loop with the RSS sampler active."""
    sampler.start()
    n = 0
    while n < limit and tl.maint_step():
        n += 1
    peak = sampler.stop()
    if n >= limit and tl.maint_step():
        raise RuntimeError(f"maintenance drain exceeded cap ({limit})")
    return n, peak


def _drain(tl, limit=5_000_000):
    n = 0
    while n < limit and tl.maint_step():
        n += 1
    if n >= limit and tl.maint_step():
        raise RuntimeError(f"maintenance drain exceeded cap ({limit})")
    return n


def _query_fingerprint(tl, lo, hi, n_queries=400, seed=0xC4):
    """Deterministic checksum over a fixed set of range queries: count of
    records plus ordered and order-insensitive record hashes. Duplicate
    timestamp tie order is unspecified by the core API, so the multiset hash is
    the semantic equality check across caps."""
    rng = random.Random(seed)
    h = hashlib.blake2b(digest_size=16)
    mh = hashlib.blake2b(digest_size=16)
    total = 0
    w = max(1, (hi - lo) // 500)
    for _ in range(n_queries):
        q = rng.randrange(lo, hi)
        cnt = 0
        sum1 = 0
        sum2 = 0
        for ts, obj in tl.range(q, q + w):
            cnt += 1
            ts_i = int(ts)
            obj_i = int(obj)
            ts_bytes = ts_i.to_bytes(8, "little", signed=True)
            obj_bytes = obj_i.to_bytes(8, "little", signed=False)
            h.update(ts_bytes)
            h.update(obj_bytes)
            item = int.from_bytes(
                hashlib.blake2b(ts_bytes + obj_bytes, digest_size=8).digest(),
                "little",
            )
            sum1 = (sum1 + item) & ((1 << 64) - 1)
            sum2 = (sum2 + ((item * item) & ((1 << 64) - 1))) & ((1 << 64) - 1)
        total += cnt
        h.update(cnt.to_bytes(8, "little", signed=False))
        mh.update(sum1.to_bytes(8, "little", signed=False))
        mh.update(sum2.to_bytes(8, "little", signed=False))
        mh.update(cnt.to_bytes(8, "little", signed=False))
    total_bytes = total.to_bytes(8, "little", signed=False)
    h.update(total_bytes)
    mh.update(total_bytes)
    return total, h.hexdigest(), mh.hexdigest()


def _layout(tl):
    s = tl.stats()
    return {
        "segments_l0": s["storage"]["segments_l0"],
        "segments_l1": s["storage"]["segments_l1"],
        "pages_total": s["storage"]["pages_total"],
        "tombstone_count": s["storage"]["tombstone_count"],
        "records_estimate": s["storage"]["records_estimate"],
        "compactions_total": s["operational"]["compactions_total"],
        "select_l0_inputs": s["compaction_selection"]["select_l0_inputs"],
        "select_l1_inputs": s["compaction_selection"]["select_l1_inputs"],
    }


def run_cell(cap, cfg):
    import timelog
    from timelog import TimelogBusyError
    N = cfg["N"]
    seed = cfg.get("seed", 1)
    n_windows = cfg.get("n_windows", 200)
    ooo_rate = cfg.get("ooo_rate", 0.30)
    flush_every = cfg.get("flush_every", 25_000)
    page_bytes = cfg.get("page_bytes", 64 * 1024)

    # Two-wave workload. Wave 1 (seed) builds a wide L1 grid across n_windows.
    # Wave 2 is the wide-OOO bulk batch whose drain we MEASURE: it overlaps
    # every L1 window, so a cap=0 drain pulls ALL of L1 into one Full-Merge
    # (the transient old+new RAM spike). A small cap splits that into several
    # per-window passes -> bounded peak.
    wave1_n = cfg.get("wave1_n", N // 2)
    wave2_n = N - wave1_n
    events1 = gen_wide_ooo(wave1_n, seed, n_windows, ooo_rate)
    events2 = gen_wide_ooo(wave2_n, seed + 1, n_windows, ooo_rate)

    tl_kwargs = dict(cfg.get("tl_kwargs", {}))
    tl_kwargs.setdefault("maintenance", "disabled")
    tl_kwargs.setdefault("busy_policy", "flush")
    tl_kwargs.setdefault("target_page_bytes", page_bytes)
    if cap > 0:
        tl_kwargs["max_compaction_windows"] = cap

    gc.disable()
    tl = timelog.Timelog(**tl_kwargs)

    def _ingest(evs):
        for idx, (ts, pid) in enumerate(evs):
            try:
                tl.append(ts, pid)
            except TimelogBusyError:
                pass  # TL_EBUSY means the record was committed.
            if (idx + 1) % flush_every == 0:
                tl.flush()
        tl.flush()

    # ----- wave 1: build the L1 grid (drain fully; this is the baseline state) -----
    _ingest(events1)
    tl.compact()
    _drain(tl)
    base_l1 = tl.stats()["storage"]["segments_l1"]

    # ----- wave 2: wide-OOO bulk batch overlapping every L1 window -----
    _ingest(events2)

    gc.collect()
    rss_before_kb = _rss_kb()

    # ----- request compaction, then drain WITH peak sampling -----
    tl.compact()
    sampler = RSSPeakSampler(interval_s=cfg.get("sample_interval_s", 0.0005))
    cpu0 = time.thread_time_ns()
    steps, peak_kb = _drain_with_peak(tl, sampler)
    drain_cpu_ms = (time.thread_time_ns() - cpu0) / 1e6

    gc.collect()
    rss_after_kb = _rss_kb()
    layout = _layout(tl)

    # ----- correctness fingerprint over the final state -----
    lo, hi = 0, n_windows * 3_600_000
    qtotal, qhash, qmultihash = _query_fingerprint(tl, lo, hi, cfg.get("queries", 400))

    tl.close()
    gc.enable()

    return {
        "cap": cap,
        "N": N,
        "base_l1_windows": base_l1,
        "rss_before_drain_mb": round(rss_before_kb / 1024, 1),
        "peak_rss_mb": round(peak_kb / 1024, 1),
        "rss_after_drain_mb": round(rss_after_kb / 1024, 1),
        "rss_spike_mb": round((peak_kb - rss_before_kb) / 1024, 1),
        "maint_steps": steps,
        "drain_cpu_ms": round(drain_cpu_ms, 1),
        "layout": layout,
        "query_total_records": qtotal,
        "query_hash": qhash,
        "query_multiset_hash": qmultihash,
    }


if __name__ == "__main__":
    default_cfg = {
        "N": 1_500_000,
        "seed": 7,
        "n_windows": 300,
        "ooo_rate": 0.30,
        "flush_every": 25_000,
        "queries": 400,
    }
    cfg = default_cfg
    if len(sys.argv) > 1:
        cfg = {**default_cfg, **json.loads(sys.argv[1])}
    cap = cfg.get("cap", 0)
    print(json.dumps(run_cell(cap, cfg)))
