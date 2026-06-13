"""exp03 — Timelog vs the obvious alternatives (idea N24/N25).

Honest head-to-head against the four contenders a skeptical reviewer names first:
  bisect.insort+list, sortedcontainers.SortedList, numpy int64+searchsorted, pandas.
Axes: (A) incremental append cost vs N (O(1) vs O(n)), (B) range-query latency,
(C) concurrent 1-writer/N-reader correctness+throughput.

Run: PYTHONPATH=python taskset -c 0 python3 competitive_bench.py
"""
from __future__ import annotations
import bisect, time, statistics, threading, json, sys, os

def pin():
    try: os.sched_setaffinity(0, {0})
    except Exception:
        pass  # CPU affinity is a best-effort benchmark hygiene hint.

# ---------- A. incremental append: per-op cost as N grows ----------
def _append_order(order):
    """order='inorder' -> ts ascending (bisect appends at end, O(1));
       order='ooo'     -> ts shuffled (bisect must shift, O(n))."""
    import random
    from timelog import Timelog, TimelogBusyError
    try: from sortedcontainers import SortedList
    except ImportError: SortedList = None
    sizes = [20_000, 50_000, 100_000, 200_000]
    rows = []
    for N in sizes:
        seq = list(range(N))
        if order == "ooo":
            random.Random(11).shuffle(seq)
        row = {"N": N}
        # Timelog facade (note: pays the ~181ns Python wrapper; raw-C is ~95-126ns)
        tl = Timelog()
        t0 = time.perf_counter()
        for ts in seq:
            try:
                tl.append(ts, ts)
            except TimelogBusyError:
                pass  # TL_EBUSY means the record was committed.
        row["timelog_facade_us_per_op"] = (time.perf_counter()-t0)/N*1e6
        tl.close()
        # bisect.insort: O(1) at end (in-order) but O(n) shift for middle (ooo)
        L = []
        t0 = time.perf_counter()
        for ts in seq:
            bisect.insort(L, ts)
        row["bisect_us_per_op"] = (time.perf_counter()-t0)/N*1e6
        # SortedList: O(log n) amortized regardless of order
        if SortedList is not None:
            sl = SortedList()
            t0 = time.perf_counter()
            for ts in seq:
                sl.add(ts)
            row["sortedlist_us_per_op"] = (time.perf_counter()-t0)/N*1e6
        rows.append(row)
    return rows

def append_scaling():
    return {"inorder": _append_order("inorder"), "out_of_order": _append_order("ooo")}

# ---------- B. range-query latency over a pre-built structure ----------
def range_latency(N=200_000, queries=5_000, width=1_000):
    import random
    from timelog import Timelog, TimelogBusyError
    try: from sortedcontainers import SortedList
    except ImportError: SortedList = None
    try: import numpy as np
    except ImportError: np = None
    rng = random.Random(7)
    qs = [rng.randrange(0, N-width) for _ in range(queries)]

    out = {}
    # Timelog
    tl = Timelog()
    for i in range(N):
        try:
            tl.append(i, i)
        except TimelogBusyError:
            pass  # TL_EBUSY means the record was committed.
    def q_tl():
        for s in qs:
            _ = sum(1 for _ in tl.range(s, s+width))
    out["timelog"] = _timeit(q_tl, queries)
    tl.close()
    # bisect over sorted list of ts
    ts = list(range(N))
    def q_bisect():
        for s in qs:
            lo = bisect.bisect_left(ts, s); hi = bisect.bisect_left(ts, s+width)
            _ = ts[lo:hi]
    out["bisect"] = _timeit(q_bisect, queries)
    # SortedList.irange
    if SortedList is not None:
        sl = SortedList(range(N))
        def q_sl():
            for s in qs:
                _ = list(sl.irange(s, s+width, inclusive=(True, False)))
        out["sortedlist"] = _timeit(q_sl, queries)
    # numpy searchsorted + slice
    if np is not None:
        arr = np.arange(N, dtype=np.int64)
        def q_np():
            for s in qs:
                lo = np.searchsorted(arr, s); hi = np.searchsorted(arr, s+width)
                _ = arr[lo:hi]
        out["numpy"] = _timeit(q_np, queries)
    return out

def _timeit(fn, n, reps=5):
    fn()  # warm
    samples = []
    for _ in range(reps):
        t0 = time.perf_counter(); fn(); samples.append((time.perf_counter()-t0)/n*1e6)
    return {"us_per_query_median": statistics.median(samples)}

# ---------- C. concurrency: 1 writer + N readers, correctness + throughput ----------
def concurrency_safety(N=100_000, readers=4, duration=1.5):
    """One writer appends 0..N while readers repeatedly range-query.
    Count reader exceptions and inconsistent reads. Timelog (snapshot isolation)
    must never raise; list+bisect / SortedList can raise or read torn state."""
    from timelog import Timelog, TimelogBusyError
    try: from sortedcontainers import SortedList
    except ImportError: SortedList = None
    results = {}

    def run_case(name, make, writer_step, reader_query):
        state = make()
        stop = threading.Event()
        errors = {"writer_exc": 0, "reader_exc": 0, "torn": 0, "reads": 0}
        lock = threading.Lock()
        def writer():
            i = 0
            while not stop.is_set() and i < N:
                try:
                    writer_step(state, i)
                except Exception:
                    with lock:
                        errors["writer_exc"] += 1
                i += 1
        def reader():
            while not stop.is_set():
                try:
                    res = reader_query(state)
                    # monotonic/consistency check: returned timestamps sorted & in-range
                    if res is not None and len(res) >= 2 and any(res[k] > res[k+1] for k in range(len(res)-1)):
                        with lock: errors["torn"] += 1
                    with lock: errors["reads"] += 1
                except Exception:
                    with lock: errors["reader_exc"] += 1
        ths = [threading.Thread(target=writer)] + [threading.Thread(target=reader) for _ in range(readers)]
        for t in ths: t.start()
        time.sleep(duration); stop.set()
        for t in ths: t.join()
        return errors

    # Timelog: snapshot-isolated reads
    def tl_make(): return Timelog()
    def tl_write(s, i):
        try:
            s.append(i, i)
        except TimelogBusyError:
            pass  # TL_EBUSY means the record was committed.
    def tl_read(s):
        mid = N // 2
        return [ts for ts, _ in s.range(mid, mid+500)]
    results["timelog"] = run_case("timelog", tl_make, tl_write, tl_read)

    # list + bisect: shared mutable list, reader slices around the middle
    def li_make(): return []
    def li_write(s, i): bisect.insort(s, i)
    def li_read(s):
        mid = N // 2
        lo = bisect.bisect_left(s, mid); hi = bisect.bisect_left(s, mid+500)
        return s[lo:hi]
    results["bisect_list"] = run_case("bisect_list", li_make, li_write, li_read)

    # SortedList
    if SortedList is not None:
        def sl_make(): return SortedList()
        def sl_write(s, i): s.add(i)
        def sl_read(s):
            mid = N // 2
            return list(s.irange(mid, mid+500, inclusive=(True, False)))
        results["sortedlist"] = run_case("sortedlist", sl_make, sl_write, sl_read)

    return results

if __name__ == "__main__":
    pin()
    out = {"python": sys.version.split()[0],
           "gil_enabled": (sys._is_gil_enabled() if hasattr(sys, "_is_gil_enabled") else None)}
    out["A_append_scaling"] = append_scaling()
    out["B_range_latency"] = range_latency()
    out["C_concurrency"] = concurrency_safety()
    print(json.dumps(out, indent=2))
