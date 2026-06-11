"""C4-wwd handle-leak gate.

Appends Python objects tracked by weakref across several time windows,
delete_range()s entire windows, drives compaction (maint_step), and asserts:

  1. Every dropped window's payload weakref becomes DEAD after compaction
     (no handle leak -- on_drop_handle fired for every physically-dropped
     record, even via the whole-window-drop fast path).
  2. Every surviving window's payload weakref stays ALIVE (no premature drop).

The build phase flushes + compacts per window so each window becomes its own
L1 segment. Then whole windows are deleted and an L0 churn record is added to
each window, forcing a compaction that pulls the fully-deleted L1 segments in
as selection inputs -- exactly the case the C4-wwd whole-window-drop path
short-circuits. The same script must pass on baseline and variant with an
identical outcome.

Run on the build whose _timelog.so is on PYTHONPATH.
"""
from __future__ import annotations
import gc
import sys
import weakref

import timelog


class Payload:
    __slots__ = ("v", "__weakref__")

    def __init__(self, v):
        self.v = v


def drain(tl, limit=1_000_000):
    n = 0
    while n < limit and tl.maint_step():
        n += 1
    if n >= limit and tl.maint_step():
        raise RuntimeError(f"maintenance drain exceeded cap ({limit})")
    return n


def main():
    window_size = 1000
    n_windows = 12
    per_window = 50
    drop_windows = set(range(0, n_windows, 2))  # delete every other window

    tl = timelog.Timelog(
        maintenance="disabled",
        busy_policy="flush",
        window_size=window_size,
        max_delta_segments=2,
    )

    # Build: one L1 segment per window (flush + compact incrementally).
    refs = []
    for w in range(n_windows):
        base = w * window_size
        wrefs = []
        for j in range(per_window):
            obj = Payload((w, j))
            wrefs.append(weakref.ref(obj))
            tl.append(base + j, obj)
            del obj
        refs.append(wrefs)
        tl.flush()
        drain(tl)

    s0 = tl.stats()
    l1_before = s0["storage"]["segments_l1"]
    l1in_before = s0["compaction_selection"]["select_l1_inputs"]

    # Delete entire windows.
    for w in drop_windows:
        base = w * window_size
        tl.delete_range(base, base + window_size)

    # Add an L0 churn record to EVERY window so compaction selection pulls in
    # every window's L1 segment (the deleted ones become whole-window drops).
    for w in range(n_windows):
        base = w * window_size
        obj = Payload(("extra", w))
        tl.append(base + 1, obj)
        del obj
        tl.flush()
        drain(tl)

    # A few extra passes to fully settle.
    for _ in range(4):
        tl.flush()
        drain(tl)

    gc.collect()

    s1 = tl.stats()
    l1in_after = s1["compaction_selection"]["select_l1_inputs"]

    # ---- Assertions -------------------------------------------------------
    leaked = []
    premature = []
    for w in range(n_windows):
        alive = [i for i, r in enumerate(refs[w]) if r() is not None]
        if w in drop_windows:
            if alive:
                leaked.append((w, len(alive)))
        else:
            if len(alive) != per_window:
                premature.append((w, per_window - len(alive)))

    ok = True
    if l1_before < n_windows:
        ok = False
        print(f"FAIL: setup did not build per-window L1 (l1_before={l1_before}, want {n_windows})")
    if l1in_after <= l1in_before:
        ok = False
        print(f"FAIL: compaction never pulled L1 inputs (before={l1in_before}, after={l1in_after})")
    if leaked:
        ok = False
        print(f"FAIL: handle LEAK in dropped windows (alive payloads): {leaked}")
    if premature:
        ok = False
        print(f"FAIL: PREMATURE drop in surviving windows (dead payloads): {premature}")

    dropped_alive = sum(1 for w in drop_windows for r in refs[w] if r() is not None)
    surviving_alive = sum(
        1 for w in range(n_windows) if w not in drop_windows for r in refs[w] if r() is not None
    )

    print(f"module={timelog._timelog.__file__}")
    print(f"l1_before={l1_before} l1in_before={l1in_before} l1in_after={l1in_after}")
    print(f"dropped_windows={sorted(drop_windows)} dropped_alive={dropped_alive}/{len(drop_windows) * per_window}")
    print(f"surviving_alive={surviving_alive}/{(n_windows - len(drop_windows)) * per_window}")
    print(f"compactions_total={s1['operational']['compactions_total']}")

    tl.close()

    if ok:
        print("PASS: no handle leak, no premature drop; whole-window-drop path exercised")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
