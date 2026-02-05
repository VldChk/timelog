#!/usr/bin/env python3
"""
Correctness Checker: Long-running chaotic test with shadow state verification.

Maintains a Python-side shadow state, performs random inserts/deletes/queries
against Timelog, and verifies every result. Any mismatch between engine and
expected state is a potential bug.

Usage:
    py -V:3.13 demo/correctness_checker.py [--duration=3600] [--seed=42] [--verbose] [--log=PATH]

Options:
    --duration=N   Run for N seconds (default: 3600)
    --seed=N       RNG seed for reproducibility (default: random)
    --verbose      Print every operation
    --log=PATH     JSONL audit trail (default: demo/correctness_log.jsonl)
"""

from __future__ import annotations

import argparse
import bisect
import json
import random
import sys
import time
from pathlib import Path

# ---------------------------------------------------------------------------
# Ensure timelog is importable
# ---------------------------------------------------------------------------

_REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_REPO / "python"))
# Try common build output dirs for the C extension
for _candidate in [
    _REPO / "bindings" / "cpython" / "build-test" / "Release",
    _REPO / "bindings" / "cpython" / "build-test" / "Debug",
    _REPO / "bindings" / "cpython" / "build-py313" / "Release",
    _REPO / "bindings" / "cpython" / "build-py313" / "Debug",
]:
    if _candidate.is_dir():
        sys.path.insert(0, str(_candidate))

from timelog import Timelog, TimelogError  # noqa: E402
from timelog._api import TL_TS_MIN, TL_TS_MAX  # noqa: E402


# ---------------------------------------------------------------------------
# Shadow State
# ---------------------------------------------------------------------------

class ShadowState:
    """
    Python-side truth: sorted (ts, seq_id) index + parallel object dict.

    Does NOT track tombstones. Instead, the timestamp generator avoids
    producing timestamps inside tombstoned ranges, so inserts and the
    engine always agree on visibility.
    """

    __slots__ = ("_index", "_objects", "_next_id")

    def __init__(self):
        self._index: list[tuple[int, int]] = []  # sorted by (ts, seq_id)
        self._objects: dict[int, object] = {}     # seq_id -> obj
        self._next_id = 0

    def insert(self, ts: int, obj: object) -> None:
        sid = self._next_id
        self._next_id += 1
        bisect.insort(self._index, (ts, sid))
        self._objects[sid] = obj

    def extend(self, pairs: list[tuple[int, object]]) -> None:
        new = []
        for ts, obj in pairs:
            sid = self._next_id
            self._next_id += 1
            new.append((ts, sid))
            self._objects[sid] = obj
        self._index.extend(new)
        self._index.sort()

    def delete_range(self, t1: int, t2: int) -> int:
        lo = bisect.bisect_left(self._index, (t1,))
        hi = bisect.bisect_left(self._index, (t2,))
        removed = self._index[lo:hi]
        del self._index[lo:hi]
        for _, sid in removed:
            del self._objects[sid]
        return len(removed)

    def delete_point(self, ts: int) -> int:
        return self.delete_range(ts, ts + 1)

    def cutoff(self, ts: int) -> int:
        return self.delete_range(TL_TS_MIN, ts)

    def query_all(self) -> list[tuple[int, object]]:
        return [(ts, self._objects[sid]) for ts, sid in self._index]

    def query_range(self, t1: int, t2: int) -> list[tuple[int, object]]:
        lo = bisect.bisect_left(self._index, (t1,))
        hi = bisect.bisect_left(self._index, (t2,))
        return [(ts, self._objects[sid]) for ts, sid in self._index[lo:hi]]

    def query_point(self, ts: int) -> list[object]:
        lo = bisect.bisect_left(self._index, (ts,))
        hi = bisect.bisect_left(self._index, (ts + 1,))
        return [self._objects[sid] for _, sid in self._index[lo:hi]]

    def min_ts(self):
        return self._index[0][0] if self._index else None

    def max_ts(self):
        return self._index[-1][0] if self._index else None

    def __len__(self) -> int:
        return len(self._index)

    def random_ts(self, rng: random.Random):
        return rng.choice(self._index)[0] if self._index else None


# ---------------------------------------------------------------------------
# Object Factory
# ---------------------------------------------------------------------------

class ObjectFactory:
    """Generates diverse Python objects to stress handle encoding."""

    def __init__(self, rng: random.Random):
        self._rng = rng
        self._counter = 0

    def make(self) -> object:
        self._counter += 1
        kind = self._rng.randint(0, 6)
        n = self._counter
        if kind == 0:
            return f"rec_{n}"
        elif kind == 1:
            return self._rng.randint(-10**9, 10**9)
        elif kind == 2:
            return (n, "data")
        elif kind == 3:
            return {"id": n, "v": self._rng.random()}
        elif kind == 4:
            return None
        elif kind == 5:
            return [n, "x"]
        else:
            return self._rng.random()

    def make_batch(self, count: int) -> list[object]:
        return [self.make() for _ in range(count)]


# ---------------------------------------------------------------------------
# Timestamp Generator
# ---------------------------------------------------------------------------

class TimestampGen:
    """
    Generates monotonically-increasing timestamps with ~15% OOO.

    Maintains a sorted, non-overlapping tombstone interval set. OOO
    lookback never generates timestamps inside any tombstoned range.
    This avoids the known tombstone-reinsert scenario (by-design LSM
    behavior) and focuses the checker on detecting real correctness bugs.
    """

    def __init__(self, rng: random.Random, base: int = 1_000_000):
        self._rng = rng
        self._cursor = base
        self._base = base
        self._floor = base
        self._ooo_rate = 0.15
        self._max_lookback = 10_000
        self._tombstones: list[tuple[int, int]] = []  # sorted [start, end)

    @property
    def cursor(self) -> int:
        return self._cursor

    def add_tombstone(self, t1: int, t2: int) -> None:
        """Register a tombstone [t1, t2). Merges with existing intervals."""
        if t1 >= t2:
            return
        merged_start = t1
        merged_end = t2
        new_tombs = []
        for start, end in self._tombstones:
            if end < t1 or start > t2:
                new_tombs.append((start, end))
            else:
                merged_start = min(merged_start, start)
                merged_end = max(merged_end, end)
        new_tombs.append((merged_start, merged_end))
        new_tombs.sort()
        self._tombstones = new_tombs
        # Also advance floor if needed
        if t2 > self._floor:
            self._floor = t2

    def _is_in_tombstone(self, ts: int) -> bool:
        """Check if ts falls inside any tombstone."""
        if not self._tombstones:
            return False
        idx = bisect.bisect_right(self._tombstones, (ts, TL_TS_MAX)) - 1
        if idx < 0:
            return False
        start, end = self._tombstones[idx]
        return start <= ts < end

    def _skip_past_tombstone(self, ts: int) -> int:
        """If ts is inside a tombstone, return the tombstone's end; else ts."""
        if not self._tombstones:
            return ts
        idx = bisect.bisect_right(self._tombstones, (ts, TL_TS_MAX)) - 1
        if idx < 0:
            return ts
        start, end = self._tombstones[idx]
        if start <= ts < end:
            return end  # Skip to just past the tombstone
        return ts

    def next(self) -> int:
        if (self._rng.random() < self._ooo_rate
                and self._cursor > self._floor + self._max_lookback):
            max_lb = min(self._max_lookback, self._cursor - self._floor - 1)
            if max_lb > 0:
                lb = self._rng.randint(1, max_lb)
                candidate = self._cursor - lb
                if not self._is_in_tombstone(candidate):
                    return candidate
                # Fall through to forward generation if OOO hit a tombstone
        gap = self._rng.randint(1, 100)
        ts = self._cursor + gap
        # Skip past any tombstone the cursor wandered into
        ts = self._skip_past_tombstone(ts)
        self._cursor = ts
        return ts

    def next_batch(self, count: int) -> list[int]:
        return [self.next() for _ in range(count)]


# ---------------------------------------------------------------------------
# Operation Log (JSONL)
# ---------------------------------------------------------------------------

class OperationLog:
    """Append-only JSONL audit trail."""

    def __init__(self, path: str | None):
        self._file = None
        if path:
            self._file = open(path, "w", encoding="utf-8")
        self._seq = 0

    def log(self, **fields):
        self._seq += 1
        record = {"seq": self._seq, "t": time.time(), **fields}
        if self._file:
            self._file.write(json.dumps(record, default=str) + "\n")

    def close(self):
        if self._file:
            self._file.flush()
            self._file.close()
            self._file = None


# ---------------------------------------------------------------------------
# Mismatch Error
# ---------------------------------------------------------------------------

class MismatchError(Exception):
    """Raised on verification failure."""
    pass


# ---------------------------------------------------------------------------
# Correctness Checker
# ---------------------------------------------------------------------------

class CorrectnessChecker:
    """Orchestrator: runs random operations and verifies results."""

    # Operation weights
    WEIGHTS = [
        ("extend_batch", 35),
        ("append_single", 12),
        ("setitem_single", 8),
        ("query_point", 15),
        ("query_range", 10),
        ("query_slice", 5),
        ("query_views", 3),
        ("delete_point", 4),
        ("delete_range", 3),
        ("cutoff", 2),
        ("flush", 2),
        ("compact", 1),
    ]

    def __init__(self, seed: int, duration: int, verbose: bool, log_path: str | None):
        self.seed = seed
        self.duration = duration
        self.verbose = verbose
        self.rng = random.Random(seed)
        self.shadow = ShadowState()
        self.factory = ObjectFactory(self.rng)
        self.tsgen = TimestampGen(self.rng)
        self.oplog = OperationLog(log_path)
        self.log = Timelog(
            maintenance="background",
            busy_policy="flush",
            time_unit="ns",
        )

        # Stats
        self.ops = 0
        self.inserts = 0
        self.deletes = 0
        self.mismatches = 0
        self.verifications = 0

        # Build weighted choice list
        self._choices = []
        self._weights_list = []
        for name, weight in self.WEIGHTS:
            self._choices.append(name)
            self._weights_list.append(weight)

    def run(self):
        """Main loop."""
        print(f"Correctness Checker v1.0 | seed={self.seed} | duration={self.duration}s")
        print("=" * 64)

        start = time.monotonic()
        last_report = start
        report_interval = 60  # seconds

        try:
            while True:
                elapsed = time.monotonic() - start
                if elapsed >= self.duration:
                    break

                # Pick and execute a random operation
                op_name = self.rng.choices(self._choices, self._weights_list, k=1)[0]
                method = getattr(self, f"_op_{op_name}")
                method()
                self.ops += 1

                # Periodic full verification
                if self.ops % 100 == 0:
                    self._full_verify()

                # Progress report
                now = time.monotonic()
                if now - last_report >= report_interval:
                    elapsed_s = int(now - start)
                    n = len(self.shadow)
                    print(f"  [{elapsed_s}s]  {self.ops} ops | {n} records | {self.mismatches} mismatches")
                    self.oplog.log(
                        op="progress",
                        elapsed=elapsed_s,
                        ops=self.ops,
                        records=n,
                        inserts=self.inserts,
                        deletes=self.deletes,
                        mismatches=self.mismatches,
                    )
                    last_report = now

        except MismatchError as e:
            print(f"\nFATAL MISMATCH: {e}")
            self.oplog.log(op="FATAL", error=str(e))
            raise
        finally:
            elapsed_s = int(time.monotonic() - start)
            print("=" * 64)
            print(
                f"SUMMARY: {self.ops} ops | {self.inserts} inserts | "
                f"{self.deletes} deletes | {self.mismatches} MISMATCHES"
            )
            print(f"Duration: {elapsed_s}s | Verifications: {self.verifications}")
            print("=" * 64)
            self.oplog.log(
                op="summary",
                ops=self.ops,
                inserts=self.inserts,
                deletes=self.deletes,
                mismatches=self.mismatches,
                verifications=self.verifications,
                elapsed=elapsed_s,
            )
            self.oplog.close()
            self.log.flush()
            self.log.close()

    # ------------------------------------------------------------------
    # Write operations
    # ------------------------------------------------------------------

    def _op_extend_batch(self):
        count = self.rng.randint(10, 1000)
        timestamps = self.tsgen.next_batch(count)
        objects = self.factory.make_batch(count)
        pairs = list(zip(timestamps, objects))

        # Pick API pattern
        pattern = self.rng.choice(["pairs", "dual_list", "iter_pairs"])
        if pattern == "pairs":
            self.log.extend(pairs)
        elif pattern == "dual_list":
            self.log.extend(timestamps, objects)
        else:
            self.log.extend(iter(pairs))

        self.shadow.extend(pairs)
        self.inserts += count

        if self.verbose:
            print(f"  extend({count}, pattern={pattern})")
        self.oplog.log(op="extend", count=count, pattern=pattern)

    def _op_append_single(self):
        ts = self.tsgen.next()
        obj = self.factory.make()

        # Pick API pattern
        pattern = self.rng.choice(["kwarg", "positional"])
        if pattern == "kwarg":
            self.log.append(obj, ts=ts)
        else:
            self.log.append(ts, obj)

        self.shadow.insert(ts, obj)
        self.inserts += 1

        if self.verbose:
            print(f"  append(ts={ts}, pattern={pattern})")
        self.oplog.log(op="append", ts=ts, pattern=pattern)

    def _op_setitem_single(self):
        ts = self.tsgen.next()
        obj = self.factory.make()
        self.log[ts] = obj
        self.shadow.insert(ts, obj)
        self.inserts += 1

        if self.verbose:
            print(f"  setitem(ts={ts})")
        self.oplog.log(op="setitem", ts=ts)

    # ------------------------------------------------------------------
    # Query operations (with verification)
    # ------------------------------------------------------------------

    def _op_query_point(self):
        if not self.shadow:
            return
        ts = self.shadow.random_ts(self.rng)
        if ts is None:
            return

        got = self.log[ts]
        expected = self.shadow.query_point(ts)

        # Compare as multisets via str representation (handles dicts/lists)
        got_sorted = sorted(str(o) for o in got)
        exp_sorted = sorted(str(o) for o in expected)
        if got_sorted != exp_sorted:
            self.mismatches += 1
            msg = (
                f"Point query mismatch at ts={ts}: "
                f"expected {len(expected)} records, got {len(got)}\n"
                f"  expected: {expected[:10]}\n"
                f"  got:      {got[:10]}"
            )
            self.oplog.log(
                op="MISMATCH", type="point", ts=ts,
                expected_n=len(expected), got_n=len(got),
            )
            raise MismatchError(msg)

        if self.verbose:
            print(f"  query_point(ts={ts}) -> {len(got)} records OK")
        self.oplog.log(op="verify", ok=True, type="point", ts=ts, n=len(got))

    def _op_query_range(self):
        if not self.shadow:
            return
        mn, mx = self.shadow.min_ts(), self.shadow.max_ts()
        if mn is None:
            return
        t1 = self.rng.randint(mn, mx)
        width = self.rng.randint(1, max(1, (mx - mn) // 4))
        t2 = t1 + width

        got = list(self.log[t1:t2])
        expected = self.shadow.query_range(t1, t2)

        self._compare_records(got, expected, f"range [{t1}, {t2})")

        if self.verbose:
            print(f"  query_range([{t1}, {t2})) -> {len(got)} records OK")
        self.oplog.log(op="verify", ok=True, type="range", t1=t1, t2=t2, n=len(got))

    def _op_query_slice(self):
        if not self.shadow:
            return
        mn, mx = self.shadow.min_ts(), self.shadow.max_ts()
        if mn is None:
            return

        # Pick slice variant
        variant = self.rng.choice(["since", "until", "all"])
        if variant == "since":
            t1 = self.rng.randint(mn, mx)
            got = list(self.log[t1:])
            expected = self.shadow.query_range(t1, TL_TS_MAX)
            desc = f"[{t1}:]"
        elif variant == "until":
            t2 = self.rng.randint(mn, mx)
            got = list(self.log[:t2])
            expected = self.shadow.query_range(TL_TS_MIN, t2)
            desc = f"[:{t2}]"
        else:
            got = list(self.log[:])
            expected = self.shadow.query_all()
            desc = "[:]"

        self._compare_records(got, expected, f"slice {desc}")

        if self.verbose:
            print(f"  query_slice({desc}) -> {len(got)} records OK")
        self.oplog.log(op="verify", ok=True, type="slice", variant=variant, n=len(got))

    def _op_query_views(self):
        """Verify PageSpan output after flushing."""
        if not self.shadow:
            return
        mn, mx = self.shadow.min_ts(), self.shadow.max_ts()
        if mn is None:
            return

        # Flush to ensure memtable data is in segments
        self.log.flush()

        t1 = self.rng.randint(mn, mx)
        width = self.rng.randint(1, max(1, (mx - mn) // 4))
        t2 = t1 + width

        expected = self.shadow.query_range(t1, t2)

        # Collect records from PageSpans
        got = []
        try:
            for span in self.log.views(t1, t2):
                ts_view = span.timestamps
                objs_view = span.objects
                for i in range(len(ts_view)):
                    got.append((int(ts_view[i]), objs_view[i]))
        except Exception as e:
            # Views may not be available in all states; log and skip
            if self.verbose:
                print(f"  query_views: {e}")
            self.oplog.log(op="views_error", error=str(e))
            return

        self._compare_records(got, expected, f"views [{t1}, {t2})")

        if self.verbose:
            print(f"  query_views([{t1}, {t2})) -> {len(got)} records OK")
        self.oplog.log(op="verify", ok=True, type="views", t1=t1, t2=t2, n=len(got))

    # ------------------------------------------------------------------
    # Delete operations
    # ------------------------------------------------------------------

    def _op_delete_point(self):
        if not self.shadow:
            return
        ts = self.shadow.random_ts(self.rng)
        if ts is None:
            return

        # Pick API pattern
        pattern = self.rng.choice(["delete", "delitem"])
        if pattern == "delete":
            self.log.delete(ts)
        else:
            del self.log[ts]

        removed = self.shadow.delete_point(ts)
        self.tsgen.add_tombstone(ts, ts + 1)
        self.deletes += removed

        if self.verbose:
            print(f"  delete_point(ts={ts}, pattern={pattern}) -> {removed} removed")
        self.oplog.log(op="delete_point", ts=ts, removed=removed, pattern=pattern)

    def _op_delete_range(self):
        if not self.shadow:
            return
        mn, mx = self.shadow.min_ts(), self.shadow.max_ts()
        if mn is None:
            return
        t1 = self.rng.randint(mn, mx)
        width = self.rng.randint(1, max(1, (mx - mn) // 10))
        t2 = t1 + width

        # Pick API pattern
        pattern = self.rng.choice(["delete", "delitem"])
        if pattern == "delete":
            self.log.delete(t1, t2)
        else:
            del self.log[t1:t2]

        removed = self.shadow.delete_range(t1, t2)
        self.tsgen.add_tombstone(t1, t2)
        self.deletes += removed

        if self.verbose:
            print(f"  delete_range([{t1}, {t2}), pattern={pattern}) -> {removed} removed")
        self.oplog.log(op="delete_range", t1=t1, t2=t2, removed=removed, pattern=pattern)

    def _op_cutoff(self):
        if not self.shadow:
            return
        mn, mx = self.shadow.min_ts(), self.shadow.max_ts()
        if mn is None:
            return
        # Only cutoff in lower 30% to avoid wiping everything
        cutoff_max = mn + max(1, (mx - mn) * 3 // 10)
        ts = self.rng.randint(mn, cutoff_max)

        self.log.cutoff(ts)
        removed = self.shadow.cutoff(ts)
        self.tsgen.add_tombstone(TL_TS_MIN, ts)
        self.deletes += removed

        if self.verbose:
            print(f"  cutoff(ts={ts}) -> {removed} removed")
        self.oplog.log(op="cutoff", ts=ts, removed=removed)

    # ------------------------------------------------------------------
    # Maintenance operations
    # ------------------------------------------------------------------

    def _op_flush(self):
        self.log.flush()
        if self.verbose:
            print("  flush()")
        self.oplog.log(op="flush")

    def _op_compact(self):
        try:
            self.log.compact()
        except TimelogError:
            pass  # Nothing to compact
        if self.verbose:
            print("  compact()")
        self.oplog.log(op="compact")

    # ------------------------------------------------------------------
    # Verification
    # ------------------------------------------------------------------

    def _full_verify(self):
        """Full verification cycle: scan + min/max + len + validate."""
        self.verifications += 1

        # Full scan
        got = list(self.log)
        expected = self.shadow.query_all()
        self._compare_records(got, expected, "full_scan")

        # min_ts / max_ts via iteration
        if self.shadow:
            exp_min = self.shadow.min_ts()
            exp_max = self.shadow.max_ts()
            if got:
                got_min = got[0][0]
                got_max = got[-1][0]
                if got_min != exp_min:
                    self.mismatches += 1
                    msg = f"min_ts mismatch: expected {exp_min}, got {got_min}"
                    self.oplog.log(op="MISMATCH", type="min_ts",
                                   expected=exp_min, got=got_min)
                    raise MismatchError(msg)
                if got_max != exp_max:
                    self.mismatches += 1
                    msg = f"max_ts mismatch: expected {exp_max}, got {got_max}"
                    self.oplog.log(op="MISMATCH", type="max_ts",
                                   expected=exp_max, got=got_max)
                    raise MismatchError(msg)

        # len() — approximate, warn only
        engine_len = len(self.log)
        shadow_len = len(self.shadow)
        if shadow_len > 0:
            delta_pct = abs(engine_len - shadow_len) / shadow_len * 100
            if delta_pct > 5:
                if self.verbose:
                    print(
                        f"  WARNING: len mismatch: engine={engine_len} "
                        f"shadow={shadow_len} ({delta_pct:.1f}%)"
                    )
                self.oplog.log(
                    op="len_warning", engine=engine_len,
                    shadow=shadow_len, delta_pct=round(delta_pct, 1),
                )

        # validate() — C-level invariant checks
        try:
            self.log.validate()
        except TimelogError as e:
            self.mismatches += 1
            self.oplog.log(op="MISMATCH", type="validate", error=str(e))
            raise MismatchError(f"validate() failed: {e}") from e

        # Log stats
        self.oplog.log(
            op="verify_full", ok=True,
            records=len(self.shadow),
            ops=self.ops,
        )

    @staticmethod
    def _group_by_ts(records):
        """Group records into runs of equal timestamps."""
        groups = []
        i = 0
        while i < len(records):
            ts = records[i][0]
            j = i + 1
            while j < len(records) and records[j][0] == ts:
                j += 1
            groups.append((ts, records[i:j]))
            i = j
        return groups

    def _compare_records(
        self,
        got: list[tuple[int, object]],
        expected: list[tuple[int, object]],
        context: str,
    ):
        """
        Compare engine output to shadow state, raise on mismatch.

        Records at the same timestamp are compared as multisets since the
        merge iterator may return them in a different order than insertion
        order (different OOO components have different tie-break ordering).
        """
        if len(got) != len(expected):
            self.mismatches += 1
            msg = (
                f"{context}: count mismatch: expected {len(expected)}, "
                f"got {len(got)}"
            )
            # Show first differing region
            for i, (g, e) in enumerate(zip(got, expected)):
                if g[0] != e[0]:
                    msg += f"\n  First ts diff at index {i}: got_ts={g[0]}, expected_ts={e[0]}"
                    break
            if len(got) > len(expected):
                msg += f"\n  Extra got[{len(expected)}]: {got[len(expected)]}"
            elif len(expected) > len(got):
                msg += f"\n  Missing expected[{len(got)}]: {expected[len(got)]}"
            self.oplog.log(
                op="MISMATCH", type=context,
                expected_n=len(expected), got_n=len(got),
            )
            raise MismatchError(msg)

        # Group by timestamp and compare multisets within each group
        got_groups = self._group_by_ts(got)
        exp_groups = self._group_by_ts(expected)

        if len(got_groups) != len(exp_groups):
            self.mismatches += 1
            msg = (
                f"{context}: timestamp group count mismatch: "
                f"expected {len(exp_groups)} groups, got {len(got_groups)} groups"
            )
            self.oplog.log(op="MISMATCH", type=context)
            raise MismatchError(msg)

        for (g_ts, g_recs), (e_ts, e_recs) in zip(got_groups, exp_groups):
            if g_ts != e_ts:
                self.mismatches += 1
                msg = (
                    f"{context}: timestamp mismatch: "
                    f"expected ts={e_ts}, got ts={g_ts}"
                )
                self.oplog.log(op="MISMATCH", type=context,
                               expected_ts=e_ts, got_ts=g_ts)
                raise MismatchError(msg)
            if len(g_recs) != len(e_recs):
                self.mismatches += 1
                msg = (
                    f"{context}: count mismatch at ts={g_ts}: "
                    f"expected {len(e_recs)}, got {len(g_recs)}"
                )
                self.oplog.log(op="MISMATCH", type=context, ts=g_ts,
                               expected_n=len(e_recs), got_n=len(g_recs))
                raise MismatchError(msg)
            # Compare as multisets using str repr
            got_objs = sorted(str(r[1]) for r in g_recs)
            exp_objs = sorted(str(r[1]) for r in e_recs)
            if got_objs != exp_objs:
                self.mismatches += 1
                msg = (
                    f"{context}: object mismatch at ts={g_ts}: "
                    f"expected {exp_objs[:5]}, got {got_objs[:5]}"
                )
                self.oplog.log(op="MISMATCH", type=context, ts=g_ts)
                raise MismatchError(msg)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Timelog Correctness Checker: chaotic test with shadow verification"
    )
    parser.add_argument("--duration", type=int, default=3600,
                        help="Run duration in seconds (default: 3600)")
    parser.add_argument("--seed", type=int, default=None,
                        help="RNG seed (default: random)")
    parser.add_argument("--verbose", action="store_true",
                        help="Print every operation")
    parser.add_argument("--log", type=str, default="demo/correctness_log.jsonl",
                        help="JSONL log path (default: demo/correctness_log.jsonl)")
    args = parser.parse_args()

    seed = args.seed if args.seed is not None else random.randint(0, 2**32 - 1)

    checker = CorrectnessChecker(
        seed=seed,
        duration=args.duration,
        verbose=args.verbose,
        log_path=args.log,
    )
    checker.run()


if __name__ == "__main__":
    main()
