"""Regression tests for the v1.3 usability-lab fixes.

Each test pins a behavior that the six-persona usability lab flagged:
silent exit for the no-context-manager lifecycle, maintenance triggers
that work without worker-driven flushes, observable backpressure,
container-protocol dunders, teaching errors, and stats enrichment.
"""
import array
import datetime
import operator
import os
from pathlib import Path
import subprocess
import sys
import time
import warnings

import pytest

from timelog import Timelog, TimelogError

REPO_ROOT = Path(__file__).resolve().parents[2]


def _subprocess_env():
    """Minimal child env, plus sanitizer/runtime passthrough.

    Sanitizer legs stage an instrumented extension and run pytest with
    LD_PRELOAD; the child must inherit that (and GIL/TSan knobs) or it dies
    loading the staged module before the behavior under test runs.
    """
    env = os.environ.copy()
    env.setdefault("PATH", os.defpath)
    for key in ("LD_PRELOAD", "ASAN_OPTIONS", "TSAN_OPTIONS",
                "LSAN_OPTIONS", "PYTHON_GIL"):
        if key in os.environ:
            env[key] = os.environ[key]
    return env


class TestCleanExitSilence:
    def test_abandoned_log_exits_silently(self):
        # The dominant real-world pattern: module-global log, records in,
        # no close(), interpreter exits. stderr must be EMPTY.
        code = "from timelog import Timelog; log = Timelog(); log[1] = 'x'"
        proc = subprocess.run(
            [sys.executable, "-c", code], capture_output=True, text=True,
            env=_subprocess_env(), timeout=60,
            cwd=REPO_ROOT)
        assert proc.returncode == 0
        assert proc.stderr.strip() == "", f"clean exit printed: {proc.stderr!r}"

    def test_exported_buffer_at_exit_does_not_crash(self):
        # A PageSpan buffer export pinned at process exit must not abort during
        # late interpreter teardown. Runtime pin leaks still warn outside
        # finalization; exit itself stays silent for the no-context-manager
        # lifecycle.
        code = ("from timelog import Timelog\n"
                "log = Timelog(maintenance='disabled')\n"
                "log.extend([(i, i) for i in range(100)])\n"
                "log.flush()\n"
                "spans = log.views()\n"
                "span = next(iter(spans))\n"
                "mv = memoryview(span)\n")
        proc = subprocess.run(
            [sys.executable, "-c", code], capture_output=True, text=True,
            env=_subprocess_env(), timeout=60,
            cwd=REPO_ROOT)
        assert proc.returncode == 0


class TestMaintenanceTriggers:
    def test_explicit_flush_triggers_compaction(self):
        # Previously: 20 user flushes -> L0=20 forever (compaction trigger
        # was only evaluated when the WORKER had flush work).
        log = Timelog(maintenance="background")
        for k in range(20):
            log.extend([(k * 1000 + i, i) for i in range(500)])
            log.flush()
        deadline = time.monotonic() + 5.0
        compacted = False
        while time.monotonic() < deadline:
            if log.stats()["operational"]["compactions_total"] > 0:
                compacted = True
                break
            time.sleep(0.05)
        assert compacted, "user-driven flushes never triggered compaction"
        assert log.stats()["storage"]["segments_l0"] < 20
        log.close()

    def test_idle_delete_debt_compaction(self):
        # Tombstone flushed into L0, then NO further writes: the idle worker
        # must fire debt-triggered compaction and physically reclaim.
        log = Timelog(maintenance="background", delete_debt_threshold=0.2)
        log.extend([(i, i) for i in range(10_000)])
        log.cutoff(9_000)      # tombstone enters the memtable pre-flush
        log.flush()            # records + tombstone land in L0 together
        deadline = time.monotonic() + 5.0
        fired = False
        while time.monotonic() < deadline:
            s = log.stats()
            if (s["operational"]["compactions_total"] > 0
                    or s["storage"]["segments_l1"] > 0):
                fired = True
                break
            time.sleep(0.05)
        assert fired, "idle delete-debt never triggered compaction"
        assert len(log) == 1_000
        log.close()


class TestBackpressureObservability:
    def test_busy_events_counts_under_silent_policy(self):
        log = Timelog(maintenance="disabled", busy_policy="silent",
                      memtable_max_bytes=4096, sealed_max_runs=1,
                      sealed_wait_ms=0)
        for b in range(3):
            log.bulk_append(array.array("q", range(b * 1000, b * 1000 + 1000)),
                            list(range(1000)))
        assert log.busy_events > 0
        assert log.stats()["operational"]["busy_events"] == log.busy_events
        log.close()

    def test_busy_events_zero_when_quiet(self):
        log = Timelog(maintenance="disabled")
        log.extend([(i, i) for i in range(100)])
        assert log.busy_events == 0
        log.close()


class TestContainerProtocol:
    def test_contains(self):
        log = Timelog(maintenance="disabled")
        log[10] = "a"
        log[20] = "b"
        assert 10 in log
        assert 15 not in log
        assert 20 in log
        log.close()

    def test_contains_rejects_non_int(self):
        log = Timelog(maintenance="disabled")
        with pytest.raises(TypeError):
            operator.contains(log, "ten")
        log.close()

    def test_reversed_raises_with_guidance(self):
        log = Timelog(maintenance="disabled")
        log[1] = "a"
        with pytest.raises(TypeError, match="prev_ts|forward"):
            reversed(log)
        log.close()

    def test_repr_open_and_closed(self):
        log = Timelog(maintenance="disabled")
        log[10] = "a"
        r = repr(log)
        assert "Timelog" in r and "len~1" in r and "'ms'" in r
        log.close()
        assert "closed" in repr(log)

    def test_reversed_slice_returns_empty(self):
        # Sequence semantics: lst[10:1] == []; an NTP step backwards must
        # not blow up a monitoring window query.
        log = Timelog(maintenance="disabled")
        log[5] = "x"
        assert list(log[100:10]) == []
        assert list(log[10:10]) == []
        # Explicit range() keeps raising (defensive API for programmatic use).
        with pytest.raises(ValueError):
            log.range(100, 10)
        log.close()


class TestTeachingErrors:
    def test_datetime_hint(self):
        log = Timelog(maintenance="disabled")
        with pytest.raises(TypeError, match=r"timestamp\(\) \* 1000"):
            log[datetime.datetime(2026, 1, 1)] = "x"
        log.close()

    def test_float_hint(self):
        log = Timelog(maintenance="disabled")
        with pytest.raises(TypeError, match="int\\(x\\)|finer time_unit"):
            log[1.5] = "x"
        log.close()

    def test_extend_skip_warns(self):
        log = Timelog(maintenance="disabled")
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            log.extend([(1, "a"), ("bad", "b"), (2, "c")])
        msgs = [str(w.message) for w in caught
                if issubclass(w.category, RuntimeWarning)]
        assert any("skipped 1" in m for m in msgs)
        assert list(log[0:10]) == [(1, "a"), (2, "c")]
        log.close()

    def test_error_messages_have_no_status_suffix(self):
        log = Timelog(maintenance="disabled")
        log.close()
        with pytest.raises(TimelogError) as ei:
            log.append("x")
        assert "invalid state" not in str(ei.value)
        assert str(ei.value).startswith("Timelog is closed")


class TestStatsEnrichment:
    def test_empty_log_bounds_are_none(self):
        log = Timelog(maintenance="disabled")
        s = log.stats()["storage"]
        assert s["min_ts"] is None and s["max_ts"] is None
        log.close()

    def test_config_echo(self):
        log = Timelog(maintenance="disabled", busy_policy="silent",
                      min_ts=100, mostly_ordered_default=False)
        cfg = log.stats()["config"]
        assert cfg["busy_policy"] == "silent"
        assert cfg["maintenance"] == "disabled"
        assert cfg["min_ts"] == 100
        assert cfg["mostly_ordered_default"] is False
        assert log.min_ts_floor == 100
        log.close()

    def test_min_ts_floor_none_by_default(self):
        log = Timelog(maintenance="disabled")
        assert log.min_ts_floor is None
        log.close()


class TestSealDropRelease:
    def test_cutoff_then_flush_releases_payloads(self):
        # v1.2 bug: flush's seal elided tombstone-covered memtable records
        # WITHOUT firing on_drop_handle -> their Python objects stayed
        # strongly held until close(). The natural retention order
        # (cutoff THEN flush) must release them like every other path.
        import gc
        import weakref

        class Payload:
            pass

        log = Timelog(maintenance="disabled")
        refs = []
        for i in range(500):
            p = Payload()
            refs.append(weakref.ref(p))
            log[i] = p
            del p
        log.cutoff(500)        # tombstone first (memtable-resident records)
        log.flush()            # seal elides them -> MUST route to drop path
        log.stats()            # any entrypoint drains the retired queue
        gc.collect()
        alive = sum(1 for r in refs if r() is not None)
        assert alive == 0, f"{alive}/500 payloads leaked by seal-time elision"
        assert len(log) == 0
        log.close()

    def test_point_delete_then_flush_releases(self):
        import gc
        import weakref

        class Payload:
            pass

        log = Timelog(maintenance="disabled")
        p = Payload()
        ref = weakref.ref(p)
        log[42] = p
        del p
        log.delete(42)
        log.flush()
        log.stats()
        gc.collect()
        assert ref() is None
        log.close()


class TestExitSilenceWithRetiredQueue:
    def test_exit_after_retention_tick_is_silent(self):
        # The documented retention runbook followed by immediate exit used to
        # warn whenever the retired queue was non-empty at teardown.
        code = (
            "import time\n"
            "from timelog import Timelog\n"
            "log = Timelog(delete_debt_threshold=0.2)\n"
            "log.extend([(i, object()) for i in range(5000)])\n"
            "log.cutoff(4000)\n"
            "log.flush()\n"
            "time.sleep(0.4)\n"   # worker compacts; retired queue fills
        )
        proc = subprocess.run(
            [sys.executable, "-c", code], capture_output=True, text=True,
            env=_subprocess_env(), timeout=60,
            cwd=REPO_ROOT)
        assert proc.returncode == 0
        assert proc.stderr.strip() == "", f"retention-exit printed: {proc.stderr!r}"


class TestTeachingErrorsParity:
    def test_append_float_ts_teaches(self):
        log = Timelog(maintenance="disabled")
        with pytest.raises(TypeError, match="int\\(x\\)|finer time_unit"):
            log.append("x", ts=1500.5)
        with pytest.raises(TypeError, match="int\\(x\\)|finer time_unit"):
            log.append(1500.5, "x")
        log.close()

    def test_append_datetime_ts_teaches(self):
        log = Timelog(maintenance="disabled")
        with pytest.raises(TypeError, match=r"timestamp\(\) \* 1000"):
            log.append("x", ts=datetime.datetime(2026, 1, 1))
        log.close()

    def test_extend_skipped_counter(self):
        log = Timelog(maintenance="disabled")
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            log.extend([(1, "a"), ("bad", "b"), (2, "c")])
            log.extend([(3, "d"), ("bad", "e"), ("bad2", "f")])
        assert log.extend_skipped == 3
        assert log.stats()["operational"]["extend_skipped"] == 3
        log.close()

    def test_reopen_resets_extend_skipped_counter(self):
        log = Timelog(maintenance="disabled")
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            log.extend([(1, "a"), ("bad", "b")])
        assert log.extend_skipped == 1
        log.close()

        log.reopen(maintenance="disabled")
        assert log.extend_skipped == 0
        assert log.stats()["operational"]["extend_skipped"] == 0
        log.close()


class TestIterRepr:
    def test_bounded_repr(self):
        log = Timelog(maintenance="disabled")
        log.extend([(i, i) for i in range(5)])
        it = log.range(1, 4)
        assert repr(it) == "<TimelogIter [1..4) remaining=3>"
        next(it)
        assert "remaining=2" in repr(it)
        it.close()
        assert repr(it) == "<TimelogIter closed>"
        log.close()

    def test_unbounded_repr(self):
        log = Timelog(maintenance="disabled")
        log[7] = "x"
        it = log.since(5)
        assert repr(it).startswith("<TimelogIter [5..)")
        it.close()
        log.close()
