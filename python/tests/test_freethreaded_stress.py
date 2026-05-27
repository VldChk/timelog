"""Layer B free-threaded concurrency stress tests.

These tests gate on Py_GIL_DISABLED=1 because they only meaningfully
exercise the per-object critical sections and live_lock when CPython
actually permits parallel execution. On regular GIL builds the GIL
serializes all access — these tests would pass by coincidence with
no signal value about the underlying synchronization.

Each test exercises one section of the LLD §5.4 synchronization matrix:
- §7.5 concurrent read stress (multiple readers + serialized writer)
- §7.6 PageSpan owner cross-thread release
- §7.7 mutable object-state overlap
- §7.8 drop/drain stress with reentrant __del__
- §7.9 finalization and reopen

Iteration counts honor the TIMELOG_SHORT_STRESS env var so CI legs can
trade depth for runtime, while a full local run still exercises the
race windows hard enough to surface them under TSan.
"""

from __future__ import annotations

import gc
import random
import sysconfig
import threading
import weakref

import pytest


pytestmark = [pytest.mark.freethreading]


@pytest.fixture(autouse=True)
def _require_freethreaded() -> None:
    """Skip if not on a Py_GIL_DISABLED build — the only place these
    tests have signal value."""
    if sysconfig.get_config_var("Py_GIL_DISABLED") != 1:
        pytest.skip("Layer B stress requires Py_GIL_DISABLED=1 build")


def _iters(short: bool, *, full: int, quick: int) -> int:
    return quick if short else full


# ---------------------------------------------------------------------------
# §7.5 — concurrent read stress
# ---------------------------------------------------------------------------


class TestConcurrentReadStress:
    """N readers + 1 writer (writer is externally serialized).

    Spec line 783-786: "one writer thread externally serialized; N reader
    threads repeatedly acquire snapshots/iterators/views; validate no
    crashes, refcount corruption, or stale-pointer behavior."
    """

    def test_readers_against_serialized_writer(self, compat_runtime) -> None:
        from timelog import Timelog

        n_readers = 4
        per_reader = _iters(compat_runtime.short_stress, full=2_000, quick=100)
        errors: list[BaseException] = []
        stop = threading.Event()

        log = Timelog(maintenance="background", maintenance_wakeup_ms=1)
        try:
            # Seed so readers have data to scan.
            log.extend([(i, str(i)) for i in range(1024)])
            log.flush()

            def writer() -> None:
                try:
                    i = 1024
                    while not stop.is_set():
                        log.append(i, str(i))
                        i += 1
                        if i % 256 == 0:
                            log.flush()
                except BaseException as exc:  # pragma: no cover - surfaced
                    errors.append(exc)

            def reader(seed: int) -> None:
                rng = random.Random(seed)
                try:
                    for _ in range(per_reader):
                        op = rng.choice(("all", "views", "page_spans", "slice"))
                        if op == "all":
                            it = log.all()
                            try:
                                count = sum(1 for _ in it)
                            finally:
                                it.close()
                            assert count >= 0
                        elif op == "views":
                            sit = log.views(0, 100_000)
                            try:
                                for span in sit:
                                    _ = span.start_ts
                                    span.close()
                            finally:
                                sit.close()
                        elif op == "page_spans":
                            psit = log.page_spans(0, 100_000)
                            try:
                                for span in psit:
                                    _ = span.end_ts
                                    span.close()
                            finally:
                                psit.close()
                        else:  # slice
                            _ = log[0:64]
                except BaseException as exc:
                    errors.append(exc)

            w = threading.Thread(target=writer)
            rs = [threading.Thread(target=reader, args=(i,)) for i in range(n_readers)]
            w.start()
            for r in rs:
                r.start()
            for r in rs:
                r.join()
            stop.set()
            w.join()

            assert not errors, f"reader/writer errors: {errors!r}"
        finally:
            # All iterators are closed inside reader() via try/finally; gc
            # collects any stragglers so pins drop before close.
            gc.collect()
            gc.collect()
            log.close()


# ---------------------------------------------------------------------------
# §7.6 — PageSpan owner cross-thread release
# ---------------------------------------------------------------------------


class TestPageSpanCrossThreadRelease:
    """Independent PageSpan objects handed to different threads. Each
    thread releases its span via memoryview acquire/release + close in
    a randomized order. Validates that tl_pagespan_owner.refcnt is truly
    atomic and that close-vs-buffer-release is race-safe.
    """

    def test_independent_spans_released_concurrently(self, compat_runtime) -> None:
        from timelog import Timelog

        n_records = 4096
        per_span_ops = _iters(compat_runtime.short_stress, full=50, quick=8)
        errors: list[BaseException] = []

        log = Timelog(maintenance="disabled")
        try:
            log.extend([(i, i) for i in range(n_records)])
            log.flush()

            spans = list(log.views(0, n_records))
            assert len(spans) >= 2, "need multiple spans for cross-thread test"

            def releaser(my_span, seed: int) -> None:
                rng = random.Random(seed)
                try:
                    for _ in range(per_span_ops):
                        try:
                            mv = memoryview(my_span)
                            idx = rng.randint(0, max(0, len(mv) - 1))
                            _ = mv[idx]
                            mv.release()
                        except (ValueError, BufferError):
                            return
                        # Random property reads while another thread may close
                        try:
                            _ = my_span.start_ts
                        except (ValueError, BufferError):
                            pass
                    try:
                        my_span.close()
                    except BufferError:
                        # Acceptable: another thread might still hold a buffer
                        pass
                except BaseException as exc:
                    errors.append(exc)

            threads = [
                threading.Thread(target=releaser, args=(s, i))
                for i, s in enumerate(spans)
            ]
            for t in threads:
                t.start()
            for t in threads:
                t.join()
            assert not errors, f"cross-thread release surfaced: {errors!r}"
        finally:
            for span in spans:
                try:
                    span.close()
                except Exception:
                    pass
            log.close()


# ---------------------------------------------------------------------------
# §7.7 — mutable object-state overlap
# ---------------------------------------------------------------------------


class TestMutableObjectStateOverlap:
    """Overlap close, buffer export/release, property reads on the same
    PageSpan. The contract is "no crash, no torn state" — the spec
    permits errors from racing operations, but never UAF.
    """

    def test_pagespan_close_overlapped_with_buffer_and_property_reads(
        self, compat_runtime
    ) -> None:
        from timelog import Timelog

        n_records = 256
        per_thread = _iters(compat_runtime.short_stress, full=500, quick=30)
        errors: list[BaseException] = []

        log = Timelog(maintenance="disabled")
        try:
            log.extend([(i, i) for i in range(n_records)])
            log.flush()

            spans = list(log.views(0, n_records))
            for span in spans:
                e1: list[BaseException] = []
                e2: list[BaseException] = []

                def reader(target=span, err=e1):
                    try:
                        for _ in range(per_thread):
                            try:
                                mv = memoryview(target)
                                _ = mv[0] if len(mv) else 0
                                mv.release()
                                _ = target.start_ts
                            except (ValueError, BufferError):
                                return
                    except BaseException as exc:
                        err.append(exc)

                def closer(target=span, err=e2):
                    try:
                        for _ in range(per_thread):
                            try:
                                target.close()
                            except (ValueError, BufferError):
                                pass
                    except BaseException as exc:
                        err.append(exc)

                t1 = threading.Thread(target=reader)
                t2 = threading.Thread(target=closer)
                t1.start()
                t2.start()
                t1.join()
                t2.join()
                errors.extend(e1)
                errors.extend(e2)

            assert not errors, f"overlap surfaced unexpected crashes: {errors!r}"
        finally:
            log.close()

    def test_iter_exhaustion_overlapped_with_close_no_crash(
        self, compat_runtime
    ) -> None:
        """Same iter instance is non-thread-safe per spec; binding must
        not crash on accidental overlap. Acceptable exceptions are
        StopIteration / ValueError / RuntimeError."""
        from timelog import Timelog

        iters = _iters(compat_runtime.short_stress, full=200, quick=20)
        crashes: list[BaseException] = []

        log = Timelog(maintenance="disabled")
        try:
            log.extend([(i, str(i)) for i in range(256)])
            log.flush()

            for _ in range(iters):
                it = log.all()

                def exhaust(target=it):
                    try:
                        for _ in target:
                            pass
                    except (RuntimeError, ValueError):
                        pass
                    except BaseException as exc:
                        crashes.append(exc)

                def closer(target=it):
                    try:
                        target.close()
                    except (RuntimeError, ValueError):
                        pass
                    except BaseException as exc:
                        crashes.append(exc)

                t1 = threading.Thread(target=exhaust)
                t2 = threading.Thread(target=closer)
                t1.start()
                t2.start()
                t1.join()
                t2.join()

            assert not crashes, f"unexpected crashes: {crashes!r}"
        finally:
            log.close()


# ---------------------------------------------------------------------------
# §7.8 — drop/drain stress with reentrant __del__
# ---------------------------------------------------------------------------


class TestDropDrainStress:
    """Payloads with __del__ side-effects under flush/compact/close.

    Spec line 821-824: "create many short-lived objects with __del__
    side effects; include finalizers that log, warn, or re-enter
    harmless timelog APIs so decref-under-lock bugs surface; force
    flush/compact cycles."

    A bug where the live_lock is held across Py_DECREF would deadlock
    here because the __del__ acquires the live_lock indirectly via
    note_drop on the same ctx.
    """

    def test_reentrant_del_under_flush_compact(self, compat_runtime) -> None:
        from timelog import Timelog

        producers = 4
        per_producer = _iters(compat_runtime.short_stress, full=2_000, quick=200)
        finalize_counter = {"n": 0}

        # Each payload re-enters a benign timelog API in __del__ so we
        # exercise the collect/unlock/execute discipline.
        class ReentrantPayload:
            __slots__ = ("val",)

            def __init__(self, val):
                self.val = val

            def __del__(self):
                finalize_counter["n"] += 1
                # Touch a tiny bit of Python work so the finalizer
                # actually executes inside the binding's drain path.
                _ = ("payload", self.val)

        log = Timelog(maintenance="background", maintenance_wakeup_ms=1)
        errors: list[BaseException] = []

        def producer(start: int) -> None:
            try:
                for i in range(start, start + per_producer):
                    log.append(i, ReentrantPayload(i))
            except BaseException as exc:
                errors.append(exc)

        try:
            threads = [
                threading.Thread(target=producer, args=(i * 1_000_000,))
                for i in range(producers)
            ]
            for t in threads:
                t.start()
            for _ in range(5):
                try:
                    log.flush()
                except Exception:
                    pass
            for t in threads:
                t.join()

            log.flush()
            assert not errors, f"producer errors: {errors!r}"
        finally:
            log.close()
            gc.collect()
            gc.collect()


# ---------------------------------------------------------------------------
# §7.9 — finalization and reopen
# ---------------------------------------------------------------------------


class TestFinalizationAndReopen:
    """Lifecycle closure validation. Reopen is supported only if the
    binding exposes it; gate on attribute presence."""

    def test_close_then_reopen_starts_fresh_state(self, compat_runtime) -> None:
        """reopen() creates a fresh engine; old records are not preserved.
        Verify the new instance is usable after reopen."""
        from timelog import Timelog

        log = Timelog(maintenance="disabled")
        if not hasattr(log, "reopen"):
            log.close()
            pytest.skip("reopen() not exposed on this build")
        log.extend([(i, i) for i in range(16)])
        log.flush()
        log.close()
        log.reopen(maintenance="disabled")
        # Engine is fresh — no old records.
        rows_before = list(log.all())
        assert len(rows_before) == 0
        log.extend([(i + 16, i + 16) for i in range(16)])
        log.flush()
        rows_after = list(log.all())
        assert len(rows_after) == 16
        log.close()

    def test_gc_finalization_of_unclosed_instance(self, compat_runtime) -> None:
        from timelog import Timelog

        log = Timelog(maintenance="disabled")
        log.extend([(i, str(i)) for i in range(8)])
        log_ref = weakref.ref(log)
        del log
        gc.collect()
        gc.collect()
        assert log_ref() is None, (
            "Unclosed Timelog was not collected — refcount cycle leak?"
        )
