"""Free-threaded concurrency stress tests.

These tests gate on Py_GIL_DISABLED=1 because they only meaningfully
exercise the per-object critical sections and live-handle lock when CPython
actually permits parallel execution. On regular GIL builds the GIL
serializes all access — these tests would pass by coincidence with
no signal value about the underlying synchronization.

Covers:
- Concurrent read stress (multiple readers + serialized writer)
- PageSpan owner cross-thread release
- Mutable object-state overlap
- Drop/drain stress with reentrant __del__
- Finalization and reopen

Iteration counts honor the TIMELOG_SHORT_STRESS env var so CI legs can
trade depth for runtime, while a full local run still exercises the
race windows hard enough to surface them under TSan.
"""

from __future__ import annotations

import gc
import random
import sys
import sysconfig
import threading
import time
import weakref

import pytest


pytestmark = [pytest.mark.freethreading]


@pytest.fixture(autouse=True)
def _require_freethreaded(compat_runtime) -> None:
    """Require both a free-threaded build and a disabled GIL runtime."""
    compat_runtime.require_free_threaded_build()
    if sysconfig.get_config_var("Py_GIL_DISABLED") != 1:
        pytest.skip("free-threaded stress requires Py_GIL_DISABLED=1 build")
    if sys._is_gil_enabled():
        pytest.fail("free-threaded stress must run with PYTHON_GIL=0")
    import timelog  # noqa: F401
    if sys._is_gil_enabled():
        pytest.fail("importing timelog re-enabled the GIL")


def _iters(short: bool, *, full: int, quick: int) -> int:
    return quick if short else full


# ---------------------------------------------------------------------------
# Concurrent read stress
# ---------------------------------------------------------------------------


class TestConcurrentReadStress:
    """N readers + 1 writer (writer is externally serialized).

    Readers repeatedly acquire snapshots/iterators/views; validate
    no crashes, refcount corruption, or stale-pointer behavior.
    """

    def test_readers_against_serialized_writer(self, compat_runtime) -> None:
        from timelog import Timelog

        n_readers = 4
        per_reader = _iters(compat_runtime.short_stress, full=500, quick=100)
        # Bound the writer so total runtime is predictable regardless of
        # reader scheduling — the goal is concurrent read/write safety, not
        # an unbounded soak. The writer also stops as soon as readers finish.
        writer_budget = _iters(compat_runtime.short_stress, full=20_000, quick=2_000)
        # Readers scan a FIXED window so per-op work does not grow with the
        # writer's appends (which would make `all` super-linear).
        scan_window = 4096
        errors: list[BaseException] = []
        stop = threading.Event()

        log = Timelog(maintenance="background", maintenance_wakeup_ms=1)
        try:
            log.extend([(i, str(i)) for i in range(scan_window)])
            log.flush()

            def writer() -> None:
                try:
                    i = scan_window
                    end = scan_window + writer_budget
                    while i < end and not stop.is_set():
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
                            # Bounded scan: stop after scan_window rows so the
                            # growing log doesn't make this op super-linear.
                            it = log.all()
                            try:
                                count = 0
                                for _row in it:
                                    count += 1
                                    if count >= scan_window:
                                        break
                            finally:
                                it.close()
                            assert count >= 0
                        elif op == "views":
                            sit = log.views(0, scan_window)
                            try:
                                for span in sit:
                                    _ = span.start_ts
                                    span.close()
                            finally:
                                sit.close()
                        elif op == "page_spans":
                            psit = log.page_spans(0, scan_window)
                            try:
                                for span in psit:
                                    _ = span.end_ts
                                    span.close()
                            finally:
                                psit.close()
                        else:  # slice — materialize so the iterator is
                                # fully consumed and released (an un-consumed
                                # slice iterator would pin a snapshot).
                            _ = list(log[0:64])
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
            # Every iterator/span is closed inside reader() via try/finally
            # and slices are materialized, so no pins should remain. gc
            # collects any stragglers before close as a belt-and-suspenders.
            gc.collect()
            gc.collect()
            log.close()


# ---------------------------------------------------------------------------
# PageSpan owner cross-thread release
# ---------------------------------------------------------------------------


class TestPageSpanCrossThreadRelease:
    """Independent PageSpan objects handed to different threads. Each
    thread releases its span via memoryview acquire/release + close in
    a randomized order. Validates that the PageSpan owner refcount is
    truly atomic and that close-vs-buffer-release is race-safe.
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
# Mutable object-state overlap
# ---------------------------------------------------------------------------


class TestMutableObjectStateOverlap:
    """Overlap close, buffer export/release, property reads on the same
    PageSpan. The contract is "no crash, no torn state" — racing
    operations may surface errors, but never use-after-free.
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
        """A single iterator instance is not thread-safe; the binding must
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
# Drop/drain stress with reentrant __del__
# ---------------------------------------------------------------------------


class TestDropDrainStress:
    """Payloads with __del__ side-effects under flush/compact/close.

    Create many short-lived objects with __del__ side effects, including
    finalizers that re-enter harmless timelog APIs so decref-under-lock
    bugs would surface; force flush/compact cycles to drive drop/drain.

    A bug where the live-handle lock is held across Py_DECREF would
    deadlock here because the finalizer reacquires that lock indirectly.
    """

    @pytest.mark.timeout(60)
    def test_reentrant_del_under_flush_compact(self, compat_runtime) -> None:
        from timelog import Timelog

        producers = 4
        per_producer = _iters(compat_runtime.short_stress, full=2_000, quick=200)
        total = producers * per_producer
        # __del__ may fire concurrently on multiple drain threads, so the
        # counter increment must be serialized to count accurately.
        finalize_lock = threading.Lock()
        finalize_counter = {"n": 0}
        writer_lock = threading.Lock()

        log = Timelog(maintenance="disabled", busy_policy="flush")

        # Each payload RE-ENTERS a benign timelog read inside __del__. The
        # finalizer runs inside the binding's retired-stack drain (when a
        # tombstone physically drops the handle while the log is open) or the
        # close-time live-set sweep. If the binding held an internal lock
        # across Py_DECREF, this re-entrant max_ts() would deadlock — the
        # collect-under-lock / execute-outside-lock discipline is exactly
        # what makes it safe. Closed-state errors are expected when the
        # finalizer fires during/after close(), so they are tolerated.
        class ReentrantPayload:
            __slots__ = ("val",)

            def __init__(self, val):
                self.val = val

            def __del__(self):
                with finalize_lock:
                    finalize_counter["n"] += 1
                try:
                    log.max_ts()
                except Exception:
                    pass

        errors: list[BaseException] = []

        def producer(start: int) -> None:
            try:
                for i in range(start, start + per_producer):
                    with writer_lock:
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
            # Concurrent flush cycles while producers append.
            maintenance_errors: list[BaseException] = []
            for _ in range(5):
                try:
                    with writer_lock:
                        log.flush()
                except BaseException as exc:
                    maintenance_errors.append(exc)
                    break
            for t in threads:
                t.join()

            assert not errors, f"producer errors: {errors!r}"
            assert not maintenance_errors, (
                f"flush during producer phase failed: {maintenance_errors!r}"
            )

            # Force the drop/drain path WHILE THE LOG IS OPEN. Tombstone the
            # whole keyspace, flush the tombstone to storage, request compaction,
            # then drive manual maintenance. In maintenance="disabled",
            # compact() only arms compact_pending; maint_step() is what actually
            # performs the merge, fires on_drop, and drains retired handles.
            # A lock-held-across-Py_DECREF bug would deadlock inside the drain
            # here (caught by pytest-timeout when installed) rather than ever
            # reaching the assertion; the close path can't surface it because it
            # short-circuits on the atomic closed flag before taking any lock.
            with writer_lock:
                log.delete(0, producers * 1_000_000 + per_producer)
                log.flush()
                log.compact()
            deadline = time.monotonic() + 10.0
            while finalize_counter["n"] == 0 and time.monotonic() < deadline:
                try:
                    with writer_lock:
                        did_work = log.maint_step()
                    if not did_work:
                        with writer_lock:
                            log.compact()
                except BaseException as exc:
                    maintenance_errors.append(exc)
                    break
                time.sleep(0.002)
            assert not maintenance_errors, (
                f"drop/drain maintenance failed: {maintenance_errors!r}"
            )

            opened_finalized = finalize_counter["n"]
            assert opened_finalized > 0, (
                "no payloads were finalized via the drop/drain path while the "
                "log was open — the reentrant __del__ contract was not "
                "exercised (a lock held across Py_DECREF would have deadlocked "
                "here instead)"
            )
        finally:
            log.close()
            gc.collect()
            gc.collect()

        # Every payload is eventually finalized: dropped via tombstone while
        # the log was open, or DECREF'd by close()'s live-set sweep.
        # Refcounting makes this deterministic once gc flushes any stragglers.
        assert finalize_counter["n"] == total, (
            f"expected all {total} payloads finalized, got "
            f"{finalize_counter['n']} — a leaked/undecref'd handle"
        )


# ---------------------------------------------------------------------------
# Finalization and reopen
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


# ---------------------------------------------------------------------------
# bulk_append under true parallelism
# ---------------------------------------------------------------------------


class TestBulkAppendFreeThreaded:
    """bulk_append (single writer, externally serialized) vs parallel readers,
    plus concurrent mutation of the caller-owned source list (the
    PySequence_Tuple snapshot must make that harmless)."""

    def test_bulk_append_with_concurrent_readers(self, compat_runtime) -> None:
        import array

        from timelog import Timelog

        batches = _iters(compat_runtime.short_stress, full=50, quick=8)
        log = Timelog(maintenance="background")
        stop = threading.Event()
        errors: list[BaseException] = []

        def reader() -> None:
            while not stop.is_set():
                try:
                    for _ in log[0:10**9]:
                        pass
                except BaseException as exc:  # snapshot reads must never error
                    errors.append(exc)
                    return

        threads = [threading.Thread(target=reader) for _ in range(4)]
        for t in threads:
            t.start()
        try:
            for batch in range(batches):
                base = batch * 1000
                log.bulk_append(
                    array.array("q", range(base, base + 1000)),
                    list(range(base, base + 1000)),
                )
        finally:
            stop.set()
            for t in threads:
                t.join()
        assert errors == []
        log.flush()
        assert len(log) == batches * 1000
        log.close()

    def test_bulk_append_with_concurrent_source_mutation(
        self, compat_runtime
    ) -> None:
        import array

        from timelog import Timelog

        rounds = _iters(compat_runtime.short_stress, full=200, quick=20)
        log = Timelog(maintenance="disabled")
        stop = threading.Event()
        source: list[object] = list(range(1000))

        def mutator() -> None:
            rng = random.Random(1234)
            while not stop.is_set():
                idx = rng.randrange(1000)
                source[idx] = rng.random()
                if rng.random() < 0.01:
                    source.append(rng.random())
                    del source[rng.randrange(len(source))]

        thread = threading.Thread(target=mutator)
        thread.start()
        inserted = 0
        try:
            for round_no in range(rounds):
                # Snapshot len/list pair under our control: bulk_append itself
                # tuple-snapshots `payload`, so torn reads must be impossible
                # even though `source` churns concurrently.
                payload = source
                ts = array.array("q", range(round_no * 2000, round_no * 2000 + len(payload)))
                try:
                    log.bulk_append(ts, payload)
                    inserted += len(ts)
                except ValueError:
                    # Length mismatch is acceptable if the mutator resized
                    # between our len() capture inside array construction and
                    # the call; nothing may be inserted in that case.
                    pass
        finally:
            stop.set()
            thread.join()
        log.flush()
        assert len(log) == inserted
        log.close()
