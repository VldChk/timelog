"""Opt-in compatibility stress harnesses for lifetime and concurrency."""

from __future__ import annotations

import gc
import threading
import time
import weakref

import pytest


pytestmark = [pytest.mark.stress]


class _Payload:
    __slots__ = ("value", "__weakref__")

    def __init__(self, value: tuple[int, int]):
        self.value = value


def _snapshot_reader(log, expected_rows, loops):
    for _ in range(loops):
        rows = [(ts, obj.value) for ts, obj in log[0:100]]
        assert rows == expected_rows

        with log.views(0, 8) as spans_iter:
            spans = list(spans_iter)
            assert len(spans) > 0

        del spans
        del rows
        time.sleep(0)


def test_snapshot_and_pagespan_lifecycle_harness(compat_runtime):
    short_stress = compat_runtime.require_stress_enabled()

    from timelog import Timelog

    iterations = 4 if short_stress else 12
    reader_loops = 6 if short_stress else 20

    for batch in range(iterations):
        refs = []
        expected_rows = []

        with Timelog() as log:
            for ts in range(8):
                obj = _Payload((batch, ts))
                refs.append(weakref.ref(obj))
                expected_rows.append((ts, (batch, ts)))
                log.append(ts, obj)
            del obj

            log.flush()

            for ts in range(8, 12):
                obj = _Payload((batch, ts))
                refs.append(weakref.ref(obj))
                expected_rows.append((ts, (batch, ts)))
                log.append(ts, obj)
            del obj

            baseline = [(ts, obj.value) for ts, obj in log[0:100]]
            assert baseline == expected_rows

            readers = [
                threading.Thread(
                    target=_snapshot_reader,
                    args=(log, expected_rows, reader_loops),
                    daemon=False,
                )
                for _ in range(2)
            ]

            for reader in readers:
                reader.start()
            for reader in readers:
                reader.join()

            del baseline
            del readers

        for _ in range(3):
            gc.collect()

        assert all(ref() is None for ref in refs)
