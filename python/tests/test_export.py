"""Export API tests: Timelog.to_numpy() and Timelog.to_dict().

Contracts under test (docs/superpowers/specs/2026-07-10-exportability-design.md):
- bounds behave exactly like log[t1:t2] slicing (None = open end, reversed =
  empty, half-open [t1, t2), TS_MAX included only via t2=None)
- to_numpy returns fresh contiguous 1-D (int64 ts, numeric values) arrays;
  dtype= accepts scalar numeric dtypes only; conversion errors propagate with
  their original type plus a row-index note; no snapshot pin outlives the call
- to_dict collapses duplicate timestamps to ONE value; which record wins is
  deliberately UNSPECIFIED (asserted weakly on purpose)
- numpy stays optional: to_dict never imports it
"""

from __future__ import annotations

import sys
import threading

import pytest

import timelog as timelog_module
from timelog import Timelog, TimelogError
from timelog._api import TL_TS_MIN, TL_TS_MAX

np = pytest.importorskip("numpy")


@pytest.fixture
def log():
    lg = Timelog()
    yield lg
    if not lg.closed:
        lg.close()


def fill(lg, n=10, start=0):
    for i in range(n):
        lg[start + i] = float(i)


# ---------------------------------------------------------------------------
# to_dict
# ---------------------------------------------------------------------------

def test_to_dict_basic(log):
    objs = {1: "a", 2: [1, 2], 3: None, 4: {"k": 1}}
    for ts, obj in objs.items():
        log[ts] = obj
    d = log.to_dict()
    assert d == objs
    assert d[2] is objs[2]          # identity preserved, no copies


def test_to_dict_bounds(log):
    fill(log, 10)
    assert set(log.to_dict(3, 7)) == {3, 4, 5, 6}       # half-open
    assert set(log.to_dict(t1=7)) == {7, 8, 9}
    assert set(log.to_dict(t2=3)) == {0, 1, 2}
    assert log.to_dict(7, 3) == {}                       # reversed -> empty
    assert log.to_dict(5, 5) == {}


def test_to_dict_empty(log):
    assert log.to_dict() == {}


def test_to_dict_duplicates_collapse_to_one_unspecified(log):
    # In-order duplicates: exactly one key, value is one of the appended ones.
    log[100] = "a"
    log[100] = "b"
    log[100] = "c"
    d = log.to_dict()
    assert set(d) == {100}
    assert d[100] in {"a", "b", "c"}


def test_to_dict_duplicates_ooo_unspecified(log):
    # OOO duplicates land in the OOO head where equal-ts order is
    # address-dependent: the contract is only "exactly one wins".
    log[1000] = "barrier"
    log[500] = "old"
    log[500] = "new"
    d = log.to_dict()
    assert set(d) == {500, 1000}
    assert d[500] in {"old", "new"}


def test_to_dict_duplicates_survive_compaction():
    # Duplicate collapse still holds after flush + real L0->L1 compaction.
    lg = Timelog(maintenance="disabled")
    try:
        lg[5] = "one"
        lg.flush()
        lg[5] = "two"
        lg.flush()
        lg.compact()
        for _ in range(64):
            if not lg.maint_step():
                break
        s = lg.stats()["storage"]
        assert s["segments_l1"] > 0, "compaction never produced L1; test is vacuous"
        d = lg.to_dict()
        assert set(d) == {5}
        assert d[5] in {"one", "two"}
    finally:
        lg.close()


def test_to_dict_tombstone_filtering(log):
    fill(log, 10)
    log.delete(3, 7)
    assert set(log.to_dict()) == {0, 1, 2, 7, 8, 9}


def test_to_dict_closed_log_raises(log):
    log.close()
    with pytest.raises(TimelogError):
        log.to_dict()


def test_to_dict_works_without_numpy(log, monkeypatch):
    fill(log, 3)
    monkeypatch.setitem(sys.modules, "numpy", None)
    assert set(log.to_dict()) == {0, 1, 2}


def test_to_dict_chunk_boundaries(log, monkeypatch):
    monkeypatch.setattr(timelog_module, "_EXPORT_CHUNK", 7)
    for n in (6, 7, 8, 15):
        lg = Timelog()
        fill(lg, n)
        assert set(lg.to_dict()) == set(range(n))
        lg.close()


def test_to_dict_releases_pin(log):
    fill(log, 5)
    log.to_dict()
    log.close()                     # would raise if a reader pin leaked
    assert log.closed


# ---------------------------------------------------------------------------
# to_numpy
# ---------------------------------------------------------------------------

def test_to_numpy_basic(log):
    fill(log, 10)
    ts, vals = log.to_numpy()
    assert ts.dtype == np.int64 and vals.dtype == np.float64
    assert ts.ndim == vals.ndim == 1
    assert ts.flags.c_contiguous and vals.flags.c_contiguous
    assert ts.flags.owndata and vals.flags.owndata
    np.testing.assert_array_equal(ts, np.arange(10))
    np.testing.assert_array_equal(vals, np.arange(10, dtype=np.float64))


def test_to_numpy_payload_types(log):
    log[1] = 3          # int
    log[2] = 2.5        # float
    log[3] = True       # bool -> 1.0 (payload; key-side bool rejection N/A)
    ts, vals = log.to_numpy()
    np.testing.assert_array_equal(vals, [3.0, 2.5, 1.0])


def test_to_numpy_bounds(log):
    fill(log, 10)
    ts, vals = log.to_numpy(3, 7)
    np.testing.assert_array_equal(ts, [3, 4, 5, 6])
    ts, _ = log.to_numpy(t1=8)
    np.testing.assert_array_equal(ts, [8, 9])
    ts, _ = log.to_numpy(t2=2)
    np.testing.assert_array_equal(ts, [0, 1])
    ts, vals = log.to_numpy(7, 3)                    # reversed -> empty
    assert len(ts) == len(vals) == 0
    assert ts.dtype == np.int64 and vals.dtype == np.float64


def test_to_numpy_empty(log):
    ts, vals = log.to_numpy()
    assert len(ts) == 0 and len(vals) == 0


def test_to_numpy_duplicates_all_exported(log):
    for v in (1.0, 2.0, 3.0):
        log[5] = v
    ts, vals = log.to_numpy()
    np.testing.assert_array_equal(ts, [5, 5, 5])
    assert sorted(vals) == [1.0, 2.0, 3.0]


def test_to_numpy_tombstone_filtering(log):
    fill(log, 10)
    log.delete(3, 7)
    ts, _ = log.to_numpy()
    np.testing.assert_array_equal(ts, [0, 1, 2, 7, 8, 9])


def test_to_numpy_ts_extremes(log):
    log[TL_TS_MIN] = 1.0
    log[0] = 2.0
    log[TL_TS_MAX] = 3.0
    ts, vals = log.to_numpy()                        # t2=None includes TS_MAX
    np.testing.assert_array_equal(ts, [TL_TS_MIN, 0, TL_TS_MAX])
    ts, _ = log.to_numpy(t2=TL_TS_MAX)               # bounded t2 excludes it
    np.testing.assert_array_equal(ts, [TL_TS_MIN, 0])


def test_to_numpy_dtype_int64_roundtrip(log):
    big = 2**60 + 1                                  # not float64-representable
    log[1] = big
    log[2] = -(2**60)
    ts, vals = log.to_numpy(dtype=np.int64)
    assert vals.dtype == np.int64
    assert vals[0] == big and vals[1] == -(2**60)


def test_to_numpy_dtype_guard():
    lg = Timelog()
    try:
        lg[1] = 1.0
        for bad in (str, object, "U8", ("i4", (2,)), "c16", "M8[ns]", bool):
            with pytest.raises(TypeError):
                lg.to_numpy(dtype=bad)
    finally:
        lg.close()


@pytest.mark.parametrize("row", [0, 2, 4])
def test_to_numpy_conversion_error_row_note(log, row):
    for i in range(5):
        log[i] = "bad" if i == row else float(i)
    with pytest.raises(ValueError) as exc_info:
        log.to_numpy()
    notes = getattr(exc_info.value, "__notes__", [])
    assert any(f"row {row} of 5" in note for note in notes)
    log.close()                     # pin released despite the error
    assert log.closed


class _TwoArgError(ValueError):
    """ValueError subclass with a mandatory 2-arg constructor."""

    def __init__(self, code, msg):
        super().__init__(code, msg)


class _RaisingValue:
    def __init__(self, exc):
        self._exc = exc

    def __float__(self):
        raise self._exc


def test_to_numpy_error_type_and_args_preserved(log):
    original = _TwoArgError(42, "boom")
    log[1] = 1.0
    log[2] = _RaisingValue(original)
    with pytest.raises(_TwoArgError) as exc_info:
        log.to_numpy()
    assert exc_info.value is original                # not reconstructed
    assert exc_info.value.args == (42, "boom")
    assert any("row 1 of 2" in n for n in getattr(exc_info.value, "__notes__", []))


def test_to_numpy_overflow_gets_note(log):
    log[1] = 10**400
    with pytest.raises(OverflowError) as exc_info:
        log.to_numpy()
    assert any("row 0 of 1" in n for n in getattr(exc_info.value, "__notes__", []))


def test_to_numpy_none_payload(log):
    # numpy's conversion semantics: None -> NaN under float dtypes (the
    # ecosystem's missing-value convention), TypeError under integer dtypes.
    log[1] = None
    _, vals = log.to_numpy()
    assert np.isnan(vals[0])
    with pytest.raises(TypeError) as exc_info:
        log.to_numpy(dtype=np.int64)
    assert any("row 0 of 1" in n for n in getattr(exc_info.value, "__notes__", []))


def test_to_numpy_closed_log_raises(log):
    log.close()
    with pytest.raises(TimelogError):
        log.to_numpy()


def test_to_numpy_missing_numpy(log, monkeypatch):
    fill(log, 3)
    monkeypatch.setitem(sys.modules, "numpy", None)
    with pytest.raises(ImportError):
        log.to_numpy()


def test_to_numpy_chunk_boundaries(log, monkeypatch):
    monkeypatch.setattr(timelog_module, "_EXPORT_CHUNK", 7)
    for n in (6, 7, 8, 15):
        lg = Timelog()
        fill(lg, n)
        ts, vals = lg.to_numpy()
        np.testing.assert_array_equal(ts, np.arange(n))
        np.testing.assert_array_equal(vals, np.arange(n, dtype=np.float64))
        lg.close()


class _AppendingValue:
    """Hostile payload: mutates the log mid-export from inside __float__."""

    def __init__(self, lg):
        self._lg = lg

    def __float__(self):
        self._lg[999999] = 123.0    # must NOT appear in the running export
        return 7.0


def test_to_numpy_snapshot_isolation_against_reentrant_writes():
    lg = Timelog()
    try:
        lg[1] = 1.0
        lg[2] = _AppendingValue(lg)
        lg[3] = 3.0
        ts, vals = lg.to_numpy()
        np.testing.assert_array_equal(ts, [1, 2, 3])
        np.testing.assert_array_equal(vals, [1.0, 7.0, 3.0])
        assert 999999 in lg.to_dict()               # later export sees it
    finally:
        lg.close()


def test_to_numpy_close_blocked_during_export():
    lg = Timelog()

    class _ClosingValue:
        def __float__(self):
            lg.close()              # pin held by the export -> must raise
            return 1.0

    lg[1] = _ClosingValue()
    with pytest.raises(TimelogError):
        lg.to_numpy()
    assert not lg.closed            # log survived the hostile close attempt
    lg.close()


def test_to_numpy_concurrent_exports(log):
    fill(log, 50_000)
    results = []
    errors = []

    def worker():
        try:
            results.append(log.to_numpy())
        except BaseException as exc:  # noqa: BLE001 - test must capture all
            errors.append(exc)

    threads = [threading.Thread(target=worker) for _ in range(4)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert not errors
    assert len(results) == 4
    for ts, vals in results:
        assert len(ts) == 50_000
        np.testing.assert_array_equal(ts, results[0][0])


@pytest.mark.stress
def test_export_1m_smoke():
    import time

    lg = Timelog.for_bulk_ingest()
    try:
        n = 1_000_000
        lg.bulk_append(np.arange(n, dtype=np.int64), [float(i) for i in range(n)])
        lg.flush()
        t0 = time.perf_counter()
        ts, vals = lg.to_numpy()
        dt_numpy = time.perf_counter() - t0
        assert len(ts) == n
        assert ts[0] == 0 and ts[-1] == n - 1 and vals[-1] == float(n - 1)
        t0 = time.perf_counter()
        d = lg.to_dict()
        dt_dict = time.perf_counter() - t0
        assert len(d) == n
        print(f"\nto_numpy 1M: {dt_numpy*1000:.1f}ms  to_dict 1M: {dt_dict*1000:.1f}ms")
    finally:
        lg.close()
