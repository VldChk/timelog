"""
Tests for the Python facade layer (LLD-B7).

This test suite drives the implementation using TDD principles.
Tests are ordered by dependency: foundational tests first.
"""

import gc
import weakref
import pytest


# =============================================================================
# Category 1: Re-exports (Foundation)
# =============================================================================


class TestReexports:
    """Verify that re-exports are identical objects from _timelog."""

    def test_exceptions_identical(self):
        """TimelogError must be same object as _timelog.TimelogError."""
        from timelog import TimelogError
        from timelog._timelog import TimelogError as _CTimelogError

        assert TimelogError is _CTimelogError

    def test_busy_error_identical(self):
        """TimelogBusyError must be same object."""
        from timelog import TimelogBusyError
        from timelog._timelog import TimelogBusyError as _CBusyError

        assert TimelogBusyError is _CBusyError

    def test_types_identical(self):
        """All exported types must match extension types."""
        from timelog import TimelogIter, PageSpan, PageSpanIter, PageSpanObjectsView
        from timelog._timelog import (
            TimelogIter as _CIter,
            PageSpan as _CSpan,
            PageSpanIter as _CSpanIter,
            PageSpanObjectsView as _CObjView,
        )

        assert TimelogIter is _CIter
        assert PageSpan is _CSpan
        assert PageSpanIter is _CSpanIter
        assert PageSpanObjectsView is _CObjView

    def test_all_exported(self):
        """Every item in __all__ must exist in module."""
        import timelog

        for name in timelog.__all__:
            assert hasattr(timelog, name), f"{name} in __all__ but not in module"


# =============================================================================
# Category 2: Version and Metadata
# =============================================================================


class TestVersion:
    """Test version metadata."""

    def test_version_defined(self):
        """__version__ must be a non-empty string."""
        from timelog import __version__

        assert isinstance(__version__, str)
        assert len(__version__) > 0

    def test_version_in_all(self):
        """__version__ must be in __all__."""
        import timelog

        assert "__version__" in timelog.__all__


# =============================================================================
# Category 3: Coercion
# =============================================================================


class TestCoercion:
    """Test _coerce_ts timestamp coercion."""

    def test_coerce_int(self):
        """Plain int passes through unchanged."""
        from timelog._api import _coerce_ts

        assert _coerce_ts(42) == 42
        assert _coerce_ts(-1) == -1
        assert _coerce_ts(0) == 0

    def test_coerce_numpy_int64(self):
        """numpy.int64 should work via __index__."""
        from timelog._api import _coerce_ts

        np = pytest.importorskip("numpy")
        val = np.int64(12345)
        assert _coerce_ts(val) == 12345

    def test_coerce_bool_rejected(self):
        """bool must be explicitly rejected."""
        from timelog._api import _coerce_ts

        with pytest.raises(TypeError, match="bool"):
            _coerce_ts(True)
        with pytest.raises(TypeError, match="bool"):
            _coerce_ts(False)

    def test_coerce_non_int_rejected(self):
        """float and str must be rejected."""
        from timelog._api import _coerce_ts

        with pytest.raises(TypeError):
            _coerce_ts(3.14)
        with pytest.raises(TypeError):
            _coerce_ts("123")


# =============================================================================
# Category 4: Slicing
# =============================================================================


class TestSlicing:
    """Test __getitem__ slice syntax."""

    def test_slice_range(self):
        """log[t1:t2] maps to log.range(t1, t2)."""
        from timelog import Timelog

        with Timelog() as log:
            log.extend([(i, f"item{i}") for i in range(10)])
            result = list(log[3:7])
            expected = list(log.range(3, 7))
            assert result == expected
            assert len(result) == 4

    def test_slice_since(self):
        """log[t1:] maps to log.since(t1)."""
        from timelog import Timelog

        with Timelog() as log:
            log.extend([(i, f"item{i}") for i in range(10)])
            result = list(log[7:])
            expected = list(log.since(7))
            assert result == expected
            assert len(result) == 3  # 7, 8, 9

    def test_slice_until(self):
        """log[:t2] maps to log.until(t2)."""
        from timelog import Timelog

        with Timelog() as log:
            log.extend([(i, f"item{i}") for i in range(10)])
            result = list(log[:3])
            expected = list(log.until(3))
            assert result == expected
            assert len(result) == 3  # 0, 1, 2

    def test_slice_all(self):
        """log[:] maps to log.all()."""
        from timelog import Timelog

        with Timelog() as log:
            log.extend([(i, f"item{i}") for i in range(5)])
            result = list(log[:])
            expected = list(log.all())
            assert result == expected
            assert len(result) == 5

    def test_slice_step_none(self):
        """Step None is allowed (equivalent to default)."""
        from timelog import Timelog

        with Timelog() as log:
            log.append(100, "a")
            result = list(log[None:None:None])
            assert len(result) == 1

    def test_slice_step_one(self):
        """Step 1 is allowed (same as default)."""
        from timelog import Timelog

        with Timelog() as log:
            log.extend([(i, i) for i in range(5)])
            result = list(log[1:4:1])
            expected = list(log[1:4])
            assert result == expected

    def test_slice_step_error(self):
        """Step != None/1 raises ValueError."""
        from timelog import Timelog

        with Timelog() as log:
            log.append(0, "x")
            with pytest.raises(ValueError, match="step"):
                log[0:10:2]

    def test_slice_step_bool_rejected(self):
        """Step=True (which equals 1) must be rejected for type consistency."""
        from timelog import Timelog

        with Timelog() as log:
            log.append(0, "x")
            with pytest.raises(ValueError, match="step"):
                log[0:10:True]

    def test_slice_step_float_rejected(self):
        """Step=1.0 (which equals 1) must be rejected for type consistency."""
        from timelog import Timelog

        with Timelog() as log:
            log.append(0, "x")
            with pytest.raises(ValueError, match="step"):
                log[0:10:1.0]

    def test_int_key_returns_list(self):
        """log[t] returns list of objects at that timestamp."""
        from timelog import Timelog

        with Timelog() as log:
            log.append(100, "x")
            log.append(100, "y")
            result = log[100]
            assert isinstance(result, list)
            assert set(result) == {"x", "y"}

    def test_int_key_empty(self):
        """log[t] returns empty list when no records at timestamp."""
        from timelog import Timelog

        with Timelog() as log:
            log.append(100, "x")
            assert log[999] == []


# =============================================================================
# Category 5: Iteration
# =============================================================================


class TestIteration:
    """Test __iter__ protocol."""

    def test_iter_all(self):
        """iter(log) is equivalent to log.all()."""
        from timelog import Timelog

        with Timelog() as log:
            log.extend([(i, f"item{i}") for i in range(5)])
            via_iter = list(log)
            via_all = list(log.all())
            assert via_iter == via_all

    def test_iter_sequence(self):
        """Results from iteration match expected sequence."""
        from timelog import Timelog

        with Timelog() as log:
            expected = [(100, "a"), (200, "b"), (300, "c")]
            for ts, obj in expected:
                log.append(ts, obj)
            result = list(log)
            assert result == expected

    def test_iter_empty(self):
        """Empty log yields no records."""
        from timelog import Timelog

        with Timelog() as log:
            result = list(log)
            assert result == []


# =============================================================================
# Category 6: at() Method
# =============================================================================


class TestAt:
    """Test at() convenience method."""

    def test_at_basic(self):
        """at(ts) returns list of objects at that timestamp."""
        from timelog import Timelog

        with Timelog() as log:
            log.append(100, "x")
            log.append(200, "y")
            via_at = log.at(100)
            assert via_at == ["x"]

    def test_at_with_duplicates(self):
        """at(ts) returns all objects at that timestamp."""
        from timelog import Timelog

        with Timelog() as log:
            log.append(100, "a")
            log.append(100, "b")
            log.append(100, "c")
            log.append(200, "d")
            result = log.at(100)
            assert set(result) == {"a", "b", "c"}
            assert len(result) == 3

    def test_at_empty(self):
        """at(ts) with no match returns empty list."""
        from timelog import Timelog

        with Timelog() as log:
            log.append(100, "x")
            result = log.at(999)
            assert result == []


# =============================================================================
# Category 7: Integration
# =============================================================================


class TestIntegration:
    """Integration tests combining multiple features."""

    def test_context_manager(self):
        """Timelog works as context manager."""
        from timelog import Timelog

        with Timelog() as log:
            log.append(1, "test")
            assert not log.closed
        assert log.closed

    def test_subclass_relationship(self):
        """Timelog is subclass of _timelog.Timelog."""
        from timelog import Timelog
        from timelog._timelog import Timelog as _CTimelog

        assert issubclass(Timelog, _CTimelog)

    def test_isinstance_check(self):
        """Timelog instance passes isinstance checks."""
        from timelog import Timelog
        from timelog._timelog import Timelog as _CTimelog

        with Timelog() as log:
            assert isinstance(log, Timelog)
            assert isinstance(log, _CTimelog)

    def test_pagespan_accessible(self):
        """PageSpan is accessible through facade."""
        from timelog import Timelog, PageSpan, PageSpanIter

        # Verify types are importable (re-export test)
        assert PageSpan is not None
        assert PageSpanIter is not None
        # Verify actual usage
        with Timelog() as log:
            log.extend([(i, i) for i in range(100)])
            log.flush()
            with log.views(0, 100) as spans_iter:
                assert isinstance(spans_iter, PageSpanIter)

    def test_type_aliases_defined(self):
        """Type aliases are defined and have correct types."""
        from timelog import Record, RecordIter, RecordBatch
        from typing import get_origin, Iterator

        assert get_origin(Record) is tuple
        assert get_origin(RecordBatch) is list
        # RecordIter is Iterator[Record], so origin is Iterator (or collections.abc.Iterator)
        origin = get_origin(RecordIter)
        assert origin is Iterator or (
            origin is not None and origin.__name__ == "Iterator"
        )


# =============================================================================
# Category 8: Error Messages
# =============================================================================


class TestErrorMessages:
    """Test that error messages provide good guidance."""

    def test_bool_error_clear(self):
        """Bool rejection error is clear about the issue."""
        from timelog._api import _coerce_ts

        with pytest.raises(TypeError) as exc_info:
            _coerce_ts(True)
        assert "bool" in str(exc_info.value).lower()


# =============================================================================
# Category 9: Finalization (Auto-close)
# =============================================================================


class TestFinalization:
    """Validate best-effort cleanup on GC when close() is not called."""

    def test_gc_finalizes_timelog(self):
        """Dropping Timelog should release engine-owned object refs."""
        from timelog import Timelog

        class Obj:
            pass

        obj = Obj()
        ref = weakref.ref(obj)

        log = Timelog()
        log.append(1, obj)

        # Timelog should own a strong reference after append
        del obj
        assert ref() is not None

        # Drop the timelog and force GC
        log = None
        gc.collect()
        gc.collect()

        assert ref() is None
