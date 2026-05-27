"""Tests for the Python facade layer."""

from importlib import metadata as importlib_metadata
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

    def test_version_defined(self):
        """__version__ must be a non-empty string."""
        from timelog import __version__

        assert isinstance(__version__, str)
        assert len(__version__) > 0

    def test_version_in_all(self):
        """__version__ must be in __all__."""
        import timelog

        assert "__version__" in timelog.__all__

    def test_resolve_version_prefers_timelog_lib(self, monkeypatch):
        """Version resolver should prefer timelog-lib distribution metadata."""
        import timelog

        calls = []

        def _fake_version(dist_name):
            calls.append(dist_name)
            if dist_name == "timelog-lib":
                return "1.0.0"
            raise importlib_metadata.PackageNotFoundError(dist_name)

        monkeypatch.setattr(importlib_metadata, "version", _fake_version)
        assert timelog._resolve_version() == "1.0.0"
        assert calls == ["timelog-lib"]

    def test_resolve_version_falls_back_to_timelog(self, monkeypatch):
        """Version resolver should fall back to legacy timelog metadata."""
        import timelog

        calls = []

        def _fake_version(dist_name):
            calls.append(dist_name)
            if dist_name == "timelog-lib":
                raise importlib_metadata.PackageNotFoundError(dist_name)
            if dist_name == "timelog":
                return "0.9.9"
            raise AssertionError(f"unexpected distribution lookup: {dist_name}")

        monkeypatch.setattr(importlib_metadata, "version", _fake_version)
        assert timelog._resolve_version() == "0.9.9"
        assert calls == ["timelog-lib", "timelog"]


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

    def test_coerce_int64_bounds_checked(self):
        """Values outside signed int64 range must raise OverflowError."""
        from timelog._api import _coerce_ts, TL_TS_MIN, TL_TS_MAX

        assert _coerce_ts(TL_TS_MIN) == TL_TS_MIN
        assert _coerce_ts(TL_TS_MAX) == TL_TS_MAX

        with pytest.raises(OverflowError, match="outside int64 range"):
            _coerce_ts(TL_TS_MIN - 1)
        with pytest.raises(OverflowError, match="outside int64 range"):
            _coerce_ts(TL_TS_MAX + 1)


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


    def test_slice_iter_len_reports_remaining_snapshot_rows(self):
        """len(log[t1:t2]) returns remaining rows for that iterator snapshot."""
        from timelog import Timelog

        with Timelog() as log:
            log.extend([(i, f"item{i}") for i in range(6)])
            it = log[1:5]

            assert len(it) == 4
            assert next(it) == (1, "item1")
            assert len(it) == 3

            # Iterator length tracks the snapshot captured at iterator creation,
            # not subsequent live appends.
            log.append(2, "late")
            assert len(it) == 3

            assert list(it) == [(2, "item2"), (3, "item3"), (4, "item4")]
            assert len(it) == 0


    def test_slice_iter_len_closed_iterator_is_zero(self):
        """len(iter) is 0 after close() because no rows remain yieldable."""
        from timelog import Timelog

        with Timelog() as log:
            log.extend([(i, f"item{i}") for i in range(4)])
            it = log[1:4]
            assert len(it) == 3
            it.close()
            assert len(it) == 0



    def test_point_max_timestamp_len_matches_equal(self):
        """len(log.point(TL_TS_MAX)) handles max timestamp without range overflow."""
        from timelog import Timelog
        from timelog._api import TL_TS_MAX

        with Timelog() as log:
            log.append(TL_TS_MAX, "max")
            assert len(log.point(TL_TS_MAX)) == 1
            assert len(log.equal(TL_TS_MAX)) == 1

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

    def test_runtime_error_matches_reexported_exception(self):
        """Runtime TL_ESTATE translation still uses the facade TimelogError."""
        from timelog import Timelog, TimelogError

        log = Timelog()
        log.close()

        with pytest.raises(TimelogError):
            log.flush()

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
# Category 8: PageSpan buffer protocol
# =============================================================================


class TestPageSpanBuffers:
    """Buffer protocol behavior for PageSpan objects."""

    def test_direct_memoryview_over_pagespan(self):
        """memoryview(span) exposes the timestamp buffer directly."""
        from timelog import Timelog

        with Timelog(maintenance="disabled") as log:
            log.extend([(i, f"v{i}") for i in range(8)])
            log.flush()
            span = next(log.views(0, 8))
            mv = memoryview(span)
            try:
                assert mv.readonly
                assert mv.ndim == 1
                assert mv.format == "q"
                assert mv.tolist() == list(range(len(mv)))
            finally:
                mv.release()
                span.close()

    def test_multiple_buffer_exports_block_close_until_all_release(self):
        """Every active buffer export must release before PageSpan.close()."""
        from timelog import Timelog

        with Timelog(maintenance="disabled") as log:
            log.extend([(i, i) for i in range(8)])
            log.flush()
            span = next(log.views(0, 8))

            mv1 = memoryview(span)
            mv2 = span.timestamps
            try:
                with pytest.raises(BufferError):
                    span.close()

                mv1.release()
                with pytest.raises(BufferError):
                    span.close()

                mv2.release()
                span.close()
                with pytest.raises(ValueError, match="closed"):
                    memoryview(span)
            finally:
                try:
                    mv1.release()
                except ValueError:
                    pass
                try:
                    mv2.release()
                except ValueError:
                    pass


# =============================================================================
# Category 9: Weakrefs
# =============================================================================


class TestWeakrefs:
    """Only Timelog supports weak references."""

    def test_timelog_weakref_proxy_and_callbacks(self):
        """Timelog weakrefs, proxies, and callbacks keep CPython semantics."""
        from timelog import Timelog

        calls = []
        log = Timelog(maintenance="disabled")
        proxy = weakref.proxy(log)
        ref1 = weakref.ref(log, lambda ref: calls.append(("a", ref)))
        ref2 = weakref.ref(log, lambda ref: calls.append(("b", ref)))

        proxy.append(1, "x")
        assert ref1() is log
        assert ref2() is log

        del log
        gc.collect()
        gc.collect()

        assert ref1() is None
        assert ref2() is None
        assert len(calls) == 2
        assert sorted(label for label, _ in calls) == ["a", "b"]
        with pytest.raises(ReferenceError):
            proxy.closed

    def test_factory_types_reject_weakrefs(self):
        """Factory-only extension types do not expose weakref slots."""
        from timelog import Timelog

        log = Timelog(maintenance="disabled")
        objects_iter = None
        try:
            log.extend([(i, i) for i in range(8)])
            log.flush()

            row_iter = log.all()
            span_iter = log.views(0, 8)
            span = next(span_iter)
            objects_view = span.objects()
            objects_iter = iter(objects_view)

            for obj in (row_iter, span_iter, span, objects_view, objects_iter):
                with pytest.raises(TypeError):
                    weakref.ref(obj)
        finally:
            objects_view = locals().get("objects_view")
            span = locals().get("span")
            span_iter = locals().get("span_iter")
            row_iter = locals().get("row_iter")
            if span is not None:
                span.close()
            if span_iter is not None:
                span_iter.close()
            if row_iter is not None:
                row_iter.close()
            del objects_iter
            log.close()


# =============================================================================
# Category 10: Non-context-manager lifecycle
# =============================================================================


class TestNonContextManagerLifecycle:
    """The common `log = Timelog()` usage must auto-clean safely."""

    def test_scope_style_auto_close_releases_payload_objects(self):
        """Dropping a plain Timelog variable releases engine-owned objects."""
        from timelog import Timelog

        class Obj:
            pass

        payload_refs = []

        def run_scope():
            log = Timelog(maintenance="disabled")
            payloads = [Obj() for _ in range(4)]
            payload_refs.extend(weakref.ref(obj) for obj in payloads)

            for ts, obj in enumerate(payloads):
                log.append(ts, obj)
            del payloads

            log.flush()
            rows = list(log.all())
            assert [ts for ts, _ in rows] == [0, 1, 2, 3]
            assert all(ref() is not None for ref in payload_refs)
            del rows
            return weakref.ref(log)

        log_ref = run_scope()
        gc.collect()
        gc.collect()

        assert log_ref() is None
        assert all(ref() is None for ref in payload_refs)

    def test_default_background_auto_close_releases_payload_objects(self):
        """Default `log = Timelog()` usage releases objects without close()."""
        from timelog import Timelog

        class Obj:
            pass

        payload_refs = []

        def run_scope():
            log = Timelog(maintenance_wakeup_ms=1)
            payloads = [Obj() for _ in range(32)]
            payload_refs.extend(weakref.ref(obj) for obj in payloads)

            log.extend((ts, obj) for ts, obj in enumerate(payloads))
            del payloads

            log.flush()
            assert len(list(log.all())) == 32
            assert all(ref() is not None for ref in payload_refs)
            return weakref.ref(log)

        log_ref = run_scope()
        gc.collect()
        gc.collect()

        assert log_ref() is None
        assert all(ref() is None for ref in payload_refs)

    def test_iterator_survives_after_user_log_reference_is_dropped(self):
        """A row iterator keeps data valid without user-held Timelog refs."""
        from timelog import Timelog

        log = Timelog(maintenance="disabled")
        log.extend([(i, f"v{i}") for i in range(4)])
        log.flush()
        iterator = log.all()
        log_ref = weakref.ref(log)

        del log
        gc.collect()

        assert log_ref() is not None
        assert list(iterator) == [(0, "v0"), (1, "v1"), (2, "v2"), (3, "v3")]
        iterator.close()
        del iterator
        gc.collect()
        gc.collect()

        assert log_ref() is None

    def test_large_iterator_survives_plain_scope_with_background_maintenance(self):
        """A large iterator remains valid after `del log` in normal usage."""
        from timelog import Timelog

        n = 5000
        log = Timelog(
            maintenance="background",
            maintenance_wakeup_ms=1,
            memtable_max_bytes=65536,
            target_page_bytes=512,
        )
        log.extend((i, f"v{i}") for i in range(n))
        log.flush()
        iterator = log.range(0, n)
        log_ref = weakref.ref(log)

        del log
        gc.collect()

        assert log_ref() is not None
        assert list(iterator) == [(i, f"v{i}") for i in range(n)]
        iterator.close()
        del iterator
        gc.collect()
        gc.collect()

        assert log_ref() is None

    def test_pagespan_survives_after_user_log_reference_is_dropped(self):
        """PageSpan buffers and object views remain valid after `del log`."""
        from timelog import Timelog

        log = Timelog(maintenance="disabled")
        log.extend([(i, f"v{i}") for i in range(4)])
        log.flush()
        span_iter = log.views(0, 4)
        span = next(span_iter)
        objects_view = span.objects()
        log_ref = weakref.ref(log)

        del log
        gc.collect()

        assert log_ref() is not None
        mv = memoryview(span)
        try:
            assert mv.tolist() == [0, 1, 2, 3]
        finally:
            mv.release()
        assert list(objects_view) == ["v0", "v1", "v2", "v3"]

        del objects_view
        span.close()
        span_iter.close()
        del span, span_iter
        gc.collect()
        gc.collect()

        assert log_ref() is None

    def test_iterator_cycle_auto_close_releases_payload_objects(self):
        """A Timelog -> payload -> iterator -> Timelog cycle must collect."""
        from timelog import Timelog

        class Box:
            pass

        log = Timelog(maintenance="disabled")
        box = Box()
        log.append(1, box)
        log.flush()
        iterator = log.all()
        box.iterator = iterator

        log_ref = weakref.ref(log)
        box_ref = weakref.ref(box)
        del log, box, iterator
        gc.collect()
        gc.collect()

        assert log_ref() is None
        assert box_ref() is None
        assert not gc.garbage

    def test_large_background_iterator_cycle_auto_closes_safely(self):
        """A multi-page background Timelog cycle must collect with active pins."""
        from timelog import Timelog

        class Box:
            pass

        n = 5000
        log = Timelog(
            maintenance="background",
            maintenance_wakeup_ms=1,
            memtable_max_bytes=65536,
            target_page_bytes=512,
        )
        box = Box()
        log.extend([(0, box), *((i, f"v{i}") for i in range(1, n))])
        log.flush()
        iterator = log.range(0, n)
        box.iterator = iterator

        log_ref = weakref.ref(log)
        box_ref = weakref.ref(box)
        del log, box, iterator
        gc.collect()
        gc.collect()

        assert log_ref() is None
        assert box_ref() is None
        assert not gc.garbage

    def test_pagespan_cycle_auto_close_releases_payload_objects(self):
        """A Timelog -> payload -> PageSpan graph must collect."""
        from timelog import Timelog

        class Box:
            pass

        log = Timelog(maintenance="disabled")
        box = Box()
        log.append(1, box)
        log.flush()
        span_iter = log.views(0, 10)
        span = next(span_iter)
        objects_view = span.objects()
        box.refs = [span_iter, span, objects_view]

        log_ref = weakref.ref(log)
        box_ref = weakref.ref(box)
        del log, box, span_iter, span, objects_view
        gc.collect()
        gc.collect()

        assert log_ref() is None
        assert box_ref() is None
        assert not gc.garbage


# =============================================================================
# Category 11: Error Messages
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
# Category 12: Finalization (Auto-close)
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

    def test_gc_cycle_with_live_iterator_releases_safely(self):
        """A cycle through a live row iterator must not close the engine first."""
        from timelog import Timelog

        log = Timelog(maintenance="disabled")
        holder = []
        log.append(1, holder)
        log.flush()
        iterator = log.all()
        holder.append(iterator)
        ref = weakref.ref(log)

        del log, holder, iterator
        gc.collect()
        gc.collect()

        assert ref() is None
        assert not gc.garbage

    def test_gc_cycle_with_live_pagespan_releases_safely(self):
        """A cycle through PageSpan/objects() must preserve snapshot lifetime."""
        from timelog import Timelog

        log = Timelog(maintenance="disabled")
        holder = []
        log.append(1, holder)
        log.flush()
        span_iter = log.views(0, 10)
        span = next(span_iter)
        objects_view = span.objects()
        holder.extend([span_iter, span, objects_view])
        ref = weakref.ref(log)

        del log, holder, span_iter, span, objects_view
        gc.collect()
        gc.collect()

        assert ref() is None
        assert not gc.garbage
