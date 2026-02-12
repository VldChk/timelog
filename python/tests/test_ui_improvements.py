"""
Tests for UI improvements (Items 0-7).

Covers: min_ts, dict-style access, auto-timestamp, extend improvements,
point access, view(), delete renames, PageSpan copy removal, views().
"""

import time
import pytest
from timelog import Timelog, PageSpanIter
from timelog._api import TL_TS_MIN, TL_TS_MAX, _now_ts


# =============================================================================
# Item 0: Reopen/configure support
# =============================================================================


class TestReopen:
    def test_reopen_after_close(self):
        """reopen() works after close and resets the engine."""
        log = Timelog()
        log.append(100, "a")
        log.close()
        log.reopen()
        log.append(200, "b")
        assert list(log) == [(200, "b")]
        log.close()

    def test_reopen_requires_closed(self):
        """reopen() requires closed state."""
        from timelog import TimelogError
        with Timelog() as log:
            with pytest.raises(TimelogError):
                log.reopen()

    def test_configure_alias(self):
        """configure() is an alias for reopen()."""
        log = Timelog()
        log.close()
        log.configure()
        log.append(1, "x")
        assert list(log) == [(1, "x")]
        log.close()


# =============================================================================
# Item 1: min_ts boundary parameter
# =============================================================================


class TestMinTs:
    def test_min_ts_rejects_below(self):
        """min_ts= kwarg rejects inserts below the threshold."""
        with Timelog(min_ts=500) as log:
            with pytest.raises(ValueError, match="below min_ts"):
                log.append(100, "before")
            log.append(600, "after")
            result = list(log)
            assert len(result) == 1
            assert result[0] == (600, "after")

    def test_min_ts_rejects_setitem(self):
        """log[ts] = obj rejects below min_ts."""
        with Timelog(min_ts=500) as log:
            with pytest.raises(ValueError, match="below min_ts"):
                log[100] = "nope"

    def test_min_ts_skips_invalid_on_extend(self):
        """extend() skips records below min_ts when insert_on_error=True."""
        with Timelog(min_ts=500) as log:
            log.extend([(100, "a"), (600, "b")])
            assert list(log) == [(600, "b")]

    def test_min_ts_none_is_default(self):
        """min_ts=None (default) does not reject anything."""
        with Timelog() as log:
            log.append(100, "a")
            assert len(list(log)) == 1

    def test_min_ts_zero(self):
        """min_ts=0 rejects negative timestamps."""
        with Timelog(min_ts=0) as log:
            with pytest.raises(ValueError, match="below min_ts"):
                log.append(-10, "neg")
            log.append(10, "pos")
            result = list(log)
            assert len(result) == 1
            assert result[0] == (10, "pos")


# =============================================================================
# Item 2: Dict-style insert + auto-timestamp
# =============================================================================


class TestSetitem:
    def test_setitem_basic(self):
        """log[ts] = obj inserts a record."""
        with Timelog() as log:
            log[100] = "hello"
            assert log[100] == ["hello"]

    def test_setitem_multiple(self):
        """Multiple inserts at same timestamp."""
        with Timelog() as log:
            log[100] = "a"
            log[100] = "b"
            result = log[100]
            assert set(result) == {"a", "b"}


class TestAppendAutoTimestamp:
    def test_append_single_arg(self):
        """append(obj) uses auto-timestamp."""
        with Timelog(time_unit="ms") as log:
            before = _now_ts("ms")
            log.append("hello")
            after = _now_ts("ms")
            records = list(log)
            assert len(records) == 1
            ts, obj = records[0]
            assert obj == "hello"
            assert before <= ts <= after

    def test_append_with_ts_kwarg(self):
        """append(obj, ts=X) uses explicit timestamp."""
        with Timelog() as log:
            log.append("hello", ts=42)
            result = list(log)
            assert result == [(42, "hello")]

    def test_append_two_positional_legacy(self):
        """append(ts, obj) — legacy C-style still works."""
        with Timelog() as log:
            log.append(100, "hello")
            result = list(log)
            assert result == [(100, "hello")]

    def test_append_auto_ts_different_units(self):
        """Auto-timestamp respects time_unit."""
        for unit in ("s", "ms", "us", "ns"):
            with Timelog(time_unit=unit) as log:
                log.append("test")
                records = list(log)
                assert len(records) == 1
                ts = records[0][0]
                # Sanity: timestamp should be positive
                assert ts > 0


# =============================================================================
# Item 3: extend() improvements
# =============================================================================


class TestExtendImprovements:
    def test_extend_dual_list(self):
        """extend(timestamps, objects) — dual-list form."""
        with Timelog() as log:
            log.extend([100, 200, 300], ["a", "b", "c"])
            result = list(log)
            assert result == [(100, "a"), (200, "b"), (300, "c")]

    def test_extend_dual_list_length_mismatch(self):
        """Mismatched lengths raise ValueError."""
        with Timelog() as log:
            with pytest.raises(ValueError):
                log.extend([100, 200], ["a"])

    def test_extend_mostly_ordered_default_true(self):
        """extend() defaults to mostly_ordered=True."""
        with Timelog() as log:
            # This should work without specifying mostly_ordered
            log.extend([(100, "a"), (200, "b")])
            assert len(list(log)) == 2

    def test_extend_default_from_init(self):
        """extend() uses mostly_ordered_default from init when None."""
        with Timelog(mostly_ordered_default=False) as log:
            assert log._mostly_ordered_default is False
            log.extend([(10, "x"), (20, "y")], mostly_ordered=None)
            assert len(list(log)) == 2

    def test_extend_pairs_list(self):
        """extend([(ts, obj), ...]) — list of pairs."""
        with Timelog() as log:
            log.extend([(10, "x"), (20, "y")])
            result = list(log)
            assert result == [(10, "x"), (20, "y")]

    def test_extend_generator(self):
        """extend(generator) — lazy generator."""
        def gen():
            for i in range(5):
                yield (i * 10, f"item{i}")

        with Timelog() as log:
            log.extend(gen())
            assert len(list(log)) == 5


# =============================================================================
# Item 4: Point access log[t] and view()
# =============================================================================


class TestPointAccess:
    def test_getitem_int_basic(self):
        """log[ts] returns list of objects."""
        with Timelog() as log:
            log.append(100, "x")
            result = log[100]
            assert result == ["x"]

    def test_getitem_int_multiple(self):
        """log[ts] with multiple records returns all."""
        with Timelog() as log:
            log[100] = "a"
            log[100] = "b"
            result = log[100]
            assert set(result) == {"a", "b"}

    def test_getitem_int_empty(self):
        """log[ts] with no match returns empty list."""
        with Timelog() as log:
            assert log[999] == []

    def test_getitem_ts_max_works(self):
        """Point query at TL_TS_MAX delegates to C point path."""
        with Timelog() as log:
            log[TL_TS_MAX] = "edge"
            assert log[TL_TS_MAX] == ["edge"]


class TestIteratorView:
    def test_view_returns_pagespaniter(self):
        """iter.view() returns a PageSpanIter."""
        with Timelog() as log:
            log.extend([(i, f"v{i}") for i in range(100)])
            log.flush()
            it = log[0:100]
            v = it.view()
            assert isinstance(v, PageSpanIter)
            v.close()
            it.close()

    def test_view_covers_same_range(self):
        """view() covers the same time range as the iterator."""
        with Timelog() as log:
            log.extend([(i, f"v{i}") for i in range(200)])
            log.flush()
            with log[50:150] as it:
                with it.view() as v:
                    spans = list(v)
                    # All timestamps in spans should be in [50, 150)
                    for span in spans:
                        for i in range(len(span)):
                            ts = span.timestamps[i]
                            assert 50 <= ts < 150
                        span.close()


# =============================================================================
# Item 5: Delete renames
# =============================================================================


class TestCutoff:
    def test_cutoff_basic(self):
        """cutoff(ts) deletes all records before ts."""
        with Timelog() as log:
            log.extend([(i, f"v{i}") for i in range(10)])
            log.cutoff(5)
            result = list(log)
            assert all(ts >= 5 for ts, _ in result)
            assert len(result) == 5

    def test_cutoff_coerces(self):
        """cutoff() coerces timestamp."""
        with Timelog() as log:
            log.append(100, "a")
            with pytest.raises(TypeError, match="bool"):
                log.cutoff(True)


class TestDelete:
    def test_delete_point(self):
        """delete(ts) deletes records at exact timestamp."""
        with Timelog() as log:
            log.extend([(100, "a"), (200, "b"), (300, "c")])
            log.delete(200)
            result = list(log)
            assert len(result) == 2
            assert all(ts != 200 for ts, _ in result)

    def test_delete_range(self):
        """delete(t1, t2) deletes records in [t1, t2)."""
        with Timelog() as log:
            log.extend([(i, f"v{i}") for i in range(10)])
            log.delete(3, 7)
            result = list(log)
            assert all(ts < 3 or ts >= 7 for ts, _ in result)
            assert len(result) == 6

    def test_delete_ts_max_raises(self):
        """Point delete at TL_TS_MAX raises ValueError."""
        with Timelog() as log:
            with pytest.raises(ValueError, match="TL_TS_MAX"):
                log.delete(TL_TS_MAX)


class TestDelitem:
    def test_delitem_point(self):
        """del log[ts] deletes at exact timestamp."""
        with Timelog() as log:
            log.extend([(100, "a"), (200, "b")])
            del log[100]
            result = list(log)
            assert result == [(200, "b")]

    def test_delitem_slice(self):
        """del log[t1:t2] deletes range."""
        with Timelog() as log:
            log.extend([(i, f"v{i}") for i in range(10)])
            del log[3:7]
            result = list(log)
            assert all(ts < 3 or ts >= 7 for ts, _ in result)

    def test_delitem_slice_open_start(self):
        """del log[:t2] deletes from beginning."""
        with Timelog() as log:
            log.extend([(i, f"v{i}") for i in range(10)])
            del log[:5]
            result = list(log)
            assert all(ts >= 5 for ts, _ in result)

    def test_delitem_slice_open_end(self):
        """del log[t1:] deletes to end."""
        with Timelog() as log:
            log.extend([(i, f"v{i}") for i in range(10)])
            del log[5:]
            result = list(log)
            assert all(ts < 5 for ts, _ in result)

    def test_delitem_step_error(self):
        """del log[::2] raises ValueError."""
        with Timelog() as log:
            with pytest.raises(ValueError, match="step"):
                del log[::2]

    def test_delitem_ts_max_raises(self):
        """del log[TL_TS_MAX] raises ValueError."""
        with Timelog() as log:
            with pytest.raises(ValueError, match="TL_TS_MAX"):
                del log[TL_TS_MAX]


# =============================================================================
# Item 6: Remove copy() from PageSpan
# =============================================================================


class TestPageSpanCopyRemoved:
    def test_copy_not_available(self):
        """PageSpan.copy() should no longer exist."""
        with Timelog() as log:
            log.extend([(i, i) for i in range(100)])
            log.flush()
            with log.views(0, 100) as spans:
                span = next(spans)
                assert not hasattr(span, "copy")
                # copy_timestamps should still work
                ts_list = span.copy_timestamps()
                assert isinstance(ts_list, list)
                span.close()


# =============================================================================
# Item 7: views() alias
# =============================================================================


class TestViews:
    def test_views_no_args(self):
        """views() returns all spans."""
        with Timelog() as log:
            log.extend([(i, i) for i in range(100)])
            log.flush()
            with log.views() as v:
                spans = list(v)
                assert len(spans) > 0
                for span in spans:
                    span.close()

    def test_views_with_range(self):
        """views(t1, t2) returns spans in range."""
        with Timelog() as log:
            log.extend([(i, i) for i in range(100)])
            log.flush()
            with log.views(20, 80) as v:
                spans = list(v)
                for span in spans:
                    for i in range(len(span)):
                        ts = span.timestamps[i]
                        assert 20 <= ts < 80
                    span.close()

    def test_views_partial_args_error(self):
        """views(t1=X) without t2 raises ValueError."""
        with Timelog() as log:
            with pytest.raises(ValueError, match="both"):
                log.views(t1=10)

    def test_views_c_level_alias(self):
        """C-level views() method exists on _CTimelog."""
        from timelog._timelog import Timelog as _CTimelog

        assert hasattr(_CTimelog, "views")


# =============================================================================
# insert_on_error
# =============================================================================


class TestInsertOnError:
    def test_atomic_rejects_bad_batch(self):
        """insert_on_error=False rejects entire batch on validation error."""
        with Timelog() as log:
            with pytest.raises(TypeError):
                log.extend([(100, "a"), ("bad", "b")], insert_on_error=False)
            assert list(log) == []  # nothing inserted

    def test_atomic_generator_rejected(self):
        """insert_on_error=False rejects generators."""
        def gen():
            yield (1, "a")
        with Timelog() as log:
            with pytest.raises(TypeError, match="sequence"):
                log.extend(gen(), insert_on_error=False)

    def test_streaming_default(self):
        """insert_on_error=True (default) streams records."""
        with Timelog() as log:
            log.extend([(100, "a"), (200, "b")])
            assert len(list(log)) == 2

    def test_streaming_skips_invalid(self):
        """insert_on_error=True skips invalid timestamps."""
        with Timelog() as log:
            log.extend([(100, "a"), ("bad", "b"), (200, "c")], insert_on_error=True)
            assert list(log) == [(100, "a"), (200, "c")]

    def test_streaming_bad_item_raises(self):
        """Non-pair items raise ValueError even in streaming mode."""
        with Timelog() as log:
            with pytest.raises(ValueError, match="expects"):
                log.extend([(100, "a"), 42, (200, "b")], insert_on_error=True)

    def test_streaming_below_min_ts_raises(self):
        """insert_on_error=True does not swallow min_ts validation errors."""
        with Timelog(min_ts=50) as log:
            with pytest.raises(ValueError, match="below min_ts"):
                log.extend([(10, "a"), (60, "b")], insert_on_error=True)
            assert list(log) == []

    def test_atomic_with_min_ts(self):
        """insert_on_error=False + min_ts rejects entire batch."""
        with Timelog(min_ts=500) as log:
            with pytest.raises(ValueError, match="below min_ts"):
                log.extend(
                    [(600, "ok"), (100, "bad")],
                    insert_on_error=False,
                )
            assert list(log) == []  # nothing inserted

    def test_atomic_success(self):
        """insert_on_error=False with valid batch inserts all."""
        with Timelog() as log:
            log.extend([(100, "a"), (200, "b")], insert_on_error=False)
            assert len(list(log)) == 2

    def test_atomic_dual_list(self):
        """insert_on_error=False works with dual-list form."""
        with Timelog(min_ts=500) as log:
            with pytest.raises(ValueError, match="below min_ts"):
                log.extend([100, 600], ["a", "b"], insert_on_error=False)
            assert list(log) == []


# =============================================================================
# __len__
# =============================================================================


class TestLen:
    def test_len_empty(self):
        """len() of empty log is 0."""
        with Timelog() as log:
            assert len(log) == 0

    def test_len_after_append(self):
        """len() increases after appends."""
        with Timelog() as log:
            log.extend([(i, i) for i in range(10)])
            assert len(log) == 10

    def test_len_after_delete(self):
        """len() may not immediately decrease (approximate)."""
        with Timelog() as log:
            log.extend([(i, i) for i in range(10)])
            log.delete(5, 10)
            # records_estimate may still include deleted records
            # just verify it returns a non-negative int
            assert isinstance(len(log), int)
            assert len(log) >= 0


# =============================================================================
# _now_ts helper
# =============================================================================


class TestNowTs:
    def test_now_ts_ms(self):
        """_now_ts('ms') returns reasonable millisecond timestamp."""
        ts = _now_ts("ms")
        # Should be within a second of time.time_ns() // 10**6
        expected = time.time_ns() // 10**6
        assert abs(ts - expected) < 1000

    def test_now_ts_all_units(self):
        """_now_ts works for all supported units."""
        for unit in ("s", "ms", "us", "ns"):
            ts = _now_ts(unit)
            assert isinstance(ts, int)
            assert ts > 0


# =============================================================================
# Constants
# =============================================================================


class TestConstants:
    def test_tl_ts_min(self):
        """TL_TS_MIN is INT64_MIN."""
        assert TL_TS_MIN == -(2**63)

    def test_tl_ts_max(self):
        """TL_TS_MAX is INT64_MAX."""
        assert TL_TS_MAX == 2**63 - 1
