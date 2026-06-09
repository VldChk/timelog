"""Characterization tests for the facade `append` contract — written FIRST against
the CURRENT Python override, so they form the regression net for folding append into C
(idea 3). They pin every behavior the fold must preserve EXACTLY: all 3 signatures,
auto-timestamp, bool rejection on the append path, the min_ts guard (incl. parity with
extend), overflow, and arity/keyword errors. These must pass on the current facade and
stay passing after the fold.
"""
from __future__ import annotations
import time
import pytest

import timelog


class TestAppendSignatures:
    def test_two_positional_legacy(self):
        tl = timelog.Timelog()
        tl.append(5, "obj")                 # append(ts, obj)
        assert list(tl.point(5)) == [(5, "obj")]
        tl.close()

    def test_one_positional_keyword_ts(self):
        tl = timelog.Timelog()
        tl.append("obj", ts=7)              # append(obj, ts=X)
        assert list(tl.point(7)) == [(7, "obj")]
        tl.close()

    def test_two_positional_with_ts_kw_ignores_kw(self):
        # Quirk of the current override: 2-positional path ignores a ts= kwarg.
        tl = timelog.Timelog()
        tl.append(5, "obj", ts=9)           # inserts at ts=5, NOT 9
        assert list(tl.point(5)) == [(5, "obj")]
        assert list(tl.point(9)) == []
        tl.close()

    def test_one_positional_autotimestamp(self):
        tl = timelog.Timelog(time_unit="ms")
        before = time.time_ns() // 10**6
        tl.append("obj")                    # auto-ts
        after = time.time_ns() // 10**6
        got = list(tl.all())
        assert len(got) == 1
        ts, val = got[0]
        assert val == "obj"
        assert before <= ts <= after        # valid ms wall-clock
        tl.close()

    @pytest.mark.parametrize("unit,div", [("s", 10**9), ("ms", 10**6), ("us", 10**3), ("ns", 1)])
    def test_autotimestamp_unit_scaling(self, unit, div):
        tl = timelog.Timelog(time_unit=unit)
        before = time.time_ns() // div
        tl.append("x")
        after = time.time_ns() // div
        ts = list(tl.all())[0][0]
        assert before <= ts <= after
        tl.close()

    def test_autotimestamp_monotonicish(self):
        tl = timelog.Timelog(time_unit="ns", mostly_ordered_default=True)
        prev = None
        for _ in range(50):
            tl.append("x")
        ts_list = [t for t, _ in tl.all()]
        assert ts_list == sorted(ts_list)   # non-decreasing wall clock
        tl.close()


class TestAppendErrors:
    def test_bool_rejected_keyword_ts(self):
        tl = timelog.Timelog()
        with pytest.raises(TypeError, match="bool"):
            tl.append("obj", ts=True)
        tl.close()

    def test_bool_rejected_positional_ts(self):
        tl = timelog.Timelog()
        with pytest.raises(TypeError, match="bool"):
            tl.append(True, "obj")          # legacy ts,obj with bool ts
        tl.close()

    def test_float_ts_rejected(self):
        tl = timelog.Timelog()
        with pytest.raises(TypeError):
            tl.append(1.5, "obj")
        with pytest.raises(TypeError):
            tl.append("obj", ts=1.5)
        tl.close()

    def test_overflow_ts(self):
        tl = timelog.Timelog()
        with pytest.raises(OverflowError):
            tl.append(2 ** 63, "obj")
        with pytest.raises(OverflowError):
            tl.append("obj", ts=2 ** 63)
        tl.close()

    def test_index_object_ts_accepted(self):
        class Ix:
            def __index__(self):
                return 11
        tl = timelog.Timelog()
        tl.append(Ix(), "obj")
        assert list(tl.point(11)) == [(11, "obj")]
        tl.close()

    def test_arity_errors(self):
        tl = timelog.Timelog()
        with pytest.raises(TypeError):
            tl.append()                     # too few
        with pytest.raises(TypeError):
            tl.append(1, 2, 3)              # too many positional
        with pytest.raises(TypeError):
            tl.append(ts=5)                 # ts kw but no obj
        with pytest.raises(TypeError):
            tl.append("obj", ts=5, foo=1)   # unknown kw
        tl.close()


class TestAppendMinTsGuard:
    def test_append_below_min_ts_raises(self):
        tl = timelog.Timelog(min_ts=100)
        with pytest.raises(ValueError, match="min_ts"):
            tl.append(50, "low")
        tl.append(150, "ok")
        assert list(tl.point(150)) == [(150, "ok")]
        tl.close()

    def test_append_and_extend_guard_agree(self):
        # The min_ts guard must be ONE source of truth: append and extend reject
        # identically below the boundary.
        tl = timelog.Timelog(min_ts=100)
        with pytest.raises(ValueError):
            tl.append(50, "a")
        with pytest.raises(ValueError):
            tl.extend([(50, "b")], insert_on_error=False)
        tl.close()

    def test_reopen_clears_guard(self):
        tl = timelog.Timelog(min_ts=100)
        with pytest.raises(ValueError):
            tl.append(50, "a")
        tl.close()
        tl.reopen(min_ts=None)
        tl.append(50, "now_ok")             # guard cleared -> must succeed
        assert list(tl.point(50)) == [(50, "now_ok")]
        tl.close()

    def test_reopen_changes_guard_no_stale_leak(self):
        # The C floor is the single source of truth and is re-applied by the
        # facade on every reopen (PyTimelog_init no longer resets it). Reopening
        # to a DIFFERENT bound must take effect exactly, with no stale leak from
        # the prior floor and no fail-open gap.
        tl = timelog.Timelog(min_ts=100)
        with pytest.raises(ValueError):
            tl.append(50, "below-old")
        tl.close()
        tl.reopen(min_ts=200)               # raise the floor
        assert tl._min_ts == 200            # property reads the C field
        with pytest.raises(ValueError):
            tl.append(150, "below-new")     # was OK under old floor=100
        tl.append(250, "ok")
        assert list(tl.point(250)) == [(250, "ok")]
        tl.close()
        tl.reopen(min_ts=50)                # lower the floor
        assert tl._min_ts == 50
        tl.append(50, "now_ok")             # rejected under floor=200, ok now
        assert list(tl.point(50)) == [(50, "now_ok")]
        tl.close()

    def test_fresh_instance_has_no_guard(self):
        # Fresh tp_alloc memory must zero-initialize the floor fields even though
        # PyTimelog_init no longer explicitly resets them.
        tl = timelog.Timelog()
        assert tl._min_ts is None
        tl.append(-999, "neg")              # no floor -> negative ts accepted
        assert list(tl.point(-999)) == [(-999, "neg")]
        tl.close()

    def test_setitem_respects_guard(self):
        tl = timelog.Timelog(min_ts=100)
        with pytest.raises(ValueError):
            tl[50] = "x"
        tl.close()
