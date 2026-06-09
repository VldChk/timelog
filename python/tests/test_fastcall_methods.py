"""Regression tests for the METH_FASTCALL conversion of the 9 positional methods
(point, since, until, equal, next_ts, prev_ts, delete_before, range, delete_range).

Locks in the behavior-preservation contracts the hostile review flagged:
- PyLong_AsLongLong == "L" parity (int/__index__ accepted; float/str/None -> TypeError;
  >int64 -> OverflowError; bool True->1 accepted at the C layer).
- Arity errors -> TypeError; keyword calls rejected (METH_FASTCALL has no kwargs).
- CHECK_CLOSED-vs-parse ORDER preserved: iterator methods (point/equal/range/since/until)
  parse first so a bad arg on a CLOSED log raises the arg TypeError; delete/next_ts/prev_ts
  check closed first so a bad arg on a closed log raises the closed error.
- Concurrency: the converted methods (incl. the delete writers) run race-free under N threads.
"""
from __future__ import annotations
import threading
import pytest

import timelog
from timelog import _timelog as C
from timelog import TimelogError

ONE_ARG = ["point", "since", "until", "equal", "next_ts", "prev_ts", "delete_before"]
TWO_ARG = ["range", "delete_range"]
ITER_METHODS = ["point", "equal", "range", "since", "until"]      # parse-first (arg error wins when closed)
CLOSED_FIRST = ["next_ts", "prev_ts", "delete_before", "delete_range"]  # closed error wins


def _fresh_raw(n=64):
    tl = C.Timelog()
    for i in range(n):
        tl.append(i, i)
    return tl


class TestFastcallParity:
    def test_results_match_known_dataset(self):
        tl = timelog.Timelog()
        for i in range(10):
            tl.append(i, i * 100)
        assert list(tl.range(2, 5)) == [(2, 200), (3, 300), (4, 400)]
        assert list(tl.point(3)) == [(3, 300)]
        assert list(tl.equal(3)) == [(3, 300)]
        assert list(tl.since(8)) == [(8, 800), (9, 900)]
        assert list(tl.until(2)) == [(0, 0), (1, 100)]
        assert tl.next_ts(3) == 4
        assert tl.prev_ts(3) == 2
        tl.delete_range(2, 4)
        assert sum(1 for _ in tl.range(0, 10)) == 8
        tl.delete_before(1)
        assert sum(1 for _ in tl.range(0, 10)) == 7
        tl.close()

    @pytest.mark.parametrize("m", ONE_ARG + TWO_ARG)
    def test_arity_error_is_typeerror(self, m):
        tl = _fresh_raw()
        meth = getattr(tl, m)
        wrong = (1, 2, 3) if m in TWO_ARG else ()  # too many for 2-arg, too few for 1-arg
        with pytest.raises(TypeError):
            meth(*wrong)
        # also the complementary wrong arity
        with pytest.raises(TypeError):
            meth(*( (1,) if m in TWO_ARG else (1, 2) ))
        tl.close()

    @pytest.mark.parametrize("m", ONE_ARG + TWO_ARG)
    def test_keyword_rejected(self, m):
        tl = _fresh_raw()
        with pytest.raises(TypeError):
            getattr(tl, m)(t=1) if m in ONE_ARG else getattr(tl, m)(t1=1, t2=2)
        tl.close()

    @pytest.mark.parametrize("m", ONE_ARG + TWO_ARG)
    def test_non_int_typeerror(self, m):
        tl = _fresh_raw()
        args_str = ("x",) * (2 if m in TWO_ARG else 1)
        args_flt = (1.5,) * (2 if m in TWO_ARG else 1)
        args_none = (None,) * (2 if m in TWO_ARG else 1)
        for bad in (args_str, args_flt, args_none):
            with pytest.raises(TypeError):
                getattr(tl, m)(*bad)
        tl.close()

    @pytest.mark.parametrize("m", ONE_ARG + TWO_ARG)
    def test_overflow_is_overflowerror(self, m):
        tl = _fresh_raw()
        big = 2 ** 63
        args = (big, big) if m in TWO_ARG else (big,)
        with pytest.raises(OverflowError):
            getattr(tl, m)(*args)
        tl.close()

    def test_bool_accepted_at_c_layer(self):
        # "L"/PyLong_AsLongLong accept bool (True->1, False->0); preserved.
        tl = C.Timelog()
        tl.append(0, "a")
        tl.append(1, "b")
        assert list(tl.point(True)) == [(1, "b")]
        assert list(tl.point(False)) == [(0, "a")]
        assert tl.next_ts(False) == 1
        tl.close()

    def test_negative_one_is_a_valid_value_not_an_error(self):
        # PyLong_AsLongLong returns -1 for the legit value -1 WITHOUT setting an
        # exception; the helper's `v==-1 && PyErr_Occurred()` must accept it.
        tl = C.Timelog()
        tl.append(-1, "neg")
        tl.append(0, "zero")
        assert list(tl.point(-1)) == [(-1, "neg")]
        assert list(tl.range(-1, 1)) == [(-1, "neg"), (0, "zero")]
        assert tl.next_ts(-1) == 0
        assert tl.prev_ts(0) == -1
        tl.delete_range(-1, 0)        # removes ts=-1 only
        assert sum(1 for _ in tl.range(-5, 5)) == 1
        tl.close()

    def test_index_object_accepted(self):
        class Ix:
            def __index__(self):
                return 3
        tl = _fresh_raw()
        # __index__ object must behave identically to its int value (== "L")
        assert list(tl.point(Ix())) == list(tl.point(3))
        assert tl.next_ts(Ix()) == tl.next_ts(3)
        tl.close()


class TestFastcallClosedOrdering:
    """The B-1 contract: closed-vs-bad-arg precedence must be byte-preserved per method."""

    @pytest.mark.parametrize("m", ITER_METHODS)
    def test_iterator_method_argerror_wins_on_closed(self, m):
        tl = _fresh_raw()
        tl.close()
        bad = ("x", "y") if m in TWO_ARG else ("x",)
        # iterator methods parse before CHECK_CLOSED -> bad arg raises TypeError, not closed
        with pytest.raises(TypeError):
            getattr(tl, m)(*bad)

    @pytest.mark.parametrize("m", CLOSED_FIRST)
    def test_closed_first_method_closederror_wins(self, m):
        tl = _fresh_raw()
        tl.close()
        bad = ("x", "y") if m in TWO_ARG else ("x",)
        # these check CHECK_CLOSED first -> closed error (TimelogError), not TypeError
        with pytest.raises(TimelogError):
            getattr(tl, m)(*bad)


@pytest.mark.freethreading
class TestFastcallConcurrency:
    """Race the converted methods from many threads. The readers ASSERT engine
    INVARIANTS on RANDOMIZED args (not constant) so a torn int64 read or a wrong
    parse produces a wrong-but-non-raising result that is caught — not discarded.
    Invariants hold for any consistent snapshot, even under concurrent mutation."""

    def test_converted_methods_race_free_and_correct(self):
        import sys, time, random
        N = 4000
        tl = timelog.Timelog(busy_policy="flush")
        for i in range(N):
            tl.append(i, i)
        gil_off = (hasattr(sys, "_is_gil_enabled") and not sys._is_gil_enabled())
        stop = threading.Event()
        errors = []

        def reader(seed):
            rng = random.Random(seed)
            try:
                while not stop.is_set():
                    x = rng.randint(-50, N + 50)
                    nt = tl.next_ts(x)
                    if nt is not None and not (nt > x):
                        errors.append(f"next_ts({x})={nt} not > x")
                    pt = tl.prev_ts(x)
                    if pt is not None and not (pt < x):
                        errors.append(f"prev_ts({x})={pt} not < x")
                    for ts, _ in tl.point(x):
                        if ts != x:
                            errors.append(f"point({x}) returned ts={ts}")
                    a = rng.randint(0, N); b = a + rng.randint(1, 300)
                    for ts, _ in tl.range(a, b):
                        if not (a <= ts < b):
                            errors.append(f"range({a},{b}) returned ts={ts}")
                    s = rng.randint(0, N)
                    for ts, _ in tl.since(s):
                        if ts < s:
                            errors.append(f"since({s}) returned ts={ts}"); break
                    for ts, _ in tl.until(s):
                        if ts >= s:
                            errors.append(f"until({s}) returned ts={ts}"); break
                    for ts, _ in tl.equal(x):
                        if ts != x:
                            errors.append(f"equal({x}) returned ts={ts}")
            except Exception as e:  # pragma: no cover - failure path
                errors.append(repr(e))

        def writer():
            try:
                i = N
                while not stop.is_set():
                    tl.append(i, i); i += 1
                    if i % 50 == 0:
                        tl.delete_range(i - 40, i - 20)   # converted 2-arg writer
                    if i % 97 == 0:
                        tl.delete_before(i - 3000)        # converted 1-arg writer
            except Exception as e:  # pragma: no cover
                errors.append(repr(e))

        threads = [threading.Thread(target=reader, args=(k,)) for k in range(6)] + \
                  [threading.Thread(target=writer) for _ in range(2)]
        for t in threads:
            t.start()
        time.sleep(2.0 if gil_off else 0.8)
        stop.set()
        for t in threads:
            t.join()
        assert not errors, f"converted methods raced/returned wrong results: {errors[:5]}"
        tl.close()
