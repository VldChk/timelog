"""Private helpers for the Timelog facade. Do not import directly."""

from __future__ import annotations

import datetime as _datetime
import operator
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from timelog import Timelog, TimelogIter

# Sentinel timestamps matching C TL_TS_MIN / TL_TS_MAX
TL_TS_MIN = -(2**63)      # INT64_MIN
TL_TS_MAX = 2**63 - 1     # INT64_MAX

# Note: auto-timestamping now lives in C (tl_py_now_ts); the former Python
# _now_ts/_UNIT_DIVISORS helpers were removed when append folded into C.


def _coerce_ts(x: object) -> int:
    """Coerce x to an int64 timestamp via ``__index__``.

    Raises:
        TypeError: If x is bool or lacks ``__index__``.
        OverflowError: If value is outside signed int64 range.
    """
    if isinstance(x, bool):
        raise TypeError("timestamp must be int (bool not allowed)")
    try:
        ts = operator.index(x)
    except TypeError:
        # The two mistakes every user makes once: teach, don't scold.
        if isinstance(x, _datetime.datetime):
            raise TypeError(
                "timestamps are integers in the log's time_unit; for a "
                "datetime use e.g. int(dt.timestamp() * 1000) with "
                "time_unit='ms' (UTC-aware datetimes recommended)"
            ) from None
        if isinstance(x, float):
            raise TypeError(
                f"timestamps are integers in the log's time_unit, not float "
                f"({x!r}); use int(x), or a finer time_unit ('us'/'ns') if "
                "you need sub-unit precision"
            ) from None
        raise
    if ts < TL_TS_MIN or ts > TL_TS_MAX:
        raise OverflowError(
            f"timestamp {ts} is outside int64 range [{TL_TS_MIN}, {TL_TS_MAX}]"
        )
    return ts


def _slice_to_iter(log: Timelog, s: slice) -> TimelogIter:
    """Convert a slice to a TimelogIter via the appropriate query method.

    Raises:
        TypeError: If s is not a slice.
        ValueError: If slice step is not None or 1.
    """
    if not isinstance(s, slice):
        raise TypeError(
            f"Timelog indices must be slices, not {type(s).__name__}; "
            "use .at(ts) or .point(ts) for single-timestamp queries"
        )

    # Reject non-int steps; bool/float are rejected even if == 1.
    if s.step is not None:
        if isinstance(s.step, bool) or not isinstance(s.step, int) or s.step != 1:
            raise ValueError(f"Timelog slice step must be None or 1, not {s.step!r}")

    start = s.start
    stop = s.stop

    if start is None and stop is None:
        return log.all()

    if start is None:
        return log.until(_coerce_ts(stop))

    if stop is None:
        return log.since(_coerce_ts(start))

    t1 = _coerce_ts(start)
    t2 = _coerce_ts(stop)
    if t1 > t2:
        # Sequence semantics: lst[10:1] == [], and the engine's own
        # convention says "empty range: t1 >= t2". Explicit range()/delete()
        # calls still raise on reversed bounds; the slice OPERATOR follows
        # Python container instincts (e.g. a wall clock stepping backwards
        # in a now-window loop should not blow up a monitoring endpoint).
        return log.range(t1, t1)
    return log.range(t1, t2)
