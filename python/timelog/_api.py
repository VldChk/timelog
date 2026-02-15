"""Private helpers for the Timelog facade. Do not import directly."""

from __future__ import annotations

import operator
import time
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from timelog import Timelog, TimelogIter

# Sentinel timestamps matching C TL_TS_MIN / TL_TS_MAX
TL_TS_MIN = -(2**63)      # INT64_MIN
TL_TS_MAX = 2**63 - 1     # INT64_MAX

_UNIT_DIVISORS = {"s": 10**9, "ms": 10**6, "us": 10**3, "ns": 1}


def _now_ts(time_unit: str) -> int:
    """Return current wall-clock time as an integer timestamp in the given unit."""
    return time.time_ns() // _UNIT_DIVISORS[time_unit]


def _coerce_ts(x: object) -> int:
    """Coerce x to an int64 timestamp via ``__index__``.

    Raises:
        TypeError: If x is bool or lacks ``__index__``.
        OverflowError: If value is outside signed int64 range.
    """
    if isinstance(x, bool):
        raise TypeError("timestamp must be int (bool not allowed)")
    ts = operator.index(x)
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

    return log.range(_coerce_ts(start), _coerce_ts(stop))
