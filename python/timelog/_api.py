"""
Internal helper functions for the Timelog facade.

This module is private API. Do not import directly.
"""

from __future__ import annotations

import operator
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from timelog import Timelog, TimelogIter


def _coerce_ts(x: object) -> int:
    """
    Coerce x to an integer timestamp.

    Uses operator.index() to support numpy.int64 and similar types
    that implement __index__.

    Args:
        x: Value to coerce to integer.

    Returns:
        Integer timestamp value.

    Raises:
        TypeError: If x is bool (to prevent True -> 1 accidents)
            or if x doesn't support __index__.
    """
    if isinstance(x, bool):
        raise TypeError("timestamp must be int (bool not allowed)")
    return operator.index(x)


def _slice_to_iter(log: Timelog, s: slice) -> TimelogIter:
    """
    Convert a slice to the appropriate iterator method call.

    Args:
        log: The Timelog instance.
        s: Slice object from __getitem__.

    Returns:
        TimelogIter for the specified range.

    Raises:
        TypeError: If s is not a slice.
        ValueError: If slice step is not None or 1.
    """
    if not isinstance(s, slice):
        raise TypeError(
            f"Timelog indices must be slices, not {type(s).__name__}; "
            "use .at(ts) or .point(ts) for single-timestamp queries"
        )

    # Reject step values that aren't None or the integer 1.
    # Explicitly reject bool (True == 1) and float (1.0 == 1) for consistency
    # with bool rejection in _coerce_ts.
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
