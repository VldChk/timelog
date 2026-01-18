"""
Timelog: Time-indexed storage engine for Python.

This module provides the Timelog class for storing and querying
time-indexed (timestamp, object) records with:

- Sub-millisecond timestamp resolution (s/ms/us/ns)
- Fast range queries: [t1, t2), since(t), until(t)
- Time-based eviction: delete_before(cutoff)
- Snapshot isolation for concurrent reads
- Zero-copy bulk timestamp access via PageSpan

Example:
    >>> from timelog import Timelog
    >>>
    >>> with Timelog(maintenance="background") as log:
    ...     log.append(1000, {"event": "start"})
    ...     log.append(2000, {"event": "end"})
    ...
    ...     for ts, obj in log[1000:]:
    ...         print(ts, obj)
    1000 {'event': 'start'}
    2000 {'event': 'end'}

Thread Safety:
    Timelog instances are NOT thread-safe. Use external locks or
    separate instances per thread.

Resource Management:
    Call close() or use the context manager to release resources.
    Note: close() may leave unflushed objects in sealed memruns
    unreachable unless flush() or background maintenance ran first.
    For guaranteed cleanup, use maintenance="background" or call
    flush() before close().
"""

from __future__ import annotations

try:
    from importlib.metadata import version as _pkg_version

    __version__ = _pkg_version("timelog")
except Exception:
    __version__ = "0+unknown"

from typing import Iterator

# Re-export from extension with clear error if not available
try:
    from timelog._timelog import (
        TimelogError,
        TimelogBusyError,
        TimelogIter,
        PageSpan,
        PageSpanIter,
        PageSpanObjectsView,
    )
    from timelog._timelog import Timelog as _CTimelog
except ImportError as e:
    raise ImportError(
        "timelog extension module not found. "
        "Ensure the package is properly installed."
    ) from e

# Import helpers
from timelog._api import _coerce_ts, _slice_to_iter

# Type aliases
Record = tuple[int, object]
RecordIter = Iterator[Record]
RecordBatch = list[Record]


class Timelog(_CTimelog):
    """
    Time-indexed multimap for (timestamp, object) records.

    A Timelog stores records indexed by timestamp with support for:

    - Fast time-range queries using half-open intervals [t1, t2)
    - Python slicing syntax: log[t1:t2], log[t1:], log[:t2]
    - Time-based eviction: delete_before(cutoff)
    - Out-of-order ingestion with LSM-style compaction
    - Snapshot isolation for concurrent reads
    - Zero-copy bulk timestamp access via page_spans()

    Thread Safety:
        NOT thread-safe. Access from multiple threads requires external
        synchronization. Consistent with sqlite3.Connection semantics.

    Warning:
        close() may leave unflushed objects unreachable if sealed memruns
        exist. Call flush() before close(), or use maintenance="background"
        to ensure all objects are properly released.

    Example:
        >>> with Timelog(time_unit="ms") as log:
        ...     log.append(1000, {"event": "start"})
        ...     log.extend([(2000, "middle"), (3000, "end")])
        ...
        ...     # Slicing syntax for range queries
        ...     for ts, obj in log[1000:3000]:
        ...         print(ts, obj)

    Args:
        time_unit: Timestamp resolution. One of "s", "ms", "us", "ns".
            Default: "ms" (milliseconds).
        maintenance: Background maintenance mode. "disabled" for manual
            control, "background" for automatic. Default: "disabled".
        memtable_max_bytes: Maximum bytes before memtable seals (default ~1MB).
        target_page_bytes: Target size for storage pages (default ~64KB).
        sealed_max_runs: Max sealed memruns before backpressure (default 4).
        drain_batch_limit: Objects to drain per operation (0=unlimited).
        busy_policy: How to handle backpressure.
            "raise": Raise TimelogBusyError (record still inserted).
            "silent": Silently continue (record inserted).
            "flush": Auto-flush then continue (record inserted).

    Raises:
        ValueError: Invalid configuration parameter.
        MemoryError: Allocation failure during open.

    See Also:
        TimelogIter: Iterator for query results.
        PageSpan: Zero-copy timestamp view.
    """

    __slots__ = ()

    def __iter__(self) -> TimelogIter:
        """
        Return an iterator over all records.

        Equivalent to calling self.all().

        Returns:
            TimelogIter yielding (timestamp, object) tuples.

        Example:
            >>> for ts, obj in log:
            ...     print(ts, obj)
        """
        return self.all()

    def __getitem__(self, s: slice) -> TimelogIter:
        """
        Return an iterator for a time range using slice syntax.

        Supported patterns:
            log[t1:t2] -> records in [t1, t2)
            log[t1:]   -> records with ts >= t1
            log[:t2]   -> records with ts < t2
            log[:]     -> all records

        Note that timestamps are DATA VALUES, not indices. Negative
        timestamps are valid data, not reverse indexing.

        Args:
            s: A slice object. Step must be None or 1.

        Returns:
            TimelogIter for the specified range.

        Raises:
            TypeError: If s is not a slice. Use .at(ts) or .point(ts)
                for single-timestamp queries.
            ValueError: If slice step is not None or 1.

        Example:
            >>> # Get records in [1000, 2000)
            >>> for ts, obj in log[1000:2000]:
            ...     print(ts, obj)
            >>>
            >>> # Get all records from timestamp 5000 onwards
            >>> recent = list(log[5000:])
        """
        return _slice_to_iter(self, s)

    def at(self, ts: int) -> TimelogIter:
        """
        Return an iterator for records at exact timestamp ts.

        This is an alias for point(ts), provided for readability.

        Args:
            ts: The exact timestamp to query.

        Returns:
            TimelogIter yielding all records with timestamp == ts.
            May yield multiple records if duplicates exist.

        Example:
            >>> # Get all records at timestamp 1000
            >>> for _, obj in log.at(1000):
            ...     print(obj)
        """
        return self.point(_coerce_ts(ts))


__all__ = [
    # Primary class
    "Timelog",
    # Exceptions
    "TimelogError",
    "TimelogBusyError",
    # Iterator types
    "TimelogIter",
    # PageSpan types
    "PageSpan",
    "PageSpanIter",
    "PageSpanObjectsView",
    # Type aliases
    "Record",
    "RecordIter",
    "RecordBatch",
    # Version
    "__version__",
]
