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
    Single-writer model. All write/maintenance calls must be externally
    serialized. Snapshot-based iterators are safe for concurrent reads,
    but the Timelog object is not generally thread-safe and some methods
    (flush/compact/close) release the GIL. The binding serializes core
    calls to avoid concurrent use during GIL-released operations, but
    this is not a full thread-safety guarantee. Use external coordination
    if the same instance can be touched from multiple threads. This
    binding requires the CPython GIL and is not supported on
    free-threaded/no-GIL Python builds.

Resource Management:
    Call close() or use the context manager to release resources.
    Note: close() will drop any unflushed records (data loss) but will
    release all Python objects still owned by the engine. For data safety,
    call flush() before close().
    In maintenance="disabled" mode, use maint_step() to run compaction
    manually when needed.
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
    - Snapshot diagnostics via stats(), validate(), min_ts/max_ts, next_ts/prev_ts

    Thread Safety:
        Single-writer. Access from multiple threads requires external
        synchronization. Iterators are snapshot-based and safe for
        concurrent reads, but the Timelog object is not generally
        thread-safe because some methods release the GIL. The binding
        serializes core calls during GIL-released operations, but this
        does not make the API fully thread-safe. This binding requires
        the CPython GIL and is not supported on free-threaded builds.

    Warning:
        close() drops any unflushed records (data loss) but releases all
        Python objects still owned by the engine. Call flush() before close()
        if you need to persist all records.

    Manual maintenance:
        In maintenance="disabled" mode, use maint_step() to perform flush/
        compaction work explicitly. compact() only requests work.

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
            control, "background" for automatic. Default: "background".
        memtable_max_bytes: Maximum bytes before memtable seals (0 = default).
        target_page_bytes: Target size for storage pages (0 = default).
        sealed_max_runs: Max sealed memruns before backpressure (0 = default).
        drain_batch_limit: Objects to drain per operation (0=unlimited).
        busy_policy: How to handle write backpressure (TL_EBUSY) for
            append/delete operations.
            "raise": Raise TimelogBusyError (record still inserted).
            "silent": Silently continue (record inserted).
            "flush": Auto-flush then continue (record inserted).
            Note: TL_EBUSY can also occur for flush/maintenance publish
            retries; those are safe to retry and are not controlled by
            busy_policy.
        ooo_budget_bytes: OOO budget before early seal (0 = default).
        sealed_wait_ms: Backpressure wait timeout in background mode
            (0 = immediate TL_EBUSY).
        maintenance_wakeup_ms: Worker wake interval (0 = default).
        max_delta_segments: L0 segment bound (0 = default).
        window_size: L1 window size (0 = default based on time_unit).
        window_origin: Window origin (default 0).
        delete_debt_threshold: Ratio [0,1] to trigger delete-debt compaction.
        compaction_target_bytes: Optional compaction output cap (0 = unlimited).
        max_compaction_inputs: Optional cap on inputs per compaction (0 = unlimited).
        max_compaction_windows: Optional cap on windows per compaction (0 = unlimited).
        adaptive_target_records: Enable adaptive segmentation (0 = disabled).
        adaptive_min_window: Minimum window size.
        adaptive_max_window: Maximum window size.
        adaptive_hysteresis_pct: Minimum % change to apply.
        adaptive_window_quantum: Snap window to multiples (0 = no snapping).
        adaptive_alpha: EWMA smoothing factor [0.0, 1.0].
        adaptive_warmup_flushes: Flushes before adapting.
        adaptive_stale_flushes: Flushes without update = stale (0 = infinite).
        adaptive_failure_backoff_threshold: Failures before backoff.
        adaptive_failure_backoff_pct: % to grow window on backoff.

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
