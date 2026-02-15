"""Timelog: in-memory time-indexed storage engine for Python.

Stores (timestamp, object) records with fast range queries, snapshot
isolation, and automatic background compaction. See the ``Timelog`` class
for full API documentation.

Example::

    >>> from timelog import Timelog
    >>> with Timelog() as log:
    ...     log.append("hello")           # auto-timestamp
    ...     log[1000] = "explicit ts"     # dict-style insert
    ...     for ts, obj in log[1000:]:
    ...         print(ts, obj)
"""

from __future__ import annotations

try:
    from importlib.metadata import version as _pkg_version

    __version__ = _pkg_version("timelog")
except Exception:
    __version__ = "0+unknown"

from typing import Iterator

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

from timelog._api import _coerce_ts, _slice_to_iter, _now_ts, TL_TS_MIN, TL_TS_MAX

Record = tuple[int, object]
RecordIter = Iterator[Record]
RecordBatch = list[Record]

_SENTINEL = object()


class Timelog(_CTimelog):
    """Time-indexed multimap for (timestamp, object) records.

    Supports slicing (``log[t1:t2]``), dict-style access (``log[ts] = obj``),
    auto-timestamped append, time-based eviction, out-of-order ingestion,
    snapshot-isolated reads, and zero-copy bulk access via ``views()``.

    Thread Safety:
        Single-writer. Multiple-thread access requires external
        synchronization. Iterators are snapshot-based and safe for
        concurrent reads. Requires the CPython GIL (no free-threaded
        builds).

    Warning:
        ``close()`` drops unflushed records. Call ``flush()`` first to
        materialize pending writes. Use the context manager for
        deterministic cleanup.

    Example::

        >>> with Timelog(time_unit="ms") as log:
        ...     log.append({"event": "start"})
        ...     log[2000] = {"event": "end"}
        ...     for ts, obj in log[1000:]:
        ...         print(ts, obj)

    Args (Essential):
        time_unit: Timestamp resolution. One of "s", "ms", "us", "ns".
            Default: "ms" (milliseconds).
        maintenance: Background maintenance mode. "disabled" for manual
            control, "background" for automatic. Default: "background".
        min_ts: If provided, sets a persistent lower-bound guard that
            rejects inserts below this timestamp (raises ValueError).
            Also deletes any existing records below the threshold on open.
        mostly_ordered_default: Default value for extend(mostly_ordered=...).
            If None is passed to extend(), this value is used.

    Args (Tuning):
        busy_policy: How to handle write backpressure (TL_EBUSY) for
            append/delete operations.
            "raise": Raise TimelogBusyError (record still inserted).
            "silent": Silently continue (record inserted).
            "flush": Auto-flush then continue (record inserted).
            Note: TL_EBUSY can also occur for flush/maintenance publish
            retries; those are safe to retry and are not controlled by
            busy_policy.
        memtable_max_bytes: Maximum bytes before memtable seals (0 = engine default).
        target_page_bytes: Target size for storage pages (0 = engine default).
        sealed_max_runs: Max sealed memruns before backpressure (0 = engine default).
        ooo_budget_bytes: OOO budget before early seal (0 = engine default).
        sealed_wait_ms: Backpressure wait timeout in background mode
            (0 = immediate TL_EBUSY).
        drain_batch_limit: Objects to drain per operation (0 = unlimited).

    Args (Advanced):
        maintenance_wakeup_ms: Worker wake interval (0 = engine default).
        max_delta_segments: L0 segment bound (0 = engine default).
        window_size: L1 window size (0 = engine default based on time_unit).
        window_origin: Window origin (default 0).
        delete_debt_threshold: Ratio [0.0, 1.0] to trigger delete-debt
            compaction. 0.0 = disabled (no delete-debt compaction).
        compaction: Dict of compaction settings. Keys:
            "target_bytes" (int): Output size cap (0 = unlimited).
            "max_inputs" (int): Max inputs per compaction (0 = unlimited).
            "max_windows" (int): Max windows per compaction (0 = unlimited).
            Example: ``compaction={"target_bytes": 1048576, "max_inputs": 4}``
        adaptive: Dict of adaptive segmentation settings, or None to
            disable (default). When provided, enables adaptive window
            sizing. Keys:
            "target_records" (int): Target records per segment. Required
                to enable adaptive mode (0 = disabled).
            "min_window" (int): Minimum window size.
            "max_window" (int): Maximum window size.
            "hysteresis_pct" (int): Minimum % change to apply.
            "window_quantum" (int): Snap window to multiples (0 = none).
            "alpha" (float): EWMA smoothing factor [0.0, 1.0].
            "warmup_flushes" (int): Flushes before adapting.
            "stale_flushes" (int): Flushes without update = stale
                (0 = infinite).
            "failure_backoff_threshold" (int): Failures before backoff.
            "failure_backoff_pct" (int): % to grow window on backoff.
            Example: ``adaptive={"target_records": 10000, "alpha": 0.3}``

    Args (Deprecated -- use ``adaptive`` and ``compaction`` dicts instead):
        compaction_target_bytes: Use ``compaction={"target_bytes": ...}``.
        max_compaction_inputs: Use ``compaction={"max_inputs": ...}``.
        max_compaction_windows: Use ``compaction={"max_windows": ...}``.
        adaptive_target_records: Use ``adaptive={"target_records": ...}``.
        adaptive_min_window: Use ``adaptive={"min_window": ...}``.
        adaptive_max_window: Use ``adaptive={"max_window": ...}``.
        adaptive_hysteresis_pct: Use ``adaptive={"hysteresis_pct": ...}``.
        adaptive_window_quantum: Use ``adaptive={"window_quantum": ...}``.
        adaptive_alpha: Use ``adaptive={"alpha": ...}``.
        adaptive_warmup_flushes: Use ``adaptive={"warmup_flushes": ...}``.
        adaptive_stale_flushes: Use ``adaptive={"stale_flushes": ...}``.
        adaptive_failure_backoff_threshold: Use
            ``adaptive={"failure_backoff_threshold": ...}``.
        adaptive_failure_backoff_pct: Use
            ``adaptive={"failure_backoff_pct": ...}``.

    Zero semantics:
        For most numeric parameters, 0 means "use engine default".
        Exceptions:
        - ``delete_debt_threshold``: 0.0 means disabled.
        - ``adaptive["target_records"]``: 0 means disabled.
        - ``adaptive``: None or omitted means disabled.

    Raises:
        ValueError: Invalid configuration parameter or unknown dict key.
        TypeError: ``adaptive`` or ``compaction`` is not a dict.
        MemoryError: Allocation failure during open.

    See Also:
        TimelogIter: Iterator for query results.
        PageSpan: Zero-copy timestamp view.
    """

    __slots__ = ("_min_ts", "_mostly_ordered_default")

    def __init__(self, *, min_ts=None, mostly_ordered_default=True, **kwargs):
        if not isinstance(mostly_ordered_default, bool):
            raise TypeError("mostly_ordered_default must be bool")
        min_ts_val = None if min_ts is None else _coerce_ts(min_ts)
        super().__init__(**kwargs)
        self._mostly_ordered_default = mostly_ordered_default
        self._min_ts = min_ts_val
        if min_ts_val is not None:
            super().delete_before(min_ts_val)

    def reopen(self, *, min_ts=_SENTINEL, mostly_ordered_default=_SENTINEL, **kwargs):
        """Reopen a closed Timelog with new configuration."""
        if not self.closed:
            raise TimelogError("Timelog must be closed to reopen")
        if min_ts is _SENTINEL:
            min_ts_val = self._min_ts
        else:
            min_ts_val = None if min_ts is None else _coerce_ts(min_ts)
        if mostly_ordered_default is _SENTINEL:
            mostly_default = self._mostly_ordered_default
        else:
            if not isinstance(mostly_ordered_default, bool):
                raise TypeError("mostly_ordered_default must be bool")
            mostly_default = mostly_ordered_default

        super().__init__(**kwargs)
        self._mostly_ordered_default = mostly_default
        self._min_ts = min_ts_val
        if min_ts_val is not None:
            super().delete_before(min_ts_val)

    def configure(self, *, min_ts=_SENTINEL, mostly_ordered_default=_SENTINEL, **kwargs):
        """Alias for reopen(); requires closed state."""
        return self.reopen(
            min_ts=min_ts,
            mostly_ordered_default=mostly_ordered_default,
            **kwargs,
        )

    @classmethod
    def for_streaming(cls, **overrides) -> "Timelog":
        """Create a Timelog for streaming writes (background maintenance, default sizing)."""
        defaults = dict(
            maintenance="background",
            busy_policy="flush",
        )
        defaults.update(overrides)
        return cls(**defaults)

    @classmethod
    def for_bulk_ingest(cls, **overrides) -> "Timelog":
        """Create a Timelog for bulk ingestion (no background maintenance, large memtable).

        Call ``flush()`` after loading to materialize pending writes.
        """
        defaults = dict(
            maintenance="disabled",
            busy_policy="flush",
            memtable_max_bytes=16 * 1024 * 1024,  # 16 MiB
        )
        defaults.update(overrides)
        return cls(**defaults)

    @classmethod
    def for_low_latency(cls, **overrides) -> "Timelog":
        """Create a Timelog for low-latency reads (small memtable, immediate backpressure)."""
        defaults = dict(
            maintenance="background",
            busy_policy="raise",
            memtable_max_bytes=256 * 1024,  # 256 KiB
            sealed_wait_ms=0,
        )
        defaults.update(overrides)
        return cls(**defaults)

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------

    def _check_min_ts(self, ts: int) -> None:
        """Raise ValueError if ts is below the min_ts guard."""
        if self._min_ts is not None and ts < self._min_ts:
            raise ValueError(
                f"timestamp {ts} is below min_ts boundary ({self._min_ts})"
            )

    def _coerce_and_guard(self, ts):
        """Coerce ts and apply min_ts guard."""
        ts = _coerce_ts(ts)
        self._check_min_ts(ts)
        return ts

    def _filtered_pairs(self, iterable):
        """Yield (ts, obj) pairs, skipping type/overflow errors but raising on non-pairs and min_ts."""
        for item in iterable:
            try:
                ts, obj = item
            except (TypeError, ValueError) as exc:
                raise ValueError("extend() expects (ts, obj) pairs") from exc
            try:
                ts = self._coerce_and_guard(ts)
            except (TypeError, OverflowError):
                continue
            yield (ts, obj)

    # ------------------------------------------------------------------
    # Write path
    # ------------------------------------------------------------------

    def append(self, obj_or_ts, obj_or_none=_SENTINEL, *, ts=None):
        """Append a record.

        Signatures::

            append(obj)              # auto-timestamp from wall clock
            append(obj, ts=1000)     # explicit keyword timestamp
            append(ts, obj)          # positional (legacy)

        Note:
            TimelogBusyError means the record WAS committed; do not retry.
        """
        if obj_or_none is _SENTINEL:
            # Single arg: append(obj) or append(obj, ts=X)
            obj = obj_or_ts
            if ts is None:
                ts = _now_ts(self.time_unit)
            else:
                ts = _coerce_ts(ts)
        else:
            # Two positional args: append(ts, obj) -- C-style compat
            ts = _coerce_ts(obj_or_ts)
            obj = obj_or_none
        self._check_min_ts(ts)
        super().append(ts, obj)

    def extend(self, ts_or_iterable, objects=None, *,
               mostly_ordered=None, insert_on_error=True):
        """Append multiple records.

        Signatures::

            extend([(ts, obj), ...])         # list of pairs
            extend(timestamps, objects)      # dual-list form
            extend(generator)                # lazy generator

        Args:
            insert_on_error: If True (default), skip invalid timestamps
                but raise on structural errors. If False, pre-validate
                all records before inserting any (generators not supported).

        Note:
            TimelogBusyError means the records WERE committed; do not retry.
        """
        if mostly_ordered is None:
            mostly_ordered = self._mostly_ordered_default

        if objects is not None:
            if not insert_on_error:
                if not hasattr(ts_or_iterable, '__len__') or not hasattr(objects, '__len__'):
                    raise TypeError(
                        "insert_on_error=False requires sized sequences for keys/values"
                    )
                pairs = list(zip(ts_or_iterable, objects, strict=True))
                normalized = []
                for ts_val, obj in pairs:
                    ts = self._coerce_and_guard(ts_val)
                    normalized.append((ts, obj))
                super().extend(normalized, mostly_ordered=mostly_ordered)
                return

            # insert_on_error=True: skip invalid keys
            if hasattr(ts_or_iterable, '__len__') and hasattr(objects, '__len__'):
                try:
                    if len(ts_or_iterable) != len(objects):
                        raise ValueError("timestamps and objects must have same length")
                except TypeError:
                    pass
            def gen():
                for ts_val, obj in zip(ts_or_iterable, objects, strict=True):
                    try:
                        ts = self._coerce_and_guard(ts_val)
                    except (TypeError, OverflowError):
                        continue
                    yield (ts, obj)

            super().extend(gen(), mostly_ordered=mostly_ordered)
            return

        if not insert_on_error:
            # Pre-validated mode: materialize and validate all items before insert
            if not hasattr(ts_or_iterable, '__len__'):
                raise TypeError(
                    "insert_on_error=False requires a sequence, not a generator"
                )
            items = list(ts_or_iterable)
            normalized = []
            for item in items:
                try:
                    ts_val, obj = item
                except Exception as exc:
                    raise ValueError("extend() expects (ts, obj) pairs") from exc
                ts = self._coerce_and_guard(ts_val)
                normalized.append((ts, obj))
            super().extend(normalized, mostly_ordered=mostly_ordered)
            return

        # insert_on_error=True: streaming with skip
        super().extend(self._filtered_pairs(ts_or_iterable),
                       mostly_ordered=mostly_ordered)

    def __setitem__(self, ts, obj):
        """Insert a record: ``log[ts] = obj``."""
        ts = self._coerce_and_guard(ts)
        super().append(ts, obj)

    # ------------------------------------------------------------------
    # Size
    # ------------------------------------------------------------------

    def __len__(self):
        """Return tombstone-aware record count (takes a fresh snapshot each call)."""
        s = self.stats()
        return int(s["storage"]["records_estimate"])

    # ------------------------------------------------------------------
    # Read path
    # ------------------------------------------------------------------

    def __iter__(self) -> TimelogIter:
        """Return an iterator over all records (equivalent to ``all()``)."""
        return self.all()

    def __getitem__(self, key):
        """Query by timestamp or time range.

        ::

            log[ts]    -> list of objects at exact timestamp ts
            log[t1:t2] -> TimelogIter over [t1, t2)
            log[t1:]   -> TimelogIter over ts >= t1
            log[:t2]   -> TimelogIter over ts < t2
            log[:]     -> TimelogIter over all records

        Timestamps are data values, not indices; negative values are
        valid timestamps, not reverse indexing. ``len(log[t1:t2])``
        returns remaining rows in the iterator's snapshot.

        Raises:
            ValueError: If slice step is not None or 1.
        """
        if isinstance(key, slice):
            return _slice_to_iter(self, key)
        ts = _coerce_ts(key)
        return [obj for _, obj in self.point(ts)]

    def at(self, ts: int):
        """Return list of objects at exact timestamp ts (alias for ``log[ts]``)."""
        return self[_coerce_ts(ts)]

    # ------------------------------------------------------------------
    # Delete path
    # ------------------------------------------------------------------

    def _delete_point_checked(self, ts: int) -> None:
        if ts >= TL_TS_MAX:
            raise ValueError(
                f"point delete at TL_TS_MAX ({TL_TS_MAX}) is not representable "
                "with half-open delete ranges"
            )
        super().delete_range(ts, ts + 1)

    def cutoff(self, ts):
        """Delete all records before ts (tombstone over ``[TL_TS_MIN, ts)``)."""
        super().delete_before(_coerce_ts(ts))

    def delete(self, t1, t2=None):
        """Delete records at a point (``delete(ts)``) or range (``delete(t1, t2)``).

        Raises:
            ValueError: If point delete at TL_TS_MAX (not representable as half-open).
        """
        t1 = _coerce_ts(t1)
        if t2 is None:
            self._delete_point_checked(t1)
        else:
            super().delete_range(t1, _coerce_ts(t2))

    def __delitem__(self, key):
        """Delete records: ``del log[ts]`` or ``del log[t1:t2]``.

        Raises:
            ValueError: If slice step is not None or 1, or point delete at TL_TS_MAX.
        """
        if isinstance(key, slice):
            if key.step is not None:
                if isinstance(key.step, bool) or not isinstance(key.step, int) or key.step != 1:
                    raise ValueError(f"slice step must be None or 1, not {key.step!r}")
            t1 = TL_TS_MIN if key.start is None else _coerce_ts(key.start)
            t2 = TL_TS_MAX if key.stop is None else _coerce_ts(key.stop)
            super().delete_range(t1, t2)
        else:
            ts = _coerce_ts(key)
            self._delete_point_checked(ts)

    # ------------------------------------------------------------------
    # Views (PageSpan)
    # ------------------------------------------------------------------

    def views(self, t1=None, t2=None, *, kind="segment"):
        """Return a PageSpanIter for zero-copy timestamp access.

        Call with no args for all records, or ``views(t1, t2)`` for [t1, t2).
        Reflects physical storage spans, not tombstone-filtered rows.

        Raises:
            ValueError: If only one of t1/t2 is provided.
        """
        if t1 is None and t2 is None:
            return self.page_spans(TL_TS_MIN, TL_TS_MAX, kind=kind)
        if t1 is None or t2 is None:
            raise ValueError("views() requires both t1 and t2, or neither")
        return self.page_spans(_coerce_ts(t1), _coerce_ts(t2), kind=kind)


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
