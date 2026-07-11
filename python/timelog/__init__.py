"""Timelog: in-memory time-indexed storage engine for Python.

Stores (timestamp, object) records with fast range queries, snapshot
isolation, and automatic background compaction. See the ``Timelog`` class
for full API documentation.

Example::

    >>> from timelog import Timelog
    >>> log = Timelog()
    >>> log.append("hello")           # auto-timestamp
    >>> log[1000] = "explicit ts"     # dict-style insert
    >>> for ts, obj in log[1000:]:
    ...     print(ts, obj)
    >>> log.close()
"""

from __future__ import annotations

from importlib import metadata as _importlib_metadata
from itertools import islice as _islice
from pathlib import Path as _Path
from typing import Iterator
import tomllib as _tomllib

# Export consumption chunk: ~5ms of np.fromiter/dict.update work per chunk so
# a large export cannot monopolize the GIL for its whole duration (a monolithic
# fromiter/dict(it) is one uninterruptible C call; measured 71-72ms stall at 1M
# rows, at identical throughput). Chunked, to_numpy's gap stays ~5-7ms;
# to_dict additionally pays one table-sized dict rehash inside update() that
# grows with the result (18ms @1M, 41ms @4M rows) — unfixable in pure Python
# (dicts cannot be presized), still 3-5x better than monolithic.
_EXPORT_CHUNK = 65536


def _resolve_local_version() -> str | None:
    """Resolve version from the source tree when imported via PYTHONPATH."""
    try:
        project_root = _Path(__file__).resolve().parents[2]
        pyproject = project_root / "pyproject.toml"
        data = _tomllib.loads(pyproject.read_text(encoding="utf-8"))
        version = data.get("project", {}).get("version")
    except (OSError, IndexError, TypeError, _tomllib.TOMLDecodeError):
        return None
    return version if isinstance(version, str) and version else None


def _resolve_version() -> str:
    """Resolve package version across distribution name variants."""
    local_version = _resolve_local_version()
    if local_version is not None:
        return local_version

    package_not_found = _importlib_metadata.PackageNotFoundError
    for dist_name in ("timelog-lib", "timelog"):
        try:
            return _importlib_metadata.version(dist_name)
        except package_not_found:
            continue
    return "0+unknown"


__version__ = _resolve_version()

try:
    from timelog._timelog import (  # noqa: E402
        TimelogError,
        TimelogBusyError,
        TimelogIter,
        PageSpan,
        PageSpanIter,
        PageSpanObjectsView,
    )
    from timelog._timelog import Timelog as _CTimelog  # noqa: E402
except ImportError as e:
    raise ImportError(
        "timelog extension module not found. "
        "Ensure the package is properly installed."
    ) from e

from timelog._api import _coerce_ts, _slice_to_iter, TL_TS_MIN, TL_TS_MAX  # noqa: E402

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
        Single-writer API contract. Multiple-thread *writes* on a single
        Timelog instance require external serialization. Lifecycle calls
        (``close()``, ``reopen()``, and ``configure()``) must also be externally
        serialized against all other users of the same instance. Iterators are
        snapshot-based and safe for concurrent reads from independent threads.

        Supported builds:
            * Regular CPython 3.12-3.14 (single interpreter).
            * Isolated subinterpreters with per-interpreter GIL (3.12+).
            * Free-threaded CPython 3.14t (Py_GIL_DISABLED=1).

    Warning:
        ``close()`` discards all records; Timelog is in-memory and nothing
        survives close. ``flush()`` materializes pending writes for zero-copy
        ``views()`` while the log is open. Call ``close()`` for deterministic
        cleanup; release active iterators, PageSpans, object views, and
        memoryview exports before closing because they hold snapshot pins.
        If explicit ``close()`` is omitted, collection auto-closes the log
        as a best-effort cleanup path.

    Example::

        >>> log = Timelog(time_unit="ms")
        >>> log.append({"event": "start"})
        >>> log[2000] = {"event": "end"}
        >>> for ts, obj in log[1000:]:
        ...     print(ts, obj)
        >>> log.close()

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
        max_delta_segments: L0 segment bound (0 = engine default, 8). The
            tiering<->leveling dial: when L0 reaches this many segments,
            compaction collapses them into L1. Lower = eager leveling (faster
            reads, more compaction CPU/write-amp); higher = lazy tiering
            (cheaper writes, higher read fan-in). Raising it above the L0 count
            your workload accumulates stops the *automatic* trigger -- a
            delete-free workload that never calls compact() then grows
            read-amplification unbounded. See docs/configuration.md for the
            measured trade-off curve and guidance.
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

    __slots__ = ("_mostly_ordered_default", "_extend_skipped")

    @property
    def _min_ts(self):
        # Single source of truth lives in C (self._min_ts_floor()); this
        # read-only property keeps _check_min_ts/extend/slicing readers working.
        return _CTimelog._min_ts_floor(self)

    def __init__(self, *, min_ts=None, mostly_ordered_default=True, **kwargs):
        if not isinstance(mostly_ordered_default, bool):
            raise TypeError("mostly_ordered_default must be bool")
        min_ts_val = None if min_ts is None else _coerce_ts(min_ts)
        super().__init__(**kwargs)
        self._mostly_ordered_default = mostly_ordered_default
        self._extend_skipped = 0
        _CTimelog._set_min_ts_floor(self, min_ts_val)
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
        self._extend_skipped = 0
        _CTimelog._set_min_ts_floor(self, min_ts_val)
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

    # These underscore helpers are not subclass extension points. Write paths
    # dispatch through Timelog.* explicitly so append(), extend(), and
    # __setitem__ share the same C-owned min_ts floor semantics.

    def _check_min_ts(self, ts: int) -> None:
        """Raise ValueError if ts is below the min_ts guard."""
        min_ts = _CTimelog._min_ts_floor(self)
        if min_ts is not None and ts < min_ts:
            raise ValueError(
                f"timestamp {ts} is below min_ts boundary ({min_ts})"
            )

    def _coerce_and_guard(self, ts):
        """Coerce ts and apply min_ts guard."""
        ts = _coerce_ts(ts)
        Timelog._check_min_ts(self, ts)
        return ts

    def _filtered_pairs(self, iterable):
        """Yield (ts, obj) pairs, skipping type/overflow errors but raising on non-pairs and min_ts.

        Skipped rows are reported with a RuntimeWarning after the stream is
        consumed — silent partial ingest in a storage engine is data loss.

        The min_ts floor is snapshotted ONCE per call: it lives in C and is
        immutable while the instance is open (set only at init/reopen), and
        a per-item C method call cost ~13% on the 10k-pair extend path
        (v1.3 perf lab regression gate).
        """
        floor = _CTimelog._min_ts_floor(self)
        coerce = _coerce_ts
        skipped = 0
        for item in iterable:
            try:
                ts, obj = item
            except (TypeError, ValueError) as exc:
                raise ValueError("extend() expects (ts, obj) pairs") from exc
            try:
                ts = coerce(ts)
            except (TypeError, OverflowError):
                skipped += 1
                continue
            if floor is not None and ts < floor:
                raise ValueError(
                    f"timestamp {ts} is below min_ts boundary ({floor})"
                )
            yield (ts, obj)
        if skipped:
            self._extend_skipped += skipped
            import warnings
            warnings.warn(
                f"extend() skipped {skipped} record(s) with invalid "
                "timestamps (insert_on_error=True); pass "
                "insert_on_error=False to validate the whole batch instead",
                RuntimeWarning, stacklevel=3)

    # ------------------------------------------------------------------
    # Write path
    # ------------------------------------------------------------------

    # append() is implemented entirely in C (METH_FASTCALL|METH_KEYWORDS):
    # 3 signatures + wall-clock auto-timestamp + _coerce_ts parity (bool reject)
    # + the min_ts floor guard (self._min_ts_floor in C). No Python override.

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
                    ts = Timelog._coerce_and_guard(self, ts_val)
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
                floor = _CTimelog._min_ts_floor(self)
                coerce = _coerce_ts
                skipped = 0
                for ts_val, obj in zip(ts_or_iterable, objects, strict=True):
                    try:
                        ts = coerce(ts_val)
                    except (TypeError, OverflowError):
                        skipped += 1
                        continue
                    if floor is not None and ts < floor:
                        raise ValueError(
                            f"timestamp {ts} is below min_ts boundary ({floor})"
                        )
                    yield (ts, obj)
                if skipped:
                    self._extend_skipped += skipped
                    import warnings
                    warnings.warn(
                        f"extend() skipped {skipped} record(s) with invalid "
                        "timestamps (insert_on_error=True); pass "
                        "insert_on_error=False to validate the whole batch "
                        "instead", RuntimeWarning, stacklevel=3)

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
                ts = Timelog._coerce_and_guard(self, ts_val)
                normalized.append((ts, obj))
            super().extend(normalized, mostly_ordered=mostly_ordered)
            return

        # insert_on_error=True: streaming with skip
        super().extend(Timelog._filtered_pairs(self, ts_or_iterable),
                       mostly_ordered=mostly_ordered)

    def __setitem__(self, ts, obj):
        """Insert a record: ``log[ts] = obj``."""
        ts = Timelog._coerce_and_guard(self, ts)
        super().append(ts, obj)

    # ------------------------------------------------------------------
    # Size
    # ------------------------------------------------------------------

    def __len__(self):
        """Return tombstone-aware record count (takes a fresh snapshot each call)."""
        s = self.stats()
        return int(s["storage"]["records_estimate"])

    def __contains__(self, ts) -> bool:
        """Return True if any record exists at exactly ``ts`` (O(log n)).

        Without this, Python's fallback would full-scan ``(ts, obj)`` tuples
        and silently answer False for timestamps that exist.
        """
        it = self.point(_coerce_ts(ts))
        try:
            return len(it) > 0          # precomputed count; nothing consumed
        finally:
            it.close()

    def __reversed__(self):
        """Descending iteration is not supported by the LSM read path."""
        raise TypeError(
            "Timelog does not support reversed(); iterate forward over a "
            "bounded window instead, e.g. list(log[t1:t2]) and reverse the "
            "materialized list, or walk back with prev_ts(ts)"
        )

    def __repr__(self) -> str:
        try:
            if self.closed:
                return f"<{type(self).__name__} closed>"
            s = self.stats()["storage"]
            n = int(s["records_estimate"])
            lo, hi = s["min_ts"], s["max_ts"]
            span = f" [{lo}..{hi}]" if (lo is not None and hi is not None) else ""
            return (f"<{type(self).__name__} len~{n} "
                    f"time_unit={self.time_unit!r}{span}>")
        except Exception:
            return object.__repr__(self)

    @property
    def extend_skipped(self) -> int:
        """Total records dropped by extend(insert_on_error=True) skips.

        Python's warning machinery deduplicates the RuntimeWarning per call
        site, so a long-running ingest loop sees it once; this counter (also
        in ``stats()['operational']['extend_skipped']``) makes recurring
        drops monitorable.
        """
        return self._extend_skipped

    @property
    def min_ts_floor(self):
        """The configured ``min_ts`` retention floor, or None.

        Distinct from ``min_ts()`` (the smallest timestamp currently in the
        data). Writes below the floor raise ValueError.
        """
        return _CTimelog._min_ts_floor(self)

    def stats(self):
        """Return engine statistics with facade enrichments.

        On top of the C engine's counters: empty-log sentinel bounds are
        mapped to None, ``operational.busy_events`` counts write-path
        backpressure under every busy_policy, and ``config`` echoes the
        effective instance configuration for dashboards/alerting.
        """
        s = super().stats()
        storage = s["storage"]
        if storage["min_ts"] == TL_TS_MAX and storage["max_ts"] == TL_TS_MIN:
            storage["min_ts"] = None    # empty-log sentinels
            storage["max_ts"] = None
        s["operational"]["busy_events"] = self.busy_events
        s["operational"]["extend_skipped"] = self._extend_skipped
        s["config"] = {
            "time_unit": self.time_unit,
            "maintenance": self.maintenance_mode,
            "busy_policy": self.busy_policy,
            "min_ts": _CTimelog._min_ts_floor(self),
            "mostly_ordered_default": self._mostly_ordered_default,
        }
        return s

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

    # ------------------------------------------------------------------
    # Export
    # ------------------------------------------------------------------

    def to_dict(self, t1=None, t2=None):
        """Export records as ``{timestamp: object}``.

        Bounds behave exactly like ``log[t1:t2]`` slicing: ``None`` = open
        end, half-open ``[t1, t2)``, reversed bounds yield ``{}``. The export
        is snapshot-isolated and holds a reader pin for its duration
        (``close()`` raises until it finishes). Values are returned as-is.

        Duplicate timestamps collapse to ONE value: the last in iteration
        order. Which record wins is deterministic for a given storage state
        but otherwise UNSPECIFIED — out-of-order ingestion and background
        compaction can reorder equal-timestamp records. If you need a
        specific winner, avoid duplicate timestamps or pick explicitly from
        ``point(ts)``.
        """
        if _EXPORT_CHUNK < 1:
            raise ValueError("_EXPORT_CHUNK must be >= 1")
        it = _slice_to_iter(self, slice(t1, t2))
        try:
            d = {}
            while len(it):
                d.update(_islice(it, _EXPORT_CHUNK))
            return d
        finally:
            it.close()

    def to_numpy(self, t1=None, t2=None, *, dtype=None):
        """Export records as a ``(timestamps, values)`` pair of numpy arrays.

        Returns two fresh, contiguous 1-D arrays: ``timestamps`` is int64;
        ``values`` is float64 unless ``dtype`` overrides it. ``dtype`` must
        be a scalar numeric dtype (integer or float kind); conversion
        semantics within it are numpy's (e.g. ``dtype=np.int64`` truncates
        floats). Value conversion follows numpy: ``bool`` becomes 1.0/0.0,
        ``None`` becomes NaN under float dtypes (TypeError under integer
        dtypes), and ints beyond 2**53 lose precision under the default —
        pass ``dtype=np.int64`` for exact big-int payloads. A non-convertible
        value raises its original exception with the failing row index
        attached as a note. Shape-compatible with ``bulk_append``.

        Bounds behave exactly like ``log[t1:t2]`` slicing; a record at
        ``TL_TS_MAX`` is included only when ``t2`` is None. Empty ranges
        return empty arrays. Snapshot-isolated; holds a reader pin for the
        duration (``close()`` raises until it finishes). Duplicate
        timestamps are all exported (multimap). numpy is imported lazily —
        ``to_dict`` works without it.
        """
        import numpy as np

        value_dtype = np.dtype(np.float64 if dtype is None else dtype)
        if value_dtype.kind not in "iuf":
            raise TypeError(
                f"to_numpy() dtype must be a scalar numeric dtype "
                f"(integer or float), not {value_dtype!r}"
            )
        pair_dtype = np.dtype([("ts", np.int64), ("value", value_dtype)])
        if _EXPORT_CHUNK < 1:
            raise ValueError("_EXPORT_CHUNK must be >= 1")
        it = _slice_to_iter(self, slice(t1, t2))
        try:
            n = len(it)
            timestamps = np.empty(n, np.int64)
            values = np.empty(n, value_dtype)
            pos = 0
            try:
                while pos < n:
                    k = min(_EXPORT_CHUNK, n - pos)
                    chunk = np.fromiter(_islice(it, k), dtype=pair_dtype, count=k)
                    timestamps[pos:pos + k] = chunk["ts"]
                    values[pos:pos + k] = chunk["value"]
                    pos += k
            except Exception as exc:
                # Any failure while filling gets the row note, whatever its
                # type (a custom __float__ can raise anything; value
                # conversion is the usual cause but not the only one, so the
                # note names the row without presuming why). The guard skips
                # pre-consumption errors (row -1) and closed iterators —
                # engine errors and exhaustion auto-close, so a row label
                # cannot mislabel those failures.
                row = n - len(it) - 1
                if row >= 0 and not it.closed:
                    exc.add_note(f"to_numpy(): raised at row {row} of {n}")
                raise
            return timestamps, values
        finally:
            it.close()


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
