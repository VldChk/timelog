# LLD-B7: Python Facade Subsystem (Public API / Ergonomics)

Date: 2026-01-16
Status: Approved (comprehensive, implementation-ready)
Scope: Pure-Python API layer over the existing CPython extension

This LLD defines the Python facade that sits above the CPython extension
module (`timelog._timelog`). It adds Pythonic ergonomics (slicing, iter
conveniences, docs, typing) without changing core semantics or duplicating
engine logic.

---

## Table of Contents

1. [Goals and Non-Goals](#1-goals-and-non-goals)
2. [Package Layout](#2-package-layout)
3. [Extension Module API Surface](#3-extension-module-api-surface)
4. [Public API Surface](#4-public-api-surface)
5. [Timelog Facade Class](#5-timelog-facade-class)
6. [Slicing Semantics](#6-slicing-semantics)
7. [Iteration Semantics](#7-iteration-semantics)
8. [PageSpan and Zero-Copy Views](#8-pagespan-and-zero-copy-views)
9. [Error Model](#9-error-model)
10. [Type Hints and Documentation](#10-type-hints-and-documentation)
11. [Implementation Details](#11-implementation-details)
12. [Performance Guidelines](#12-performance-guidelines)
13. [Testing Plan](#13-testing-plan)
14. [Compatibility Notes](#14-compatibility-notes)
15. [Future Extensions](#15-future-extensions)

---

## 1. Goals and Non-Goals

### 1.1 Goals

1. **Stable Pythonic API**: Provide a user-friendly public API that maps 1:1
   to the binding while adding Python idioms.

2. **Slicing Sugar**: Support `log[t1:t2]` syntax for time-range queries.

3. **Iteration Sugar**: Support `for (ts, obj) in log:` syntax.

4. **Re-export Consistency**: Export extension types and exceptions with
   consistent names and documentation.

5. **Type Hints**: Full PEP 484/526 type hints for IDE support and static
   analysis tools (mypy, pyright).

6. **Documentation**: Comprehensive docstrings suitable for Sphinx/pdoc.

7. **Zero Overhead**: No performance penalty for using the facade vs direct
   extension access.

### 1.2 Non-Goals

- No new data structures or algorithmic logic in Python.
- No changes to core/binding semantics (no retries, no rollback changes).
- No new exception taxonomy beyond existing binding types.
- No `__len__` on Timelog (expensive, unclear semantics with tombstones).
- No `log[t]` direct integer indexing (ambiguous with duplicates).
- No dataframe/vectorized integrations (future work).
- No alternative payload modes (bytes/slabs - future work).

---

## 2. Package Layout

### 2.1 Directory Structure

```
python/
  timelog/
    __init__.py      # Public API and facade class
    _api.py          # Implementation details for facade helpers
    py.typed         # Marker for PEP 561 typing
```

### 2.2 File Purposes

| File | Purpose |
|------|---------|
| `__init__.py` | Primary public surface: Timelog class, re-exports, type aliases |
| `_api.py` | Internal helpers: slice parsing, timestamp coercion |
| `py.typed` | Empty marker file for PEP 561 (typing support) |

### 2.3 Build Integration

The build system (CMake/setuptools) installs the extension as
`timelog/_timelog.*` alongside the pure-Python package. No compiled
artifacts live under `python/` at source time.

```
# After installation:
site-packages/
  timelog/
    __init__.py
    _api.py
    py.typed
    _timelog.cpython-312-x86_64-linux-gnu.so  # Linux
    _timelog.cp312-win_amd64.pyd              # Windows
```

---

## 3. Extension Module API Surface

This section documents the complete API exposed by `timelog._timelog` that
the facade wraps. This serves as the contract between binding and facade.

### 3.1 Types Exported by Extension

| Type | Description |
|------|-------------|
| `Timelog` | Main engine wrapper (tp_flags includes BASETYPE) |
| `TimelogIter` | Snapshot-based iterator yielding `(ts, obj)` |
| `PageSpan` | Zero-copy timestamp view with buffer protocol |
| `PageSpanIter` | Streaming iterator yielding `PageSpan` objects |
| `PageSpanObjectsView` | Lazy sequence view over decoded objects |

### 3.2 Exceptions Exported by Extension

| Exception | Base | Description |
|-----------|------|-------------|
| `TimelogError` | `Exception` | Base for timelog-specific errors |
| `TimelogBusyError` | `TimelogError` | Transient backpressure condition |

### 3.3 Timelog Type - Constructor

```python
Timelog(
    time_unit: str = None,           # "s", "ms", "us", "ns" (default: "ms")
    maintenance: str = None,         # "disabled", "background" (default: "disabled")
    memtable_max_bytes: int = None,  # Default: ~1MB
    target_page_bytes: int = None,   # Default: ~64KB
    sealed_max_runs: int = None,     # Default: 4
    drain_batch_limit: int = None,   # 0 = unlimited (default: 0)
    busy_policy: str = None          # "raise", "silent", "flush" (default: "raise")
)
```

### 3.4 Timelog Type - Properties

| Property | Type | Description |
|----------|------|-------------|
| `closed` | `bool` | True if timelog has been closed |
| `time_unit` | `str` | Configured time unit |
| `maintenance_mode` | `str` | "disabled" or "background" |
| `busy_policy` | `str` | "raise", "silent", or "flush" |
| `retired_queue_len` | `int` | Approximate objects awaiting DECREF |
| `alloc_failures` | `int` | Allocation failures in on_drop callback |

### 3.5 Timelog Type - Methods

**Write Operations:**
- `append(ts: int, obj: object) -> None`
- `extend(iterable: Iterable[tuple[int, object]]) -> None`
- `delete_range(t1: int, t2: int) -> None`
- `delete_before(cutoff: int) -> None`

**Maintenance Operations:**
- `flush() -> None`
- `compact() -> None`
- `start_maintenance() -> None`
- `stop_maintenance() -> None`
- `close() -> None`

**Iterator Factories:**
- `range(t1: int, t2: int) -> TimelogIter`
- `since(t1: int) -> TimelogIter`
- `until(t2: int) -> TimelogIter`
- `all() -> TimelogIter`
- `equal(t: int) -> TimelogIter`
- `point(t: int) -> TimelogIter`

**PageSpan Factory:**
- `page_spans(t1: int, t2: int, *, kind: str = "segment") -> PageSpanIter`

**Context Manager:**
- `__enter__() -> Timelog`
- `__exit__(exc_type, exc_val, exc_tb) -> bool`

### 3.6 TimelogIter Type

| Member | Type | Description |
|--------|------|-------------|
| `closed` | `bool` | Property: True if exhausted or closed |
| `close()` | `None` | Release resources (idempotent) |
| `next_batch(n)` | `list[tuple[int, object]]` | Batch retrieval |
| `__iter__()` | `TimelogIter` | Returns self |
| `__next__()` | `tuple[int, object]` | Next record or StopIteration |
| `__enter__()` | `TimelogIter` | Context manager entry |
| `__exit__(...)` | `bool` | Context manager exit (closes) |

### 3.7 PageSpan Type

| Member | Type | Description |
|--------|------|-------------|
| `timestamps` | `memoryview` | Property: Read-only int64 buffer |
| `start_ts` | `int` | Property: First timestamp in span |
| `end_ts` | `int` | Property: Last timestamp in span |
| `closed` | `bool` | Property: True if closed |
| `objects()` | `PageSpanObjectsView` | Lazy object sequence |
| `copy_timestamps()` | `list[int]` | Copy timestamps to list |
| `copy()` | `list[int]` | Alias for copy_timestamps() |
| `close()` | `None` | Release resources |
| `__len__()` | `int` | Number of records in span |
| `__enter__()` | `PageSpan` | Context manager entry |
| `__exit__(...)` | `bool` | Context manager exit |

**Buffer Protocol:**
- Exports read-only 1D array of int64 timestamps
- Raises `BufferError` if close() called while buffer exported

### 3.8 PageSpanIter Type

| Member | Type | Description |
|--------|------|-------------|
| `closed` | `bool` | Property: True if exhausted or closed |
| `close()` | `None` | Release resources |
| `__iter__()` | `PageSpanIter` | Returns self |
| `__next__()` | `PageSpan` | Next span or StopIteration |
| `__enter__()` | `PageSpanIter` | Context manager entry |
| `__exit__(...)` | `bool` | Context manager exit |

### 3.9 PageSpanObjectsView Type

| Member | Type | Description |
|--------|------|-------------|
| `__len__()` | `int` | Number of objects |
| `__getitem__(i)` | `object` | Access by index (supports negative) |
| `__iter__()` | `Iterator[object]` | Iterate objects |
| `copy()` | `list[object]` | Copy all objects to list |

---

## 4. Public API Surface

### 4.1 Module Exports (`timelog/__init__.py`)

```python
# Re-exported from _timelog
from timelog._timelog import (
    TimelogError,
    TimelogBusyError,
    TimelogIter,
    PageSpan,
    PageSpanIter,
    PageSpanObjectsView,
)

# Facade class and type aliases are defined locally in __init__.py:
# - Timelog
# - Record, RecordIter, RecordBatch

# Version
__version__: str
```

### 4.2 `__all__` Declaration

```python
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
```

### 4.3 Type Aliases

```python
from typing import Iterator

# Record is a (timestamp, object) tuple
Record = tuple[int, object]

# Iterator over records
RecordIter = Iterator[Record]

# Batch of records (from next_batch)
RecordBatch = list[Record]
```

---

## 5. Timelog Facade Class

### 5.1 Class Definition

```python
from timelog._timelog import Timelog as _CTimelog

class Timelog(_CTimelog):
    """
    Time-indexed multimap for (timestamp, object) records.

    A Timelog stores records indexed by timestamp with support for:
    - Fast time-range queries: [t1, t2), since(t), until(t)
    - Time-based eviction: delete_before(cutoff)
    - Out-of-order ingestion with LSM-style compaction
    - Snapshot isolation for concurrent reads

    Thread Safety:
        NOT thread-safe. Access from multiple threads requires external
        synchronization. Consistent with sqlite3.Connection semantics.

    Example:
        >>> with Timelog() as log:
        ...     log.append(1000, {"event": "start"})
        ...     log.append(2000, {"event": "end"})
        ...     for ts, obj in log[1000:2000]:
        ...         print(ts, obj)
        1000 {'event': 'start'}

    Args:
        time_unit: Timestamp resolution ("s", "ms", "us", "ns"). Default: "ms"
        maintenance: Background maintenance mode. Default: "disabled"
        memtable_max_bytes: Max bytes before memtable seals. Default: ~1MB
        target_page_bytes: Target page size. Default: ~64KB
        sealed_max_runs: Max sealed memruns before backpressure. Default: 4
        drain_batch_limit: Objects to drain per operation (0=unlimited).
        busy_policy: Backpressure handling ("raise", "silent", "flush").

    Raises:
        ValueError: Invalid configuration parameter
        MemoryError: Allocation failure during open
    """
    __slots__ = ()

    def __iter__(self) -> TimelogIter:
        """Return an iterator over all records."""
        return self.all()

    def __getitem__(self, s: slice) -> TimelogIter:
        """
        Return an iterator for a time range using slice syntax.

        Supported patterns:
            log[t1:t2] -> log.range(t1, t2)  # [t1, t2)
            log[t1:]   -> log.since(t1)      # [t1, +inf)
            log[:t2]   -> log.until(t2)      # (-inf, t2)
            log[:]     -> log.all()          # all records

        Args:
            s: A slice object. Step must be None or 1.

        Returns:
            TimelogIter for the specified range.

        Raises:
            TypeError: If s is not a slice (use .at(ts) for point queries)
            ValueError: If slice step is not None or 1
        """
        return _slice_to_iter(self, s)

    def at(self, ts: int) -> TimelogIter:
        """
        Return an iterator for records at exact timestamp ts.

        Alias for point(ts). Use this for single-timestamp queries.

        Args:
            ts: The exact timestamp to query.

        Returns:
            TimelogIter yielding all records with timestamp == ts.

        Example:
            >>> for _, obj in log.at(1000):
            ...     print(obj)
        """
        return self.point(_coerce_ts(ts))
```

### 5.2 Design Rationale

1. **Subclass, not wrapper**: Subclassing `_CTimelog` avoids per-instance
   overhead and preserves isinstance() checks.

2. **`__slots__ = ()`**: No additional instance attributes, ensuring the
   facade adds zero memory overhead.

3. **Thin forwarders**: All methods delegate to the C extension with minimal
   Python overhead.

4. **Basetype flag**: The extension type has `Py_TPFLAGS_BASETYPE`, making
   subclassing safe and supported.

---

## 6. Slicing Semantics

### 6.1 Supported Patterns

| Syntax | Method Call | Range Semantics |
|--------|-------------|-----------------|
| `log[t1:t2]` | `log.range(t1, t2)` | Half-open `[t1, t2)` |
| `log[t1:]` | `log.since(t1)` | Unbounded `[t1, +inf)` |
| `log[:t2]` | `log.until(t2)` | Unbounded `(-inf, t2)` |
| `log[:]` | `log.all()` | All records |

### 6.2 Edge Cases

| Case | Behavior |
|------|----------|
| `t1 >= t2` | Returns empty iterator (core behavior) |
| `step != None/1` | Raises `ValueError` |
| `log[t]` (non-slice) | Raises `TypeError` with guidance |
| Negative timestamps | Treated as data values (not indices) |

### 6.3 Implementation

```python
# python/timelog/_api.py

import operator

def _coerce_ts(x):
    """
    Coerce x to an integer timestamp.

    Uses operator.index() to support numpy.int64 and similar types.
    Explicitly rejects bool to avoid True -> 1 accidents.
    """
    if isinstance(x, bool):
        raise TypeError("timestamp must be int (bool not allowed)")
    return operator.index(x)

def _slice_to_iter(log, s):
    """
    Convert a slice to the appropriate iterator method call.
    """
    if not isinstance(s, slice):
        raise TypeError(
            f"Timelog indices must be slices, not {type(s).__name__}; "
            "use .at(ts) for point queries"
        )

    if s.step is not None and s.step != 1:
        raise ValueError("Timelog slice step must be None or 1")

    start = s.start
    stop = s.stop

    if start is None and stop is None:
        return log.all()
    if start is None:
        return log.until(_coerce_ts(stop))
    if stop is None:
        return log.since(_coerce_ts(start))
    return log.range(_coerce_ts(start), _coerce_ts(stop))
```

### 6.4 Why No Integer Indexing

`log[t]` is intentionally not supported because:

1. **Ambiguity with duplicates**: Multiple records can share the same
   timestamp. What would `log[1000]` return?

2. **Not a sequence**: Timelog is not an indexed sequence; `t` is a
   timestamp value, not a position.

3. **Clear alternative**: Use `log.at(t)` or `log.point(t)` to get an
   iterator over all records at timestamp t.

---

## 7. Iteration Semantics

### 7.1 Basic Iteration

```python
# Iterate all records
for ts, obj in log:
    print(ts, obj)

# Equivalent to:
for ts, obj in log.all():
    print(ts, obj)
```

### 7.2 Range Iteration

```python
# Using slicing
for ts, obj in log[1000:2000]:
    print(ts, obj)

# Using method
for ts, obj in log.range(1000, 2000):
    print(ts, obj)
```

### 7.3 Batch Iteration

```python
# Efficient batch processing
with log.all() as it:
    while True:
        batch = it.next_batch(1000)
        if not batch:
            break
        process_batch(batch)
```

### 7.4 Snapshot Isolation

Iteration is snapshot-based:
- Changes after iterator creation do not affect the iterator's view.
- Multiple concurrent iterators see consistent snapshots.
- Iterator holds resources until exhausted or closed.

```python
# Safe concurrent iteration
it1 = log.all()
log.append(9999, "new")  # Does not affect it1
it2 = log.all()          # it2 sees the new record
```

### 7.5 Resource Management

```python
# Option 1: Context manager (recommended)
with log.range(t1, t2) as it:
    for ts, obj in it:
        process(ts, obj)
# Resources released at end of block

# Option 2: Exhaust iterator
for ts, obj in log.all():
    process(ts, obj)
# Resources released on exhaustion

# Option 3: Explicit close
it = log.all()
try:
    for ts, obj in it:
        if should_stop(ts, obj):
            break
finally:
    it.close()  # Explicit release
```

---

## 8. PageSpan and Zero-Copy Views

### 8.1 Overview

PageSpan provides zero-copy access to timestamp arrays, useful for bulk
timestamp analysis without per-record Python object allocation.

```python
with log.page_spans(t1, t2) as spans:
    for span in spans:
        # Zero-copy access to timestamps as numpy-compatible buffer
        mv = span.timestamps
        arr = numpy.asarray(mv)  # No copy, shares memory

        # Lazy access to objects
        for obj in span.objects():
            process(obj)
```

### 8.2 PageSpan Properties

| Property | Description |
|----------|-------------|
| `timestamps` | Read-only memoryview of int64 timestamps |
| `start_ts` | First timestamp in span |
| `end_ts` | Last timestamp in span |
| `closed` | True if span is closed |
| `len(span)` | Number of records in span |

### 8.3 Buffer Protocol Integration

PageSpan implements the buffer protocol, enabling direct use with:
- `numpy.asarray()` (zero-copy)
- `memoryview()` (built-in)
- `struct.unpack_from()` (low-level)

```python
# Direct buffer access
span = next(iter(log.page_spans(0, 1000)))
mv = memoryview(span)  # Or span.timestamps
print(mv.format)       # 'q' (signed 64-bit)
print(mv.shape)        # (N,)
print(mv.readonly)     # True
```

### 8.4 Buffer Lifecycle

Buffers hold the PageSpan open until released:

```python
span = next(iter(log.page_spans(0, 1000)))
mv = span.timestamps

# This raises BufferError - buffer still exported
span.close()  # BufferError!

# Must release buffer first
del mv
span.close()  # OK
```

### 8.5 Objects Access

The `objects()` method returns a lazy view:

```python
with log.page_spans(0, 1000) as spans:
    for span in spans:
        objs = span.objects()
        print(len(objs))      # O(1)
        print(objs[0])        # O(1) - lazy decode
        print(objs[-1])       # Negative indexing supported

        # Copy all to list
        obj_list = objs.copy()
```

---

## 9. Error Model

### 9.1 Exception Hierarchy

```
Exception
  +-- TimelogError           (timelog-specific errors)
        +-- TimelogBusyError (transient backpressure)
  +-- ValueError             (invalid arguments)
  +-- TypeError              (type mismatches)
  +-- OverflowError          (timestamp overflow)
  +-- MemoryError            (allocation failure)
  +-- SystemError            (internal errors)
  +-- BufferError            (buffer protocol violations)
```

### 9.2 Error Translation (from LLD-B6)

| Status Code | Python Exception |
|-------------|------------------|
| `TL_EINVAL` | `ValueError` |
| `TL_ESTATE` | `TimelogError` |
| `TL_EBUSY` | `TimelogBusyError` |
| `TL_ENOMEM` | `MemoryError` |
| `TL_EOVERFLOW` | `OverflowError` |
| `TL_EINTERNAL` | `SystemError` |

### 9.3 Facade Error Additions

The facade adds these errors (not from binding):

| Error | Condition |
|-------|-----------|
| `TypeError` | Non-slice indexing: `log[t]` |
| `TypeError` | Bool timestamp: `log[True:]` |
| `ValueError` | Slice step: `log[::2]` |

### 9.4 No Exception Wrapping

The facade does **not** wrap or translate binding exceptions. This ensures:
- Single source of truth for error messages
- No translation drift from LLD-B6
- Predictable exception types for users

---

## 10. Type Hints and Documentation

### 10.1 Type Annotations

The facade uses inline type hints compatible with Python 3.9+:

```python
from __future__ import annotations
from typing import Iterator, Iterable, TYPE_CHECKING

if TYPE_CHECKING:
    from timelog._timelog import TimelogIter, PageSpan, PageSpanIter

Record = tuple[int, object]
RecordIter = Iterator[Record]
RecordBatch = list[Record]

class Timelog(_CTimelog):
    def append(self, ts: int, obj: object) -> None: ...
    def extend(self, items: Iterable[Record]) -> None: ...
    def range(self, t1: int, t2: int) -> TimelogIter: ...
    # ... etc
```

### 10.2 Stub Files

For V1, inline annotations are sufficient. Separate `.pyi` stub files may
be added in V2 for more complex type relationships.

### 10.3 PEP 561 Compliance

The `py.typed` marker file enables:
- mypy to recognize the package as typed
- IDE autocomplete and type checking
- Downstream packages to inherit type information

### 10.4 Docstring Style

Use NumPy/Google style docstrings:

```python
def append(self, ts: int, obj: object) -> None:
    """
    Append a record at timestamp ts with payload obj.

    The timestamp must be within int64 range [TL_TS_MIN, TL_TS_MAX].
    Records at the same timestamp are allowed (duplicates).

    Args:
        ts: Timestamp value in the configured time unit.
        obj: Any Python object to store (reference held by engine).

    Raises:
        OverflowError: If ts is outside int64 range.
        TimelogError: If timelog is closed.
        TimelogBusyError: If backpressure with busy_policy="raise".
        MemoryError: If allocation fails.

    Note:
        For TL_EBUSY, the record IS inserted even if exception raised.
        This is critical for understanding backpressure semantics.
    """
```

---

## 11. Implementation Details

### 11.1 Complete `__init__.py`

```python
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
"""

from __future__ import annotations

try:
    from importlib.metadata import version as _pkg_version
    __version__ = _pkg_version("timelog")
except Exception:
    __version__ = "0+unknown"

from typing import TYPE_CHECKING, Iterator

# Re-export from extension
from timelog._timelog import (
    TimelogError,
    TimelogBusyError,
    TimelogIter,
    PageSpan,
    PageSpanIter,
    PageSpanObjectsView,
)
from timelog._timelog import Timelog as _CTimelog

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
        sealed_max_runs: Max sealed memruns before backpressure.
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
```

### 11.2 Complete `_api.py`

```python
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
    # Explicit bool rejection before index() call
    # bool is a subclass of int, so isinstance(True, int) is True
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

    # Reject step values other than None or 1
    if s.step is not None and s.step != 1:
        raise ValueError(
            f"Timelog slice step must be None or 1, not {s.step!r}"
        )

    start = s.start
    stop = s.stop

    # All four combinations
    if start is None and stop is None:
        return log.all()

    if start is None:
        return log.until(_coerce_ts(stop))

    if stop is None:
        return log.since(_coerce_ts(start))

    return log.range(_coerce_ts(start), _coerce_ts(stop))
```

### 11.3 `py.typed` File

```
# This file is empty and serves as a marker for PEP 561.
# Its presence indicates that this package supports type checking.
```

---

## 12. Performance Guidelines

### 12.1 Zero Overhead Principles

The facade must not introduce performance overhead:

1. **No data copying**: Never materialize iterators or convert to lists.
2. **No extra allocations**: Use `__slots__ = ()` for zero per-instance cost.
3. **Direct forwarding**: Facade methods are thin wrappers.
4. **Lazy imports**: Only import what's needed.

### 12.2 Hot Path Analysis

| Operation | Facade Overhead | Notes |
|-----------|-----------------|-------|
| `log.append(ts, obj)` | ~0% | Direct C call |
| `log[t1:t2]` | ~1% | Slice parsing + method call |
| `for x in log:` | ~0% | Direct C iterator |
| `span.timestamps` | ~0% | Direct buffer |

### 12.3 Batch Processing Guidance

For best performance with large datasets:

```python
# GOOD: Use next_batch for bulk processing
with log.all() as it:
    while batch := it.next_batch(10000):
        process_batch(batch)

# GOOD: Use PageSpan for timestamp analysis
with log.page_spans(t1, t2) as spans:
    for span in spans:
        timestamps = numpy.asarray(span.timestamps)
        # Process without per-record Python overhead

# AVOID: Creating many small iterators
for t in range(0, 10000):
    list(log.at(t))  # Creates new snapshot each time
```

---

## 13. Testing Plan

### 13.1 Test File Location

```
python/tests/test_facade.py
```

### 13.2 Test Categories

**Category 1: Slicing Tests**
- `test_slice_range`: `log[t1:t2]` maps to `range(t1, t2)`
- `test_slice_since`: `log[t1:]` maps to `since(t1)`
- `test_slice_until`: `log[:t2]` maps to `until(t2)`
- `test_slice_all`: `log[:]` maps to `all()`
- `test_slice_step_none`: Step None is allowed
- `test_slice_step_one`: Step 1 is allowed
- `test_slice_step_error`: Step != None/1 raises ValueError
- `test_slice_non_slice_error`: `log[t]` raises TypeError

**Category 2: Iteration Tests**
- `test_iter_all`: `iter(log)` equivalent to `log.all()`
- `test_iter_sequence`: Results match direct method call
- `test_iter_empty`: Empty log yields no records

**Category 3: at() Tests**
- `test_at_basic`: `at(ts)` returns same as `point(ts)`
- `test_at_with_duplicates`: Returns all matching records
- `test_at_empty`: No match returns empty iterator

**Category 4: Coercion Tests**
- `test_coerce_int`: Plain int passes through
- `test_coerce_numpy_int64`: numpy.int64 works
- `test_coerce_bool_rejected`: bool raises TypeError
- `test_coerce_non_int_rejected`: float/str raise TypeError

**Category 5: Re-export Tests**
- `test_exceptions_identical`: TimelogError is same object
- `test_types_identical`: Types match extension types
- `test_all_exported`: All items in __all__ exist

**Category 6: Integration Tests**
- `test_context_manager`: with statement works
- `test_pagespan_reexport`: PageSpan accessible
- `test_version_defined`: __version__ is string

### 13.3 Test Template

```python
"""Tests for the Python facade layer (LLD-B7)."""

import pytest
from timelog import (
    Timelog,
    TimelogError,
    TimelogBusyError,
    TimelogIter,
    PageSpan,
    PageSpanIter,
    PageSpanObjectsView,
    Record,
    __version__,
)
from timelog._timelog import Timelog as _CTimelog
from timelog._timelog import TimelogError as _CTimelogError


class TestSlicing:
    """Test __getitem__ slice syntax."""

    def test_slice_range(self):
        with Timelog() as log:
            log.extend([(i, i) for i in range(10)])

            result = list(log[3:7])
            expected = list(log.range(3, 7))

            assert result == expected
            assert len(result) == 4

    def test_slice_step_error(self):
        with Timelog() as log:
            with pytest.raises(ValueError, match="step"):
                log[0:10:2]

    def test_slice_non_slice_error(self):
        with Timelog() as log:
            with pytest.raises(TypeError, match="slices"):
                log[5]


class TestIteration:
    """Test __iter__ protocol."""

    def test_iter_all(self):
        with Timelog() as log:
            log.extend([(i, f"item{i}") for i in range(5)])

            via_iter = list(log)
            via_all = list(log.all())

            assert via_iter == via_all


class TestAt:
    """Test at() convenience method."""

    def test_at_basic(self):
        with Timelog() as log:
            log.append(100, "a")
            log.append(100, "b")
            log.append(200, "c")

            result = [obj for _, obj in log.at(100)]
            assert set(result) == {"a", "b"}


class TestCoercion:
    """Test timestamp coercion."""

    def test_coerce_bool_rejected(self):
        with Timelog() as log:
            with pytest.raises(TypeError, match="bool"):
                log[True:]


class TestReexports:
    """Test that re-exports are identical objects."""

    def test_exceptions_identical(self):
        assert TimelogError is _CTimelogError

    def test_timelog_subclass(self):
        assert issubclass(Timelog, _CTimelog)

    def test_version_string(self):
        assert isinstance(__version__, str)
        assert __version__
```

---

## 14. Compatibility Notes

### 14.1 Python Version Requirements

- **Minimum**: Python 3.9 (for `tuple[int, object]` syntax)
- **Recommended**: Python 3.10+ (for improved error messages)

### 14.2 Module Names

| Python Import | Extension File | Notes |
|---------------|----------------|-------|
| `import timelog` | N/A | Pure Python package |
| `from timelog import Timelog` | N/A | Facade class |
| `from timelog._timelog import Timelog` | `_timelog.*.so` | C extension |

### 14.3 `__module__` Attributes

All extension types report `__module__ == "timelog._timelog"`:

```python
>>> Timelog.__module__
'timelog._timelog'
>>> TimelogIter.__module__
'timelog._timelog'
```

### 14.4 Lazy Import Handling

The facade imports `_timelog` at module load time. If the extension is not
available, a clear ImportError is raised:

```python
try:
    from timelog._timelog import Timelog as _CTimelog
except ImportError as e:
    raise ImportError(
        "timelog extension module not found. "
        "Ensure the package is properly installed."
    ) from e
```

---

## 15. Future Extensions

The following are explicitly out of scope for B7 but documented for future:

### 15.1 V2 Considerations

- **Async iteration**: `async for` support with asyncio
- **DataFrame integration**: Direct pandas/polars export
- **Vectorized payloads**: bytes/memoryview payload mode
- **`__contains__`**: `ts in log` syntax
- **`__len__`**: If efficient count becomes available

### 15.2 Type Stub Evolution

Consider generating `.pyi` stubs from C extension for:
- More precise generic types
- Overload support for methods
- Protocol definitions

---

## 16. Summary

The Python facade (LLD-B7) provides:

1. **Pythonic API**: Slicing (`log[t1:t2]`) and iteration (`for x in log`)
2. **Zero overhead**: Subclass with no per-instance state
3. **Full re-exports**: All extension types and exceptions
4. **Type safety**: PEP 484 hints and PEP 561 marker
5. **Documentation**: Comprehensive docstrings

The implementation is small (~200 lines across 2-3 files) and purely Python,
serving as a thin ergonomic layer over the high-performance C extension.

---

## Appendix A: Quick Reference Card

```python
from timelog import Timelog, TimelogError, TimelogBusyError

# Create and configure
log = Timelog(time_unit="ms", maintenance="background")

# Write operations
log.append(1000, {"event": "start"})
log.extend([(2000, "a"), (3000, "b")])
log.delete_range(1000, 2000)
log.delete_before(1000)

# Query operations (all return iterators)
log.all()           # All records
log.range(t1, t2)   # [t1, t2)
log.since(t1)       # [t1, +inf)
log.until(t2)       # (-inf, t2)
log.point(t)        # ts == t
log.at(t)           # Alias for point(t)

# Slicing syntax (maps to above)
log[:]              # all()
log[t1:t2]          # range(t1, t2)
log[t1:]            # since(t1)
log[:t2]            # until(t2)

# Iteration
for ts, obj in log:
    ...
for ts, obj in log[1000:2000]:
    ...

# Batch processing
it = log.all()
batch = it.next_batch(1000)

# Zero-copy bulk access
for span in log.page_spans(t1, t2):
    timestamps = span.timestamps  # memoryview
    objects = span.objects()      # lazy sequence

# Context manager
with Timelog() as log:
    ...
# auto-closed

# Maintenance
log.flush()
log.compact()
log.start_maintenance()
log.stop_maintenance()
log.close()
```
