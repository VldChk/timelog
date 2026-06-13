# Release Notes

Concise user-facing summary of the current release line. Deeper behavior
contracts live in `docs/python-api.md`, `docs/configuration.md`, and
`docs/performance.md`.

## 1.3.0

Focus: Python-facing usability and hot-path performance.

- `append(obj)` is handled in C, including auto-timestamping according to the
  instance `time_unit`.
- Common positional calls use lower-overhead dispatch paths:
  `append`, `range`, `since`, `until`, `point`, `equal`, `next_ts`,
  `prev_ts`, `delete_range`, and `delete_before`.
- `bulk_append(timestamps, objects)` adds an all-or-nothing typed-buffer ingest
  path for native-endian 1-D int64 timestamp buffers and list/tuple payloads.
- `extend(..., insert_on_error=True)` can skip type-invalid timestamps with a
  warning and exposes the cumulative `extend_skipped` counter; use
  `insert_on_error=False` for all-or-nothing validation.
- `min_ts` / `min_ts_floor`, richer `stats()["config"]`, `busy_events`, and
  `retired_queue_len` make long-running non-context-manager usage easier to
  monitor.
- `views()` / `PageSpan` usability is expanded with timestamp memoryviews,
  lazy `PageSpan.objects()`, `copy_timestamps()`, and typed stubs.
- Performance artifacts show v1.3 same-harness wins versus the v1.2.0 wheel:
  `append(obj)` 513.9 ns -> 117.1 ns, `append(ts, obj)` 352.1 ns -> 103.9 ns,
  and `bulk_append(np.int64 array, list)` 113.3 ns/record in its committed
  200k-record benchmark.

## 1.2.0

Focus: CPython runtime isolation and free-threaded readiness.

- The CPython extension uses multi-phase module initialization, per-module
  exception/type state, and module-owned heap types.
- Regular CPython 3.12-3.14 remains supported.
- Isolated subinterpreters with a per-interpreter GIL are supported.
- CPython 3.14t free-threaded builds are supported on the configured wheel set;
  the extension declares `Py_mod_gil = Py_MOD_GIL_NOT_USED` and import must not
  re-enable the GIL.
- Mutable binding state is synchronized explicitly with atomics, a core lock,
  handle-context locking, object critical sections, and atomic owner refs.
- Iterator, `PageSpan`, and handle/engine lifetime was refactored so readers can
  outlive the Python `Timelog` wrapper without use-after-free.
- CI gained required subinterpreter/free-threaded compatibility legs and
  advisory ThreadSanitizer coverage for the free-threaded stress suite.

## Persistent Contract Across Both Releases

- Timelog is in-memory. `close()` discards all records, flushed or not.
- `flush()` materializes pending writes into immutable in-memory segments while
  the instance is open; it is not durability.
- Writes and lifecycle operations on the same instance require external
  serialization. Snapshot readers can run concurrently.
- Write-path `TimelogBusyError` means the write was accepted; do not blindly
  retry the same write.
