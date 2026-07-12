# Release Notes

Concise user-facing summary of the current release line. Deeper behavior
contracts live in `docs/python-api.md`, `docs/configuration.md`, and
`docs/performance.md`.

## 1.4.0

Focus: export APIs and a large internal simplification at zero regression.

- `to_numpy(t1=None, t2=None, *, dtype=None)` exports a time range as a pair
  of fresh contiguous 1-D numpy arrays (`int64` timestamps, `float64` values;
  `dtype` overrides the value dtype with any scalar numeric dtype, e.g.
  `np.int64` for exact big-int payloads). numpy stays an optional dependency,
  imported lazily.
- `to_dict(t1=None, t2=None)` exports a time range as `{timestamp: object}`.
  Duplicate timestamps collapse to one value; which record wins is
  deterministic for a given storage state but otherwise unspecified (see
  `docs/python-api.md`). `to_dict` never imports numpy.
- Export bounds behave exactly like `log[t1:t2]` slicing; exports are
  snapshot-isolated, consume in bounded chunks so large exports cannot
  monopolize the GIL, and release their reader pin on every path. Conversion
  failures in `to_numpy` keep their original exception type with the failing
  row index attached as a note (PEP 678). Measured ~71-79 ns/record
  (`to_numpy`) and ~60 ns/record (`to_dict`) at 1M records.
- Internal simplification campaign: net -4,829 lines removed (dead functions,
  speculative surfaces, duplicated plumbing) with the full validation matrix
  green; same-harness A/B shows no regression and small wins (mixed read
  +5.5%, query-after-delete +7.2%, append +2.4%).
- `extend()` no longer raises a latent `SystemError` (NULL return without an
  exception) on non-EBUSY mid-stream engine failure.
- MSVC builds now use the C11 `<stdatomic.h>` backend (gated), aligning
  Windows atomics with the GCC/Clang path.

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
- Timestamp-buffer interop covers `bulk_append()` input buffers and
  `PageSpan.timestamps` memoryviews.
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
