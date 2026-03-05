# Configuration

Sources of truth:
- C API config: `core/include/timelog/timelog.h` (`tl_config_t`)
- Python facade kwargs/presets: `python/timelog/__init__.py`

## Key Runtime Modes

- `maintenance="background"` (default)
- `maintenance="disabled"` (manual maintenance)

`Contract`
- In background mode, maintenance worker is auto-started by open.

## Important Parameters

- `time_unit`: `s|ms|us|ns`
- `target_page_bytes`
- `memtable_max_bytes`
- `ooo_budget_bytes`
- `sealed_max_runs`
- `sealed_wait_ms`
- `max_delta_segments`
- `window_size`, `window_origin`
- `delete_debt_threshold`
- `compaction={target_bytes,max_inputs,max_windows}`
- `adaptive={target_records,min_window,max_window,hysteresis_pct,window_quantum,alpha,warmup_flushes,stale_flushes,failure_backoff_threshold,failure_backoff_pct}`

## Python Presets

- `for_streaming`: background + flush busy policy.
- `for_bulk_ingest`: disabled maintenance + larger memtable.
- `for_low_latency`: stricter busy behavior + small memtable.

## Zero Semantics

`Contract`
- For most numeric fields, `0` means "use engine default".
- Exceptions are documented in the public header and facade docs (notably fields where `0` can mean disabled or immediate behavior).
