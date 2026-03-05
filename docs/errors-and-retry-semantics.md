# Errors and Retry Semantics

Source of truth: `core/include/timelog/timelog.h` status-code documentation.

## Status Model

- `TL_OK`: success
- `TL_EOF`: end/no work
- `TL_EINVAL`: caller contract violation
- `TL_ESTATE`: invalid state for operation
- `TL_EBUSY`: busy/transient depending on API family
- `TL_ENOMEM`, `TL_EOVERFLOW`: operation failed without commit
- `TL_EINTERNAL`: severe internal failure

## Critical Rule: `TL_EBUSY` on Writes

`Contract`
- For write APIs (`append`, `append_batch`, `delete_*`), `TL_EBUSY` means the write was accepted.
- Do not retry the same write blindly, or duplicates can be introduced.

## Maintenance and Flush Retries

`Contract`
- `TL_EBUSY` from maintenance/flush paths can indicate publish contention and is retryable.
- `TL_ENOMEM` / `TL_EOVERFLOW` on write APIs indicate no write commit and are retryable after mitigation.

## Python Exception Mapping

- Engine errors surface through `TimelogError` hierarchy.
- `TimelogBusyError` is used for busy-policy-visible write/backpressure outcomes.
- Operational handling should follow engine semantics above.
