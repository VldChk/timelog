# C2-bulk — typed-buffer `bulk_append` patch-only audit note

Current saved artifacts:

- `prototype.patch`

The serious-audit report records a prior lab run where the patch was built, gated, and measured at
roughly 9-10x faster than per-append and 2.4x faster than `extend`. This directory does **not** currently
preserve the raw benchmark script/output, exact command transcript, or full test logs for that run.

## Current verification status

- The patch is useful design evidence for the API shape and refcount/rollback review.
- It is not sufficient, by itself, to prove the saved performance numbers.
- Productionization must rerun the benchmark and save raw JSON/stdout plus the relevant C/Python test logs.

## Blocking production caveat

The patch accepts byte-order-prefixed `int64` buffer formats and direct-casts the buffer to `int64_t*`.
Before a PR, reject non-native-endian buffers or byteswap into scratch storage, and add explicit tests for
native/non-native NumPy arrays.
