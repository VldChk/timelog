# C3-dlpack — DLPack export patch-only audit note

Current saved artifacts:

- `prototype.patch`

The serious-audit report records a prior lab run where `np.from_dlpack(span)` consumed PageSpan timestamps
zero-copy and read-only. This directory does **not** currently preserve the raw consumer script/output,
pointer-identity transcript, dependency versions, or full test/sanitizer logs for that run.

## Current verification status

- The patch is useful design evidence for a DLPack timestamp export.
- It is not sufficient, by itself, to prove the saved zero-copy or timing claims.
- Productionization must rerun the consumer checks, save raw evidence, and include ASan/UBSan coverage.

## Production caveats

The deleter must not run Python C-API cleanup on the wrong interpreter/thread state. Treat DLPack as a
medium feature requiring the same shared export-pin helper as Arrow/buffer exports.
