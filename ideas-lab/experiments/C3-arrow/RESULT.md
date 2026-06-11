# C3-arrow — Arrow C Data export patch-only audit note

Current saved artifacts:

- `prototype.patch`

The serious-audit report records a prior lab run where the patch exposed PageSpan timestamps through the
Arrow C Data interface and pyarrow/polars consumed the timestamp buffer zero-copy. This directory does
**not** currently preserve the raw consumer script/output, pointer-identity transcript, dependency versions,
or full test/sanitizer logs for that run.

## Current verification status

- The patch is useful design evidence for a timestamp-only Arrow export.
- It is not sufficient, by itself, to prove the saved zero-copy or timing claims.
- Productionization must rerun the consumer checks, save raw evidence, and include ASan/UBSan coverage.

## Production caveats

Do not expose encoded payload handles as numeric Arrow data. The feature needs a shared PageSpan export-pin
helper and an explicit release-callback/thread-state contract for Python consumers.
