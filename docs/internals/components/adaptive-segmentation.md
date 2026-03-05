# Internals: Adaptive Segmentation

Sources:
- `core/src/maint/tl_adaptive.*`
- `core/src/maint/tl_compaction.c`

## Purpose

Adaptive segmentation tunes effective window size to keep segment density near a target under varying data distributions.

## Inputs

- `target_records`
- window bounds (`min_window`, `max_window`)
- hysteresis and quantum snapping
- EWMA smoothing (`alpha`)
- warmup/staleness/backoff controls

## Behavior

`Implementation note`
- Candidate window is computed from density estimates and constrained by guardrails.
- Resizing is disabled when grid is frozen.
- Success/failure feedback updates adaptive state.

`Out of scope`
- Adaptive behavior is an implementation strategy; API contract remains timestamp/range semantics.
