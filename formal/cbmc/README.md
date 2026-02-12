# CBMC harnesses

This directory contains bounded model checking harnesses for key safety/correctness properties in timelog internals.

## Prerequisites

- `cbmc` on PATH.
- Run from repository root (`/workspace/timelog`).

## Harnesses and properties

- `intervals_harness.c`
  - Insert/coalesce invariants for `tl_intervals_insert` / `tl_intervals_insert_unbounded`.
  - Union correctness: `max_seq_union(ts) == max(max_seq_a(ts), max_seq_b(ts))` at probe points.
  - Non-overlap and ordering invariants.
  - Timestamp-boundary overflow behavior in `tl_intervals_covered_span`.
- `heap_harness.c`
  - Heap pop order is non-decreasing by `(ts, tie_break_key)`.
  - Tie-break stability for equal timestamps.
- `filter_harness.c`
  - Tombstone predicate semantics for `tl_filter_iter_next`: filter iff `tomb_seq > watermark`.
- `page_harness.c`
  - `lower_bound`/`upper_bound` boundary correctness and partition properties.
  - Boundary checks at `TL_TS_MIN` and `TL_TS_MAX`.

## Commands

Use these exact commands (all include pointer/bounds safety checks):

```bash
cbmc formal/cbmc/intervals_harness.c \
  --function harness_intervals_insert_invariants \
  --bounds-check --pointer-check --signed-overflow-check --unsigned-overflow-check \
  --unwind 8 --unwinding-assertions

cbmc formal/cbmc/intervals_harness.c \
  --function harness_intervals_union_and_max_seq \
  --bounds-check --pointer-check --signed-overflow-check --unsigned-overflow-check \
  --unwind 8 --unwinding-assertions

cbmc formal/cbmc/heap_harness.c \
  --function harness_heap_ordering_and_tiebreak_stability \
  --bounds-check --pointer-check --signed-overflow-check --unsigned-overflow-check \
  --unwind 10 --unwinding-assertions

cbmc formal/cbmc/filter_harness.c \
  --function harness_filter_tombstone_watermark_predicate \
  --bounds-check --pointer-check --signed-overflow-check --unsigned-overflow-check \
  --unwind 6 --unwinding-assertions

cbmc formal/cbmc/page_harness.c \
  --function harness_page_search_boundaries \
  --bounds-check --pointer-check --signed-overflow-check --unsigned-overflow-check \
  --unwind 8 --unwinding-assertions
```

## Bound parameters

These bounds are encoded in harness assumptions and command line unwind values:

- Intervals insert steps: `steps <= 6`, CBMC `--unwind 8`.
- Intervals union set sizes: `na <= 4`, `nb <= 4`, CBMC `--unwind 8`.
- Heap entries: `n <= 8`, CBMC `--unwind 10`.
- Page row count: `n <= 16`, CBMC `--unwind 8`.
- Filter model: single-record merge model, CBMC `--unwind 6`.

