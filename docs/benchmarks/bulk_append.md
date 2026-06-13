# `bulk_append` — measured provenance

Saved measurement backing the `bulk_append(timestamps, objects)` typed-buffer ingest
fast path in the v1.3 release.

## Method

- Harness shape: source-tree release build, 200,000 records, median of 5 repeats,
  ns/record.
- Source tree: branch `release/v1.3`, tree at `adc9c6f` (contains the bulk_append
  implementation commit `6f9ca8f`; benchmark run on the working tree at that commit,
  which predates the later alignment-guard branch — one extra predictable branch
  per call, no re-run warranted).
- Host: AMD Ryzen AI 7 PRO 350, Linux, pinned to core 2 via `taskset`.
- Python: CPython 3.13.12 (GCC 13.3.0), release build of `_timelog`
  (no sanitizers), staged extension `python/timelog/_timelog.cpython-313-x86_64-linux-gnu.so`.

## Results (2026-06-11)

| Path | ns/record | Relative |
|------|-----------|----------|
| `bulk_append(np.int64 array, list)` | **113.3** | 1.00× (baseline) |
| `append(int(ts), obj)` loop (post-fold C append) | 252.1 | bulk is **2.23×** faster |
| `extend(zip(ts_list, objects))` | 397.2 | bulk is **3.51×** faster |

Endianness contract verified in the same run: a byteswapped (non-native) int64 array is
rejected with `ValueError: bulk_append() timestamps must be native byte order (byteswap
the array first)` and inserts nothing.

## Interpretation (bounded claims)

- The historical C2 figure "9–10× vs per-append" was measured against the **pre-v1.3
  Python-facade append** (~1 µs/record). v1.3's folded C `append` is itself ~4× faster
  than that baseline, so the honest current ratios are the ones above. Do not quote the
  9–10× figure for v1.3.
- 113 ns/record places bulk ingest near the engine's batch-append cost; the remaining
  per-record overhead is dominated by per-object `INCREF` + handle encode, which any
  payload-carrying path must pay.
- `bulk_append` wins by skipping per-element tuple construction, argument dispatch, and
  `int` unboxing. The advantage grows with batch size and is workload-independent
  (in-order vs OOO ordering is handled downstream by the same engine paths as `extend`).
