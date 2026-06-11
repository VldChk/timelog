# EXP C7-mem — Memory / allocator audit (measurement only, no core change)

Build: Release (build-rel). Correctness gate was locally reported as C core 480 passed / 0 failed and
pytest 98 passed, 16 skipped; this tree preserves the result summary and CSV/JSON measurement artifacts,
not raw test transcripts.
Module measured: baseline staged `python/timelog/_timelog.cpython-313-*.so` via `PYTHONPATH=python`.
Python 3.13.12, GCC build, 16 cores, 64 GiB RAM. Worker pinned to CPU 0.

Harness: `ideas-lab/harness/mem_probe.py`
  - Two processes: monitor forks worker; monitor samples worker RSS from /proc/<pid>/statm
    every 100 ms and merges with worker tracemalloc samples into a per-run CSV.
  - Workload: 3-5M appends (~12% out-of-order) with periodic flush + compaction drain,
    then a delete-storm (50% of span deleted in 40 chunks, compaction drives physical deletes),
    then settle + malloc_trim(0) + close.
  - Slopes fit over the steady ingest region to separate Python growth (tracemalloc up)
    from native fragmentation (RSS up, tracemalloc flat).

## Native vs Python split (the diagnostic)
At peak (3M, glibc): RSS = 692 MB but tracemalloc_cur = 91.5 MB.
=> ~600 MB (~87%) is held by the native C core (pages/segments/manifests/OOO runs), not Python.
Ingest slopes: RSS ~53 MB/s vs tracemalloc ~8.6 MB/s => ~84% of growth is native.
This is a NATIVE-allocator story; Python-level tuning cannot move it.

## Allocator A/B (same workload + seed; jemalloc UNAVAILABLE on this box)
jemalloc: only static .a archives exist (no libjemalloc.so), libjemalloc2 not installed
and apt needs root (no passwordless sudo) — honestly skipped.
mimalloc: usable .so from snap (kf6-core24), originally staged as harness/libmimalloc.so, LD_PRELOAD.
The current harness no longer searches the repo-local directory by default; reruns must use a system
allocator library or explicitly opt in with `TIMELOG_MEM_PROBE_PRELOAD_DIRS`.
Historical staged binary provenance:
  path: ideas-lab/harness/libmimalloc.so (ignored, not committed)
  size: 110280 bytes
  sha256: 22a487e05be1eb23ba6596b4b020f2069ac4f433580fdd4ca9b82dd8b0523efa
  mi_version(): 212

3M, seed 1234:
  alloc      peak_RSS  ingest_done  delete_done  after_trim  after_close
  glibc       692.19      692.19       692.19       663.68       281.20
  arena2      692.46      692.21       692.21       663.70       328.96
  mimalloc    604.45      604.05       604.05       604.45       163.30
  -> mimalloc peak -87.7 MB (-12.7%), after-trim -59.2 MB (-8.9%)
  -> MALLOC_ARENA_MAX=2: ~0% (worker is single-threaded; glibc spawns no extra arenas)

3M, seed 777 (stability check):
  -> mimalloc peak -85.8 MB (-12.2%), after-trim -48.0 MB (-7.2%); arena2 ~0%

5M (single, glibc vs mimalloc):
  peak:        1014.6 -> 901.4 MB  (-113 MB, -11.2%)
  ingest_done:  976.5 -> 869.6 MB  (-107 MB, -11.0%)
  after_close:  465.3 -> 294.7 MB  (-170 MB, -36.7%)

## Verdict
mimalloc gives the lowest RSS at the measured high-water and ingest/delete landmarks: ~11-13%
lower peak/active-workload RSS, and markedly lower residual RSS after the workload. Consistent
across seeds and at 3M/5M. A later steady-state spot check narrowed the claim to
peak/fragmentation rather than a universal steady-state win. MALLOC_ARENA_MAX=2 does nothing for
this single-threaded workload (would matter under the multi-threaded background-maintenance
default, untested here).
Recommendation = cool-but-costly: a real peak/fragmentation RSS win, but it requires
shipping/depending on mimalloc (LD_PRELOAD or linking) rather than a code change; worth
recommending as an optional deployment knob, not a default core change.
