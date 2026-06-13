# Timelog Documentation

Timelog is a native-C, in-memory, time-indexed multimap for Python.

This documentation is the canonical, publishable reference for users and contributors.
Historical iteration docs are archived under `docs/archive/`.

## Current Release (1.3.0)

- Carries the v1.2 runtime isolation work: multi-phase `_timelog`
  initialization, module-local heap types/exceptions, isolated subinterpreters,
  and the supported CPython 3.14t free-threaded wheel set.
- Adds the v1.3 hot-path work: C-level `append(obj)` auto-timestamping,
  lower-overhead query/delete dispatch, typed-buffer `bulk_append`, and gated
  branchless search.
- Keeps Timelog explicitly in-memory: `flush()` materializes data for
  open-instance readers and zero-copy views; `close()` discards all records.
- Current benchmark framing lives in `docs/performance.md`; historical workload
  reports remain snapshots, not universal guarantees.

## Start Here

1. `docs/what-is-timelog.md`
2. `docs/getting-started.md`
3. `docs/release-notes.md`
4. `docs/python-api.md`
5. `docs/configuration.md`
6. `docs/errors-and-retry-semantics.md`
7. `docs/operations.md`
8. `docs/performance.md`

## Advanced Internals

1. `docs/internals/hld.md`
2. `docs/internals/components/write-path.md`
3. `docs/internals/components/read-path.md`
4. `docs/internals/components/storage-and-manifest.md`
5. `docs/internals/components/compaction-and-maintenance.md`
6. `docs/internals/components/adaptive-segmentation.md`
7. `docs/internals/components/python-binding-architecture.md`
8. `docs/internals/components/tombstone-watermark-model.md`

## Quality and Delivery

1. `docs/testing-and-ci.md`
2. `docs/PERFORMANCE_METHODOLOGY.md`
3. `docs/CI_TESTS.md`
4. `docs/pypi-release.md`

## Glossary

- `docs/glossary.md`

## Historical Design Docs

- V1 archive: `docs/archive/v1/`
- V2 archive: `docs/archive/v2/`
