# Internals HLD

This page describes the current high-level design of Timelog.

## System Model

Timelog is an in-memory, time-indexed multimap with L0/L1 layering.

- L0: memtable and flush outputs, may overlap.
- L1: compaction outputs, window-partitioned and non-overlapping.
- Manifest: immutable catalog root, atomically published.
- Memview/snapshot: consistent read view for iterators.

## Core Invariants

`Contract`
- Half-open interval semantics (`[t1, t2)`).
- Immutable published storage objects.
- Snapshot-consistent reads.
- External single-writer requirement.

`Implementation note`
- Publication uses short critical sections with writer lock and seqlock counter updates.
- Maintenance supports background and manual control planes.

## Module Map

- Core orchestration: `core/src/tl_timelog.c`
- Delta/memtable/memview: `core/src/delta/*`
- Storage and manifest: `core/src/storage/*`
- Query path: `core/src/query/*`
- Maintenance/adaptive: `core/src/maint/*`

See component pages for detailed mechanics.
