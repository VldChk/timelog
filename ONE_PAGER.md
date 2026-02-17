# Timelog: Technical One‑Pager

## What Timelog Is
**Timelog is a native‑C, in‑memory, time‑indexed multimap for Python.**  
It is designed for timestamp‑first workloads where the primary operation is time slicing (e.g., “all events in `[t1, t2)`”), not hash lookup. Timelog makes that operation a first‑class primitive, while keeping ingestion cheap under out‑of‑order streams.

At a high level, it combines a memtable‑style write buffer, immutable in‑memory segments, and LSM‑inspired flush/compaction to preserve fast reads as the structure grows and fragments.

## Problem It Solves
A lot of real Python systems (streaming/windowed algorithms, rolling aggregations, log/event processing, TTL caches, schedulers, circuit breakers) spend most of their time answering:

“give me all rows in `[t1, t2)`”

In practice teams either (a) maintain ad‑hoc indexing/filtering logic in Python, paying high per‑row overhead and fighting correctness under deletes and out‑of‑order inserts, or (b) reach for heavier external TSDB infrastructure even when they only need an embedded time index.

Timelog fills this gap: a lightweight, embedded, C‑native timestamp index with snapshot‑consistent reads and efficient range scans.

## Data and Consistency Model
Timelog stores **(timestamp → one or more values)** (multimap semantics; duplicate timestamps are valid).  
All time ranges are **half‑open**: **`[t1, t2)`**.  
Reads are **snapshot‑consistent**: a query operates over a stable view even while writes and maintenance continue.  
Concurrency is intentionally simple: **single writer + concurrent readers** (writer coordination is explicit; readers do not block).

Deletes are **logical time‑range deletes** (tombstones). The engine is built to preserve correct “insert → delete → insert” semantics by sequencing deletes relative to inserts.

## Architecture Summary
Writes go to mutable in‑memory structures (the ingest buffer). When the buffer fills or policy triggers, it seals into an immutable run and flushes into immutable segments. Over time, segments are compacted to reduce overlap and keep read fan‑out bounded.

Reads take a snapshot, plan the relevant sources (active state + sealed runs + segments), and then answer queries using binary searches inside pages plus a k‑way merge across sources, applying tombstone filtering in a version/sequence‑aware way.

The goal is predictable query behavior without turning ingestion into a write‑amplification machine.

## Performance / Complexity Positioning (Scoped Claims)
These are the intended, defensible claims (not marketing promises):

- **Append / batch append:** amortized **O(1)** per record on the memtable path, with bounded contention from maintenance.  
- **Delete range:** inserts a tombstone interval into an interval structure; cost is typically **logarithmic + local merge work**, nearly constant time.  
- **Point lookup:** near **O(log N)** when read fan‑out is bounded (practically: log + duplicates).  
- **Range query:** seek cost plus scan; near **O(log N + M)** with bounded fan‑out, where **M** is results returned.

(Where “bounded fan‑out” is the key assumption: flush/compaction exist largely to keep it true.)

## Where It Fits
Timelog is a good fit when you want timestamp slicing as a primitive inside Python:

- embedded analytics/serving paths  
- real‑time and near‑real‑time event pipelines  
- systems that need fast `[t1, t2)` retrieval without external database overhead  

## Current Boundaries
- **In‑memory only**: no durable storage layer and no SQL/query language.  
- Not positioned as a distributed TSDB; it is an embedded engine.  
- Write concurrency is intentionally constrained (single writer) to keep the core simple and fast.
– No Numpy integration

## Quality and Delivery Confidence
- Large C test surface (hundreds of assertions across core suites), plus binding and Python façade tests.  
- Cross‑platform CI (Linux/Windows) for PR validation.  
- Separate correctness and benchmark/methodology workflows (intended for reproducible evaluation).

**Short definition:**  
Timelog is a C‑native, timestamp‑indexed multimap for Python that makes `[t1, t2)` retrieval a first‑class operation with cheap ingestion and snapshot‑consistent reads under out‑of‑order streams.
