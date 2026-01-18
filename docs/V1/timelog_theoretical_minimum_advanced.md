# Timelog — The Theoretical Minimum for Time‑Indexed Data Structures (Advanced)

> This document is a corrected and expanded Markdown conversion of the attached PDF **“Timelog: The Theoretical Minimum for Time‑Indexed Data Structures”**.  
> It is **tech‑agnostic**: it focuses on *data structures, algorithms, and systems concepts* you must internalize to engineer Timelog effectively, regardless of implementation language.

---

## How to use this document

Read it as a set of mental models:

1. Start with the *workload model* (what time‑indexed systems are optimized for).
2. Learn the *storage primitives* (sorted arrays, pages, manifests, tombstones).
3. Learn the *core algorithms* (range bounding, pruning, k‑way merge, compaction).
4. Learn the *systems constraints* (caches, vectorization, concurrency and snapshots).
5. Use the checklist at the end to verify you “have the minimum”.

Wherever possible, the text is written to support **reasoning and proof obligations** (what must be true for correctness), not only intuition.

---

## Table of contents

- [Introduction](#introduction)
- [Time-series data modeling and access patterns](#time-series-data-modeling-and-access-patterns)
- [Sorted contiguous arrays](#sorted-contiguous-arrays)
- [Bitmap indexes and deletion masks](#bitmap-indexes-and-deletion-masks)
- [Pagination in time-series queries](#pagination-in-time-series-queries)
- [CPU-efficient execution and vectorized principles](#cpu-efficient-execution-and-vectorized-principles)
- [LSM trees and memtable-segment flushing](#lsm-trees-and-memtable-segment-flushing)
- [Snapshot isolation and read/write concurrency](#snapshot-isolation-and-readwrite-concurrency)
- [Log-structured merge systems and write-optimized storage](#log-structured-merge-systems-and-write-optimized-storage)
- [Compressed indexes: Roaring bitmaps](#compressed-indexes-roaring-bitmaps)
- [Range-based pruning and query optimization](#range-based-pruning-and-query-optimization)
- [K-way merge as the core query algorithm](#k-way-merge-as-the-core-query-algorithm)
- [Trade-offs in systems design](#trade-offs-in-systems-design)
- [Clean layering and interface boundaries](#clean-layering-and-interface-boundaries)
- [Theoretical minimum checklist for Timelog engineers](#theoretical-minimum-checklist-for-timelog-engineers)
- [Glossary](#glossary)
- [References and further reading](#references-and-further-reading)

---

## Introduction

This learning resource provides a foundation for engineers working on **Timelog** — an in‑memory, time‑indexed store optimized for:

- fast **time‑range selection** (`[t1, t2)`, “last N minutes”), and  
- fast **time‑based eviction / retention** (“drop everything older than T”).

The goal is not to teach a specific implementation, but to teach the *ideas that make the design work*: how sorted layouts, paging, tombstones, log‑structured ingestion, and snapshot reads combine into a system that is both **fast** and **correct**.

---

## Time-series data modeling and access patterns

Time‑series data is a sequence of observations keyed by time (log events, sensor readings, market ticks). A time‑indexed system is largely defined by its **dominant access patterns**.

### The core workload traits

Time‑series workloads typically exhibit:

- **High volume, high throughput.** It is normal to store billions of points and ingest very quickly.
- **Mostly append‑only writes.** Most new data arrives “at the end of time”. Updates to old points are uncommon compared to inserts.
- **Time‑bounded queries dominate.** Nearly all user queries specify a time window: “from 1pm to 2pm”, “last hour”, “until now”.
- **Retention and downsampling are first‑class.** Old data is deleted in bulk (by time range) or compacted into lower‑resolution summaries.

### The key implication

If you know the primary workload is: **append + range scan + bulk eviction**, then the “correct” storage choices almost always bias toward:

- *sorted data* (so you can find boundaries in `O(log n)`),  
- *contiguous layouts* (so the scan is bandwidth‑efficient), and  
- *bulk maintenance* (so deletes and out‑of‑order data are handled with compaction rather than in‑place mutation).

This is why many time‑series engines lean toward log‑structured + sorted‑run formats (LSM/TSM-style), and why Timelog’s HLD does the same.

---

## Sorted contiguous arrays

One foundational structure for time‑indexed systems is a **sorted contiguous array** of records `(ts, payload)` (or, for Timelog V1, `(ts, handle)`).

### Why sorted arrays are so effective

A sorted contiguous layout maps directly to CPU and memory behavior:

1. **Range scans become sequential scans.**  
   After you find the start and end offsets, scanning `[t1, t2)` is a forward walk over memory — predictable, prefetch‑friendly, and high throughput.

2. **Boundary finding is cheap (`O(log n)`).**  
   Binary search gives the range offsets. The scan work is proportional to the result size.

3. **Memory is compact and predictable.**  
   Contiguous arrays avoid per-node pointers (as in trees), reducing overhead and cache misses.

4. **The core invariant is simple.**  
   “Records are in non‑decreasing timestamp order” is an invariant you can reason about, test, and preserve during maintenance.

### Boundary finding: `lower_bound` and half-open ranges

For a sorted timestamp array `A[0..n)`:

- `lower_bound(t)` returns the smallest index `i` such that `A[i] >= t` (or `n` if none).
- `upper_bound(t)` returns the smallest index `i` such that `A[i] > t` (or `n` if none).

A half‑open time range query `[t1, t2)` maps to:

- `i1 = lower_bound(t1)`
- `i2 = lower_bound(t2)`
- scan `A[i1..i2)`

This is one reason `[t1, t2)` is widely used: it composes cleanly with boundary finding and avoids off‑by‑one ambiguity.

### Strengths and weaknesses (the “minimum” you must remember)

Strengths:

- Finding time boundaries is `O(log n)`; scanning a range is `O(k)` where `k` is output size.
- Sequential scans are cache‑ and bandwidth‑efficient.
- The layout is simple and tends to be SIMD‑friendly for comparisons and filtering.

Weaknesses (and why Timelog uses LSM-style ingestion):

- Out‑of‑order insertion into a single global sorted array is expensive (shifts → `O(n)` worst‑case).
- Deletions either create holes (requiring masks) or force rewriting.
- A single huge array has poor locality for maintenance; you want **pages/segments** as rewrite units.

### Engineering notes (expanded): pages and fence pointers

Real systems rarely binary search a “monolithic 400M-row array” directly. Instead they use a two‑level scheme:

1. A **catalog / fence-pointer index**: store the first timestamp (or min/max) of each page/block in a small array.
2. Binary search this small index to locate candidate pages.
3. Binary search *within* a candidate page to find exact offsets.

This reduces cache-missy random probes and makes maintenance manageable.

---

## Bitmap indexes and deletion masks

A bitmap index is a **bit array** where each bit represents membership (present/absent) or a boolean property.

In Timelog’s context, the most important use is **deletion tracking** without costly in‑place mutation.

### Deletion as a first-class problem

Time‑series retention (“delete everything before cutoff”) is a bulk delete. If your base representation is immutable (or treated as immutable for readers), you need a way to:

- make deletes *logically* visible immediately, and  
- reclaim space later without blocking readers.

### Two conceptual delete representations

1. **Range tombstones** (interval deletes)  
   Represent deletes as a set of time intervals `[a, b)` that are logically deleted.

   - Great for “delete older than T” or “delete [t1, t2)”.
   - Membership test is: “is this timestamp in any tombstone interval?”.

2. **Per-page / per-block deletion masks** (bitsets)  
   Represent deletes inside a block as a bitset of row positions.

   - Great when only part of a page is affected (e.g., boundary pages of a delete range).
   - The scan checks the mask to skip deleted rows.

A practical system often uses both:
- range tombstones for large deletes,
- per-page masks for partial overlap.

### Why bitsets work well (and where they hurt)

Advantages:

- Very fast boolean logic (`AND/OR/XOR`) on machine words.
- Efficient counting via `popcount`.
- Natural fit for batch filtering: apply a delete mask to a vector of rows.

Costs and pitfalls:

- A bitset is sized by *the number of rows*, not by “how many are deleted”.
- For large domains, a naive global bitmap can be too large (hence compressed schemes like Roaring).
- Masks add per-row checks during scans; compaction is required to reclaim performance.

### Engineering notes (expanded): “delete debt” and compaction

Logical deletes are cheap, but they create debt:

- too many tombstones increases membership-test overhead,
- too many deleted rows in pages increases wasted scan work.

Therefore you must understand:

- **tombstone coalescing** (merge overlapping delete intervals),
- **folding deletes during compaction** (rewrite pages and drop deleted records),
- and the performance dynamics of “tombstone density”.

---

## Pagination in time-series queries

A time-range query can return huge results. Pagination is how you return results safely and predictably.

### The three common pagination strategies

1. **Offset pagination (limit/offset).**  
   Simple for humans; can be expensive for large offsets and fragile under concurrent inserts (because new rows shift later offsets).

2. **Time-window pagination.**  
   Page by time (e.g., 5 minutes per page). Natural for time‑series; counts per page vary.

3. **Cursor / continuation token pagination.**  
   Page using a token returned by the server (“resume from here”). Usually the most robust.

### Engineering notes (expanded): cursor semantics under duplicates

A subtlety that matters for Timelog V1:

- duplicates at the same timestamp exist,
- tie order among duplicates is *unspecified*,
- therefore a cursor that is “just the last timestamp” can be ambiguous.

Two safe patterns are:

- **time-window paging** (cursor is `(t_start, t_end)`), or  
- **cursor includes an internal position** (e.g., an offset inside a specific immutable snapshot / segment).

Because Timelog’s read model is snapshot-based, pagination tokens should typically be interpreted **within a snapshot**, not across arbitrary evolving state.

---

## CPU-efficient execution and vectorized principles

“Vectorization” in systems design means: structure your data and algorithms so the CPU executes **tight, predictable loops** over contiguous memory, minimizing stalls.

Even in Timelog V1 (handle-based, not analytics), vectorization matters for:

- scanning timestamp arrays,
- applying bitsets/masks for deletions,
- merging and filtering in batches.

### The relevant CPU mental model

Modern CPUs are limited less by arithmetic and more by:

- cache misses (waiting for memory),
- branch mispredictions (pipeline flushes),
- poor locality (pointer chasing),
- instruction overhead per element (too much per-row work).

### Practical principles (portable across languages)

A CPU-efficient design tends to:

1. **Batch work (vector-at-a-time)** instead of tuple-at-a-time.  
   Operate on blocks/pages or arrays of timestamps.

2. **Prefer contiguous hot fields.**  
   Keep timestamps and masks contiguous so the CPU can prefetch.

3. **Minimize unpredictable branches.**  
   Turn conditionals into masks where possible; use fast paths (fully live / fully deleted pages).

4. **Exploit word-at-a-time operations.**  
   Bitsets and other packed representations enable wide operations naturally.

A canonical reference for this approach is the MonetDB/X100 work on “vector-at-a-time” query execution.

### Engineering notes (expanded): what Timelog can and cannot vectorize

- Timelog can make the *index path* CPU-efficient (timestamps, metadata, masks, merges).
- If payloads are opaque handles (e.g., Python object references later), dereferencing payloads will still be cache-unfriendly. Timelog’s “win” is selecting and narrowing by time quickly, not making payload objects contiguous.

---

## LSM trees and memtable-segment flushing

Log-Structured Merge (LSM) design is a core pattern for write-heavy workloads:

- writes go to a **memtable** (fast mutable structure),
- periodically flushed into immutable **sorted runs/segments**,
- background compaction merges runs to control overlap and cost.

The classical LSM story is on-disk (WAL + SSTables). For Timelog V1, the same idea applies **in-memory**:

- the “runs” can be immutable in-memory segments,
- compaction can rewrite pages in memory,
- atomic publication makes new segments visible without disrupting readers.

### Why LSM-style design exists (first principles)

LSM exists because “keep everything in one sorted structure” is expensive for writes.

LSM transforms the problem:

- *Instead of* paying `O(n)` for insertion into a global sorted array,
- you accept temporary disorder in a write-optimized structure,
- and later pay merging cost in batches (like merge sort).

### Memtable requirements (conceptual)

For Timelog’s workload (mostly increasing timestamps), the memtable should:

- accept high-throughput inserts,
- support ordered iteration (or produce ordered iterators efficiently),
- support `lower_bound`-like range start.

Candidate families (not prescriptions):

- skip lists (ordered; good for concurrency in some systems),
- balanced trees,
- run buffers (append + sort at flush),
- hybrids exploiting “mostly-in-order” writes.

### Flush and compaction

Flushing produces a new immutable run that is:

- sorted by timestamp,
- organized into pages/blocks,
- described by metadata (min/max timestamps per page).

Compaction merges runs:

- rewriting them into fewer, larger, less-overlapping runs,
- folding tombstones (deletes) into output pages,
- reclaiming wasted space.

### A conceptual pipeline diagram

```mermaid
flowchart LR
  W[Writes] --> MT[Memtable (mutable)]
  MT -->|flush| R0[Run / Segment (immutable)]
  R0 -->|compaction| R1[Compacted Segments]
  R1 -->|publish| M[Manifest / Catalog (atomic swap)]
  M --> Q[Queries read snapshot]
```

---

## Snapshot isolation and read/write concurrency

Snapshot isolation ensures each query reads a **consistent view** of the dataset “as of” query start.

For Timelog, this underpins:

- multiple readers without global locks,
- background maintenance (flush/compact) without blocking readers,
- atomic manifest swaps.

### Conceptual techniques to know

1. **Copy-on-write snapshots.**  
   Readers see immutable structures; writers build new ones and swap pointers.

2. **MVCC (multi-version concurrency control).**  
   Multiple versions exist; readers choose versions ≤ snapshot version.

3. **Immutable segment architecture (LSM-style).**  
   Most data is already immutable; reads select a stable set of segments.

Timelog’s V1 HLD aligns strongly with (1) and (3): immutable segments plus an atomically published manifest.

### The core proof obligation

To reason about correctness, you need invariants such as:

- each segment iterator is ordered,
- the set of segments a query reads does not change during the query,
- tombstones visible to the query do not disappear mid-query.

If these hold, merge + filter produces correct results.

### Engineering notes (expanded): reclamation is part of snapshotting

A snapshot system must eventually reclaim old segments. The general concept (tech-agnostic) is:

- readers “pin” a version,
- writers publish a new version,
- old versions are freed only after no readers can reference them.

Different systems implement this with reference counts, epochs, hazard pointers, or garbage collection. The minimum is understanding the *idea* and the correctness requirement.

---

## Log-structured merge systems and write-optimized storage

Log-structured design generalizes the LSM pattern:

- treat writes as appends to a log,
- perform organization and cleanup via background merges.

### Why it fits time-series

Time-series is naturally log-like:

- new points typically have increasing time,
- bulk deletes align with time ranges,
- historical data becomes “cold” and changes rarely.

This enables:

- **hot/cold separation**: compact the recent time window frequently, leave old data alone.

### The key trade-off: read amplification vs write amplification

Log-structured systems are always balancing:

- fast writes now, merges later, and
- potentially reading across multiple runs during queries.

You should understand how to bound worst-case query cost by limiting:

- number of runs,
- overlap in time ranges,
- and tombstone growth.

---

## Compressed indexes: Roaring bitmaps

Naive bitmaps are fast but can be too large when the domain is huge and sparse.

Roaring bitmaps compress by chunking the space of 32-bit integers into `2^16`-sized blocks (“containers”) and choosing a representation per container:

- a **sorted array container** for sparse chunks,
- a **bitmap container** for dense chunks,
- (many implementations also include a run container for long runs).

Implementations typically switch representations based on cardinality thresholds (commonly around 4096).

### Why Roaring is a “systems” idea, not just a compression trick

Roaring is successful because it simultaneously improves:

- **space** (fits more in cache),
- **speed** (fast unions/intersections via word-at-a-time operations),
- **predictability** (container-level metadata like cardinality enables fast paths).

### When compressed bitmaps matter for Timelog

For Timelog V1, the most relevant conceptual uses are:

- compact representation of large deletion sets (when per-page bitsets become too costly),
- representing sets of pages/blocks affected by tombstones,
- presence/absence maps for coarse-grained pruning.

But a key principle: **do not compress prematurely**. For many page sizes, a plain bitset per page is already tiny (hundreds of bytes) and simpler.

---

## Range-based pruning and query optimization

Query optimization in time-indexed systems starts with one objective:

> avoid reading data that cannot possibly match the time range.

### The pruning ladder

A typical pruning approach operates at multiple granularities:

1. **Segment-level pruning.**  
   If a segment covers `[min_ts, max_ts]` and the query is `[t1, t2)`, skip if no overlap.

2. **Page/block-level pruning.**  
   Inside a segment, pages have their own `[min_ts, max_ts]`. Skip pages with no overlap.

3. **Within-page boundary finding.**  
   Binary search inside the page’s timestamp array to find offsets.

This turns a “huge scan” into “small scan + sequential read”.

### Additional pruning techniques to know (even if not used in V1)

- **Series/key pruning.** If you have many series, prune by key before time.
- **Bloom filters.** Quickly test “does this run contain this key?” to skip runs.
- **Index sampling / sparse indexes.** Keep a small mapping from time to offset.

Timelog V1 is time-index-centric, but engineers should recognize these patterns.

### Engineering notes (expanded): fence pointers

A crucial theoretical idea is the “fence pointer” index:

- store the first key of each block/page in a small in-memory index,
- use binary search on that small index to find the first relevant block.

This is the standard pattern behind many sorted-run formats (SSTables, columnar row groups, etc.) and maps directly to Timelog’s manifest/page catalog design.

---

## K-way merge as the core query algorithm

Once data is split across multiple sorted components (memtable snapshot + multiple immutable runs), reads become:

1. prune candidate components,
2. seek each to the time range,
3. **merge sorted iterators**,
4. apply tombstones / delete masks,
5. emit results.

This merge step is where “systems ideas” and “algorithmic ideas” meet.

### The canonical k-way merge

Given `k` sorted iterators, produce a globally sorted stream by:

- keeping a min-heap keyed by the current head element of each iterator,
- repeatedly popping the smallest timestamp and advancing that iterator.

Time complexity is:

- `O(N log k)` comparisons for `N` output records,
- plus seek and pruning overhead.

A minimal pseudocode sketch:

```
heap = []
for it in iterators:
    if it.has_next():
        heap.push((it.peek_ts(), it))

while heap not empty:
    (ts, it) = heap.pop_min()
    rec = it.next()
    if not deleted(rec):
        emit(rec)
    if it.has_next():
        heap.push((it.peek_ts(), it))
```

### Where systems reality shows up

- If you allow too many small runs, `k` grows and `log k` hurts.
- If tombstones are not folded, you do extra work for deleted data.
- If runs overlap heavily, you do extra merge work.

Compaction exists largely to keep k-way merge cheap.

### Duplicates and tie order in Timelog V1

Timelog V1 preserves duplicates and does not guarantee stable tie order. That implies:

- the merge comparator is timestamp only,
- no “newer overwrites older” semantics are required,
- results are non-decreasing by timestamp; ties may appear in any order.

---

## Trade-offs in systems design

Every serious design decision is a trade-off. The theoretical minimum is being able to *name* the trade-off and reason about its consequences.

Key trade-offs that appear in Timelog-like systems:

- **Performance vs maintainability.**  
  Low-level tricks can create fragile complexity. Clear invariants and boundaries are essential.

- **Write optimization vs read optimization.**  
  LSM-style designs favor write throughput but require merge work and can create read amplification.

- **Memory vs CPU.**  
  Indexes and metadata reduce CPU work but consume memory. Compression saves memory but costs CPU.

- **Simplicity vs feature richness.**  
  Every new feature increases the state space you must test and the invariants you must preserve.

A mature system makes these trade-offs explicit and revisits them only when requirements change.

---

## Clean layering and interface boundaries

Clean boundaries are not “style” — they are how you prevent performance engineering from turning into an unmaintainable tangle.

A layered view that maps well to Timelog:

- **API layer**: user-facing operations, input validation, convenience wrappers.
- **Core engine**: query planning (pruning + merge), snapshot creation, orchestration.
- **Storage/index layer**: segments, pages, tombstones, and iterators.

The key architectural principle:

> layers communicate through *narrow* interfaces, and internal representations do not leak outward.

This keeps you free to change internal structures (e.g., tombstone representation) without rewriting the whole system.

---

## Theoretical minimum checklist for Timelog engineers

An engineer should be comfortable with these concepts before touching the core.

### Workload and invariants

- Explain the dominant time-series access patterns (append, range scan, retention).
- Define the core ordering invariant (“non-decreasing timestamps per component”).
- Explain half-open intervals `[t1, t2)` and why they compose.

### Data structures

- Sorted arrays and binary search (`lower_bound`, `upper_bound`).
- Paging / blocking and fence-pointer indexes.
- Bitsets / bitmaps and word-at-a-time operations.
- Interval sets (range tombstones) and coalescing.

### Core algorithms

- Range pruning using min/max metadata.
- k-way merge with a heap, and why `k` matters.
- Compaction as merge sort + delete folding.
- Understanding read amplification and write amplification.

### Systems concepts

- CPU cache behavior, locality, sequential scans, branch prediction.
- “Vectorization” as batch processing and tight loops.
- Snapshot isolation as “stable view” for queries.
- Safe reclamation of old versions (conceptually: pin/publish/reclaim).

### Architecture and trade-offs

- Ability to articulate trade-offs and justify a choice.
- Clean boundaries: iterators as a contract, immutable segments, manifest/catalog concepts.

If an engineer can discuss these fluently, they have the “theoretical minimum” to work on Timelog’s core correctly.

---

## Glossary

**Append-only** — data is added at the end; old data is not modified in-place.  
**Compaction** — rewriting multiple immutable runs into fewer runs, folding deletes and reducing overlap.  
**Fence pointer** — a small index storing boundary keys of blocks/pages to speed navigation.  
**Half-open interval** — `[t1, t2)` includes `t1` and excludes `t2`.  
**LSM** — Log-Structured Merge: write buffering + immutable sorted runs + compaction.  
**Manifest / catalog** — metadata structure describing which segments/pages are visible to readers.  
**Memtable** — mutable in-memory structure holding recent writes before flush.  
**Run / segment** — immutable sorted component produced by flush or compaction.  
**Tombstone** — delete marker written as data and applied logically until reclaimed.

---

## References and further reading

The PDF cited several canonical sources and project materials. Below is a cleaned list with short “why it matters” annotations.

### Foundational papers / docs

- **O’Neil et al., “The Log‑Structured Merge‑Tree (LSM‑Tree)”**  
  Why: foundational model for buffering writes and merging sorted runs.

- **InfluxDB TSM / storage engine documentation**  
  Why: time-series specific adaptations of log-structured storage, tombstones, compactions.

- **Lemire et al., “Roaring Bitmaps”**  
  Why: practical compressed bitmap format with strong performance properties.

- **Boncz et al., MonetDB/X100 / vectorized execution**  
  Why: explains why “vector-at-a-time” execution is faster on modern CPUs.

### Software design references (for long-term maintainability)

- **Robert C. Martin, “Clean Architecture”**  
  Why: clean boundaries and dependency management; useful when optimizing low-level systems.

- **Ford et al., “Software Architecture: The Hard Parts”**  
  Why: practical framework for reasoning about trade-offs.

### Project-provided resources (commonly shipped alongside Timelog)

If these PDFs exist in your project repository, they align naturally with the sections above:

- `lsmtree.pdf`
- `roaring_bitmaps.pdf`
- `MonetDb.pdf`
- `In-memory indexing and the Time‑Structured Merge Tree (TSM) _ InfluxDB OSS v1 Documentation.pdf`

---

*End of document.*
