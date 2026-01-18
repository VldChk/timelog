# Timelog: Fast Time-Range Indexing and Eviction for Python Objects

## The north star vision

Timelog (Python-object mode) is an in-memory, time-indexed multimap of object references with an LSM-style ingest buffer and immutable, time-sorted segments, optimized for fast time-range selection and fast time-based eviction—not for vectorized analytics on payloads.

That sentence is deliberately opinionated. Timelog is not trying to be “a faster pandas,” and it is not trying to compete with a full time-series database. It is trying to make one family of operations—finding “the right slice of time” and retaining only “the right slice of history”—feel native, predictable, and cheap inside Python workflows.

## Problem statement

If you work with time-series or event-style data in Python—streams, logs, windowed processing, incremental ingestion from files, or any pipeline where “time” is the organizing axis—you quickly end up asking the same questions over and over:

You want all records between two timestamps. You want everything in the last five minutes. You want to drop everything older than fifteen minutes. You want the time boundaries to be the primary way you navigate, filter, and enforce retention, not an afterthought.

Python gives you great expressiveness, but its native containers are not built around time as an index. A list is good at appends but gives you O(n) scans unless you carefully maintain a parallel sorted structure. A dict is great for point lookups but has no natural notion of “range” and doesn’t preserve a time order you can exploit. Higher-level tools can solve this, but they often push you toward a much heavier model (dataframes, columnar engines, full storage layers) when what you really need is a lightweight, always-on “time index” underneath whatever you already have.

The practical pain is not that Python can’t compute. The pain is that time-boundary selection and retention become the hidden tax inside everything else. You end up re-implementing partial indexing strategies, or you accept linear scans, or you adopt a heavy database-like dependency for a problem that is conceptually simpler: “keep my objects in time order, let me slice by time fast, and let me evict old history predictably.”

Timelog exists to remove that tax.

## Overview

At its core, Timelog treats a timestamp the way arrays treat an integer index. You put in records keyed by an int64 Unix timestamp (seconds, milliseconds, microseconds, or nanoseconds depending on how you initialize it), and you ask for ranges using half-open intervals like [t1, t2). That choice is not pedantry; it is what makes windowing and chaining operations compose cleanly without off-by-one ambiguity.

The value stored alongside each timestamp is not interpreted by Timelog. In the “Python-object mode” that motivates the project, the value is an opaque handle that will later correspond to a CPython object reference. Timelog does not chase pointers for you, does not assume values are numeric, and does not claim it can run vectorized analytics over payloads. The contract is narrower and, for many pipelines, more useful: Timelog makes the time selection step fast and makes retention a first-class operation.

Internally, Timelog is designed around the observation that time-series writes are usually mostly increasing but never perfectly increasing. If you require perfect monotonicity, one out-of-order event—a single late arrival—forces you into expensive middle insertions and unpredictable latency spikes. Timelog avoids that cliff by making one rule non-negotiable: all writes go through a delta layer first. New records are accumulated in a mutable ingest buffer (a memtable), and periodically that buffer is sealed and flushed into immutable, time-sorted segments. Those segments are laid out in pages—cache-friendly contiguous blocks with metadata like min/max timestamp and row counts—so that queries can prune whole pages quickly and then do tight, predictable scans where needed.

Reads are built on a snapshot model. When you query Timelog, you read against a stable view consisting of an immutable manifest (the catalog of segments/pages) plus a stable view of the memtable as of that moment. That snapshot is what makes background maintenance possible without “dirty reads.” Timelog can build new immutable segments, reclaim deletes, and then publish a new manifest via an atomic pointer swap. New queries see the new world; in-flight queries keep reading the old one, which remains valid because it is immutable.

Deletes are treated the same way as writes: as time-based intent that becomes visible at snapshot boundaries and is physically reclaimed later. The dominant operation Timelog optimizes for is time-range deletion—retention policies like “drop everything older than T,” or explicit deletes of [t1, t2). Instead of doing expensive in-place removal, Timelog records tombstones and applies them during reads; compaction then folds them into new segments and drops fully deleted pages/segments when possible. This is how you keep latency predictable in an append-heavy system while still supporting eviction and cleanup.

One subtle but important decision in V1 is how duplicates are handled. Multiple records may share the same timestamp, and Timelog preserves them. What Timelog does not guarantee in V1 is stable ordering among equal timestamps across insert history or compactions. The system guarantees non-decreasing timestamp order in query results; ties are unspecified. That tradeoff keeps the core smaller and faster while still matching the needs of most retention and range-query workloads.

The end result is not a database. It is a specialized in-memory time index that can sit under Python code the way a queue or map sits under other workflows. You can append events, ask for the last N minutes, or evict old history, and the cost is driven by page pruning, binary search boundaries, and a bounded merge across a small number of sorted components—not by scanning everything you ever stored.

If you imagine publishing this on HackerNews, the honest headline isn’t “fast time-series analytics in Python.” The honest headline is: “make time slicing and time eviction cheap enough that you stop thinking about them.”
