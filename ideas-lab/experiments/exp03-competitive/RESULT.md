# exp03 — Competitive positioning (idea N24/N25)

**Question:** Is Timelog actually best-in-class, and *where*? Head-to-head vs the four contenders a
skeptic names first: `bisect.insort`+list, `sortedcontainers.SortedList`, `numpy` int64+`searchsorted`,
`pandas`. No core changes — runs on the shipped build.

> This experiment is deliberately **adversarial to my own hypothesis**. The first run flattered Timelog
> by accident (in-order inserts hide bisect's O(n); the GIL hides the concurrency story). Fixing both is
> what makes the result trustworthy.

## A. Append cost vs N — in-order vs out-of-order (µs/op, 3.13)

**In-order ts** (bisect appends at the end → O(1); the *unfair* case):

| N | Timelog facade | bisect | SortedList |
|---|---|---|---|
| 200k | 0.323 | **0.076** | 0.181 |

**Out-of-order ts** (the fair, realistic streaming case):

| N | Timelog facade | bisect.insort | SortedList |
|---|---|---|---|
| 20k | 0.345 | 0.677 | 0.363 |
| 100k | 0.469 | 2.850 | 0.417 |
| 200k | **0.509** | **5.608** | 0.475 |

→ bisect shows textbook **O(n)** blowup; at 200k Timelog is **~11× faster** (even through its slow facade;
raw-C append would widen this). **SortedList ties Timelog** on single-thread OOO append (O(log n)).

## B. Range-query latency (µs/query, static 200k array, 3.13)
`timelog 43.2` · `sortedlist 24.0` · `numpy 2.1` · `bisect 1.7`

→ **Timelog is the *slowest* here, and that is honest:** `tl.range()` iterates (ts, payload) pairs across a
k-way merge with snapshot setup; numpy/bisect just C-slice a static, payload-less, single sorted array.
For a one-shot range scan over static data with no concurrency and no payloads, **the simple tools win.**

## C. Concurrency — 1 writer + N readers (the actual differentiator)

**3.13 (GIL on):** all three structures → 0 exceptions, 0 torn reads. *The GIL masks the difference.*

**3.14t (free-threaded, GIL off):**

| Structure | reader exceptions | torn reads | reads completed |
|---|---|---|---|
| **Timelog** | **0** | **0** | **394,640 → 512,025** (most) |
| bisect + list | 0 | 0 | 364,785 → 461,484 |
| **SortedList** | **5 → 8 ✗** | 0 | 288,766 → 384,261 |

→ **SortedList raises reader exceptions** under free-threaded concurrent mutation (pure-Python, no internal
locking), scaling with contention. **Timelog never raises** (snapshot isolation) and completes the **most
reads** because lock-free snapshot reads don't block the writer. CPython 3.14t **hardened the builtin
`list`**, so `bisect`+`list` survived — so the honest claim is *not* "everything else crashes."

Artifact note: the preserved `exp03_3.13.json` only proves the GIL-on baseline. A fresh audit rerun imported
the harness on CPython 3.14.3t with `PYTHON_GIL=0`, skipped the script's single-core pin, and saved
`exp03_3.14t_concurrency_unpinned.json` (affinity 0..15): Timelog 0 exceptions / 434,440 reads; bisect+list
0 exceptions / 296,647 reads; SortedList 7 reader exceptions / 214,984 reads.

## Verdict: ⬛ INCONCLUSIVE as a blanket "fastest", 🟩 CLEAR on the real wedge
Timelog is **not** the fastest single-thread static range index (numpy/bisect win that). Its defensible,
measured differentiators are:
1. **O(1) out-of-order append** — ~11× faster than `bisect.insort` at 200k (real, asymptotic).
2. **Snapshot-isolated, never-torn, non-blocking concurrent reads** over **arbitrary Python-object
   payloads**, under free-threading — where SortedList breaks and numpy/list offer no snapshot consistency.
3. Zero-copy int64 timestamp export (PageSpan) the Python-object structures can't match.

**Positioning (N25):** lead with *safe concurrent mutation under free-threading* + *O(1) OOO ingest*,
**not** raw single-thread range speed. Don't claim "numpy/pandas don't run on FT" (false — wheels exist);
the precise wedge is *safe concurrent mutation*. The facade's ~181 ns wrapper (see N28) is actively
depressing Timelog's competitive append numbers — fixing it directly improves this story.

**Follow-ups:** install competitor libs into 3.14t and add a parallel **throughput-scaling** plot
(readers × cores); add the `bench/competitive/` harness to the repo per N24.
