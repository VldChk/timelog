# Timelog V2 LLD (Background Maintenance)

This document defines the background maintenance subsystem for Timelog V2.
It aligns with:
- proposal_unified.md
- timelog_v2_c_hld.md
- timelog_v2_lld_write_path.md
- timelog_v2_lld_compaction_policy.md
- timelog_v2_lld_read_path.md

Scope:
- Scheduling and concurrency for flush and compaction.
- Coordination with snapshot isolation and atomic manifest swaps.
- Backpressure and maintenance modes (background vs manual).

Out of scope:
- Memtable insertion/sealing details (write-path LLD).
- Compaction selection/merge details (compaction-policy LLD).
- Read-path iterator logic (read-path LLD).

---

## 1. Goals

1) Bound memory usage by flushing sealed memruns.
2) Bound read amplification by compacting L0 into L1.
3) Preserve snapshot isolation during background work.
4) Keep publication atomic and short.

---

## 2. Concurrency model and locks

### 2.1 Locks and atomics

Required synchronization primitives:
- flush_mu: serializes flush build + publish (single flusher at a time).
- writer_mu: serializes publication of new manifests.
- maint_mu: protects maintenance state flags and thread lifecycle.
- memtable.mu: protects the sealed memrun queue.
- memtable.cond: backpressure waiters for sealed queue space (paired with memtable.mu).
- view_seq: seqlock counter for snapshot consistency (atomic fetch-add).

### 2.2 Lock ordering

To avoid deadlocks, enforce a strict ordering:

maint_mu -> flush_mu -> writer_mu -> memtable.mu

Rules:
- Long-running build phases must not hold writer_mu.
- writer_mu is held only during publication (short critical section).
- memtable.mu is used only to access the sealed queue or to mark memruns.
- Writers must not take maint_mu while holding writer_mu. Use deferred
  signaling (set a local flag under writer_mu, then signal under maint_mu).

### 2.3 Publication protocol (summary)

All publication (flush or compaction) uses:
1) writer_mu lock
2) view_seq = atomic_fetch_add(+1) (odd)
3) swap manifest pointer to new manifest
4) update memtable sealed queue (for flush)
5) view_seq = atomic_fetch_add(+1) (even)
6) writer_mu unlock

Snapshots retry if they see odd or mismatched view_seq.

---

## 3. Maintenance modes

### 3.1 Background mode

- A dedicated worker thread performs flush and compaction.
- Write path signals the worker when work becomes available.
- Worker prioritizes flush over compaction.

### 3.2 Manual mode

- No background thread.
- Caller must invoke tl_maint_step() to perform one unit of work.
- Write path returns TL_EBUSY if sealed queue is full.

---

## 4. Maintenance state and work flags

Define a maintenance state struct and worker lifecycle:

```c
typedef enum tl_worker_state {
    TL_MAINT_STOPPED,
    TL_MAINT_RUNNING,
    TL_MAINT_STOPPING
} tl_worker_state_t;

typedef struct tl_maint_state {
    tl_mutex_t  mu;
    tl_cond_t   cond;
    tl_worker_state_t state;
    bool        shutdown;

    bool        flush_pending;
    bool        compact_pending;
} tl_maint_state_t;
```

Semantics:
- state: STOPPED -> RUNNING -> STOPPING -> STOPPED.
- STOPPING means a stop is in progress; callers must not spawn a new worker.
- flush_pending: at least one sealed memrun exists.
- compact_pending: compaction requested by policy or user.

Flags are set under maint_mu and consumed by the worker.
flush_pending is a signal, not a count; flush_mu ensures only one flush runs.

---

## 5. Work scheduling and priority

Priority order (always):
1) Flush sealed memruns (bounds memory).
2) Compaction (bounds read amplification).

Rationale:
- Sealed memruns consume memory and can block writes.
- Compaction improves reads but is less urgent.

Fairness rule:
- After each successful flush, if compaction_needed() is true, run exactly
  one compaction step before flushing more. This prevents L0 growth under
  sustained ingest.

---

## 6. Worker thread loop (background mode)

Pseudo-logic:

```
while not shutdown:
  lock(maint_mu)
  wait until flush_pending or compact_pending or shutdown
  if shutdown: break
  take local copies of pending flags
  clear flags
  unlock(maint_mu)

  if do_flush:
    while flush_one_and_publish() == TL_OK:
      if compaction_needed():
        compact_one_step()
        break

  if do_compact and compaction_needed():
    compact_one_step()
```

Notes:
- flush_one_and_publish() is defined in write-path LLD.
- compaction_needed() and compact_one_step() are defined in compaction-policy LLD.

---

## 7. Flush execution (worker view)

Flush steps:
1) Acquire flush_mu (serialize flush).
2) Peek oldest sealed memrun (memtable.mu); pin it (refcnt++).
   Do not remove it from the sealed queue yet.
   Removal happens under memtable.mu during publish.
3) Build L0 segment off-lock.
4) Publish new manifest and remove memrun from sealed queue under writer_mu
   (then memtable.mu).
5) Release memrun reference after publication; release flush_mu.

If segment build fails:
- memrun remains sealed and visible to snapshots.
- drop pin, set flush_pending again, and retry later.

---

## 8. Compaction execution (worker view)

Compaction steps:
1) Select L0 and overlapping L1 per compaction-policy LLD.
2) Build new L1 segments off-lock (merge + tombstone folding).
3) Publish manifest update under writer_mu.

If manifest pointer changes during build:
- abort and retry later (EBUSY).

Compaction never mutates existing segments; it replaces them by manifest swap.

---

## 9. Backpressure rules

If sealed queue length reaches sealed_max_runs:
- In manual mode: writer returns TL_EBUSY.
- In background mode: either fail-fast or bounded wait (configurable).

Bounded wait should be short and should not hold writer_mu.
Backpressure waits use memtable.cond (distinct from maint_cond) to avoid
mixing unrelated wait predicates.

---

## 10. Snapshot isolation guarantees

Background work must preserve:
- No snapshot sees both a memrun and its flushed segment.
- No snapshot misses data during flush publish.
- No snapshot sees partially updated manifest.

These are guaranteed by:
- view_seq seqlock around manifest swap and memrun removal.
- writer_mu held during snapshot capture (see read-path LLD).
- immutable segments and refcounted manifests.

---

## 11. API surfaces (maintenance control)

### 11.1 tl_maint_start()

- Valid only in background mode.
- Initializes thread and sets state=RUNNING.
- Idempotent if already running.
- Returns TL_EBUSY if a stop is in progress (state=STOPPING).

### 11.2 tl_maint_stop()

- Sets shutdown=true, signals cond, joins worker thread.
- Idempotent if already stopped or stopping.
- STOPPING may return TL_OK before the worker has exited.

### 11.3 tl_maint_step()

Manual mode only:
- Attempts one unit of work.
- Priority: flush one sealed memrun; else compact one step if needed.
- Returns TL_OK if work performed, TL_EOF if nothing to do.

---

## 12. Failure handling and retry policy

- ENOMEM during build: leave sources intact, set pending, retry later.
- EBUSY (manifest changed): retry once or defer.
- Any fatal error should be surfaced to caller via status codes on manual steps
  and logged in background mode.

---

## 13. Validation checklist

- Worker never holds writer_mu during heavy build work.
- view_seq is always even when idle.
- L1 remains non-overlapping after each compaction publish.
- L0 count does not grow unbounded if maintenance runs.

---

## 14. Compatibility notes

This LLD is disjoint in scope (no overlap) with:
- timelog_v2_lld_write_path.md (memtable + flush details)
- timelog_v2_lld_compaction_policy.md (selection/merge details)
- timelog_v2_lld_read_path.md (iterator logic)

It is collectively exhaustive with those LLDs for all maintenance behavior.

---

This LLD defines how background maintenance is scheduled and synchronized
without changing the storage or read/write semantics defined elsewhere.

