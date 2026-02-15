# Timelog V2 LLD (Compaction Policy)

This document defines the compaction-policy LLD for Timelog V2. It is
disjoint in scope with the write-path LLD and covers selection, scheduling,
heuristics, and L1 output rules. It aligns with:
- proposal_unified.md
- timelog_v2_c_hld.md
- timelog_v2_lld_storage_pages.md
- timelog_v2_lld_read_path.md

Scope:
- When to compact (triggers and heuristics).
- Which L0/L1 segments to compact (selection).
- How to build L1 outputs (windowed non-overlap).
- Manifest updates for compaction.

Out of scope:
- Memtable ingestion and flush (write-path LLD).
- Read-path iterators and query planning (read-path LLD).

---

## 1. Compaction goals

1) Enforce L1 non-overlap by time window.
2) Bound read amplification (limit K in k-way merge).
3) Fold tombstones to reclaim deletes.
4) Keep compaction work bounded and predictable.

---

## 2. Invariants required by the read path

Compaction must guarantee:
- L1 segments are aligned to fixed windows.
- L1 segments do not overlap by time.
- L1 segments contain no tombstones (folded during compaction).
- L0 segments may overlap; compaction reduces their count.

These invariants are required by the read-path LLD pruning rules.

---

## 3. Configuration inputs

Key config parameters:
- window_size (time units, tl_config_t; if 0, choose default at init)
- window_origin (tl_config_t, default 0)
- max_delta_segments (L0 bound)
- max_compaction_inputs (optional cap)
- max_compaction_windows (optional cap)
- compaction_target_bytes (optional cap)
- delete_debt_threshold (ratio, default 0.0 = disabled)

---

## 4. Window mapping

Definitions:

window_id = floor((ts - window_origin) / window_size)
window_start = window_origin + window_id * window_size
window_end = window_start + window_size

All L1 outputs must satisfy:
window_start <= ts < window_end

---

## 5. Triggering compaction

Compaction is requested when any of:
- L0 count >= max_delta_segments
- explicit tl_compact() call
- delete debt exceeds delete_debt_threshold (optional)
- time-based schedule (optional)

Write path only signals a request. The policy here decides what to compact.

Delete debt metric (window-scoped):
- Compute tombstone_covered_span as the union length of tombstone intervals
  within a window (clip to [window_start, window_end)).
- delete_debt_ratio = tombstone_covered_span / window_size.
- If delete_debt_ratio >= delete_debt_threshold, request compaction for that
  window.

---

## 6. Selection policy (baseline)

### 6.1 Baseline policy (simple, correct)

1) Select all L0 segments as inputs.
2) Compute global [min_ts, max_ts) across selected L0 records AND tombstones.
3) Determine the set of window_ids covered by that range.
4) Select all L1 segments whose windows intersect those window_ids.

Compaction inputs = selected L0 + selected L1.

This is simple and guarantees L1 non-overlap.

### 6.2 Bounded policy (heuristic)

To limit work per compaction:
- Select the oldest N L0 segments (N <= max_compaction_inputs).
- Compute covered windows from those L0 segments (records + tombstones).
- Select only L1 segments in those windows.
- If max_compaction_windows is set, cap the number of windows and delay the rest.

This reduces latency at the cost of more frequent compactions.

### 6.3 Tombstone-driven policy (optional)

If tombstone density in a window exceeds a threshold:
- prioritize that window for compaction even if L0 count is low.

---

## 7. Compaction merge algorithm

### 7.1 Inputs
- L0 segments (may have tombstones)
- L1 segments (tombstones should be empty but included defensively)

### 7.2 Tombstone set
- Build an effective tombstone set as the union of all tombstones from L0
  (and L1 if present).
- Clip tombstones to the compaction output range.

Residual tombstones:
- If a tombstone extends beyond the selected output windows (due to caps),
  the residual intervals outside the output range must remain visible.
- Emit a tombstone-only L0 segment carrying the residual intervals, or defer
  those windows and include the full tombstone range in a later compaction.

### 7.3 Merge
- Create iterators for all input segments.
- Perform k-way merge by timestamp.
- Skip records covered by effective tombstones.

### 7.4 Output partitioning
- Split the merged stream on window boundaries.
- For each window with live records, build an L1 segment:
  - pages and catalog from storage LLD
  - window_start/window_end set
  - tombstones = NULL

If a window has no live records, emit no segment for that window.

---

## 8. Manifest update rules (compaction)

### 8.1 Build new manifest

1) Copy old L1 list excluding selected windows.
2) Insert new L1 segments for those windows (sorted by window_start).
3) Copy old L0 list excluding selected L0 segments.
4) Keep remaining L0 segments in flush order.

### 8.2 Publish protocol

1) Build outputs off-lock.
2) Acquire publish lock (writer_mu).
3) view_seq = atomic_fetch_add(+1) (odd).
4) Verify manifest pointer unchanged (if changed, abort and retry).
5) Swap manifest pointer to new manifest.
6) view_seq = atomic_fetch_add(+1) (even).
7) Release lock.

Retry policy:
- Retry up to 3 times if the manifest changes during publish.
- If still changing, return TL_EBUSY and let the caller retry later.

Old manifests and segments remain pinned until snapshots release them.

---

## 9. Delete reclamation rules

- Tombstones are folded during compaction.
- Output L1 segments are tombstone-free.
- Fully deleted windows produce no L1 segment.
- V2 always rewrites pages; it does not emit per-page row bitsets.

This reduces delete debt and improves scan performance.

---

## 10. Scheduling and heuristics

### 10.1 Background mode

Priority order:
1) Flush sealed memruns (write-path LLD).
2) Compaction if requested or L0 above threshold.

Fairness rule:
- If L0 >= max_delta_segments, run one compaction step after each flush (or
  after a bounded number of flushes) to prevent starvation.

### 10.2 Manual mode

- tl_maint_step performs one unit of work.
- If flush is pending, flush first.
- Otherwise, perform at most one compaction step.

### 10.3 Heuristic caps

To keep compaction bounded:
- max L0 segments per compaction
- max total input bytes
- max windows per compaction

If caps are exceeded, defer remaining windows to future compactions.

---

## 11. Validation checklist

- All L1 outputs are window-aligned and non-overlapping.
- L1 outputs contain no tombstones.
- All selected L0 segments are removed from manifest.
- All selected L1 windows are replaced in manifest.
- Manifest remains sorted by window_start for L1.

---

## 12. Read-path compatibility check

This policy preserves the assumptions in timelog_v2_lld_read_path.md:
- L1 non-overlap enables efficient pruning by binary search.
- L0 remains small and bounded by max_delta_segments.
- Tombstones are eventually folded, keeping delete filtering cost bounded.

---

This LLD is the definitive compaction-policy reference for V2.

