"""Formal reference model for timelog checker.

This module provides a deterministic, executable model of the abstract
insert/delete/query semantics used by the correctness checker.
"""

from __future__ import annotations

import bisect
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class SnapshotMetadata:
    snapshot_seq: int
    watermark_seq: int


@dataclass
class Tombstone:
    t1: int
    t2: int
    seq: int


class ReferenceModel:
    """Single-threaded formal oracle with seq/watermark metadata."""

    def __init__(self) -> None:
        self._op_seq = 0
        self._max_tomb_seq = 0
        self._index: list[tuple[int, int]] = []  # (ts, rid)
        self._rows_by_rid: dict[int, Any] = {}
        self._row_insert_seq: dict[int, int] = {}
        self._row_watermark_seq: dict[int, int] = {}
        self._tombstones: list[Tombstone] = []

    @property
    def op_seq(self) -> int:
        return self._op_seq

    @property
    def watermark_seq(self) -> int:
        return self._max_tomb_seq

    def insert_rows(self, rows: list[Any]) -> None:
        if not rows:
            return
        for row in rows:
            self._op_seq += 1
            rid = int(row.rid)
            ts = int(row.ts)
            bisect.insort(self._index, (ts, rid))
            self._rows_by_rid[rid] = row
            self._row_insert_seq[rid] = self._op_seq
            self._row_watermark_seq[rid] = self._max_tomb_seq

    def delete_range(self, t1: int, t2: int) -> None:
        self._op_seq += 1
        self._max_tomb_seq = self._op_seq
        self._tombstones.append(Tombstone(int(t1), int(t2), self._op_seq))

    def _snapshot(self) -> SnapshotMetadata:
        return SnapshotMetadata(snapshot_seq=self._op_seq, watermark_seq=self._max_tomb_seq)

    def _visible_at(self, rid: int, ts: int, snap: SnapshotMetadata) -> bool:
        if self._row_insert_seq.get(rid, snap.snapshot_seq + 1) > snap.snapshot_seq:
            return False
        row_wm = self._row_watermark_seq.get(rid, 0)
        for tomb in self._tombstones:
            if tomb.seq > snap.snapshot_seq:
                continue
            if tomb.t1 <= ts < tomb.t2 and tomb.seq > row_wm:
                return False
        return True

    def query_range(self, t1: int, t2: int) -> tuple[list[Any], SnapshotMetadata]:
        snap = self._snapshot()
        lo = bisect.bisect_left(self._index, (int(t1), -1))
        hi = bisect.bisect_left(self._index, (int(t2), -1))
        out: list[Any] = []
        for ts, rid in self._index[lo:hi]:
            if self._visible_at(rid, ts, snap):
                out.append(self._rows_by_rid[rid])
        return out, snap

    def query_since(self, t1: int) -> tuple[list[Any], SnapshotMetadata]:
        snap = self._snapshot()
        lo = bisect.bisect_left(self._index, (int(t1), -1))
        out: list[Any] = []
        for ts, rid in self._index[lo:]:
            if self._visible_at(rid, ts, snap):
                out.append(self._rows_by_rid[rid])
        return out, snap

    def query_point(self, ts: int) -> tuple[list[Any], SnapshotMetadata]:
        snap = self._snapshot()
        lo = bisect.bisect_left(self._index, (int(ts), -1))
        hi = bisect.bisect_right(self._index, (int(ts), 2**63))
        out: list[Any] = []
        for cur_ts, rid in self._index[lo:hi]:
            if self._visible_at(rid, cur_ts, snap):
                out.append(self._rows_by_rid[rid])
        return out, snap

    def query_all(self) -> tuple[list[Any], SnapshotMetadata]:
        snap = self._snapshot()
        out: list[Any] = []
        for ts, rid in self._index:
            if self._visible_at(rid, ts, snap):
                out.append(self._rows_by_rid[rid])
        return out, snap
