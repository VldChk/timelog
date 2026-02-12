#!/usr/bin/env python3
import re
import sys

LINE_RE = re.compile(r"^TLTRACE\s+(.*)$")
KV_RE = re.compile(r"([a-zA-Z0-9_]+)=([^\s]+)")

class Model:
    def __init__(self):
        self.last_seq = 0
        self.active_snaps = set()
        self.in_query = 0

    def step(self, ev, i):
        name = ev.get("ev", "")
        seq = int(ev.get("seq", 0))
        snap = int(ev.get("snap", 0))
        st = int(ev.get("st", 0))

        if seq and seq < self.last_seq:
            raise SystemExit(f"divergence at line {i}: non-monotonic seq {seq} < {self.last_seq}")
        self.last_seq = max(self.last_seq, seq)

        if name == "snapshot_acquire" and st == 0 and snap:
            self.active_snaps.add(snap)
        elif name == "snapshot_release" and snap:
            if snap not in self.active_snaps:
                raise SystemExit(f"divergence at line {i}: release of unknown snapshot {snap}")
            self.active_snaps.remove(snap)
        elif name == "query_begin" and st == 0:
            self.in_query += 1
        elif name == "query_end":
            if self.in_query == 0:
                raise SystemExit(f"divergence at line {i}: query_end without query_begin")
            self.in_query -= 1


def parse(path):
    events = []
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for i, line in enumerate(f, 1):
            m = LINE_RE.match(line.strip())
            if not m:
                continue
            data = dict(KV_RE.findall(m.group(1)))
            events.append((i, data))
    return events


def main():
    if len(sys.argv) != 2:
        print("usage: check_trace.py <trace.log>", file=sys.stderr)
        return 2
    events = parse(sys.argv[1])
    model = Model()
    for i, ev in events:
        model.step(ev, i)
    print(f"trace ok: {len(events)} events")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
