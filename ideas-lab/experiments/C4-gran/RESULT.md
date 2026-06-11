# C4-gran — max_compaction_windows / granular-drain audit

This experiment checks whether Timelog's existing `max_compaction_windows` cap is enough to bound
wide-OOO compaction memory transients. No production patch is needed to enable the cap; the saved
`prototype.patch` is intentionally empty.

## Fresh C-level spot sweep

Build and run from repo root:

```bash
gcc -std=c11 -Wall -Wextra -Werror -O2 -Icore/include \
  ideas-lab/experiments/C4-gran/peak_rss_c.c build-rel/libtimelog.a \
  -lpthread -lm -o /tmp/timelog_peak_rss_c
for cap in 0 2 4 8; do
  /tmp/timelog_peak_rss_c "$cap" 300000 80 7
done
```

The C harness uses integer handles, so RSS is core-engine memory rather than Python payload noise.

| cap | maint steps | drain CPU | RSS spike | max step transient | select L0 | select L1 | final L0 | final L1 | multiset hash | ordered hash |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|
| 0 | 1 | 13.8 ms | 4.7 MiB | 4.7 MiB | 60 | 80 | 0 | 80 | `3e32beedfff9467e` | `7e4889ec57079134` |
| 2 | 30 | 139.9 ms | 4.0 MiB | 3.8 MiB | 53 | 4160 | 7 | 80 | `3e32beedfff9467e` | `bc04245eb6f5d6e0` |
| 4 | 30 | 141.2 ms | 4.1 MiB | 3.8 MiB | 53 | 4160 | 7 | 80 | `3e32beedfff9467e` | `bc04245eb6f5d6e0` |
| 8 | 30 | 139.5 ms | 4.2 MiB | 3.8 MiB | 53 | 4160 | 7 | 80 | `3e32beedfff9467e` | `bc04245eb6f5d6e0` |

## Interpretation

- Correctness is preserved in this spot sweep modulo duplicate-timestamp tie ordering: query counts and
  the order-insensitive `(timestamp, handle)` multiset hash are identical for all caps. The ordered hash
  differs between the one-pass merge and capped drains because the capped drain leaves 7 L0 segments and
  duplicate timestamp tie order is explicitly unspecified by the core API.
- The existing cap slightly reduces the largest observed transient in this workload, but it does not
  meaningfully bound wide-OOO RSS.
- The cap creates many small passes that repeatedly select overlapping L1 windows (`select_l1_inputs`
  80 -> 4160) and raises drain CPU by roughly 10x in this spot sweep.
- The cap also leaves some L0 segments after the bounded drain (`final L0 = 7`), so it is not equivalent
  to the one-pass full merge.

## Verdict

The existing `max_compaction_windows` knob is useful as a compaction-shaping control, but it is not a
production-ready fix for wide-OOO memory transients. A true wide-OOO granular-compaction feature would
need new sub-window slicing or another policy that avoids repeatedly re-merging the same L1 windows.

Seed as **not low-hanging**. Keep the harness as evidence and route any real fix through a separate
design/prototype.
