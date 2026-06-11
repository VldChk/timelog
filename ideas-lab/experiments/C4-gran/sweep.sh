#!/usr/bin/env bash
# C4-gran sweep driver: run each max_compaction_windows cap in a FRESH process
# (clean RSS high-water per cell) and collect JSON lines.
set -euo pipefail
cd /home/vldvhk/Documents/timelog
HARNESS=ideas-lab/experiments/C4-gran/peak_rss_lab.py

# cfg overrides come as $1 (json fragment without the cap key)
BASECFG="${1:-{}}"
OUT="${2:-/dev/stdout}"

if [[ "$OUT" != "/dev/stdout" ]]; then
  : > "$OUT"
fi

for cap in 0 2 4 8; do
  cfg=$(python3 -c "import json,sys; d=json.loads(sys.argv[1]); d['cap']=$cap; print(json.dumps(d))" "$BASECFG")
  if [[ "$OUT" == "/dev/stdout" ]]; then
    PYTHONPATH=python python3 "$HARNESS" "$cfg"
  else
    PYTHONPATH=python python3 "$HARNESS" "$cfg" | tee -a "$OUT"
  fi
done
