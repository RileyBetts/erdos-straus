#!/usr/bin/env bash
# If a programme-report TeX is newer than its PDF, rebuild before the turn ends.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root"
input="$(cat)"

status="$(python3 -c '
import json, sys
raw = sys.argv[1]
try:
    data = json.loads(raw) if raw.strip() else {}
except Exception:
    data = {}
print(data.get("status") or "completed")
' "$input")"

if [[ "$status" == "aborted" ]]; then
  printf '%s\n' '{}'
  exit 0
fi

shopt -s nullglob
stale=0
for tex in erdos-straus-programme-report-*.tex; do
  pdf="${tex%.tex}.pdf"
  if [[ ! -f "$pdf" || "$tex" -nt "$pdf" ]]; then
    stale=1
    break
  fi
done

if [[ "$stale" -eq 1 ]]; then
  ./build-programme-report.sh || true
fi

printf '%s\n' '{}'
