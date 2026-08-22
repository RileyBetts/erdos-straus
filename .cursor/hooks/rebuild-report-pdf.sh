#!/usr/bin/env bash
# Rebuild the programme-report PDF after its TeX is edited.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
input="$(cat)"

python3 -c '
import json, os, subprocess, sys

root, raw = sys.argv[1], sys.argv[2]
try:
    data = json.loads(raw) if raw.strip() else {}
except json.JSONDecodeError:
    data = {}

path = data.get("file_path") or data.get("path") or ""
name = os.path.basename(path)
if not (
    name.startswith("erdos-straus-programme-report-") and name.endswith(".tex")
):
    sys.exit(0)

script = os.path.join(root, "build-programme-report.sh")
tex = os.path.join(root, name)
subprocess.check_call([script, tex], cwd=root)
' "$root" "$input"
