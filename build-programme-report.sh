#!/usr/bin/env bash
# Rebuild committed programme-report PDFs from their TeX.
# Usage: ./build-programme-report.sh [tex-file ...]
# With no arguments, rebuild every erdos-straus-programme-report-*.tex.
set -euo pipefail

root="$(cd "$(dirname "$0")" && pwd)"
cd "$root"

if ! command -v pdflatex >/dev/null 2>&1; then
  echo "pdflatex not found; install TeX Live before rebuilding the report PDF." >&2
  exit 1
fi

build_one() {
  local tex="$1"
  local base="${tex%.tex}"
  if [[ "$tex" != *.tex || ! -f "$tex" ]]; then
    echo "missing TeX file: $tex" >&2
    return 1
  fi
  if [[ "${FORCE:-}" != 1 && -f "${base}.pdf" && ! "$tex" -nt "${base}.pdf" ]]; then
    echo "up to date: ${base}.pdf"
    return 0
  fi
  if [[ -z "${SOURCE_DATE_EPOCH:-}" ]]; then
    SOURCE_DATE_EPOCH="$(git log -1 --format=%ct -- "$tex" 2>/dev/null || true)"
    export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-$(date +%s)}"
  fi
  local pass
  for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error "$tex" >/dev/null
  done
  rm -f "${base}.aux" "${base}.log" "${base}.out" "${base}.toc"
  echo "rebuilt ${base}.pdf"
}

if [[ $# -eq 0 ]]; then
  shopt -s nullglob
  set -- erdos-straus-programme-report-*.tex
  if [[ $# -eq 0 ]]; then
    echo "no erdos-straus-programme-report-*.tex files found" >&2
    exit 1
  fi
fi

for tex in "$@"; do
  build_one "$(basename "$tex")"
done
