#!/usr/bin/env bash
set -euo pipefail
# Lightweight formatter wrapper for LaTeX sources.
# Uses latexindent (texlab's default) so local runs match editor behavior.
# Usage: scripts/format.sh [files...]
# If no files are given, formats main.tex, preamble.tex, and all chapters/*.tex.

if ! command -v latexindent >/dev/null 2>&1; then
  echo "latexindent not installed; apt-get install latexindent" >&2
  exit 1
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if [[ $# -gt 0 ]]; then
  targets=("$@")
else
  mapfile -t targets < <(find . -maxdepth 2 -type f -name '*.tex' \( -path './chapters/*' -o -name 'main.tex' -o -name 'preamble.tex' \) | sort)
fi

echo "[format.sh] latexindent -w on ${#targets[@]} file(s)"
latexindent -w "${targets[@]}"
echo "[format.sh] formatted ${#targets[@]} file(s)"
