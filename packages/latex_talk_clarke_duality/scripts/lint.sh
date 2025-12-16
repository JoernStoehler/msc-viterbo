#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

MAIN=${MAIN:-main.tex}
OUTDIR=${OUTDIR:-build/lint}
mkdir -p "$OUTDIR"

if command -v chktex >/dev/null 2>&1; then
  echo "[lint.sh] chktex -q -v0 \"$MAIN\""
  chktex -q -v0 "$MAIN" || true
fi

echo "[lint.sh] generating version.tex"
./scripts/gen-version.sh

echo "[lint.sh] latexmk -pdf -halt-on-error -output-directory=\"$OUTDIR\" \"$MAIN\""
latexmk -pdf -halt-on-error -interaction=nonstopmode -file-line-error \
  -silent -output-directory="$OUTDIR" \
  -pdflatex="pdflatex -synctex=1 -file-line-error -interaction=nonstopmode %O %S" \
  "$MAIN"

echo "[lint.sh] SUCCESS (outdir=$OUTDIR)"

