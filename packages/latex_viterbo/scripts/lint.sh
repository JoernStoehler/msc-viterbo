#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

MAIN=${1:-main.tex}
OUTDIR=${OUTDIR:-build/lint}
mkdir -p "$OUTDIR"

# 1) Structural lint
if command -v chktex >/dev/null 2>&1; then
  chktex -q -v0 -l .chktexrc "$MAIN"
fi

# 2) Fast draft compile for early errors (no PDF output)
latexmk -pdf -halt-on-error -interaction=nonstopmode -file-line-error \
  -silent -output-directory="$OUTDIR" \
  -pdflatex="pdflatex -draftmode -synctex=1 -file-line-error -interaction=nonstopmode %O %S" \
  "$MAIN"

# 3) HTML sanity (always on to catch drift early)
mkdir -p "$OUTDIR/html"
if ! command -v latexmlc >/dev/null 2>&1; then
  echo "latexmlc not installed; install latexml (apt) inside the devcontainer" >&2
  exit 1
fi
latexmlc --destination="$OUTDIR/html/main.html" --path=chapters "$MAIN"

echo "lint.sh: OK"
