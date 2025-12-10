#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

MAIN=${1:-main.tex}
OUTDIR=${OUTDIR:-build/lint}
mkdir -p "$OUTDIR"

# 1) Structural lint (suppression flags live in .chktexrc via CmdLine block)
#    Note: chktex exits non‑zero when any warning fires, so we let it print but don't fail the run.
if command -v chktex >/dev/null 2>&1; then
  echo "[lint.sh] chktex -q -v0 \"$MAIN\""
  chktex -q -v0 "$MAIN" || true
fi

# 2) Fast draft compile for early errors (no PDF output)
echo "[lint.sh] latexmk -pdf -output-directory=\"$OUTDIR\" \"$MAIN\" (lint)"
latexmk -pdf -halt-on-error -interaction=nonstopmode -file-line-error \
  -silent -output-directory="$OUTDIR" \
  -pdflatex="pdflatex -synctex=1 -file-line-error -interaction=nonstopmode %O %S" \
  "$MAIN"

# 3) HTML sanity (always on to catch drift early)
mkdir -p "$OUTDIR/html"
if ! command -v latexmlc >/dev/null 2>&1; then
  echo "latexmlc not installed; install latexml (apt) inside the devcontainer" >&2
  exit 1
fi
echo "[lint.sh] latexmlc --destination=\"$OUTDIR/html/main.html\" \"$MAIN\""
latexmlc --destination="$OUTDIR/html/main.html" --path=chapters "$MAIN"

echo "[lint.sh] SUCCESS (outdir=$OUTDIR)"
