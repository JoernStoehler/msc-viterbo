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
else
  echo "[lint.sh] WARNING: chktex not found (skipping structural lint, local devcontainer only)" >&2
fi

# 2) Fast draft compile for early errors (no PDF output)
if ! command -v pdflatex >/dev/null 2>&1; then
  echo "[lint.sh] ERROR: pdflatex not found (TexLive is local devcontainer only)" >&2
  exit 1
fi
echo "[lint.sh] latexmk -pdf -output-directory=\"$OUTDIR\" \"$MAIN\" (lint)"
latexmk -pdf -halt-on-error -interaction=nonstopmode -file-line-error \
  -silent -output-directory="$OUTDIR" \
  -pdflatex="pdflatex -synctex=1 -file-line-error -interaction=nonstopmode %O %S" \
  "$MAIN"

# 3) HTML sanity (always on to catch drift early)
mkdir -p "$OUTDIR/html"
if ! command -v latexmlc >/dev/null 2>&1; then
  echo "[lint.sh] WARNING: latexmlc not found (skipping HTML lint)" >&2
  echo "[lint.sh] latexml is not available via apt-get on Ubuntu" >&2
  echo "[lint.sh] HTML linting requires latexml installation" >&2
else
  echo "[lint.sh] latexmlc --destination=\"$OUTDIR/html/main.html\" \"$MAIN\""
  latexmlc --destination="$OUTDIR/html/main.html" --path=chapters "$MAIN"
fi

echo "[lint.sh] SUCCESS (outdir=$OUTDIR)"
