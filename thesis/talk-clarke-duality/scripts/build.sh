#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

OUTDIR=${OUTDIR:-}
MAIN=${MAIN:-main.tex}
LATEX_OPTS=(-interaction=nonstopmode -file-line-error -synctex=1)

usage() {
  cat <<'EOF'
Usage: scripts/build.sh [--production]

Builds the talk PDF via latexmk.

Options:
  --production   Clean and build into dist/ (default: build/).
  -h, --help     Show this help.

Env vars:
  OUTDIR   Override output dir (default: build for preview, dist for production).
  MAIN     Entry TeX file (default: main.tex).
EOF
}

MODE=preview
while [[ $# -gt 0 ]]; do
  case "$1" in
    --production) MODE=production; OUTDIR=${OUTDIR:-dist}; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; usage >&2; exit 64 ;;
  esac
done

if [[ -z "$OUTDIR" ]]; then
  OUTDIR=build
fi

mkdir -p "$OUTDIR"

if ! command -v pdflatex >/dev/null 2>&1; then
  echo "[build.sh] ERROR: pdflatex not found (TexLive is local devcontainer only)" >&2
  exit 1
fi

echo "[build.sh] generating version.tex"
./scripts/gen-version.sh

if [[ $MODE == production ]]; then
  echo "[build.sh] latexmk -C"
  latexmk -C
fi

echo "[build.sh] latexmk -pdf -output-directory=\"$OUTDIR\" \"$MAIN\""
latexmk -pdf "${LATEX_OPTS[@]}" \
  -output-directory="$OUTDIR" \
  "$MAIN"

echo "[build.sh] artifacts in $OUTDIR"
echo "[build.sh] SUCCESS"

