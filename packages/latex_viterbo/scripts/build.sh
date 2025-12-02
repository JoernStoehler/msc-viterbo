#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

OUTDIR=${OUTDIR:-build}
MAIN=main.tex
DO_PDF=true
DO_HTML=true
LATEX_OPTS=(-interaction=nonstopmode -file-line-error -synctex=1)

usage() {
  cat <<'EOF'
Usage: scripts/build.sh [--production] [--pdf-only] [--html-only]

Options:
  --production   Clean and build into dist/ with full latexmk; HTML via latexmlc.
  --pdf-only     Build PDF only.
  --html-only    Build HTML only.
  -h, --help     Show this help.

Env vars:
  OUTDIR   Override output dir (default: build for preview, dist for production).
EOF
}

MODE=preview

while [[ $# -gt 0 ]]; do
  case "$1" in
    --production) MODE=production; OUTDIR=${OUTDIR:-dist}; shift ;;
    --pdf-only) DO_HTML=false; shift ;;
    --html-only) DO_PDF=false; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; usage >&2; exit 64 ;;
  esac
done

[[ "$DO_PDF" == false && "$DO_HTML" == false ]] && { echo "Nothing to build (pdf-only/html-only both false)" >&2; exit 64; }

mkdir -p "$OUTDIR"

if [[ $MODE == production ]]; then
  # Clean old outputs for a fresh production build
  latexmk -C
fi

if $DO_PDF; then
  latexmk -pdf "${LATEX_OPTS[@]}" \
    -output-directory="$OUTDIR" \
    "$MAIN"
fi

if $DO_HTML; then
  mkdir -p "$OUTDIR/html"
  if ! command -v latexmlc >/dev/null 2>&1; then
    echo "latexmlc not installed; install latexml (apt) inside the devcontainer" >&2
    exit 1
  fi
  latexmlc --destination="$OUTDIR/html/index.html" --path=chapters "$MAIN"
fi

echo "build.sh: artifacts in $OUTDIR";
