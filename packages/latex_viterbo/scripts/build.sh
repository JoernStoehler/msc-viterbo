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
  SKIN_DIR="$ROOT_DIR/assets/html/css"
  cp -f "$SKIN_DIR"/arxiv-html-papers-20250916.css "$OUTDIR/html/" || true
  cp -f "$SKIN_DIR"/ar5iv.0.8.4.css "$OUTDIR/html/" || true
  cp -f "$SKIN_DIR"/arxiv-html-papers-theme-20250916.css "$OUTDIR/html/" || true

  latexmlc \
    --preload='[nobibtex,rawstyles,nobreakuntex,magnify=1.3,zoomout=1.3,tokenlimit=249999999,iflimit=3999999,absorblimit=1299999,pushbacklimit=599999]latexml.sty' \
    --preload=ar5iv.sty \
    --path=chapters \
    --path="$ROOT_DIR/assets/latexml/ar5iv-bindings/bindings" \
    --path="$ROOT_DIR/assets/latexml/ar5iv-bindings/supported_originals" \
    --path="$SKIN_DIR" \
    --path="$OUTDIR/html" \
    --format=html5 --pmml --mathtex --timeout=2700 \
    --noinvisibletimes --nodefaultresources \
    --css=arxiv-html-papers-20250916.css \
    --css=ar5iv.0.8.4.css \
    --css=arxiv-html-papers-theme-20250916.css \
    --destination="$OUTDIR/html/index.html" \
    "$MAIN"

  # Postprocess: move TOC as first child of ltx_page_main (flex layout like arXiv)
  python3 - "$OUTDIR/html/index.html" <<'PY'
import pathlib, sys

path = pathlib.Path(sys.argv[1])
html = path.read_text()

# Inject local fixes (hide LaTeXML logo/timestamp that crowds right margin)
if "</head>" in html and "ltx-local-fixes" not in html:
    fix = (
        '<style id="ltx-local-fixes">'
        '.ltx_page_logo{display:none;}'
        '</style>'
    )
    html = html.replace("</head>", fix + "</head>", 1)

toc_start = html.find('<nav class="ltx_TOC')
if toc_start != -1:
    toc_end = html.find("</nav>", toc_start)
    if toc_end != -1:
        toc_end += len("</nav>")
        toc = html[toc_start:toc_end]
        toc = toc.replace('class="ltx_TOC', 'class="ltx_TOC active', 1)
        html = html[:toc_start] + html[toc_end:]
        main_tag = '<div class="ltx_page_main">'
        main_idx = html.find(main_tag)
        if main_idx != -1:
            insert_at = main_idx + len(main_tag)
            html = html[:insert_at] + "\n" + toc + "\n" + html[insert_at:]
        else:
            html = toc + html

path.write_text(html)
PY
fi

echo "build.sh: artifacts in $OUTDIR";
