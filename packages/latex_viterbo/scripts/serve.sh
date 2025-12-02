#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/serve.sh [--production] [--watch] [--port PORT]

Serves the built thesis (HTML + PDF) via a local HTTP server.
- By default builds a preview into build/ and serves it.
- --production builds into dist/ using the production build script.
- --watch (if `entr` is available) rebuilds on source changes.
EOF
}

PORT=8000
MODE=preview
WATCH=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --production) MODE=production; shift ;;
    --watch) WATCH=true; shift ;;
    --port) PORT=${2:-}; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown arg: $1" >&2; usage >&2; exit 64 ;;
  esac
done

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if [[ $MODE == production ]]; then
  OUTDIR=dist
  BUILD_CMD=("$ROOT_DIR/scripts/build.sh" --production)
else
  OUTDIR=build
  BUILD_CMD=("$ROOT_DIR/scripts/build.sh")
fi

# Initial build
"${BUILD_CMD[@]}"

SERVE_DIR="$ROOT_DIR/$OUTDIR"

# Start server
( cd "$SERVE_DIR" && python3 -m http.server "$PORT" --bind 127.0.0.1 ) &
SERVER_PID=$!
cleanup() { kill $SERVER_PID 2>/dev/null || true; rm -f "${WATCH_LIST:-}"; }
trap cleanup EXIT

if $WATCH; then
  if ! command -v inotifywait >/dev/null 2>&1; then
    echo "--watch requires inotifywait (package: inotify-tools)" >&2
    exit 1
  fi

  WATCH_TARGETS=()
  [[ -d chapters ]] && WATCH_TARGETS+=(chapters)
  [[ -d assets ]] && WATCH_TARGETS+=(assets)
  [[ -f main.tex ]] && WATCH_TARGETS+=(main.tex)
  [[ -f references.bib ]] && WATCH_TARGETS+=(references.bib)
  [[ -f includeonly.tex ]] && WATCH_TARGETS+=(includeonly.tex)

  if [[ ${#WATCH_TARGETS[@]} -eq 0 ]]; then
    echo "No files to watch; exiting." >&2
    exit 1
  fi

  inotifywait -m -r -e close_write,move,create,delete --format '%w%f' "${WATCH_TARGETS[@]}" \
    | while read -r _; do
        "${BUILD_CMD[@]}"
      done
else
  wait $SERVER_PID
fi
