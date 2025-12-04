#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if [[ -d tests/smoke ]]; then
  uv run pytest -q tests/smoke "$@"
else
  echo "[smoke] tests/smoke not found; skipping" >&2
fi
