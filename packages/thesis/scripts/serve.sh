#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${PROJECT_ROOT}"

if ! command -v quarto >/dev/null 2>&1; then
  echo "quarto not installed; install from https://quarto.org/docs/download/" >&2
  exit 1
fi

echo "[thesis] quarto preview --port 8000 --host 0.0.0.0"
quarto preview --port 8000 --host 0.0.0.0
