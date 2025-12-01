#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
CONFIG="${PROJECT_ROOT}/mkdocs.yml"
cd "${PROJECT_ROOT}"

if ! command -v mkdocs >/dev/null 2>&1; then
  echo "mkdocs not installed; install with 'uv tool install mkdocs-material' or pip" >&2
  exit 1
fi

echo "[thesis] mkdocs serve -f ${CONFIG} --dev-addr 0.0.0.0:8000"
mkdocs serve -f "${CONFIG}" --dev-addr 0.0.0.0:8000
