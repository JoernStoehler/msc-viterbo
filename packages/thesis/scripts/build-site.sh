#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
CONFIG="${PROJECT_ROOT}/mkdocs.yml"
cd "${PROJECT_ROOT}"

if ! command -v uv >/dev/null 2>&1; then
  echo "uv not installed; install uv to use the pinned MkDocs toolchain" >&2
  exit 1
fi

echo "[thesis] uv sync --frozen"
uv sync --frozen

echo "[thesis] uv run --frozen mkdocs build -f ${CONFIG}"
uv run --frozen mkdocs build -f "${CONFIG}"
