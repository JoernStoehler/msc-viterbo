#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
CONFIG="${PROJECT_ROOT}/mkdocs.yml"

cd "${PROJECT_ROOT}"

if ! command -v uv >/dev/null 2>&1; then
  echo "uv is required for pinned MkDocs tooling; install uv first." >&2
  exit 1
fi

echo "[thesis] uv sync --frozen"
uv sync --frozen

echo "[thesis] uv run --frozen python scripts/lint_math.py"
uv run --frozen python scripts/lint_math.py

echo "[thesis] uv run --frozen mkdocs build -f ${CONFIG}"
uv run --frozen mkdocs build -f "${CONFIG}"
