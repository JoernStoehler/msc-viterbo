#!/usr/bin/env bash
set -euo pipefail

# Build Python API docs with pdoc.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${PROJECT_ROOT}"
echo "[python] uv run --with pdoc pdoc viterbo -o build/docs"
uv run --with pdoc pdoc viterbo -o build/docs
