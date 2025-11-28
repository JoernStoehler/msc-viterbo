#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${PROJECT_ROOT}"

# Build static HTML via MkDocs + Material using the locked deps in pyproject/uv.lock.
# Output: build/site/

echo "[thesis] mkdocs build --strict (uv --frozen)"
uv run --frozen mkdocs build --strict
