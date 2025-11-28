#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${PROJECT_ROOT}"

# Build static HTML via MkDocs + Material. Dependencies are pulled on-the-fly via uv.
# Output: build/site/

echo "[thesis] mkdocs build --strict"
uv run \
  --with mkdocs \
  --with mkdocs-material \
  --with mkdocs-material-extensions \
  --with pymdown-extensions \
  mkdocs build --strict
