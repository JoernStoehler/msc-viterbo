#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Lint + typecheck the Python package.
uv run ruff check --fix . || true
uv run ruff format . || true
uv run pyright || true
