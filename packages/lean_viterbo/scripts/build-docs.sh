#!/usr/bin/env bash
set -euo pipefail

# Build Lean docs via lake.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${PROJECT_ROOT}"
echo "[lean] lake exe doc"
lake exe doc
