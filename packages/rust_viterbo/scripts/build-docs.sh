#!/usr/bin/env bash
set -euo pipefail

# Build Rust API docs.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${PROJECT_ROOT}"
echo "[rust] cargo doc --no-deps"
cargo doc --no-deps
