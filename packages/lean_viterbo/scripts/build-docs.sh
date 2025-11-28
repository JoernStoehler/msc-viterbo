#!/usr/bin/env bash
set -euo pipefail

# Build Lean docs with doc-gen4.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${PROJECT_ROOT}"

# Ensure doc-gen4 is available via lake dependency; mathlib cache handled by lake.

echo "[lean] lake -Kdoc=on exe doc-gen4 (outputs to ./doc)"
lake -Kdoc=on exe doc-gen4
rm -rf build/doc
if [ -d doc ]; then
  mv doc build/doc
else
  echo "ERROR: doc-gen4 did not produce ./doc" >&2
  exit 1
fi
