#!/usr/bin/env bash
set -euo pipefail

# Build Lean docs with doc-gen4 via a dedicated docbuild project.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
DOCBUILD_ROOT="${PROJECT_ROOT}/docbuild"

cd "${DOCBUILD_ROOT}"

# Ensure docbuild uses the same toolchain as the main project.
if [ ! -e "${DOCBUILD_ROOT}/lean-toolchain" ]; then
  ln -sf ../lean-toolchain "${DOCBUILD_ROOT}/lean-toolchain"
fi

echo "[lean] lake -Kdoc=on exe cache get (mathlib oleans)"
lake -Kdoc=on exe cache get

echo "[lean] lake -Kdoc=on build docs"
lake -Kdoc=on build docs

rm -rf "${PROJECT_ROOT}/build/doc"
if [ -d "${DOCBUILD_ROOT}/.lake/build/doc" ]; then
  mv "${DOCBUILD_ROOT}/.lake/build/doc" "${PROJECT_ROOT}/build/doc"
else
  echo "ERROR: doc-gen4 output not found at ${DOCBUILD_ROOT}/.lake/build/doc" >&2
  exit 1
fi
