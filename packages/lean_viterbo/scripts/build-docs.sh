#!/usr/bin/env bash
set -euo pipefail

# Build Lean docs using doc-gen4 via the docbuild project.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
DOCBUILD_ROOT="${PROJECT_ROOT}/docbuild"

# Use a shared doc build dir so multiple worktrees reuse the same HTML output.
SHARED_DOC_BUILD="/workspaces/worktrees/shared/lean/docbuild-build"
mkdir -p "${SHARED_DOC_BUILD}"

# Ensure docbuild/.lake/build points at the shared location. If a local build
# dir exists, sync its contents over before replacing it with the symlink.
if [ ! -L "${DOCBUILD_ROOT}/.lake/build" ]; then
  if [ -d "${DOCBUILD_ROOT}/.lake/build" ]; then
    rsync -a --remove-source-files "${DOCBUILD_ROOT}/.lake/build/" "${SHARED_DOC_BUILD}/"
    find "${DOCBUILD_ROOT}/.lake/build" -type d -empty -delete
    rmdir "${DOCBUILD_ROOT}/.lake/build" 2>/dev/null || true
  fi
  ln -sfn "${SHARED_DOC_BUILD}" "${DOCBUILD_ROOT}/.lake/build"
fi

cd "${DOCBUILD_ROOT}"

# Share toolchain with main project.
if [ ! -e "${DOCBUILD_ROOT}/lean-toolchain" ]; then
  ln -sf ../lean-toolchain "${DOCBUILD_ROOT}/lean-toolchain"
fi

echo "[lean] lake -Kdoc=on exe cache get (mathlib oleans)"
MATHLIB_NO_CACHE_ON_UPDATE=1 lake -Kdoc=on exe cache get

echo "[lean] lake -Kdoc=on build docs (doc-gen4)"
lake -Kdoc=on build docs

rm -rf "${PROJECT_ROOT}/build/doc"
mkdir -p "${PROJECT_ROOT}/build"

# doc-gen4 attaches the docs facet to the package that owns the sources
# (here: the path dependency `lean_viterbo`). As a result the HTML output
# lands in that package's `.lake/build/doc`, not in the auxiliary
# `docbuild/.lake` directory. Prefer that location, but keep the old path
# as a fallback in case we ever change the layout again.
DOC_OUT_MAIN="${PROJECT_ROOT}/.lake/build/doc"
DOC_OUT_DOCBUILD="${DOCBUILD_ROOT}/.lake/build/doc"

if [ -d "${DOC_OUT_MAIN}" ]; then
  mv "${DOC_OUT_MAIN}" "${PROJECT_ROOT}/build/doc"
elif [ -d "${DOC_OUT_DOCBUILD}" ]; then
  mv "${DOC_OUT_DOCBUILD}" "${PROJECT_ROOT}/build/doc"
else
  echo "ERROR: doc-gen4 output not found at ${DOC_OUT_MAIN} or ${DOC_OUT_DOCBUILD}" >&2
  exit 1
fi
