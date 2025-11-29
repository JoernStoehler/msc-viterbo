#!/usr/bin/env bash
set -euo pipefail

# Build Lean docs using doc-gen4 via the docbuild project.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
DOCBUILD_ROOT="${PROJECT_ROOT}/docbuild"

# Use a shared doc build dir so multiple worktrees reuse the same HTML output.
SHARED_DOC_BUILD="/workspaces/worktrees/shared/lean/docbuild-build"
mkdir -p "${SHARED_DOC_BUILD}"

# Ensure docbuild/.lake exists before wiring the shared build dir.
mkdir -p "${DOCBUILD_ROOT}/.lake"

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

LOCKDIR="/workspaces/worktrees/shared/lean/locks"
mkdir -p "${LOCKDIR}"
LOCKFILE="${LOCKDIR}/lean-docs.lock"

flock "${LOCKFILE}" bash -c '
  set -euo pipefail
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake -Kdoc=on exe cache get
  echo "[lean] lake -Kdoc=on build ProbingViterbo:docs (doc-gen4)"
  lake -Kdoc=on build ProbingViterbo:docs
'

echo "Docs remain in ${PROJECT_ROOT}/.lake/build/doc (shared cache)."
