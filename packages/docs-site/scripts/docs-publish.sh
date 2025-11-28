#!/usr/bin/env bash
set -euo pipefail

# Glue layer: copy already-built docs into public/ for GitHub Pages.
# Assumptions:
# - Each package owns its docs and emits static HTML under packages/<pkg>/build/... (or shared target for Rust).
# - This script does NO builds; run package-specific build commands first.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DOCS_SITE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${DOCS_SITE_ROOT}/../.." && pwd)"

THESIS_SRC="${REPO_ROOT}/packages/thesis/build/site"
PUBLIC_ROOT="${DOCS_SITE_ROOT}/public"
API_DEST="${PUBLIC_ROOT}/api"
THESIS_DEST="${PUBLIC_ROOT}/thesis"

echo "Docs site root: ${DOCS_SITE_ROOT}"
echo "Repo root:      ${REPO_ROOT}"

echo
echo "[1/4] Clean staging directories"
rm -rf "${THESIS_DEST}" "${API_DEST}"
mkdir -p "${THESIS_DEST}" "${API_DEST}"

echo
echo "[2/4] Stage thesis static site (if present)"
if [ -d "${THESIS_SRC}" ]; then
  rsync -a --delete "${THESIS_SRC}/" "${THESIS_DEST}/"
else
  echo "- skip thesis (missing: ${THESIS_SRC})"
fi

echo
echo "[3/4] Stage package API docs (best-effort)"

stage_api() {
  local src="$1" dest_sub="$2"
  local dest="${API_DEST}/${dest_sub}"
  if [ -d "${src}" ]; then
    echo "- copying ${src} -> ${dest}"
    mkdir -p "${dest}"
    rsync -a --delete "${src}/" "${dest}/"
  else
    echo "- skip ${dest_sub} (not built: ${src} missing)"
  fi
}

# Rust (cargo doc): optional target/doc from shared target dir
stage_api "${REPO_ROOT}/worktrees/shared/target/doc" "rust"

# Python (pdoc/sphinx): expected under packages/python_viterbo/build/docs
stage_api "${REPO_ROOT}/packages/python_viterbo/build/docs" "python"

# Lean (lake doc): expected under packages/lean_viterbo/build/doc
stage_api "${REPO_ROOT}/packages/lean_viterbo/build/doc" "lean"

echo
echo "[4/4] Landing page stays in public/index.html; nothing to build"

echo
echo "Done. Extend per-package build steps; this script only copies outputs."
