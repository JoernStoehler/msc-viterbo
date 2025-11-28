#!/usr/bin/env bash
set -euo pipefail

# Fresh glue layer: stage per-package docs and build the Astro site.
# Assumptions:
# - Each package owns its docs and may emit build artifacts under packages/<pkg>/build/docs or target/doc.
# - We only copy prebuilt docs; heavy builds should be run explicitly before calling this script.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DOCS_SITE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${DOCS_SITE_ROOT}/../.." && pwd)"

THESIS_SRC="${REPO_ROOT}/packages/thesis/src"
THESIS_DEST="${DOCS_SITE_ROOT}/src/content/thesis"
API_DEST="${DOCS_SITE_ROOT}/public/api"

echo "Docs site root: ${DOCS_SITE_ROOT}"
echo "Repo root:      ${REPO_ROOT}"

echo
echo "[1/5] Clean staging directories"
rm -rf "${THESIS_DEST}" "${API_DEST}"
mkdir -p "${THESIS_DEST}" "${API_DEST}"

echo
echo "[2/5] Stage thesis MDX + assets (no mutations)"
rsync -a --delete --exclude 'build/' --exclude '.DS_Store' --exclude '*.bak.*' \
  "${THESIS_SRC}/" "${THESIS_DEST}/"

echo
echo "[3/5] Stage package API docs (best-effort)"

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
echo "[4/5] Install Node deps if needed"
if [ ! -d "${DOCS_SITE_ROOT}/node_modules" ]; then
  (cd "${DOCS_SITE_ROOT}" && npm install --loglevel error)
else
  echo "node_modules present – skipping npm install"
fi

echo
echo "[5/5] Build Astro site"
(cd "${DOCS_SITE_ROOT}" && npm run build)

echo
echo "Done. Extend this script (or the per-package build steps) instead of wiring packages directly into Astro."
