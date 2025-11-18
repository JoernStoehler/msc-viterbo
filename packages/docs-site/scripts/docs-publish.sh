#!/usr/bin/env bash
set -euo pipefail

# Build and aggregate all docs (thesis + API) before publishing the Astro site.
# This is the single entry point that future issues will extend with real commands.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DOCS_SITE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${DOCS_SITE_ROOT}/../.." && pwd)"

echo "Docs site root: ${DOCS_SITE_ROOT}"
echo "Repo root:      ${REPO_ROOT}"

echo
echo "[1/3] Generating demo figures via Python..."
(
  cd "${REPO_ROOT}/packages/python_viterbo"
  uv run python -m viterbo.dummy_plot
)

echo
echo "[2/3] Installing Node dependencies (npm install --loglevel error)..."
if [ ! -d "${DOCS_SITE_ROOT}/node_modules" ]; then
  (cd "${DOCS_SITE_ROOT}" && npm install --loglevel error)
else
  echo "node_modules already present – skipping npm install"
fi

echo
echo "[3/3] Building Astro site..."
(cd "${DOCS_SITE_ROOT}" && npm run build)

echo
echo "TODO: extend this script with:"
echo "  - rust/python/lean API doc builds (cargo doc, pdoc, lake doc, ...)"
echo "  - gh-pages artifact packaging"
