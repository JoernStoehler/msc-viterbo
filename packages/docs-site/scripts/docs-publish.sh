#!/usr/bin/env bash
set -euo pipefail

# End-to-end docs pipeline: build all package docs, stage them into public/, and publish to gh-pages.
# Fails fast on build errors unless a package is explicitly skipped via SKIP_* env vars.
# SKIP flags: SKIP_THESIS=1, SKIP_RUST=1, SKIP_PYTHON=1, SKIP_LEAN=1, SKIP_PUBLISH=1

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DOCS_SITE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${DOCS_SITE_ROOT}/../.." && pwd)"

build_thesis() {
  if [[ ${SKIP_THESIS:-0} -eq 1 ]]; then echo "[thesis] skipped"; return; fi
  (cd "${REPO_ROOT}/packages/thesis" && ./scripts/build-site.sh)
}

build_rust() {
  if [[ ${SKIP_RUST:-0} -eq 1 ]]; then echo "[rust] skipped"; return; fi
  (cd "${REPO_ROOT}/packages/rust_viterbo" && ./scripts/build-docs.sh)
}

build_python() {
  if [[ ${SKIP_PYTHON:-0} -eq 1 ]]; then echo "[python] skipped"; return; fi
  (cd "${REPO_ROOT}/packages/python_viterbo" && ./scripts/build-docs.sh)
}

build_lean() {
  if [[ ${SKIP_LEAN:-0} -eq 1 ]]; then echo "[lean] skipped"; return; fi
  (cd "${REPO_ROOT}/packages/lean_viterbo" && ./scripts/build-docs.sh)
}

stage_hub() {
  echo "[stage] copying built artifacts into packages/docs-site/public"
  "${SCRIPT_DIR}/stage-hub.sh"
}

publish() {
  if [[ ${SKIP_PUBLISH:-0} -eq 1 ]]; then echo "[publish] skipped"; return; fi
  echo "[publish] pushing gh-pages via worktree"
  "${SCRIPT_DIR}/publish-ghpages.sh"
}

echo "== build all docs =="
build_thesis
build_rust
build_python
build_lean

echo "== stage hub =="
stage_hub

echo "== publish =="
publish

echo "Done."
