#!/usr/bin/env bash
set -euo pipefail

# End-to-end docs pipeline: build all package docs, stage them into public/, and publish to gh-pages.
# Fails fast on build errors unless a package is explicitly skipped via SKIP_* env vars.
# SKIP flags: SKIP_THESIS=1, SKIP_RUST=1, SKIP_PYTHON=1, SKIP_LEAN=1, SKIP_PUBLISH=1

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DOCS_SITE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${DOCS_SITE_ROOT}/../.." && pwd)"

err() { echo "ERROR: $*" >&2; exit 1; }

build_thesis() {
  if [[ ${SKIP_THESIS:-0} -eq 1 ]]; then echo "[thesis] skipped"; return; fi
  local script="${REPO_ROOT}/packages/thesis/scripts/build-site.sh"
  if [[ -x "${script}" ]]; then
    echo "[thesis] building via ${script}"; (cd "${REPO_ROOT}/packages/thesis" && "${script}")
  else
    err "thesis build script missing: ${script} (set SKIP_THESIS=1 to bypass)"
  fi
}

build_rust() {
  if [[ ${SKIP_RUST:-0} -eq 1 ]]; then echo "[rust] skipped"; return; fi
  echo "[rust] cargo doc --no-deps"
  (cd "${REPO_ROOT}/packages/rust_viterbo" && cargo doc --no-deps)
}

build_python() {
  if [[ ${SKIP_PYTHON:-0} -eq 1 ]]; then echo "[python] skipped"; return; fi
  echo "[python] uv run pdoc viterbo -o build/docs"
  (cd "${REPO_ROOT}/packages/python_viterbo" && uv run pdoc viterbo -o build/docs)
}

build_lean() {
  if [[ ${SKIP_LEAN:-0} -eq 1 ]]; then echo "[lean] skipped"; return; fi
  echo "[lean] lake exe doc"
  (cd "${REPO_ROOT}/packages/lean_viterbo" && lake exe doc)
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
