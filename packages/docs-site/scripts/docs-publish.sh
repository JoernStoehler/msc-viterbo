#!/usr/bin/env bash
set -euo pipefail

# End-to-end docs pipeline: build all package docs, stage them into public/, and publish to gh-pages.
# SKIP flags: SKIP_THESIS=1, SKIP_RUST=1, SKIP_PYTHON=1, SKIP_LEAN=1, SKIP_PUBLISH=1
# Lean docs: set LEAN_DOCS=0 to skip; warm cache ~30s, cold cache (wiped) ~20–25m.
# Outdated warnings: set WARN_OUTDATED=1 to check source vs. staged mtimes (off by default to avoid noisy false positives).

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DOCS_SITE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${DOCS_SITE_ROOT}/../.." && pwd)"

build_thesis() {
  [[ ${SKIP_THESIS:-0} -eq 1 ]] && { echo "[thesis] skipped"; return; }
  (cd "${REPO_ROOT}/packages/thesis" && ./scripts/build-site.sh)
}

build_rust() {
  [[ ${SKIP_RUST:-0} -eq 1 ]] && { echo "[rust] skipped"; return; }
  (cd "${REPO_ROOT}/packages/rust_viterbo" && ./scripts/build-docs.sh)
}

build_python() {
  [[ ${SKIP_PYTHON:-0} -eq 1 ]] && { echo "[python] skipped"; return; }
  (cd "${REPO_ROOT}/packages/python_viterbo" && ./scripts/build-docs.sh)
}

build_lean() {
  if [[ ${SKIP_LEAN:-0} -eq 1 || ${LEAN_DOCS:-1} -eq 0 ]]; then
    echo "[lean] skipped (enable via LEAN_DOCS=1; warm ~30s, cold ~20–25m if cache wiped)"
    return
  fi
  echo "[lean] building docs (shared cache: warm ~30s, cold ~20–25m if wiped)"
  (cd "${REPO_ROOT}/packages/lean_viterbo" && ./scripts/build-docs.sh)
}

resolve_cargo_target_dir() {
  if [ -n "${CARGO_TARGET_DIR:-}" ]; then
    realpath -m "${CARGO_TARGET_DIR}"
    return
  fi
  local cfg="${REPO_ROOT}/.cargo/config.toml"
  if [ -f "${cfg}" ]; then
    local parsed
    parsed=$(python3 - "$cfg" "$REPO_ROOT" <<'PY' || true
import os, sys, tomllib
cfg, root = sys.argv[1], sys.argv[2]
try:
    data = tomllib.load(open(cfg, 'rb'))
    td = data.get('build', {}).get('target-dir')
except FileNotFoundError:
    td = None
if td:
    if not os.path.isabs(td):
        td = os.path.normpath(os.path.join(root, td))
    print(os.path.realpath(td))
PY
    )
    if [ -n "${parsed}" ]; then
      echo "${parsed}"
      return
    fi
  fi
  realpath -m "${REPO_ROOT}/target"
}

stage_all() {
  echo "[stage] copying built artifacts into packages/docs-site/public"
  local THESIS_SRC="${REPO_ROOT}/packages/thesis/build/site"
  local PUBLIC_ROOT="${DOCS_SITE_ROOT}/public"
  local API_DEST="${PUBLIC_ROOT}/api"
  local THESIS_DEST="${PUBLIC_ROOT}/thesis"
  local CARGO_TARGET_DIR_RESOLVED
  CARGO_TARGET_DIR_RESOLVED="$(resolve_cargo_target_dir)"
  local RUST_DOC_SRC="${CARGO_TARGET_DIR_RESOLVED}/doc"

  rm -rf "${THESIS_DEST}" "${API_DEST}"
  mkdir -p "${THESIS_DEST}" "${API_DEST}"

  echo "- staging thesis"
  if [ -d "${THESIS_SRC}" ]; then
    rsync -a --delete "${THESIS_SRC}/" "${THESIS_DEST}/"
  else
    echo "  thesis missing: ${THESIS_SRC}" >&2
  fi

  stage_api() {
    local src="$1" dest_sub="$2"
    local dest="${API_DEST}/${dest_sub}"
    if [ -d "${src}" ]; then
      echo "- staging ${dest_sub} from ${src}"
      mkdir -p "${dest}"
      rsync -a --delete "${src}/" "${dest}/"
    else
      echo "  ${dest_sub} docs missing: ${src}" >&2
    fi
  }

  stage_api "${RUST_DOC_SRC}" "rust"
  stage_api "${REPO_ROOT}/packages/python_viterbo/build/docs" "python"
  stage_api "${REPO_ROOT}/packages/lean_viterbo/.lake/build/doc" "lean"

  warn_if_outdated() {
    local label="$1" src_dir="$2" doc_dir="$3"
    if [[ ${WARN_OUTDATED:-0} -ne 1 ]]; then
      return
    fi
    if [ ! -d "${doc_dir}" ]; then
      echo "WARN: ${label} docs missing at ${doc_dir}; build before publish." >&2
      return
    fi
    local src_mtime doc_mtime
    src_mtime=$(find "${src_dir}" -path "*/build" -prune -o -type f -printf '%T@\n' | sort -nr | head -n1 || true)
    doc_mtime=$(find "${doc_dir}" -type f -printf '%T@\n' | sort -nr | head -n1 || true)
    if [ -n "${src_mtime}" ] && [ -n "${doc_mtime}" ]; then
      if awk "BEGIN {exit !(${doc_mtime} < ${src_mtime})}"; then
        echo "WARN: ${label} docs older than sources; rebuild recommended." >&2
      fi
    fi
  }

  if [[ ${WARN_OUTDATED:-0} -eq 1 ]]; then
    echo "[stage] checking mtimes (WARN_OUTDATED=1)"
    warn_if_outdated "Thesis" "${REPO_ROOT}/packages/thesis" "${THESIS_SRC}"
    warn_if_outdated "Rust API" "${REPO_ROOT}/packages/rust_viterbo" "${RUST_DOC_SRC}"
    warn_if_outdated "Python API" "${REPO_ROOT}/packages/python_viterbo" "${REPO_ROOT}/packages/python_viterbo/build/docs"
    warn_if_outdated "Lean docs" "${REPO_ROOT}/packages/lean_viterbo" "${REPO_ROOT}/packages/lean_viterbo/.lake/build/doc"
  fi
}

publish() {
  if [[ ${SKIP_PUBLISH:-0} -eq 1 ]]; then echo "[publish] skipped"; return; fi
  echo "[publish] pushing gh-pages via worktree"
  local PUBLIC_DIR="${DOCS_SITE_ROOT}/public"
  local BRANCH="gh-pages"
  local WORKTREE_GLOB="/tmp/docs-site-gh-pages.*"
  local WORKTREE_NAME_PREFIX="docs-site-gh-pages"
  # Use a deterministic trap with the path baked in; otherwise the EXIT trap
  # would reference an unset local under `set -u` once the function returns.
  local WORKTREE_DIR
  WORKTREE_DIR="$(mktemp -d /tmp/docs-site-gh-pages.XXXXXX)"

  echo "[publish] pruning stale gh-pages worktrees"
  (
    cd "${REPO_ROOT}" && git worktree prune >/dev/null
  ) || true
  for stale in ${WORKTREE_GLOB}; do
    [[ -d "${stale}" ]] || continue
    echo "  removing stale ${stale}"
    rm -rf "${stale}" || true
  done
  if [[ -d "${REPO_ROOT}/.git/worktrees" ]]; then
    find "${REPO_ROOT}/.git/worktrees" -maxdepth 1 -type d -name "${WORKTREE_NAME_PREFIX}.*" -print -exec rm -rf {} +
  fi

  if [ ! -d "${PUBLIC_DIR}" ]; then
    echo "ERROR: public/ not found; stage failed" >&2
    exit 1
  fi

  cd "${REPO_ROOT}"
  if ! git show-ref --verify --quiet "refs/heads/${BRANCH}"; then
    echo "Creating ${BRANCH} branch"
    git branch "${BRANCH}" >/dev/null
  fi

  echo "Adding worktree at ${WORKTREE_DIR}"
  git worktree add --force "${WORKTREE_DIR}" "${BRANCH}" >/dev/null

  cleanup() {
    # We must not rely on locals here: trap runs after locals are unset.
    local dir="$1"
    cd "${REPO_ROOT}" && git worktree remove --force "${dir}" >/dev/null || true
    rm -rf "${dir}" || true
  }
  trap "cleanup ${WORKTREE_DIR@Q}" EXIT INT TERM

  echo "Clearing old contents"
  rm -rf "${WORKTREE_DIR:?}"/*

  echo "Copying public -> worktree"
  cp -a "${PUBLIC_DIR}"/. "${WORKTREE_DIR}/"

  cd "${WORKTREE_DIR}"
  if [ -z "$(git status --porcelain)" ]; then
    echo "[publish] no staged changes; skipping commit/push" >&2
    exit 0
  fi

  git add -A
  commit_msg="docs: publish $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  git commit -m "${commit_msg}" >/dev/null

  echo "Pushing ${BRANCH}"
  git push origin "${BRANCH}"

  echo "Published to ${BRANCH}. Worktree cleaned."
}

echo "== build all docs =="
build_thesis
build_rust
build_python
build_lean

echo "== stage =="
stage_all

echo "== publish =="
publish

echo "Done."
