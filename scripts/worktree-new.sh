#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: worktree-new.sh [--force] <path> <branch>

Creates a new worktree at <path> for <branch>, fetches remotes, runs safety checks, and hydrates deps (python uv sync, cargo fetch/build).
USAGE
}

force=false
if [[ ${1:-} == "--force" ]]; then
  force=true
  shift
fi

if [[ $# -ne 2 ]]; then
  usage >&2
  exit 64
fi

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
path="$1"
branch="$2"

cd "$repo_root"

git fetch --all --prune || true

if ! $force; then
  if git status --short | grep -q .; then
    echo "[error] main worktree has uncommitted changes; rerun with --force if you really want to proceed" >&2
    exit 1
  fi
  if git rev-parse --verify main >/dev/null 2>&1 && git rev-parse --verify origin/main >/dev/null 2>&1; then
    behind=$(git rev-list --count main..origin/main || echo 0)
    if [[ "$behind" != "0" ]]; then
      echo "[error] main is behind origin/main by ${behind} commits; pull or use --force" >&2
      exit 1
    fi
  fi
fi

git worktree add "$path" "$branch"

cd "$path"

prep_git_lfs
prep_python
prep_rust
prep_latex

echo "Worktree ready at $path"
echo "Next: cd $path"

prep_git_lfs() {
  if command -v git >/dev/null && command -v git-lfs >/dev/null; then
    git lfs install --local --skip-repo || true
  fi
}

prep_python() {
  if command -v uv >/dev/null && [[ -d packages/python_viterbo ]]; then
    (cd packages/python_viterbo && uv sync --locked --extra dev)
  fi
}

prep_rust() {
  if command -v cargo >/dev/null && [[ -d packages/rust_viterbo ]]; then
    local target_dir
    target_dir="${CARGO_TARGET_DIR:-/workspaces/worktrees/shared/target}"
    mkdir -p "$target_dir"
    CARGO_TARGET_DIR="$target_dir" cargo fetch --manifest-path packages/rust_viterbo/Cargo.toml
    CARGO_TARGET_DIR="$target_dir" cargo build --manifest-path packages/rust_viterbo/Cargo.toml
  fi
}

prep_latex() {
  : # nothing to hydrate; use scripts in packages/latex_viterbo when needed
}
