#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: worktree-remove.sh <path>

Safely removes a worktree. Use --force as second arg to proceed if dirty.
USAGE
}

if [[ $# -lt 1 || $# -gt 2 ]]; then
  usage >&2
  exit 64
fi

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
path="$1"
force="${2:-}"

cd "$repo_root"

if [[ ! -d "$path/.git" ]]; then
  echo "Worktree $path does not look like a git worktree" >&2
  exit 1
fi

if [[ "$force" != "--force" ]]; then
  if (cd "$path" && git status --short | grep -q .); then
    echo "[warn] worktree dirty; rerun with --force to remove" >&2
    exit 1
  fi
fi

git worktree remove "${force:+--force}" "$path"

echo "Removed worktree $path"
