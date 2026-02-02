#!/usr/bin/env bash
set -euo pipefail

# Works in both Local and Codespace environments.
# Each worktree builds independently (no shared Rust build cache).

# Why this script exists:
# - Agents use worktrees to avoid stepping on each other.
# - We want failures to be loud/obvious because missing tools usually means the
#   devcontainer isn't ready or is broken.
# - We print commands before running them so logs explain what happened.

log() {
  echo "[worktree-new] $*"
}

die() {
  echo "[worktree-new][error] $*" >&2
  exit 1
}

fmt_cmd() {
  local -a parts=()
  local arg
  for arg in "$@"; do
    parts+=("$(printf '%q' "$arg")")
  done
  printf '%s' "${parts[*]}"
}

run() {
  log "$(fmt_cmd "$@")"
  "$@"
}

run_in_dir() {
  local dir="$1"
  shift
  log "(cd $(printf '%q' "$dir") && $(fmt_cmd "$@"))"
  (cd "$dir" && "$@")
}

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    die "required tool '$cmd' not found (devcontainer setup likely broken or still initializing)"
  fi
}

require_dir() {
  local dir="$1"
  if [[ ! -d "$dir" ]]; then
    die "expected directory $(printf '%q' "$dir") not found (repo checkout likely incomplete)"
  fi
}

require_origin_remote() {
  if ! git remote get-url origin >/dev/null 2>&1; then
    die "expected git remote 'origin' to exist; this repo assumes origin is configured"
  fi
}

usage() {
  cat <<'USAGE'
Usage: worktree-new.sh [--force] [--no-hydrate] <path> <branch>

Creates a new worktree at <path> for <branch>.
- If <branch> exists locally, checks it out in the new worktree.
- If only origin/<branch> exists, creates a local <branch> from it.
- Otherwise, creates <branch> from main.

Also fetches remotes, runs safety checks, and hydrates deps (python uv sync, cargo fetch/build).
Pass --no-hydrate to skip the expensive dependency hydration step.
USAGE
}

prep_git_lfs() {
  # Why: the repo uses LFS; missing git-lfs is a strong signal the devcontainer
  # isn't ready (or something is very wrong with the setup).
  run git lfs install --local --skip-repo
}

prep_python() {
  run_in_dir experiments uv sync --locked --extra dev
}

prep_rust() {
  run cargo fetch --manifest-path crates/Cargo.toml
  run cargo build --manifest-path crates/Cargo.toml --exclude viterbo_ffi
}

prep_ffi() {
  run_in_dir experiments uv run maturin develop --manifest-path ../crates/ffi/Cargo.toml
}

prep_latex() {
  : # nothing to hydrate; use thesis/scripts as needed
}

main() {
  local force=false
  local hydrate=true
  local -a positional=()
  local arg
  for arg in "$@"; do
    case "$arg" in
      --force) force=true ;;
      --no-hydrate) hydrate=false ;;
      -h|--help)
        usage
        return 0
        ;;
      -*)
        usage >&2
        die "unknown option: $arg"
        ;;
      *) positional+=("$arg") ;;
    esac
  done

  if [[ ${#positional[@]} -ne 2 ]]; then
    usage >&2
    return 64
  fi

  local repo_root
  repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
  local path="${positional[0]}"
  local branch="${positional[1]}"

  cd "$repo_root"

  require_cmd git
  require_cmd git-lfs
  require_cmd uv
  require_cmd python3
  require_cmd cargo
  require_dir experiments
  require_dir crates

  require_origin_remote

  run git fetch --prune origin

  if ! $force; then
    local status
    status="$(git status --short)"
    if [[ -n "$status" ]]; then
      echo "[error] main worktree has uncommitted changes; rerun with --force if you really want to proceed" >&2
      log "git status --short"
      printf '%s\n' "$status"
      return 1
    fi
    if git rev-parse --verify main >/dev/null 2>&1 && git rev-parse --verify origin/main >/dev/null 2>&1; then
      local behind
      behind=$(git rev-list --count main..origin/main || echo 0)
      if [[ "$behind" != "0" ]]; then
        echo "[error] main is behind origin/main by ${behind} commits; pull or use --force" >&2
        return 1
      fi
    fi
  fi

  if ! git rev-parse --verify main >/dev/null 2>&1; then
    die "expected branch 'main' to exist locally; checkout main and retry"
  fi
  if ! git rev-parse --verify origin/main >/dev/null 2>&1; then
    die "expected remote-tracking branch 'origin/main' to exist after fetch; check your remotes and retry"
  fi

  # Check if worktree path already exists
  if [[ -e "$path" ]]; then
    if $force; then
      log "path $path already exists, proceeding anyway (--force)"
    else
      die "path $path already exists; remove it first or use --force"
    fi
  fi

  # Check if worktree is already registered
  if git worktree list | grep -q "^$path "; then
    if $force; then
      log "worktree at $path already registered, proceeding anyway (--force)"
    else
      die "worktree at $path already registered; use 'git worktree remove $path' or --force"
    fi
  fi

  # Why: `git worktree add <path> <branch>` requires <branch> to already exist.
  # This script does the right thing for common workflows:
  # - existing local branch -> reuse it
  # - existing origin/<branch> -> create a local tracking branch
  # - missing branch -> create it from main
  if git show-ref --verify --quiet "refs/heads/$branch"; then
    log "using existing local branch $branch"
    run git worktree add "$path" "$branch"
  elif git show-ref --verify --quiet "refs/remotes/origin/$branch"; then
    log "using origin/$branch (creating local tracking branch $branch)"
    run git worktree add -b "$branch" "$path" "origin/$branch"
    run_in_dir "$path" git branch --set-upstream-to "origin/$branch" "$branch" || true
  else
    log "creating new branch $branch from main"
    run git worktree add -b "$branch" "$path" main
  fi

  cd "$path"

  prep_git_lfs
  if $hydrate; then
    prep_python
    prep_rust
    prep_ffi
  else
    log "skipping dependency hydration (--no-hydrate)"
  fi
  prep_latex

  echo "Worktree ready at $path"
  echo "Next: cd $path"
}

main "$@"
