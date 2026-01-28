#!/usr/bin/env bash
set -euo pipefail

# DEPRECATED: This script is for the local devcontainer only.
#
# In GitHub Codespaces, use catnip for worktree management instead.
# Catnip automatically manages worktrees via refs/catnip/* branches.
# See: https://github.com/wandb/catnip
#
# This script will be removed once catnip workflow is validated.

# Why this script exists:
# - `git worktree remove` is easy to misuse (e.g. passing an unintended flag/path).
# - Removing a dirty worktree can silently destroy uncommitted work.
# - It's also easy to delete the only checkout that contains unmerged/unpushed commits.
# This wrapper adds basic guardrails and prints diagnostics before removal.

die() {
  echo "[worktree-remove][error] $*" >&2
  exit 1
}

usage() {
  cat <<'USAGE'
Usage: worktree-remove.sh [--force] <path>

Safely removes a worktree.
By default, refuses to remove dirty worktrees.
Also refuses to remove a detached-HEAD worktree if its HEAD commit is not referenced by any branch/tag/remote (unless --force).
Prints an optional follow-up command to delete the associated branch (but does NOT delete it automatically).

Options:
  --force       Proceed even if the worktree is dirty (passes --force to git)
  -h, --help    Show this help text
USAGE
}

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    die "required tool '$cmd' not found"
  fi
}

print_main_sync_diagnostics() {
  # Why: help catch "I thought my local main was up to date" mistakes.
  local main_dirty=false
  local main_ahead="0"
  local main_behind="0"

  local status=""
  status="$(git status --porcelain=v1 --untracked-files=all || true)"
  if [[ -n "$status" ]]; then
    main_dirty=true
  fi

  if git rev-parse --verify main >/dev/null 2>&1 && git rev-parse --verify origin/main >/dev/null 2>&1; then
    local counts=""
    counts="$(git rev-list --left-right --count main...origin/main 2>/dev/null || true)"
    if [[ -n "$counts" ]]; then
      main_ahead="$(awk '{print $1}' <<<"$counts")"
      main_behind="$(awk '{print $2}' <<<"$counts")"
    fi
  fi

  if $main_dirty || [[ "$main_ahead" != "0" ]] || [[ "$main_behind" != "0" ]]; then
    if $main_dirty; then
      echo "[worktree-remove][warn] main worktree has uncommitted changes" >&2
      echo "[worktree-remove][hint] inspect: git status --short" >&2
    fi
    if [[ "$main_behind" != "0" ]]; then
      echo "[worktree-remove][warn] main is behind origin/main by $main_behind commits" >&2
      echo "[worktree-remove][hint] update: git fetch origin && git switch main && git pull --ff-only" >&2
    fi
    if [[ "$main_ahead" != "0" ]]; then
      echo "[worktree-remove][warn] main is ahead of origin/main by $main_ahead commits" >&2
      echo "[worktree-remove][hint] push: git push origin main" >&2
    fi
  fi
}

print_detached_head_diagnostics() { # $1=path, $2=force(true/false)
  # Why: commits on detached HEAD can be lost after worktree removal if they are
  # not referenced by any branch/tag/remote ref.
  local path="$1"
  local force="$2"

  local head_hash=""
  head_hash="$(git -C "$path" rev-parse --verify HEAD 2>/dev/null || true)"
  if [[ -z "$head_hash" ]]; then
    echo "[worktree-remove][warn] could not determine HEAD commit for $path" >&2
    return 0
  fi

  local head_short=""
  head_short="$(git rev-parse --short "$head_hash" 2>/dev/null || echo "$head_hash")"

  local containing_ref=""
  containing_ref="$(git for-each-ref --contains "$head_hash" --format='%(refname)' refs/heads refs/tags refs/remotes 2>/dev/null | head -n 1 || true)"
  if [[ -n "$containing_ref" ]]; then
    echo "[worktree-remove][info] detached HEAD at $head_short (reachable via $containing_ref)"
    return 0
  fi

  echo "[worktree-remove][warn] detached HEAD at $head_short is not referenced by any branch/tag/remote" >&2
  echo "[worktree-remove][hint] create a branch before removal: git -C $(printf '%q' "$path") switch -c <branch-name>" >&2
  if [[ "$force" != "true" ]]; then
    echo "[worktree-remove][warn] refusing to remove detached-HEAD worktree; rerun with --force to discard it" >&2
    return 1
  fi
  echo "[worktree-remove][warn] removing anyway due to --force; this commit may become unreachable" >&2
}

print_branch_diagnostics() { # $1=branch, $2=have_origin(true/false)
  # Why: before removing a worktree, make it obvious if the branch still contains
  # unique work (unmerged commits) or if it's not pushed anywhere.
  local branch="$1"
  local have_origin="$2"
  if [[ -z "$branch" ]]; then
    return 0
  fi
  local branch_ref="refs/heads/$branch"

  if git merge-base --is-ancestor "$branch_ref" main >/dev/null 2>&1; then
    echo "[worktree-remove][info] branch $branch is merged into main"
  elif git rev-parse --verify origin/main >/dev/null 2>&1 && git merge-base --is-ancestor "$branch_ref" origin/main >/dev/null 2>&1; then
    echo "[worktree-remove][warn] branch $branch is merged into origin/main, but local main is behind" >&2
    echo "[worktree-remove][hint] update main: git fetch origin && git switch main && git pull --ff-only" >&2
  else
    local ahead=""
    ahead="$(git rev-list --count "main..$branch_ref" 2>/dev/null || true)"
    if [[ -n "$ahead" ]]; then
      echo "[worktree-remove][warn] branch $branch has $ahead commits not in main" >&2
      echo "[worktree-remove][hint] inspect: git log --oneline --decorate main..$(printf '%q' "$branch")" >&2
    else
      echo "[worktree-remove][warn] branch $branch is not merged into main" >&2
    fi
  fi

  if git rev-parse --verify "refs/remotes/origin/$branch" >/dev/null 2>&1; then
    local counts=""
    counts="$(git rev-list --left-right --count "refs/remotes/origin/$branch...$branch_ref" 2>/dev/null || true)"
    if [[ -n "$counts" ]]; then
      local behind ahead
      behind="$(awk '{print $1}' <<<"$counts")"
      ahead="$(awk '{print $2}' <<<"$counts")"
      if [[ "$ahead" != "0" ]]; then
        echo "[worktree-remove][warn] branch $branch is ahead of origin/$branch by $ahead commits (not pushed)" >&2
        echo "[worktree-remove][hint] push: git push -u origin $(printf '%q' "$branch")" >&2
      fi
      if [[ "$behind" != "0" ]]; then
        echo "[worktree-remove][warn] branch $branch is behind origin/$branch by $behind commits" >&2
        echo "[worktree-remove][hint] update: git fetch origin && git rebase origin/$(printf '%q' "$branch")" >&2
      fi
    fi
  else
    if [[ "$have_origin" == "true" ]]; then
      echo "[worktree-remove][warn] branch $branch has no origin/$branch (likely not pushed)" >&2
      echo "[worktree-remove][hint] push: git push -u origin $(printf '%q' "$branch")" >&2
    fi
  fi
}

main() {
  local force=false
  local -a positional=()
  local arg
  local end_of_options=false
  for arg in "$@"; do
    if $end_of_options; then
      positional+=("$arg")
      continue
    fi
    case "$arg" in
      --force) force=true ;;
      -h|--help)
        usage
        return 0
        ;;
      --) end_of_options=true ;;
      -*)
        usage >&2
        echo "[worktree-remove][error] unknown option: $arg" >&2
        return 64
        ;;
      *) positional+=("$arg") ;;
    esac
  done

  if [[ ${#positional[@]} -ne 1 ]]; then
    usage >&2
    return 64
  fi

  local repo_root
  repo_root="$(cd "$(dirname "$0")/.." && pwd)"
  local path="${positional[0]}"

  cd "$repo_root"
  require_cmd git

  if [[ ! -e "$path/.git" ]]; then
    die "worktree $path does not look like a git worktree"
  fi

  local have_origin=false
  if git remote get-url origin >/dev/null 2>&1; then
    have_origin=true
    # Why: comparisons against origin/* should reflect the current remote state.
    if ! git fetch --prune origin --quiet; then
      echo "[worktree-remove][warn] git fetch origin failed; origin/* diagnostics may be stale" >&2
    fi
  fi
  print_main_sync_diagnostics

  if ! $force; then
    if (cd "$path" && git status --porcelain=v1 --untracked-files=all | grep -q .); then
      echo "[worktree-remove][warn] worktree dirty; rerun with --force to remove" >&2
      return 1
    fi
  else
    local dirty=""
    dirty="$(cd "$path" && git status --porcelain=v1 --untracked-files=all || true)"
    if [[ -n "$dirty" ]]; then
      echo "[worktree-remove][warn] removing dirty worktree due to --force; uncommitted changes will be lost" >&2
      echo "[worktree-remove][hint] git status --short (in $path):" >&2
      printf '%s\n' "$dirty" >&2
    fi
  fi

  local branch=""
  branch="$(git -C "$path" symbolic-ref --quiet --short HEAD 2>/dev/null || true)"
  if [[ -n "$branch" ]]; then
    print_branch_diagnostics "$branch" "$have_origin"
  else
    print_detached_head_diagnostics "$path" "$force"
  fi

  local -a git_args=(git worktree remove)
  if $force; then
    git_args+=(--force)
  fi
  git_args+=("$path")
  "${git_args[@]}"

  echo "Removed worktree $path"
  if [[ -n "$branch" ]]; then
    echo "Optional: delete branch (NOT done automatically): git branch -d $(printf '%q' "$branch")"
  fi
}

main "$@"
