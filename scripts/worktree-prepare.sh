#!/usr/bin/env bash
set -Eeuo pipefail
IFS=$'\n\t'

# A small, boring helper to prep a new worktree for all toolchains we ship.

DEFAULT_SHARED_BASE="/workspaces/worktrees/shared"

log()   { printf '[prep] %s\n' "$*"; }
warn()  { printf '[prep][warn] %s\n' "$*" >&2; }
die()   { printf '[prep][error] %s\n' "$*" >&2; exit 64; }
have()  { command -v "$1" >/dev/null 2>&1; }

usage() {
  cat <<'EOF'
Usage: worktree-prepare.sh /absolute/path/to/worktree

Prepares caches and dependencies for all packages. Run after
`git worktree add <path> <branch>`.
EOF
}

trap 'warn "failed at line ${LINENO} (exit $?)"' ERR

main() {
  if [[ $# -ne 1 ]]; then
    usage >&2
    exit 64
  fi

  local worktree
  worktree="$(realpath "$1")"

  [[ -d "$worktree" ]] || die "worktree path $worktree does not exist"

  cd "$worktree"
  log "preparing worktree at $worktree"

  prepare_git_lfs
  prepare_python
  prepare_lean
  prepare_rust
  prepare_latex
  log "worktree prep complete"
}

prepare_git_lfs() {
  if have git && have git-lfs; then
    git lfs install --local --skip-repo || warn "git lfs initialization failed"
    log "git lfs initialized"
  else
    log "git or git-lfs missing; skipped git lfs init"
  fi
}

prepare_python() {
  if have uv && [[ -d packages/python_viterbo ]]; then
    log "python_viterbo: uv sync --locked --extra dev"
    (cd packages/python_viterbo && uv sync --locked --extra dev)
  else
    log "python_viterbo prep skipped (uv missing or package absent)"
  fi
}

prepare_lean() {
  if ! have lake || [[ ! -d packages/lean_viterbo ]]; then
    log "lean_viterbo prep skipped (lake missing or package absent)"
    return
  fi

  log "lean_viterbo: link shared cache + lake exe cache get"
  pushd packages/lean_viterbo >/dev/null

  local shared_base shared_pkgs
  shared_base="${SHARED_LEAN_BASE:-$DEFAULT_SHARED_BASE/lean}"
  shared_pkgs="$shared_base/packages"
  mkdir -p "$shared_pkgs" .lake

  # Move existing local packages to the shared cache once, then link.
  if [[ -d .lake/packages && ! -L .lake/packages ]]; then
    if have rsync; then
      rsync -a .lake/packages/ "$shared_pkgs"/ 2>/dev/null || true
    else
      cp -a .lake/packages/. "$shared_pkgs"/ 2>/dev/null || true
    fi
    rm -rf .lake/packages
  fi
  ln -sfn "$shared_pkgs" .lake/packages

  log "lean_viterbo: lake exe cache get"
  lake exe cache get || warn "lean cache download failed; run lake exe cache get manually"
  log "lean_viterbo: lake build"
  lake build -q || warn "lean build failed; run lake build manually"

  popd >/dev/null
}

prepare_rust() {
  if ! have cargo || [[ ! -d packages/rust_viterbo ]]; then
    log "rust_viterbo prep skipped (cargo missing or package absent)"
    return
  fi

  local target_dir
  target_dir="${CARGO_TARGET_DIR:-$DEFAULT_SHARED_BASE/target}"
  mkdir -p "$target_dir"

  log "rust_viterbo: cargo fetch (shared target dir: $target_dir)"
  CARGO_TARGET_DIR="$target_dir" cargo fetch --manifest-path packages/rust_viterbo/Cargo.toml
  log "rust_viterbo: cargo build dev"
  CARGO_TARGET_DIR="$target_dir" cargo build --manifest-path packages/rust_viterbo/Cargo.toml
}

prepare_latex() {
  if [[ ! -d packages/latex_viterbo ]]; then
    log "latex_viterbo prep skipped (package absent)"
    return
  fi
  log "latex_viterbo: nothing to prepare (use scripts/build.sh when needed)"
}

main "$@"
