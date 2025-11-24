#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'

usage() {
  cat <<'EOF' >&2
Usage: worktree-prepare.sh [options] /absolute/path/to/worktree

Options (defaults: general + python + docs + lean cache + rust):
  --general       Run cheap, repo-wide setup (git lfs init). Always on.
  --python        Prep packages/python_viterbo (uv sync --locked --extra dev).
  --docs          Prep packages/docs-site (npm install).
  --lean          Prep packages/lean_viterbo (shared cache, no build).
  --rust          Prep packages/rust_viterbo (shared target dir, cargo fetch).
  --all           Same as defaults (kept for clarity).
  --minimal       Only --general (skip python/docs/lean/rust).
  -h, --help  Show this help.

Pick only what you need to save time.\n
EOF
  exit 64
}

WORKTREE=""
GENERAL=true
PYTHON=true
DOCS=true
LEAN=true
RUST=true

while [[ $# -gt 0 ]]; do
  case "$1" in
    --general) GENERAL=true ;;
    --python) PYTHON=true ;;
    --docs) DOCS=true ;;
    --lean) LEAN=true ;;
    --rust) RUST=true ;;
    --all) GENERAL=true; PYTHON=true; DOCS=true; LEAN=true; RUST=true ;;
    --minimal) GENERAL=true; PYTHON=false; DOCS=false; LEAN=false; RUST=false ;;
    -h|--help) usage ;;
    *)
      if [[ -z "$WORKTREE" ]]; then
        WORKTREE="$1"
      else
        printf 'Unexpected argument: %s\n' "$1" >&2
        usage
      fi
      ;;
  esac
  shift
done

[[ -n "$WORKTREE" ]] || usage
if [[ ! -d "$WORKTREE" ]]; then
  printf 'worktree path %s does not exist\n' "$WORKTREE" >&2
  exit 64
fi

cd "$WORKTREE"

log() { printf '[prep] %s\n' "$*"; }

if $GENERAL; then
  if command -v git >/dev/null 2>&1 && command -v git-lfs >/dev/null 2>&1; then
    git lfs install --local --skip-repo || true
    log "git lfs initialized"
  else
    log "git or git-lfs missing; skipped git lfs init"
  fi
fi

if $PYTHON; then
  if [[ -x packages/python_viterbo/scripts/worktree-prepare.sh ]]; then
    log "python_viterbo prep"
    (cd packages/python_viterbo && scripts/worktree-prepare.sh)
  else
    log "python prep script missing; skipped"
  fi
fi

if $DOCS; then
  if [[ -x packages/docs-site/scripts/worktree-prepare.sh ]]; then
    log "docs-site prep"
    (cd packages/docs-site && scripts/worktree-prepare.sh)
  else
    log "docs-site prep script missing; skipped"
  fi
fi

if $LEAN; then
  if [[ -x packages/lean_viterbo/scripts/worktree-prepare.sh ]]; then
    log "lean_viterbo prep"
    (cd packages/lean_viterbo && scripts/worktree-prepare.sh)
  else
    log "lean prep script missing; skipped"
  fi
fi

if $RUST; then
  if [[ -x packages/rust_viterbo/scripts/worktree-prepare.sh ]]; then
    log "rust_viterbo prep"
    (cd packages/rust_viterbo && scripts/worktree-prepare.sh)
  else
    log "rust prep script missing; skipped"
  fi
fi

log "worktree prep complete for $WORKTREE"
