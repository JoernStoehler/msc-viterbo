#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'

usage() {
  cat <<'EOF' >&2
Usage: worktree-prepare.sh /absolute/path/to/worktree
EOF
  exit 64
}

WORKTREE="${1:-}"
[[ -n "$WORKTREE" ]] || usage

if [[ ! -d "$WORKTREE" ]]; then
  printf 'worktree path %s does not exist\n' "$WORKTREE" >&2
  exit 64
fi

cd "$WORKTREE"

if command -v uv >/dev/null 2>&1 && [[ -f packages/python_viterbo/pyproject.toml ]]; then
  (cd packages/python_viterbo && uv sync --locked --extra dev)
fi

if command -v npm >/dev/null 2>&1 && [[ -f packages/docs-site/package.json ]]; then
  (cd packages/docs-site && npm install)
fi

if command -v lake >/dev/null 2>&1 && [[ -f packages/lean_viterbo/lakefile.lean ]]; then
  (cd packages/lean_viterbo && lake build || true)
fi

printf 'worktree bootstrap completed for %s\n' "$WORKTREE"
