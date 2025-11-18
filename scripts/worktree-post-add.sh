#!/usr/bin/env bash
set -euo pipefail

# -----------------------------------------------------------------------------
# worktree-post-add.sh – shared hook after creating a git worktree.
#
# Why it exists:
# - Every worktree starts from scratch (fresh node_modules, uv envs, etc.).
# - Running a small, deterministic setup script keeps agents from repeating
#   the same bootstrapping steps manually.
# - The hook is invoked by scripts/provision-worktree.sh and agentx so every
#   creation path stays consistent.
#
# Maintenance guidelines:
# - Keep commands idempotent and fast; this runs for every new worktree.
# - Gate optional steps on both the required tooling and config files.
# - Prefer sync/verify commands (uv sync --locked) instead of install commands
#   that would mutate lockfiles.
# - When you need additional setup (e.g. npm install for a future package),
#   add it here with a short comment referencing the owning package.
# -----------------------------------------------------------------------------

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 <absolute-path-to-worktree>" >&2
  exit 1
fi

WORKTREE_PATH="$1"
if [[ ! -d "$WORKTREE_PATH" ]]; then
  echo "worktree path $WORKTREE_PATH does not exist" >&2
  exit 1
fi

# Pre-warm the Python environment so pytest and tooling are ready to run.
if command -v uv >/dev/null 2>&1 \
   && [[ -f "$WORKTREE_PATH/packages/python_viterbo/pyproject.toml" ]]; then
  (cd "$WORKTREE_PATH/packages/python_viterbo" && uv sync --locked --extra dev)
fi

# Placeholder for future package hooks. Add more sections above this line.

echo "Post-add hook completed for $WORKTREE_PATH"
