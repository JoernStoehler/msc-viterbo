#!/usr/bin/env bash
set -euo pipefail

# -----------------------------------------------------------------------------
# agentctl-bootstrap-hook.sh
#
# Invoked automatically when AGENTCTL_BOOTSTRAP_HOOK is set to
# `bash scripts/agentctl-bootstrap-hook.sh`. agentctl sets the following env vars
# before running the hook:
#   - AGENTCTL_REPO_ROOT: absolute path to the monorepo root
#   - AGENTCTL_WORKTREE: absolute path to the bootstrapped worktree
#   - AGENTCTL_WORKTREE_BRANCH: branch name checked out in that worktree
#
# Purpose: run the same lightweight setup we use after `git worktree add`
# (uv sync, etc.) without hard-coding commands into the Rust binary.
# Customize this file whenever toolchains change; keep commands idempotent.
# -----------------------------------------------------------------------------

for var in AGENTCTL_REPO_ROOT AGENTCTL_WORKTREE AGENTCTL_WORKTREE_BRANCH; do
  if [[ -z "${!var:-}" ]]; then
    echo "Missing env var $var required by agentctl bootstrap hook" >&2
    exit 1
  fi
done

REPO_ROOT="$AGENTCTL_REPO_ROOT"
WORKTREE_PATH="$AGENTCTL_WORKTREE"

# Pre-warm the Python environment so pytest and tooling are ready to run.
if command -v uv >/dev/null 2>&1 \
   && [[ -f "$WORKTREE_PATH/packages/python_viterbo/pyproject.toml" ]]; then
  (cd "$WORKTREE_PATH/packages/python_viterbo" && uv sync --locked --extra dev)
fi

# Placeholder for additional package-specific hooks (npm install, lake build, …).
# Add commands above this line and keep them idempotent.

echo "agentctl bootstrap hook completed for $WORKTREE_PATH ($AGENTCTL_WORKTREE_BRANCH)"
