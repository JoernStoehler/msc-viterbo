#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="/workspaces/msc-viterbo"

# Ensure various directories exist and are owned by the non-root user
mkdir -p \
  "${HOME}/.config" \
  "${HOME}/.local" \
  "${HOME}/.cache"
sudo chown -R $USER:$USER \
  "${HOME}/.config" \
  "${HOME}/.local" \
  "${HOME}/.cache"

# Ensure worktrees directory exists (bind-mounted) and is easy to find
WORKTREES_DIR="/var/tmp/msc-viterbo/worktrees"
mkdir -p "${WORKTREES_DIR}"
if [[ ! -L "/workspaces/worktrees" ]]; then
  ln -s "${WORKTREES_DIR}" "/workspaces/worktrees"
fi

# Ensure agentx namespace for this project exists
AGENTX_ROOT="${HOME}/.agentx"
AGENTX_PROJECT_DIR="${AGENTX_ROOT}/msc-viterbo"
mkdir -p "${AGENTX_PROJECT_DIR}"

# Install or update Codex CLI via npm (config and cache are volume-backed)
if command -v npm >/dev/null 2>&1; then
  mkdir -p "${HOME}/.local/bin" "${HOME}/.cache/npm"
  npm config set prefix "${HOME}/.local"
  npm config set cache "${HOME}/.cache/npm"
  npm i -g @openai/codex || true
fi

echo "Devcontainer post-create setup complete."
