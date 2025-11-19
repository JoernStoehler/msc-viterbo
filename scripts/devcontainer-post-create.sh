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

# Ensure the /workspaces/worktrees mount exists; fail fast if not
WORKTREES_DIR="/workspaces/worktrees"
if ! mountpoint -q "${WORKTREES_DIR}"; then
  echo "Expected ${WORKTREES_DIR} to be a host bind mount. Check devcontainer mounts." >&2
  exit 1
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

# Ensure agentctl binary is installed
if command -v cargo >/dev/null 2>&1 && ! command -v agentctl >/dev/null 2>&1; then
  (cd "${REPO_ROOT}/packages/agentctl" && cargo install --locked --path . --root "${HOME}/.local")
fi

echo "Devcontainer post-create setup complete."
