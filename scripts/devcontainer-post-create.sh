#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="/workspaces/msc-viterbo"

# Ensure various directories exist and are owned by the non-root user
mkdir -p \
  "${HOME}/.config" \
  "${HOME}/.local" \
  "${HOME}/.cache" \
  "${HOME}/.lake"
sudo chown -R $USER:$USER \
  "${HOME}/.config" \
  "${HOME}/.local" \
  "${HOME}/.cache" \
  "${HOME}/.lake"

# Ensure the /workspaces/worktrees mount exists; fail fast if not
WORKTREES_DIR="/workspaces/worktrees"
if ! mountpoint -q "${WORKTREES_DIR}"; then
  echo "Expected ${WORKTREES_DIR} to be a host bind mount. Check devcontainer mounts." >&2
  exit 1
fi

# Install or update Codex CLI via npm (config and cache are volume-backed)
if command -v npm >/dev/null 2>&1; then
  mkdir -p "${HOME}/.local/bin" "${HOME}/.cache/npm"
  npm config set prefix "${HOME}/.local"
  npm config set cache "${HOME}/.cache/npm"
  npm i -g @openai/codex || true
  npm install -g "${REPO_ROOT}/packages/agentctl"
fi

# Ensure VS Code tunnel CLI is present inside the container
install_code_tunnel() {
  if command -v code-tunnel >/dev/null 2>&1; then
    echo "code-tunnel already installed ($(code-tunnel --version 2>/dev/null || true))"
    return 0
  fi

  local url="https://update.code.visualstudio.com/latest/cli-linux-x64/stable"
  local tmpdir
  tmpdir="$(mktemp -d)"

  echo "Installing VS Code CLI (tunnel) from ${url}"
  curl -fsSL "${url}" -o "${tmpdir}/vscode-cli.tar.gz"
  tar -xzf "${tmpdir}/vscode-cli.tar.gz" -C "${tmpdir}"

  if command -v sudo >/dev/null 2>&1; then
    sudo install -m 0755 "${tmpdir}/code" /usr/local/bin/code-tunnel
  else
    install -m 0755 "${tmpdir}/code" /usr/local/bin/code-tunnel
  fi

  rm -rf "${tmpdir}"
}

install_code_tunnel

echo "Devcontainer post-create setup complete."
