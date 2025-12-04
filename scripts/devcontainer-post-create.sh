#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="/workspaces/msc-viterbo"

# Ensure various directories exist and are owned by the non-root user
# Bind mounts may be root-owned; create them with sudo, fix ownership, then add nested dirs.
sudo mkdir -p \
  "${HOME}/.config" \
  "${HOME}/.local" \
  "${HOME}/.cache" \
  "${HOME}/.texlive2023" \
  "${HOME}/.texmf-var" \
  "${HOME}/.texmf-config"
sudo chown -R "${USER}:${USER}" \
  "${HOME}/.config" \
  "${HOME}/.local" \
  "${HOME}/.cache" \
  "${HOME}/.texlive2023" \
  "${HOME}/.texmf-var" \
  "${HOME}/.texmf-config"
mkdir -p "${HOME}/.cache/LaTeXML"

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
fi

echo "code-tunnel baked into image: $(code-tunnel --version 2>/dev/null || true)"

# Sanity-check LaTeX tooling baked into the image
latexmk --version >/dev/null 2>&1 || true

# Pre-warm TeX formats in user tree if missing (speeds first latexmk run)
if [ ! -d "${HOME}/.texlive2023/texmf-var/web2c" ]; then
  TEXMFVAR="${HOME}/.texlive2023/texmf-var" fmtutil-user --all >/dev/null 2>&1 || true
fi

echo "Devcontainer post-create setup complete."
