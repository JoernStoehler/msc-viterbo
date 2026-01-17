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

# Ensure the /workspaces/worktrees mount exists; fail fast if not.
WORKTREES_DIR="/workspaces/worktrees"
if ! mountpoint -q "${WORKTREES_DIR}"; then
  echo "ERROR: ${WORKTREES_DIR} is not mounted." >&2
  echo "This devcontainer requires a bind mount configured in devcontainer.json." >&2
  exit 1
fi

# Configure npm paths (config and cache are volume-backed)
if command -v npm >/dev/null 2>&1; then
  mkdir -p "${HOME}/.local/bin" "${HOME}/.cache/npm"
  npm config set prefix "${HOME}/.local"
  npm config set cache "${HOME}/.cache/npm"
fi

# Configure git credentials via GitHub CLI (if available) so pushes work without manual setup.
if command -v gh >/dev/null 2>&1; then
  gh auth setup-git || true
fi

echo "code-tunnel baked into image: $(code-tunnel --version 2>/dev/null || true)"

# Verify LaTeX tooling is available (baked into the devcontainer image)
latexmk --version >/dev/null 2>&1 || true

# Pre-warm TeX formats in user tree if missing (speeds first latexmk run)
if [ ! -d "${HOME}/.texlive2023/texmf-var/web2c" ]; then
  TEXMFVAR="${HOME}/.texlive2023/texmf-var" fmtutil-user --all >/dev/null 2>&1 || true
fi

echo "Devcontainer post-create setup complete."
