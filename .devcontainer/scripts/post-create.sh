#!/usr/bin/env bash
set -euo pipefail

# Devcontainer lifecycle script: postCreateCommand
# Environment-aware: handles both local and codespace environments.

if [[ ${1:-} == "--help" || ${1:-} == "-h" ]]; then
  cat <<'EOF'
Usage: .devcontainer/scripts/post-create.sh

Devcontainer postCreateCommand lifecycle script.
Called automatically when the container is created.

Environment detection via DEVCONTAINER_ENV:
  - "local": Jörn's Ubuntu desktop with bind mounts
  - "codespace": GitHub Codespaces

Sets up:
  - User directories (~/.config, ~/.local, ~/.cache, etc.)
  - npm prefix/cache configuration
  - GitHub CLI git credential helper
  - [local only] TeX format pre-warming
  - [local only] Worktrees mount verification
  - [codespace only] Background cache warming (optional)
EOF
  exit 0
fi

REPO_ROOT="/workspaces/msc-viterbo"
ENV="${DEVCONTAINER_ENV:-unknown}"

echo "Devcontainer post-create: environment=$ENV"

# -----------------------------------------------------------------------------
# Common setup (both environments)
# -----------------------------------------------------------------------------

# Ensure various directories exist and are owned by the non-root user
sudo mkdir -p \
  "${HOME}/.config" \
  "${HOME}/.local" \
  "${HOME}/.cache"
sudo chown -R "${USER}:${USER}" \
  "${HOME}/.config" \
  "${HOME}/.local" \
  "${HOME}/.cache"

# Configure npm paths
if command -v npm >/dev/null 2>&1; then
  mkdir -p "${HOME}/.local/bin" "${HOME}/.cache/npm"
  npm config set prefix "${HOME}/.local"
  npm config set cache "${HOME}/.cache/npm"
fi

# Configure git credentials via GitHub CLI
if command -v gh >/dev/null 2>&1; then
  gh auth setup-git || true
fi

# -----------------------------------------------------------------------------
# Local-only setup
# -----------------------------------------------------------------------------

if [[ "$ENV" == "local" ]]; then
  # Ensure TeX directories exist
  sudo mkdir -p \
    "${HOME}/.texlive2023" \
    "${HOME}/.texmf-var" \
    "${HOME}/.texmf-config"
  sudo chown -R "${USER}:${USER}" \
    "${HOME}/.texlive2023" \
    "${HOME}/.texmf-var" \
    "${HOME}/.texmf-config"
  mkdir -p "${HOME}/.cache/LaTeXML"

  # Verify worktrees mount exists (required for local env)
  WORKTREES_DIR="/workspaces/worktrees"
  if ! mountpoint -q "${WORKTREES_DIR}"; then
    echo "ERROR: ${WORKTREES_DIR} is not mounted." >&2
    echo "Local devcontainer requires bind mount configured in devcontainer.json." >&2
    echo "Check that /srv/devworktrees/msc-viterbo/worktrees/ exists on host." >&2
    exit 1
  fi

  # VS Code tunnel CLI check
  echo "code-tunnel: $(code-tunnel --version 2>/dev/null || echo 'not found')"

  # Verify LaTeX tooling
  if command -v latexmk >/dev/null 2>&1; then
    echo "latexmk: $(latexmk --version 2>/dev/null | head -1 || echo 'available')"
  else
    echo "WARNING: latexmk not found (TexLive may not be installed)" >&2
  fi

  # Pre-warm TeX formats in user tree if missing
  if [ ! -d "${HOME}/.texlive2023/texmf-var/web2c" ]; then
    echo "Pre-warming TeX formats..."
    TEXMFVAR="${HOME}/.texlive2023/texmf-var" fmtutil-user --all >/dev/null 2>&1 || true
  fi
fi

# -----------------------------------------------------------------------------
# Codespace-only setup
# -----------------------------------------------------------------------------

if [[ "$ENV" == "codespace" ]]; then
  echo "Codespace environment"

  # Verify LaTeX tooling
  if command -v latexmk >/dev/null 2>&1; then
    echo "latexmk: $(latexmk --version 2>/dev/null | head -1 || echo 'available')"
  else
    echo "WARNING: latexmk not found" >&2
  fi
fi

# -----------------------------------------------------------------------------
# Done
# -----------------------------------------------------------------------------

echo "Devcontainer post-create setup complete."
