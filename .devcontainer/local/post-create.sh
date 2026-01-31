#!/usr/bin/env bash
# Local devcontainer post-create setup (Jörn's Ubuntu desktop).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Local devcontainer post-create..."

# Common setup
source "${SCRIPT_DIR}/../scripts/setup-common.sh"

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

# Verify tools
echo "code-tunnel: $(code-tunnel --version 2>/dev/null || echo 'not found')"
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

echo "Local post-create complete."
