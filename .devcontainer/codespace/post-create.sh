#!/usr/bin/env bash
# Codespace devcontainer post-create setup.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Codespace devcontainer post-create..."

# Common setup
source "${SCRIPT_DIR}/../scripts/setup-common.sh"

# Verify core tools
echo "rust: $(rustc --version 2>/dev/null || echo 'not found')"
echo "uv: $(uv --version 2>/dev/null || echo 'not found')"
echo "node: $(node --version 2>/dev/null || echo 'not found')"

# Verify LaTeX tooling
if command -v latexmk >/dev/null 2>&1; then
  echo "latexmk: $(latexmk --version 2>/dev/null | head -1 || echo 'available')"
else
  echo "WARNING: latexmk not found (TexLive may not be installed)" >&2
fi

echo "Codespace post-create complete."
