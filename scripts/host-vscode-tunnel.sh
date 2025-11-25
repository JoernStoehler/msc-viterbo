#!/usr/bin/env bash
set -euo pipefail

# Launch a VS Code tunnel from the host into the devcontainer.
# Usage: scripts/host-vscode-tunnel.sh [--name my-tunnel] [extra code tunnel args]

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if ! command -v devcontainer >/dev/null 2>&1; then
  echo "devcontainer CLI not found. Install with 'npm i -g @devcontainers/cli' or via VS Code Dev Containers extension." >&2
  exit 1
fi

TUNNEL_NAME="${TUNNEL_NAME:-msc-viterbo}"
CODE_TUNNEL_BIN="${CODE_TUNNEL_BIN:-/usr/local/bin/code-tunnel}"

devcontainer exec --workspace-folder "${REPO_ROOT}" -- "${CODE_TUNNEL_BIN}" tunnel --accept-server-license-terms --name "${TUNNEL_NAME}" "$@"
