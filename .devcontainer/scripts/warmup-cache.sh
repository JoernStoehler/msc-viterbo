#!/usr/bin/env bash
set -euo pipefail

# Background cache warming script for Codespaces.
# Populates Rust and Python dependency caches to speed up first builds.
#
# This script is designed to run in the background during postCreate.
# It does NOT block container startup.
#
# Usage (from post-create.sh):
#   nohup .devcontainer/scripts/warmup-cache.sh >> ~/.cache/warmup.log 2>&1 &

if [[ ${1:-} == "--help" || ${1:-} == "-h" ]]; then
  cat <<'EOF'
Usage: .devcontainer/scripts/warmup-cache.sh

Background cache warming for Codespaces.
Runs cargo fetch/build and uv sync to populate caches.

Designed to run in background (nohup ... &) during container startup.
Progress logged to ~/.cache/warmup.log.

Note: In Codespaces, caches don't persist across rebuilds.
This warmup runs on every container creation.
EOF
  exit 0
fi

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

log() {
  echo "[warmup-cache][$(date -Iseconds)] $*"
}

log "Starting cache warmup..."

# Python dependencies
if [[ -d packages/python_viterbo ]]; then
  log "Warming Python cache (uv sync)..."
  if (cd packages/python_viterbo && uv sync --locked --extra dev); then
    log "Python cache warmed."
  else
    log "WARNING: Python cache warmup failed (non-fatal)."
  fi
fi

# Rust dependencies
if [[ -d packages/rust_viterbo ]]; then
  log "Warming Rust cache (cargo fetch + build)..."
  if cargo fetch --manifest-path packages/rust_viterbo/Cargo.toml; then
    log "Rust fetch complete."
  else
    log "WARNING: Rust fetch failed (non-fatal)."
  fi

  # Debug build to populate target cache
  if cargo build --manifest-path packages/rust_viterbo/Cargo.toml; then
    log "Rust build complete."
  else
    log "WARNING: Rust build failed (non-fatal)."
  fi
fi

log "Cache warmup complete."
